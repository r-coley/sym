/*
 * sym.c SVR4 / UnixWare symbol + backtrace 
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <signal.h>
#include <setjmp.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/procfs.h>
#include <libelf.h>
#include <elf.h>
#include <link.h>

#define BASEVADDR	0x08000000

/* ---------- types ---------- */
typedef unsigned long	Addr_t;

typedef struct d1_fname {
	char   *filename;   /* basename or full path if comp_dir known */
	Addr_t  lo_pc;      /* link-time */
	Addr_t  hi_pc;      /* link-time */
	Addr_t  off;        /* offset into .line */
	int     line_idx;   /* start index in d1_lines */
	int     nlines;     /* number of lines for this CU */
} d1_fname_t;

typedef struct d1_lineent {
	Addr_t pc;          /* runtime pc (bias already applied) */
	long  line;
} d1_lineent_t;

typedef struct d1_func {
	Addr_t low_pc;
	Addr_t high_pc;
	int nargs;
} d1_func_t;

typedef struct obj obj_t;
struct obj {
	char	name[256];

	/* relocation / coverage */
	Addr_t  map_base;      /* page-aligned runtime base from link_map */
	Addr_t  bias;          /* runtime_va = bias + linktime_va */
	Addr_t  min_vaddr;     /* lowest PT_LOAD p_vaddr (link-time) */
	Addr_t  max_end;       /* max (p_vaddr+p_memsz) across PT_LOAD */
	Addr_t  lo, hi;        /* runtime coverage [lo,hi) */
	int	has_range;

	int	unnamed;
	int	is_main;
	int	etype;         /* ELF e_type (ET_EXEC/ET_DYN/...) */

	/* symbols */
	Elf32_Sym * symtab;
	int	nsyms;
	char	*strtab;

	Elf32_Sym * dynsym;
	int	ndyn;
	char	*dynstr;

	/* DWARF1 (.debug + .line) raw sections */
	uchar_t *d1_debug;
	size_t		d1_debug_sz;
	uchar_t *d1_line;
	size_t		d1_line_sz;
	/* DWARF1 parsed: compile units + line entries */
	d1_fname_t	*d1_fnames;
	int		d1_nfnames;
	d1_lineent_t	*d1_lines;
	int		d1_nlines;
	int		d1_parsed;
	d1_func_t *d1_funcs;
	int d1_nfuncs;
	int d1_funcs_parsed;

	obj_t  * next;
};

/* ---------- globals ---------- */

static obj_t *g_objs;
static char	g_main_path[256];

extern struct r_debug _r_debug;
extern void	_start();

/* ---------- helpers ---------- */
asm Addr_t get_ebp(void) { movl	%ebp, %eax }

static void *
xmalloc(size_t n)
{
	void	*p;

	if (!(p = malloc(n))) {
		perror("malloc");
		exit(1);
	}
	return p;
}

static void	
xfree(void *p)
{
	if (p) free(p);
}

#ifndef HAVE_STRNLEN
static size_t
strnlen(const char *s, size_t max)
{
	size_t n = 0;
	while (n < max && s[n]) n++;
	return n;
}
#endif

/* ---------- DWARF1 (.debug + .line) minimal line resolver ---------- */

#ifndef FORM_MASK
#define FORM_MASK 0x0f
#endif

/* DWARF1 forms (low nibble) */
#define FORM_ADDR   0x1
#define FORM_REF    0x2
#define FORM_BLOCK2 0x3
#define FORM_BLOCK4 0x4
#define FORM_DATA2  0x5
#define FORM_DATA4  0x6
#define FORM_DATA8  0x7
#define FORM_STRING 0x8

/* DWARF1 tags/attrs we care about */
#define TAG_compile_unit 0x0011
#define TAG_source_file  TAG_compile_unit /* SVR4 compatibility */
#define TAG_subroutine   0x23
#define TAG_formal_param 0x29

/* Note: attributes include the form in the low nibble. */
#define AT_name      (0x0030|FORM_STRING)
#define AT_stmt_list (0x0100|FORM_DATA4)
#define AT_low_pc    (0x0110|FORM_ADDR)
#define AT_high_pc   (0x0120|FORM_ADDR)
#define AT_sibling   (0x0010|FORM_REF)
#define AT_comp_dir  (0x01b0|FORM_STRING)

/* Parser cursor (little-endian) */
static uchar_t *d1_ptr;
static uchar_t *d1_end;

static uchar_t
d1_get_u8(void)
{
	if (d1_ptr >= d1_end) return 0;
	return *d1_ptr++;
}

static ushort_t
d1_get_u16(void)
{
	ushort_t x = 0;
	uchar_t *p = (uchar_t *)&x;
	if (d1_ptr + 2 > d1_end) return 0;
	*p++ = *d1_ptr++;
	*p   = *d1_ptr++;
	return x;
}

static ulong_t
d1_get_u32(void)
{
	ulong_t x = 0;
	uchar_t *p = (uchar_t *)&x;
	if (d1_ptr + 4 > d1_end) return 0;
	*p++ = *d1_ptr++;
	*p++ = *d1_ptr++;
	*p++ = *d1_ptr++;
	*p   = *d1_ptr++;
	return x;
}

static char *
d1_get_cstr(void)
{
	size_t n;
	char *s;
	if (d1_ptr >= d1_end) return NULL;
	n = strnlen((char *)d1_ptr, (size_t)(d1_end - d1_ptr));
	if (d1_ptr + n >= d1_end) return NULL;
	s = (char *)xmalloc(n + 1);
	memcpy(s, d1_ptr, n + 1);
	d1_ptr += n + 1;
	return s;
}

static void
d1_skip_bytes(size_t n)
{
	if (d1_ptr + n > d1_end) d1_ptr = d1_end;
	else d1_ptr += n;
}

static void
d1_skip_form(ushort_t attrname)
{
	/* attrname includes form in low nibble */
	switch (attrname & FORM_MASK) {
	case FORM_ADDR:
	case FORM_REF:
	case FORM_DATA4:
		(void)d1_get_u32();
		break;
	case FORM_DATA2:
		(void)d1_get_u16();
		break;
	case FORM_DATA8:
		d1_skip_bytes(8);
		break;
	case FORM_BLOCK2: {
			ushort_t len = d1_get_u16();
			d1_skip_bytes(len);
		}
		break;
	case FORM_BLOCK4: {
			ulong_t len = d1_get_u32();
			d1_skip_bytes(len);
		}
		break;
	case FORM_STRING: {
			char *s = d1_get_cstr();
			xfree(s);
		}
		break;
	default:
		/* unknown: bail by forcing end */
		d1_ptr = d1_end;
		break;
	}
}

static void
d1_free_parsed(obj_t *o)
{
	int i;
	if (!o) return;
	if (o->d1_fnames) {
		for (i = 0; i < o->d1_nfnames; i++)
			xfree(o->d1_fnames[i].filename);
		xfree(o->d1_fnames);
	}
	xfree(o->d1_lines);
	o->d1_fnames = NULL;
	o->d1_lines = NULL;
	o->d1_nfnames = 0;
	o->d1_nlines = 0;
	o->d1_parsed = 0;
	xfree(o->d1_funcs);
	o->d1_funcs = NULL;
	o->d1_nfuncs = 0;
	o->d1_funcs_parsed = 0;
}

/*
 * Parse a single DWARF1 .line sub-section starting at 'off' and
 * append LINE entries into o->d1_lines (pc already bias-adjusted).
 */
static int
d1_parse_line_sub(obj_t *o, Addr_t off)
{
	ulong_t total_len;
	ulong_t base;
	uchar_t *sub_end;
	int n = 0;

	if (!o || !o->d1_line || o->d1_line_sz < 12) return 0;
	if (off >= (Addr_t)o->d1_line_sz) return 0;

	d1_ptr = o->d1_line + off;
	d1_end = o->d1_line + o->d1_line_sz;

	total_len = d1_get_u32();
	if (total_len < 8) return 0;

	/* DWARF1 layout: [len][base][entries...] */
	base = d1_get_u32();

	sub_end = d1_ptr + (total_len - 8);
	if (sub_end > d1_end) sub_end = d1_end;

	while (d1_ptr < sub_end) {
		Addr_t pc;
		ulong_t line = d1_get_u32();
		ulong_t delta;
		(void)d1_get_u16();               /* column (ignored) */
		delta = d1_get_u32();

		pc = (Addr_t)(base + delta);

		/* bias adjust */
		if (o->etype == ET_DYN) pc += o->bias;

		o->d1_lines = (d1_lineent_t *)realloc(
		    o->d1_lines,
		    (o->d1_nlines + 1) * (int)sizeof(d1_lineent_t));
		if (!o->d1_lines) {
			o->d1_nlines = 0;
			return 0;
		}
		o->d1_lines[o->d1_nlines].pc = pc;
		o->d1_lines[o->d1_nlines].line = (long)line;
		o->d1_nlines++;
		n++;
	}

	return n;
}

static int
d1_cmp_lineent(const void *a, const void *b)
{
	const d1_lineent_t *la = (const d1_lineent_t *)a;
	const d1_lineent_t *lb = (const d1_lineent_t *)b;
	if (la->pc < lb->pc) return -1;
	if (la->pc > lb->pc) return 1;
	return 0;
}

/*
 * Parse DWARF1 .debug for compile units with stmt_list + low/high pc.
 */
static void
d1_parse(obj_t *o)
{
	uchar_t *p, *end;

	if (!o || o->d1_parsed) return;
	o->d1_parsed = 1;

	if (!o->d1_debug || !o->d1_line) return;

	p = o->d1_debug;
	end = o->d1_debug + o->d1_debug_sz;

	while (p + 4 <= end) {
		ulong_t word, length;
		uchar_t *rec_end;
		ushort_t tag;
		int insrc;

		char *name = NULL;
		char *comp_dir = NULL;
		Addr_t low_pc = 0, high_pc = 0, stmt_off = 0;
		int have_stmt = 0;


		ulong_t sib_off = 0;
		int have_sib = 0;
		int nargs = 0;
		d1_ptr = p;
		d1_end = end;

		word = d1_get_u32();

		/* end/padding records */
		if (word <= 8) {
			if (word < 4)
				p += 4;
				else
				p += word;
			continue;
		}

		length = word - 6;
		rec_end = d1_ptr + length;
		if (rec_end > end) break;

		tag = d1_get_u16();
		insrc = (tag == TAG_source_file);

		while (d1_ptr < rec_end) {
			ushort_t attr = d1_get_u16();

			switch(attr) {
			case AT_name: {
				char *s = d1_get_cstr();
				if (s && (int)strlen(s) >= 2 &&
				    strcmp(s + strlen(s) - 2, ".h") == 0) {
					insrc = 0;
				}
				if (insrc) {
					xfree(name);
					name = s;
				} else {
					xfree(s);
				}
				continue;
			    }
			    break;
			case AT_comp_dir: {
				char *s = d1_get_cstr();
				if (insrc) {
					xfree(comp_dir);
					comp_dir = s;
				} else {
					xfree(s);
				}
				continue;
			    }
			    break;
			case AT_stmt_list: {
				stmt_off = (Addr_t)d1_get_u32();
				have_stmt = 1;
				continue;
			    }
			    break;

			case AT_low_pc: {
				low_pc = (Addr_t)d1_get_u32();
				continue;
			    }
			    break;

			case AT_high_pc: {
				high_pc = (Addr_t)d1_get_u32();
				continue;
			    }
			    break;
			}

			d1_skip_form(attr);
		}


		/* commit subroutine args (DWARF1): count TAG_formal_param children until sibling */
		if (tag == TAG_subroutine && have_sib && sib_off > 0 &&
		    sib_off < (ulong_t)o->d1_debug_sz && high_pc >= low_pc) {
			uchar_t *q = rec_end;
			uchar_t *sib = o->d1_debug + sib_off;
			nargs = 0;

			while (q + 4 <= end && q < sib) {
				ulong_t w2, len2;
				uchar_t *re2;
				ushort_t t2;

				d1_ptr = q;
				d1_end = end;

				w2 = d1_get_u32();

				/* padding/end records */
				if (w2 <= 8) {
					if (w2 < 4) q += 4;
					else q += w2;
					continue;
				}

				len2 = w2 - 6;
				re2 = d1_ptr + len2;
				if (re2 > end) break;

				t2 = d1_get_u16();
				if (t2 == TAG_formal_param)
					nargs++;

				q = re2;
			}

			if (o->etype == ET_DYN) {
				low_pc  += o->bias;
				high_pc += o->bias;
			}

			if (low_pc && high_pc > low_pc) {
				d1_func_t *nf = (d1_func_t *)realloc(o->d1_funcs,
				    (o->d1_nfuncs + 1) * (int)sizeof(d1_func_t));
				if (nf) {
					o->d1_funcs = nf;
					o->d1_funcs[o->d1_nfuncs].low_pc = low_pc;
					o->d1_funcs[o->d1_nfuncs].high_pc = high_pc;
					o->d1_funcs[o->d1_nfuncs].nargs = nargs;
					o->d1_nfuncs++;
					o->d1_funcs_parsed = 1;
				}
			}
		}

		/* commit this CU */
		if (insrc && name && have_stmt && high_pc >= low_pc) {
			d1_fname_t cu;
			char pathbuf[512];

			memset(&cu, 0, sizeof(cu));
			cu.lo_pc = low_pc;
			cu.hi_pc = high_pc;
			cu.off = stmt_off;

			if (comp_dir && comp_dir[0] && name[0] && name[0] != '/') {
				sprintf(pathbuf, "%s/%s", comp_dir, name);
				cu.filename = strdup(pathbuf);
			} else {
				cu.filename = strdup(name);
			}

			cu.line_idx = o->d1_nlines;
			cu.nlines = d1_parse_line_sub(o, cu.off);

			if (cu.nlines > 1) {
				qsort(o->d1_lines + cu.line_idx, cu.nlines,
				    sizeof(d1_lineent_t), d1_cmp_lineent);
			}

			o->d1_fnames = (d1_fname_t *)realloc(
			    o->d1_fnames,
			    (o->d1_nfnames + 1) * (int)sizeof(d1_fname_t));
			if (o->d1_fnames) {
				o->d1_fnames[o->d1_nfnames++] = cu;
			} else {
				xfree(cu.filename);
			}
		}

		xfree(name);
		xfree(comp_dir);

		p = rec_end;
	}
}

/*
 * Lookup file:line for runtime PC 'pc' in object 'o'.
 * Returns 1 on success, 0 otherwise.
 */
static int
d1_func_nargs(obj_t *o, Addr_t pc, int *out_nargs)
{
	int i;
	if (!o || !out_nargs) return 0;
	d1_parse(o);
	if (!o->d1_funcs || o->d1_nfuncs <= 0) return 0;
	for (i = 0; i < o->d1_nfuncs; i++) {
		if (pc >= o->d1_funcs[i].low_pc && 
		    pc < o->d1_funcs[i].high_pc) {
			*out_nargs = o->d1_funcs[i].nargs;
			return 1;
		}
	}
	return 0;
}


static int
d1_lookup(obj_t *o, Addr_t pc, const char **file_out, long *line_out)
{
	int i;

	if (!o || !file_out || !line_out) return 0;

	d1_parse(o);

	if (!o->d1_fnames || !o->d1_lines) return 0;

	for (i = 0; i < o->d1_nfnames; i++) {
		Addr_t lo, hi;
		d1_fname_t *cu = &o->d1_fnames[i];

		lo = (o->etype == ET_DYN) ? (cu->lo_pc + o->bias) : cu->lo_pc;
		hi = (o->etype == ET_DYN) ? (cu->hi_pc + o->bias) : cu->hi_pc;

		if (pc < lo || pc > hi)
			continue;

		if (cu->nlines > 0) {
			int l = 0, r = cu->nlines - 1, best = -1;
			d1_lineent_t *base = o->d1_lines + cu->line_idx;

			while (l <= r) {
				int m = (l + r) / 2;
				if (base[m].pc <= pc) {
					best = m;
					l = m + 1;
				} else {
					r = m - 1;
				}
			}

			if (best >= 0) {
				*file_out = cu->filename ? cu->filename : "??";
				*line_out = base[best].line;
				return 1;
			}
		}

		*file_out = cu->filename ? cu->filename : "??";
		*line_out = 0;
		return 1;
	}

	return 0;
}

void
sym_set_main_path(const char *p)
{
	if (!p || !p[0]) {
		g_main_path[0] = 0;
		return;
	}
	strncpy(g_main_path, p, sizeof(g_main_path) - 1);
	g_main_path[sizeof(g_main_path) - 1] = 0;
}

/* ---------- proc/link_map -> object list ---------- */
static obj_t *
rld_build(void)
{
	struct link_map *lm;
	obj_t *head, **tail;
	Addr_t pagesz;

	head = NULL;
	tail = &head;

	pagesz = (Addr_t)sysconf(_SC_PAGESIZE);
	if (pagesz == 0) pagesz = 4096;

	lm = _r_debug.r_map;
	while (lm) {
		obj_t * o;

		o = (obj_t * )calloc(1, sizeof(*o));
		if (!o) break;

		o->map_base = ((Addr_t)lm->l_addr) & ~(pagesz - 1);

		if (!lm->l_name || !*(char *)lm->l_name) {
			strcpy(o->name, "<anon>");
			o->unnamed = 1;
		} else {
			strncpy(o->name, (char *)lm->l_name, sizeof(o->name)-1);
			o->name[sizeof(o->name) - 1] = 0;
			o->unnamed = 0;
		}
		*tail = o;
		tail = &o->next;
		lm = lm->l_next;
	}

	return head;
}

/* ---------- ELF load (symbols + PT_LOAD min/max) ---------- */

static void	
obj_clear_symbols(obj_t *o)
{
	/* DWARF1 cached parse + raw sections */
	d1_free_parsed(o);
	xfree(o->d1_debug); 
	o->d1_debug = NULL; 
	o->d1_debug_sz = 0;
	xfree(o->d1_line);  
	o->d1_line  = NULL; 
	o->d1_line_sz  = 0;

	xfree(o->symtab);
	o->symtab = NULL;
	o->nsyms = 0;
	xfree(o->strtab);
	o->strtab = NULL;

	xfree(o->dynsym);
	o->dynsym = NULL;
	o->ndyn = 0;
	xfree(o->dynstr);
	o->dynstr = NULL;
}

static void	
obj_load_elf(obj_t *o)
{
	Elf 	*e;
	Elf32_Ehdr * eh;
	Elf32_Phdr * ph;
	Elf_Scn *scn;
	int	have_pt, fd, i;
	size_t	shstrndx;
	Addr_t min_vaddr, max_end;

	/* allow relative (main exe often ./sym) */
	if ((fd = open(o->name, O_RDONLY)) == -1) return;

	if (elf_version(EV_CURRENT) == EV_NONE) {
		close(fd);
		return;
	}

	if (!(e = elf_begin(fd, ELF_C_READ, NULL))) {
		close(fd);
		return;
	}

	if (!(eh = elf32_getehdr(e))) {
		elf_end(e);
		close(fd);
		return;
	}

	/* record ELF type so we can apply load-bias correctly */
	o->etype = (int)eh->e_type;

	/* section header string table index (UnixWare 1.0: use ehdr) */
	shstrndx = (size_t)eh->e_shstrndx;

	/* program headers -> PT_LOAD min/max */
	have_pt = 0;
	min_vaddr = 0;
	max_end = 0;

	ph = elf32_getphdr(e);
	if (ph) {
		for (i = 0; i < (int)eh->e_phnum; i++) {
			Addr_t vend;

			if (ph[i].p_type != PT_LOAD) continue;

			if (!have_pt || (Addr_t)ph[i].p_vaddr < min_vaddr)
				min_vaddr = (Addr_t)ph[i].p_vaddr;

			vend = (Addr_t)ph[i].p_vaddr + (Addr_t)ph[i].p_memsz;
			if (!have_pt || vend > max_end)
				max_end = vend;

			have_pt = 1;
		}
	}

	if (have_pt) {
		o->min_vaddr = min_vaddr;
		o->max_end = max_end;

		/*
		 * Load bias rules:
		 *  - ET_DYN: runtime_va = st_value + bias, where 
		 *    bias ~= map_base - min_vaddr
		 *  - ET_EXEC: st_value is already an absolute VA at 
		 * runtime (non-PIE)
		 */
		o->bias = (o->etype == ET_DYN) ? o->map_base - o->min_vaddr : 0;

		o->lo = o->bias + o->min_vaddr;
		o->hi = o->bias + o->max_end;
		o->has_range = 1;
	}

	/* (re)load symbols */
	obj_clear_symbols(o);

	scn = NULL;
	while ((scn = elf_nextscn(e, scn)) != NULL) {
		Elf32_Shdr * sh;
		Elf_Data * d;
		const char *sname;

		if (!(sh = elf32_getshdr(scn))) continue;

		d = elf_getdata(scn, NULL);
		if (!d || !d->d_buf) continue;

		sname = elf_strptr(e, shstrndx, sh->sh_name);
		if (sname) {
			if (strcmp(sname, ".debug") == 0) {
				o->d1_debug = (uchar_t *)xmalloc(sh->sh_size);
				memcpy(o->d1_debug, d->d_buf, sh->sh_size);
				o->d1_debug_sz = (size_t)sh->sh_size;
			}
			if (strcmp(sname, ".line") == 0) {
				o->d1_line = (uchar_t *)xmalloc(sh->sh_size);
				memcpy(o->d1_line, d->d_buf, sh->sh_size);
				o->d1_line_sz = (size_t)sh->sh_size;
			}
		}
		if (sh->sh_type == SHT_SYMTAB) {
			Elf_Scn * s;
			Elf32_Shdr * sh2;
			Elf_Data * d2;

			o->symtab = (Elf32_Sym * )xmalloc(sh->sh_size);
			memcpy(o->symtab, d->d_buf, sh->sh_size);
			o->nsyms = (int)(sh->sh_size / sh->sh_entsize);

			if (s = elf_getscn(e, sh->sh_link)) {
				sh2 = elf32_getshdr(s);
				d2 = elf_getdata(s, NULL);
				if (sh2 && d2 && d2->d_buf) {
					o->strtab = 
					    (char *)xmalloc(sh2->sh_size);
					memcpy(o->strtab, 
					    d2->d_buf, sh2->sh_size);
				}
			}
		}

		if (sh->sh_type == SHT_DYNSYM) {
			Elf_Scn *s;
			Elf32_Shdr *sh2;
			Elf_Data *d2;

			o->dynsym = (Elf32_Sym * )xmalloc(sh->sh_size);
			memcpy(o->dynsym, d->d_buf, sh->sh_size);
			o->ndyn = (int)(sh->sh_size / sh->sh_entsize);

			if (s = elf_getscn(e, sh->sh_link)) {
				sh2 = elf32_getshdr(s);
				d2 = elf_getdata(s, NULL);
				if (sh2 && d2 && d2->d_buf) {
					o->dynstr = 
					    (char *)xmalloc(sh2->sh_size);
					memcpy(o->dynstr, 
					    d2->d_buf, sh2->sh_size);
				}
			}
		}
	}
	elf_end(e);
	close(fd);
}

/*
 * Identify the main executable:
 *  - iterate unnamed link_map entries
 *  - temporarily set name = g_main_path
 *  - load ELF and accept it if PT_LOAD min_vaddr looks executable-like
 *  - then anchor bias using runtime &_start:
 *      bias = &_start - min_vaddr
 */
static void	
identify_and_load_main(void)
{
	obj_t 	*o;
	char	oldname[256];

	if (!g_main_path[0]) return;

	for (o = g_objs; o; o = o->next) {
		if (!o->unnamed) continue;

		/* save old name */
		strncpy(oldname, o->name, sizeof(oldname) - 1);
		oldname[sizeof(oldname) - 1] = 0;

		/* try as main */
		strncpy(o->name, g_main_path, sizeof(o->name) - 1);
		o->name[sizeof(o->name) - 1] = 0;

		obj_load_elf(o);

		if (o->has_range && o->min_vaddr >= (Addr_t)BASEVADDR) {
			o->is_main = 1;

			/*
			 * Only PIE executables (ET_DYN) need anchoring.
			 * Non-PIE ET_EXEC already uses absolute VAs.
			 */
			o->bias = (o->etype == ET_DYN)
			    ? (Addr_t)(void *) &_start - o->min_vaddr : 0;

			o->lo   = o->bias + o->min_vaddr;
			o->hi   = o->bias + o->max_end;
			o->has_range = 1;
			return;
		}

		/* restore name if not accepted */
		strncpy(o->name, oldname, sizeof(o->name) - 1);
		o->name[sizeof(o->name) - 1] = 0;
	}
}

int
sym_rld_refresh(void)
{
	obj_t	*o, *n;

	/* free old */
	o = g_objs;
	while (o) {
		n = o->next;
		obj_clear_symbols(o);
		free(o);
		o = n;
	}
	g_objs = NULL;

	g_objs = rld_build();

	/* load ELF for objects with real names first */
	for (o = g_objs; o; o = o->next) {
		if (!o->unnamed)
			obj_load_elf(o);
	}

	/* then identify + load main executable */
	identify_and_load_main();

	return g_objs ? 0 : -1;
}

/* -------- name -> VA (prefer DSOs first, avoid SHN_UNDEF stubs) -------- */

static int	
sym_is_func(const Elf32_Sym *s)
{
	int	t = ELF32_ST_TYPE(s->st_info);
	return (t == STT_FUNC);
}

Addr_t
sym_resolve_global(const char *name)
{
	int	pass;
	obj_t 	*o;

	if (!name || !name[0]) return (Addr_t)0;

	/* pass 0: DSOs (not main), pass 1: main */
	for (pass = 0; pass < 2; pass++) {
		for (o = g_objs; o; o = o->next) {
			int	i;

			if (pass == 0 && o->is_main) continue;
			if (pass == 1 && !o->is_main) continue;

			/* prefer real funcs from symtab */
			if (o->symtab && o->strtab) {
				for (i = 0; i < o->nsyms; i++) {
					Elf32_Sym * s;
					const char	*n;
					Addr_t va;

					s = &o->symtab[i];
					if (s->st_shndx == SHN_UNDEF) continue;
					if (s->st_name == 0) continue;
					if (!sym_is_func(s)) continue;

					n = o->strtab + s->st_name;
					if (!n || !n[0]) continue;
					if (strcmp(n, name) != 0) continue;

					va = ((o->etype==ET_DYN) ? o->bias : 0);
					va += (Addr_t)s->st_value;
					return va;
				}
			}

			/* then dynsym */
			if (o->dynsym && o->dynstr) {
				for (i = 0; i < o->ndyn; i++) {
					Elf32_Sym * s;
					const char	*n;
					Addr_t va;

					s = &o->dynsym[i];
					if (s->st_shndx == SHN_UNDEF) continue;
					if (s->st_name == 0) continue;
					if (!sym_is_func(s)) continue;

					n = o->dynstr + s->st_name;
					if (!n || !n[0]) continue;
					if (strcmp(n, name) != 0) continue;

					va = (o->etype == ET_DYN) ? o->bias : 0;
					va += (Addr_t)s->st_value;
					return va;
				}
			}
		}
	}
	return (Addr_t)0;
}

/* ---------- VA -> symbol (closest STT_FUNC, smallest delta) ---------- */

static int	
in_range(obj_t *o, Addr_t a)
{
	return (o->has_range && a >= o->lo && a < o->hi);
}

static void	
scan_table_best(obj_t *o, Addr_t va, Elf32_Sym *tab, int nsyms, const char *strs, int want_func, const char *where, const char **bestn, Addr_t *best_sva, Addr_t *best_delta, int *best_is_func)
{
	int	i;

	/* Never let non-FUNC symbols override an already-selected FUNC. */
	if (!want_func && best_is_func && *best_is_func) return;

	if (!tab || !strs) return;

	for (i = 0; i < nsyms; i++) {
		Elf32_Sym * s;
		const char	*n;
		Addr_t sva;
		Addr_t delta;
		int	t;

		s = &tab[i];
		if (s->st_shndx == SHN_UNDEF) continue;
		if (s->st_name == 0) continue;

		t = ELF32_ST_TYPE(s->st_info);
		if (want_func && t != STT_FUNC) continue;

		sva = (Addr_t)s->st_value + ((o->etype == ET_DYN) ? o->bias : 0);
		if (sva > va) continue;

		delta = va - sva;

		n = strs + s->st_name;
		if (!n || !n[0]) continue;

		if (delta < *best_delta) {
			*best_delta = delta;
			*best_sva = sva;
			*bestn = n;
			if (best_is_func)
				*best_is_func = (t == STT_FUNC);
		}
	}
}

int
sym_addr_to_symbol(Addr_t va, char *buf, size_t bufsz)
{
	obj_t 	*o, *besto;
	const char	*bestn;
	Addr_t best_sva, best_delta;
	int	best_is_func;

	/* init */
	besto = NULL;
	bestn = NULL;
	best_sva = 0;
	best_delta = (Addr_t)0xffffffffUL;
	best_is_func = 0;

	/* 1) Owning object first */
	for (o = g_objs; o; o = o->next) {
		if (!in_range(o, va)) continue;

		/* Prefer STT_FUNC first */
		scan_table_best(o, va, o->symtab, o->nsyms, o->strtab, 
				1, "symtab(func)", &bestn, &best_sva, 
				&best_delta, &best_is_func);

		scan_table_best(o, va, o->dynsym, o->ndyn, o->dynstr, 
				1, "dynsym(func)", &bestn, &best_sva, 
				&best_delta, &best_is_func);

		/* If nothing, allow STT_NOTYPE/etc as fallback inside same object */
		if (!bestn) {
			scan_table_best(o, va, o->symtab, o->nsyms, o->strtab, 
					0, "symtab(any)", &bestn, &best_sva, 
					&best_delta, &best_is_func);

			scan_table_best(o, va, o->dynsym, o->ndyn, o->dynstr, 
					0, "dynsym(any)", &bestn, &best_sva, 
					&best_delta, &best_is_func);
		}

		if (bestn) {
			besto = o;
			break;
		}
	}

	/* 2) Fallback: scan all objects (bounded) */
	if (!bestn) {
		Addr_t bound;

		bound = (Addr_t)0x200000; /* 2MB */

		for (o = g_objs; o; o = o->next) {
			Addr_t before;
			const char	*n0;
			Addr_t sva0;
			Addr_t d0;
			int	is_func0;

			if (!o->has_range)  continue;

			/*
			 * quick bound: only consider symbols not too far 
			 * away unless object claims ownership 
			 */
			before = 0;
			n0 = NULL;
			sva0 = 0;
			d0 = best_delta;
			is_func0 = 0;

			/* try STT_FUNC first */
			scan_table_best(o, va, o->symtab, o->nsyms, o->strtab, 
					1, "symtab(func)", &n0, &sva0, 
					&d0, &is_func0);

			scan_table_best(o, va, o->dynsym, o->ndyn, o->dynstr, 
					1, "dynsym(func)", &n0, &sva0, 
					&d0, &is_func0);

			if (n0 && d0 < best_delta) {
				if (in_range(o, va) || d0 < bound) {
					best_delta = d0;
					best_sva = sva0;
					bestn = n0;
					besto = o;
				}
			}
		}
	}

	if (!bestn || !besto) {
		sprintf(buf, "0x%08lx", (ulong_t)va);
		(void)bufsz;
		return - 1;
	}

	sprintf(buf, "%s:%s+0x%lx",
	    besto->name, bestn, (ulong_t)(va - best_sva));
	(void)bufsz;
	return 0;
}

/* ---------- safe memory reads for self unwind ---------- */

static sigjmp_buf g_segv_jmp;
static void	(*g_old_segv)(int);

static void	
sym_segv_handler(int sig)
{
	(void)sig;
	siglongjmp(g_segv_jmp, 1);
}

static int	
safe_memcpy(void *dst, const void *src, size_t len)
{
	g_old_segv = signal(SIGSEGV, sym_segv_handler);
	if (sigsetjmp(g_segv_jmp, 1) != 0) {
		(void)signal(SIGSEGV, g_old_segv);
		return -1;
	}
	memcpy(dst, src, len);
	(void)signal(SIGSEGV, g_old_segv);
	return 0;
}

static int	
safe_read_addr(Addr_t addr, Addr_t *out)
{
	Addr_t tmp;

	if (safe_memcpy(&tmp, (const void *)addr, sizeof(tmp)) < 0) return - 1;
	*out = tmp;
	return 0;
}

static int	
frame_sane(Addr_t ebp, Addr_t next_ebp)
{
	if (next_ebp == 0) return 0;
	if (next_ebp <= ebp) return 0;
	if ((next_ebp - ebp) > (Addr_t)0x100000) return 0;
	if ((next_ebp & 0x3) != 0) return 0;
	return 1;
}

/* sym_backtrace() output control flags */
#define BT_F_ARGS 0x0001u   /* include (a0,a1,a2) */
#define BT_F_ESP  0x0002u   /* include esp=0x... */
#define BT_F_FILE 0x0004u   /* include file:line (DWARF1 .debug/.line) */

/*
 * Backtrace:
 *  - walk EBP chain collecting return PCs
 *  - print oldest->newest
 *  - then append "sym_backtrace" explicitly
 */
static int
sym_backtrace(int max_depth, int no_args, unsigned flags)
{
	Addr_t ebp, next_ebp, ret, self;
	Addr_t pcs_local[64];
	Addr_t fps_local[64];
	int	limit, n, depth;
	char	sbuf[256];
	enum { 
		BT_SYM_WIDTH = 20 
	};

	sym_rld_refresh();
	ebp = get_ebp(); /* must be first executable work */
	if (ebp == 0) {
		printf("backtrace: cannot obtain EBP\n");
		return 0;
	}

	limit = max_depth;
	if (limit < 0) limit = 0;
	if (limit > (int)(sizeof(pcs_local) / sizeof(pcs_local[0])))
		limit = (int)(sizeof(pcs_local) / sizeof(pcs_local[0]));

	n = 0;
	for (depth = 0; depth < limit; depth++) {
		if (safe_read_addr(ebp + (Addr_t)0, &next_ebp) < 0) break;
		if (safe_read_addr(ebp + (Addr_t)4, &ret) < 0) break;
		if (ret == 0) break;

		pcs_local[n] = ret;
		fps_local[n] = ebp;
		n++;

		if (!frame_sane(ebp, next_ebp)) break;
		ebp = next_ebp;
	}

	/* print oldest->newest */
	for (depth = n - 1; depth >= 0; depth--) {
		const char *symp = "Unknown";
		const char *c;
		Addr_t fp, esp, a0, a1, a2;
		char a0s[16], a1s[16], a2s[16];

		fp = fps_local[depth];
		esp = fp + (Addr_t)8;

		/* default arg strings (used only if BT_F_ARGS is set) */
		strcpy(a0s, "????????");
		strcpy(a1s, "????????");
		strcpy(a2s, "????????");
		if (flags & BT_F_ARGS) {
			if (safe_read_addr(esp + (Addr_t)0, &a0) == 0)
				sprintf(a0s, "0x%08lx", (ulong_t)a0);
			if (safe_read_addr(esp + (Addr_t)4, &a1) == 0)
				sprintf(a1s, "0x%08lx", (ulong_t)a1);
			if (safe_read_addr(esp + (Addr_t)8, &a2) == 0)
				sprintf(a2s, "0x%08lx", (ulong_t)a2);
		}

		if (sym_addr_to_symbol(pcs_local[depth], sbuf, sizeof(sbuf)) == 0) {
			symp = sbuf;
			c = strchr(sbuf, ':');
			if (c) symp = c + 1; /* strip "obj:" prefix */
		}

		{
			char symcol[BT_SYM_WIDTH + 1];
			sprintf(symcol, "%-*.*s", BT_SYM_WIDTH, BT_SYM_WIDTH, symp);

			printf("%-2d %s", (n - 1) - depth, symcol);
		
			/*
			 * Resolve owning object once for this PC 
			 * (used by args + file:line) 
			 */
			{
				obj_t *oo;
				Addr_t pc = pcs_local[depth];

				for (oo = g_objs; oo; oo = oo->next) {
					if (!oo->has_range) continue;
					if (pc >= oo->lo && pc < oo->hi) break;
				}

				if (flags & BT_F_ARGS) {
					int want = 2, dn = 0;
					if (oo && d1_func_nargs(oo, pc, &dn)) {
						if (dn < 0) dn = 0;
						if (dn < want) want = dn;
					}
					printf("(");
					if (want >= 1) printf("%s", a0s);
					if (want >= 2) printf(",%s", a1s);
					if (want >= 3) printf(",%s", a2s);
					printf(")");
				}

				if (flags & BT_F_ESP)
					printf("  esp=0x%08lx", (ulong_t)esp);

				if (flags & BT_F_FILE) {
					const char *df = NULL;
					long dl = 0;
					if (oo && d1_lookup(oo, pc, &df, &dl))
						printf("  %s:%ld\n", 
							df ? df : "??", dl);
					else
						printf("  ??:0\n");
				} else {
					printf("\n");
				}
			}

			/* end per-frame */
		}

		/* C89: depth is signed int; break safely at 0 */
		if (depth == 0) break;
	}
	printf("\n");
	return n;
}

void
sym_print_maps(void)
{
	obj_t 	*o;
	int 	idx;

	if (!g_objs) {
		printf("(no objects loaded)\n");
		return;
	}

	printf("Idx %-10s %-10s %-10s %-10s Flg Name\n",
	    "Lo", "Hi", "Map_Base", "Bias");
	printf("--- ---------- ---------- ---------- ---------- --- ----\n");

	idx = 0;
	for (o = g_objs; o; o = o->next, idx++) {
		char 	flags[8];
		int 	fi = 0;

		if (o->is_main) flags[fi++] = 'M';
		if (o->unnamed) flags[fi++] = 'U';
		flags[fi] = 0;

		if (o->has_range) {
			printf("%3d 0x%08lx 0x%08lx 0x%08lx 0x%08lx %-3s %s\n",
			    idx,
			    (ulong_t)o->lo,
			    (ulong_t)o->hi,
			    (ulong_t)o->map_base,
			    (ulong_t)o->bias,
			    flags,
			    o->name);
		} else {
			printf("%5d  %-10s %-10s 0x%08lx 0x%08lx  %-5s  %s\n",
			    idx,
			    "?", "?",
			    (ulong_t)o->map_base,
			    (ulong_t)o->bias,
			    flags,
			    o->name);
		}
	}
}

/* ---------- TEST harness ---------- */

#ifdef TEST
static void	
bt_leaf(void)
{
	(void)sym_backtrace(32, 2, BT_F_ARGS | BT_F_FILE);
}

static void	
bt_mid(void)
{
	bt_leaf();
}

int
main(int argc, char **argv)
{
	char	b[256];
	Addr_t 	va;
	int	n;

	if (argc > 0)
		sym_set_main_path(argv[0]);

	(void)sym_rld_refresh();

	va = sym_resolve_global("printf");
	n = sym_addr_to_symbol(va, b, sizeof(b));
	printf("printf:  va=%lx lookup=%d %s\n\n", va, n, b);

	bt_mid();
	sym_print_maps();
	return 0;
}
#endif
