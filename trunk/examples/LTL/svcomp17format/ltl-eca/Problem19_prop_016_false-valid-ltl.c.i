
typedef long unsigned int size_t;
typedef unsigned char __u_char;
typedef unsigned short int __u_short;
typedef unsigned int __u_int;
typedef unsigned long int __u_long;
typedef signed char __int8_t;
typedef unsigned char __uint8_t;
typedef signed short int __int16_t;
typedef unsigned short int __uint16_t;
typedef signed int __int32_t;
typedef unsigned int __uint32_t;
typedef signed long int __int64_t;
typedef unsigned long int __uint64_t;
typedef long int __quad_t;
typedef unsigned long int __u_quad_t;
typedef unsigned long int __dev_t;
typedef unsigned int __uid_t;
typedef unsigned int __gid_t;
typedef unsigned long int __ino_t;
typedef unsigned long int __ino64_t;
typedef unsigned int __mode_t;
typedef unsigned long int __nlink_t;
typedef long int __off_t;
typedef long int __off64_t;
typedef int __pid_t;
typedef struct { int __val[2]; } __fsid_t;
typedef long int __clock_t;
typedef unsigned long int __rlim_t;
typedef unsigned long int __rlim64_t;
typedef unsigned int __id_t;
typedef long int __time_t;
typedef unsigned int __useconds_t;
typedef long int __suseconds_t;
typedef int __daddr_t;
typedef int __key_t;
typedef int __clockid_t;
typedef void * __timer_t;
typedef long int __blksize_t;
typedef long int __blkcnt_t;
typedef long int __blkcnt64_t;
typedef unsigned long int __fsblkcnt_t;
typedef unsigned long int __fsblkcnt64_t;
typedef unsigned long int __fsfilcnt_t;
typedef unsigned long int __fsfilcnt64_t;
typedef long int __fsword_t;
typedef long int __ssize_t;
typedef long int __syscall_slong_t;
typedef unsigned long int __syscall_ulong_t;
typedef __off64_t __loff_t;
typedef __quad_t *__qaddr_t;
typedef char *__caddr_t;
typedef long int __intptr_t;
typedef unsigned int __socklen_t;
struct _IO_FILE;

typedef struct _IO_FILE FILE;


typedef struct _IO_FILE __FILE;
typedef struct
{
  int __count;
  union
  {
    unsigned int __wch;
    char __wchb[4];
  } __value;
} __mbstate_t;
typedef struct
{
  __off_t __pos;
  __mbstate_t __state;
} _G_fpos_t;
typedef struct
{
  __off64_t __pos;
  __mbstate_t __state;
} _G_fpos64_t;
typedef __builtin_va_list __gnuc_va_list;
struct _IO_jump_t; struct _IO_FILE;
typedef void _IO_lock_t;
struct _IO_marker {
  struct _IO_marker *_next;
  struct _IO_FILE *_sbuf;
  int _pos;
};
enum __codecvt_result
{
  __codecvt_ok,
  __codecvt_partial,
  __codecvt_error,
  __codecvt_noconv
};
struct _IO_FILE {
  int _flags;
  char* _IO_read_ptr;
  char* _IO_read_end;
  char* _IO_read_base;
  char* _IO_write_base;
  char* _IO_write_ptr;
  char* _IO_write_end;
  char* _IO_buf_base;
  char* _IO_buf_end;
  char *_IO_save_base;
  char *_IO_backup_base;
  char *_IO_save_end;
  struct _IO_marker *_markers;
  struct _IO_FILE *_chain;
  int _fileno;
  int _flags2;
  __off_t _old_offset;
  unsigned short _cur_column;
  signed char _vtable_offset;
  char _shortbuf[1];
  _IO_lock_t *_lock;
  __off64_t _offset;
  void *__pad1;
  void *__pad2;
  void *__pad3;
  void *__pad4;
  size_t __pad5;
  int _mode;
  char _unused2[15 * sizeof (int) - 4 * sizeof (void *) - sizeof (size_t)];
};
typedef struct _IO_FILE _IO_FILE;
struct _IO_FILE_plus;
extern struct _IO_FILE_plus _IO_2_1_stdin_;
extern struct _IO_FILE_plus _IO_2_1_stdout_;
extern struct _IO_FILE_plus _IO_2_1_stderr_;
typedef __ssize_t __io_read_fn (void *__cookie, char *__buf, size_t __nbytes);
typedef __ssize_t __io_write_fn (void *__cookie, const char *__buf,
     size_t __n);
typedef int __io_seek_fn (void *__cookie, __off64_t *__pos, int __w);
typedef int __io_close_fn (void *__cookie);
extern int __underflow (_IO_FILE *);
extern int __uflow (_IO_FILE *);
extern int __overflow (_IO_FILE *, int);
extern int _IO_getc (_IO_FILE *__fp);
extern int _IO_putc (int __c, _IO_FILE *__fp);
extern int _IO_feof (_IO_FILE *__fp) __attribute__ ((__nothrow__ , __leaf__));
extern int _IO_ferror (_IO_FILE *__fp) __attribute__ ((__nothrow__ , __leaf__));
extern int _IO_peekc_locked (_IO_FILE *__fp);
extern void _IO_flockfile (_IO_FILE *) __attribute__ ((__nothrow__ , __leaf__));
extern void _IO_funlockfile (_IO_FILE *) __attribute__ ((__nothrow__ , __leaf__));
extern int _IO_ftrylockfile (_IO_FILE *) __attribute__ ((__nothrow__ , __leaf__));
extern int _IO_vfscanf (_IO_FILE * __restrict, const char * __restrict,
   __gnuc_va_list, int *__restrict);
extern int _IO_vfprintf (_IO_FILE *__restrict, const char *__restrict,
    __gnuc_va_list);
extern __ssize_t _IO_padn (_IO_FILE *, int, __ssize_t);
extern size_t _IO_sgetn (_IO_FILE *, void *, size_t);
extern __off64_t _IO_seekoff (_IO_FILE *, __off64_t, int, int);
extern __off64_t _IO_seekpos (_IO_FILE *, __off64_t, int);
extern void _IO_free_backup_area (_IO_FILE *) __attribute__ ((__nothrow__ , __leaf__));
typedef __gnuc_va_list va_list;
typedef __off_t off_t;
typedef __ssize_t ssize_t;

typedef _G_fpos_t fpos_t;

extern struct _IO_FILE *stdin;
extern struct _IO_FILE *stdout;
extern struct _IO_FILE *stderr;

extern int remove (const char *__filename) __attribute__ ((__nothrow__ , __leaf__));
extern int rename (const char *__old, const char *__new) __attribute__ ((__nothrow__ , __leaf__));

extern int renameat (int __oldfd, const char *__old, int __newfd,
       const char *__new) __attribute__ ((__nothrow__ , __leaf__));

extern FILE *tmpfile (void) ;
extern char *tmpnam (char *__s) __attribute__ ((__nothrow__ , __leaf__)) ;

extern char *tmpnam_r (char *__s) __attribute__ ((__nothrow__ , __leaf__)) ;
extern char *tempnam (const char *__dir, const char *__pfx)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) ;

extern int fclose (FILE *__stream);
extern int fflush (FILE *__stream);

extern int fflush_unlocked (FILE *__stream);

extern FILE *fopen (const char *__restrict __filename,
      const char *__restrict __modes) ;
extern FILE *freopen (const char *__restrict __filename,
        const char *__restrict __modes,
        FILE *__restrict __stream) ;

extern FILE *fdopen (int __fd, const char *__modes) __attribute__ ((__nothrow__ , __leaf__)) ;
extern FILE *fmemopen (void *__s, size_t __len, const char *__modes)
  __attribute__ ((__nothrow__ , __leaf__)) ;
extern FILE *open_memstream (char **__bufloc, size_t *__sizeloc) __attribute__ ((__nothrow__ , __leaf__)) ;

extern void setbuf (FILE *__restrict __stream, char *__restrict __buf) __attribute__ ((__nothrow__ , __leaf__));
extern int setvbuf (FILE *__restrict __stream, char *__restrict __buf,
      int __modes, size_t __n) __attribute__ ((__nothrow__ , __leaf__));

extern void setbuffer (FILE *__restrict __stream, char *__restrict __buf,
         size_t __size) __attribute__ ((__nothrow__ , __leaf__));
extern void setlinebuf (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__));

extern int fprintf (FILE *__restrict __stream,
      const char *__restrict __format, ...);
extern int printf (const char *__restrict __format, ...);
extern int sprintf (char *__restrict __s,
      const char *__restrict __format, ...) __attribute__ ((__nothrow__));
extern int vfprintf (FILE *__restrict __s, const char *__restrict __format,
       __gnuc_va_list __arg);
extern int vprintf (const char *__restrict __format, __gnuc_va_list __arg);
extern int vsprintf (char *__restrict __s, const char *__restrict __format,
       __gnuc_va_list __arg) __attribute__ ((__nothrow__));


extern int snprintf (char *__restrict __s, size_t __maxlen,
       const char *__restrict __format, ...)
     __attribute__ ((__nothrow__)) __attribute__ ((__format__ (__printf__, 3, 4)));
extern int vsnprintf (char *__restrict __s, size_t __maxlen,
        const char *__restrict __format, __gnuc_va_list __arg)
     __attribute__ ((__nothrow__)) __attribute__ ((__format__ (__printf__, 3, 0)));

extern int vdprintf (int __fd, const char *__restrict __fmt,
       __gnuc_va_list __arg)
     __attribute__ ((__format__ (__printf__, 2, 0)));
extern int dprintf (int __fd, const char *__restrict __fmt, ...)
     __attribute__ ((__format__ (__printf__, 2, 3)));

extern int fscanf (FILE *__restrict __stream,
     const char *__restrict __format, ...) ;
extern int scanf (const char *__restrict __format, ...) ;
extern int sscanf (const char *__restrict __s,
     const char *__restrict __format, ...) __attribute__ ((__nothrow__ , __leaf__));
extern int fscanf (FILE *__restrict __stream, const char *__restrict __format, ...) __asm__ ("" "__isoc99_fscanf") ;
extern int scanf (const char *__restrict __format, ...) __asm__ ("" "__isoc99_scanf") ;
extern int sscanf (const char *__restrict __s, const char *__restrict __format, ...) __asm__ ("" "__isoc99_sscanf") __attribute__ ((__nothrow__ , __leaf__));


extern int vfscanf (FILE *__restrict __s, const char *__restrict __format,
      __gnuc_va_list __arg)
     __attribute__ ((__format__ (__scanf__, 2, 0))) ;
extern int vscanf (const char *__restrict __format, __gnuc_va_list __arg)
     __attribute__ ((__format__ (__scanf__, 1, 0))) ;
extern int vsscanf (const char *__restrict __s,
      const char *__restrict __format, __gnuc_va_list __arg)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__format__ (__scanf__, 2, 0)));
extern int vfscanf (FILE *__restrict __s, const char *__restrict __format, __gnuc_va_list __arg) __asm__ ("" "__isoc99_vfscanf")
     __attribute__ ((__format__ (__scanf__, 2, 0))) ;
extern int vscanf (const char *__restrict __format, __gnuc_va_list __arg) __asm__ ("" "__isoc99_vscanf")
     __attribute__ ((__format__ (__scanf__, 1, 0))) ;
extern int vsscanf (const char *__restrict __s, const char *__restrict __format, __gnuc_va_list __arg) __asm__ ("" "__isoc99_vsscanf") __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__format__ (__scanf__, 2, 0)));


extern int fgetc (FILE *__stream);
extern int getc (FILE *__stream);
extern int getchar (void);

extern int getc_unlocked (FILE *__stream);
extern int getchar_unlocked (void);
extern int fgetc_unlocked (FILE *__stream);

extern int fputc (int __c, FILE *__stream);
extern int putc (int __c, FILE *__stream);
extern int putchar (int __c);

extern int fputc_unlocked (int __c, FILE *__stream);
extern int putc_unlocked (int __c, FILE *__stream);
extern int putchar_unlocked (int __c);
extern int getw (FILE *__stream);
extern int putw (int __w, FILE *__stream);

extern char *fgets (char *__restrict __s, int __n, FILE *__restrict __stream)
     ;

extern __ssize_t __getdelim (char **__restrict __lineptr,
          size_t *__restrict __n, int __delimiter,
          FILE *__restrict __stream) ;
extern __ssize_t getdelim (char **__restrict __lineptr,
        size_t *__restrict __n, int __delimiter,
        FILE *__restrict __stream) ;
extern __ssize_t getline (char **__restrict __lineptr,
       size_t *__restrict __n,
       FILE *__restrict __stream) ;

extern int fputs (const char *__restrict __s, FILE *__restrict __stream);
extern int puts (const char *__s);
extern int ungetc (int __c, FILE *__stream);
extern size_t fread (void *__restrict __ptr, size_t __size,
       size_t __n, FILE *__restrict __stream) ;
extern size_t fwrite (const void *__restrict __ptr, size_t __size,
        size_t __n, FILE *__restrict __s);

extern size_t fread_unlocked (void *__restrict __ptr, size_t __size,
         size_t __n, FILE *__restrict __stream) ;
extern size_t fwrite_unlocked (const void *__restrict __ptr, size_t __size,
          size_t __n, FILE *__restrict __stream);

extern int fseek (FILE *__stream, long int __off, int __whence);
extern long int ftell (FILE *__stream) ;
extern void rewind (FILE *__stream);

extern int fseeko (FILE *__stream, __off_t __off, int __whence);
extern __off_t ftello (FILE *__stream) ;

extern int fgetpos (FILE *__restrict __stream, fpos_t *__restrict __pos);
extern int fsetpos (FILE *__stream, const fpos_t *__pos);


extern void clearerr (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__));
extern int feof (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int ferror (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;

extern void clearerr_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__));
extern int feof_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int ferror_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;

extern void perror (const char *__s);

extern int sys_nerr;
extern const char *const sys_errlist[];
extern int fileno (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int fileno_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;
extern FILE *popen (const char *__command, const char *__modes) ;
extern int pclose (FILE *__stream);
extern char *ctermid (char *__s) __attribute__ ((__nothrow__ , __leaf__));
extern void flockfile (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__));
extern int ftrylockfile (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) ;
extern void funlockfile (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__));


extern void __assert_fail (const char *__assertion, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert_perror_fail (int __errnum, const char *__file,
      unsigned int __line, const char *__function)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void __assert (const char *__assertion, const char *__file, int __line)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));


typedef float float_t;
typedef double double_t;

extern double acos (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __acos (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double asin (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __asin (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double atan (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __atan (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double atan2 (double __y, double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __atan2 (double __y, double __x) __attribute__ ((__nothrow__ , __leaf__));
 extern double cos (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __cos (double __x) __attribute__ ((__nothrow__ , __leaf__));
 extern double sin (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __sin (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double tan (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __tan (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double cosh (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __cosh (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double sinh (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __sinh (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double tanh (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __tanh (double __x) __attribute__ ((__nothrow__ , __leaf__));


extern double acosh (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __acosh (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double asinh (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __asinh (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double atanh (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __atanh (double __x) __attribute__ ((__nothrow__ , __leaf__));


 extern double exp (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __exp (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double frexp (double __x, int *__exponent) __attribute__ ((__nothrow__ , __leaf__)); extern double __frexp (double __x, int *__exponent) __attribute__ ((__nothrow__ , __leaf__));
extern double ldexp (double __x, int __exponent) __attribute__ ((__nothrow__ , __leaf__)); extern double __ldexp (double __x, int __exponent) __attribute__ ((__nothrow__ , __leaf__));
 extern double log (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __log (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double log10 (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __log10 (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double modf (double __x, double *__iptr) __attribute__ ((__nothrow__ , __leaf__)); extern double __modf (double __x, double *__iptr) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));


extern double expm1 (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __expm1 (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double log1p (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __log1p (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double logb (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __logb (double __x) __attribute__ ((__nothrow__ , __leaf__));


extern double exp2 (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __exp2 (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double log2 (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __log2 (double __x) __attribute__ ((__nothrow__ , __leaf__));


 extern double pow (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)); extern double __pow (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__));
extern double sqrt (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __sqrt (double __x) __attribute__ ((__nothrow__ , __leaf__));


extern double hypot (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)); extern double __hypot (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__));


extern double cbrt (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __cbrt (double __x) __attribute__ ((__nothrow__ , __leaf__));


extern double ceil (double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern double __ceil (double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern double fabs (double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern double __fabs (double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern double floor (double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern double __floor (double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern double fmod (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)); extern double __fmod (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__));
extern int __isinf (double __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int __finite (double __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));

extern int isinf (double __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int finite (double __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern double drem (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)); extern double __drem (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__));
extern double significand (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __significand (double __x) __attribute__ ((__nothrow__ , __leaf__));

extern double copysign (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern double __copysign (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));


extern double nan (const char *__tagb) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern double __nan (const char *__tagb) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));

extern int __isnan (double __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int isnan (double __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern double j0 (double) __attribute__ ((__nothrow__ , __leaf__)); extern double __j0 (double) __attribute__ ((__nothrow__ , __leaf__));
extern double j1 (double) __attribute__ ((__nothrow__ , __leaf__)); extern double __j1 (double) __attribute__ ((__nothrow__ , __leaf__));
extern double jn (int, double) __attribute__ ((__nothrow__ , __leaf__)); extern double __jn (int, double) __attribute__ ((__nothrow__ , __leaf__));
extern double y0 (double) __attribute__ ((__nothrow__ , __leaf__)); extern double __y0 (double) __attribute__ ((__nothrow__ , __leaf__));
extern double y1 (double) __attribute__ ((__nothrow__ , __leaf__)); extern double __y1 (double) __attribute__ ((__nothrow__ , __leaf__));
extern double yn (int, double) __attribute__ ((__nothrow__ , __leaf__)); extern double __yn (int, double) __attribute__ ((__nothrow__ , __leaf__));

extern double erf (double) __attribute__ ((__nothrow__ , __leaf__)); extern double __erf (double) __attribute__ ((__nothrow__ , __leaf__));
extern double erfc (double) __attribute__ ((__nothrow__ , __leaf__)); extern double __erfc (double) __attribute__ ((__nothrow__ , __leaf__));
extern double lgamma (double) __attribute__ ((__nothrow__ , __leaf__)); extern double __lgamma (double) __attribute__ ((__nothrow__ , __leaf__));


extern double tgamma (double) __attribute__ ((__nothrow__ , __leaf__)); extern double __tgamma (double) __attribute__ ((__nothrow__ , __leaf__));

extern double gamma (double) __attribute__ ((__nothrow__ , __leaf__)); extern double __gamma (double) __attribute__ ((__nothrow__ , __leaf__));
extern double lgamma_r (double, int *__signgamp) __attribute__ ((__nothrow__ , __leaf__)); extern double __lgamma_r (double, int *__signgamp) __attribute__ ((__nothrow__ , __leaf__));

extern double rint (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __rint (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double nextafter (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern double __nextafter (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern double nexttoward (double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern double __nexttoward (double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern double remainder (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)); extern double __remainder (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__));
extern double scalbn (double __x, int __n) __attribute__ ((__nothrow__ , __leaf__)); extern double __scalbn (double __x, int __n) __attribute__ ((__nothrow__ , __leaf__));
extern int ilogb (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern int __ilogb (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double scalbln (double __x, long int __n) __attribute__ ((__nothrow__ , __leaf__)); extern double __scalbln (double __x, long int __n) __attribute__ ((__nothrow__ , __leaf__));
extern double nearbyint (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __nearbyint (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double round (double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern double __round (double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern double trunc (double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern double __trunc (double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern double remquo (double __x, double __y, int *__quo) __attribute__ ((__nothrow__ , __leaf__)); extern double __remquo (double __x, double __y, int *__quo) __attribute__ ((__nothrow__ , __leaf__));
extern long int lrint (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long int __lrint (double __x) __attribute__ ((__nothrow__ , __leaf__));
__extension__
extern long long int llrint (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long long int __llrint (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long int lround (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long int __lround (double __x) __attribute__ ((__nothrow__ , __leaf__));
__extension__
extern long long int llround (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long long int __llround (double __x) __attribute__ ((__nothrow__ , __leaf__));
extern double fdim (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)); extern double __fdim (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__));
extern double fmax (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern double __fmax (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern double fmin (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern double __fmin (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int __fpclassify (double __value) __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__const__));
extern int __signbit (double __value) __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__const__));
extern double fma (double __x, double __y, double __z) __attribute__ ((__nothrow__ , __leaf__)); extern double __fma (double __x, double __y, double __z) __attribute__ ((__nothrow__ , __leaf__));

extern double scalb (double __x, double __n) __attribute__ ((__nothrow__ , __leaf__)); extern double __scalb (double __x, double __n) __attribute__ ((__nothrow__ , __leaf__));

extern float acosf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __acosf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float asinf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __asinf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float atanf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __atanf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float atan2f (float __y, float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __atan2f (float __y, float __x) __attribute__ ((__nothrow__ , __leaf__));
 extern float cosf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __cosf (float __x) __attribute__ ((__nothrow__ , __leaf__));
 extern float sinf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __sinf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float tanf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __tanf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float coshf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __coshf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float sinhf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __sinhf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float tanhf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __tanhf (float __x) __attribute__ ((__nothrow__ , __leaf__));


extern float acoshf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __acoshf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float asinhf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __asinhf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float atanhf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __atanhf (float __x) __attribute__ ((__nothrow__ , __leaf__));


 extern float expf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __expf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float frexpf (float __x, int *__exponent) __attribute__ ((__nothrow__ , __leaf__)); extern float __frexpf (float __x, int *__exponent) __attribute__ ((__nothrow__ , __leaf__));
extern float ldexpf (float __x, int __exponent) __attribute__ ((__nothrow__ , __leaf__)); extern float __ldexpf (float __x, int __exponent) __attribute__ ((__nothrow__ , __leaf__));
 extern float logf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __logf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float log10f (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __log10f (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float modff (float __x, float *__iptr) __attribute__ ((__nothrow__ , __leaf__)); extern float __modff (float __x, float *__iptr) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));


extern float expm1f (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __expm1f (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float log1pf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __log1pf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float logbf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __logbf (float __x) __attribute__ ((__nothrow__ , __leaf__));


extern float exp2f (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __exp2f (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float log2f (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __log2f (float __x) __attribute__ ((__nothrow__ , __leaf__));


 extern float powf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)); extern float __powf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__));
extern float sqrtf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __sqrtf (float __x) __attribute__ ((__nothrow__ , __leaf__));


extern float hypotf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)); extern float __hypotf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__));


extern float cbrtf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __cbrtf (float __x) __attribute__ ((__nothrow__ , __leaf__));


extern float ceilf (float __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern float __ceilf (float __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern float fabsf (float __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern float __fabsf (float __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern float floorf (float __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern float __floorf (float __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern float fmodf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)); extern float __fmodf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__));
extern int __isinff (float __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int __finitef (float __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));

extern int isinff (float __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int finitef (float __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern float dremf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)); extern float __dremf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__));
extern float significandf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __significandf (float __x) __attribute__ ((__nothrow__ , __leaf__));

extern float copysignf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern float __copysignf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));


extern float nanf (const char *__tagb) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern float __nanf (const char *__tagb) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));

extern int __isnanf (float __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int isnanf (float __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern float j0f (float) __attribute__ ((__nothrow__ , __leaf__)); extern float __j0f (float) __attribute__ ((__nothrow__ , __leaf__));
extern float j1f (float) __attribute__ ((__nothrow__ , __leaf__)); extern float __j1f (float) __attribute__ ((__nothrow__ , __leaf__));
extern float jnf (int, float) __attribute__ ((__nothrow__ , __leaf__)); extern float __jnf (int, float) __attribute__ ((__nothrow__ , __leaf__));
extern float y0f (float) __attribute__ ((__nothrow__ , __leaf__)); extern float __y0f (float) __attribute__ ((__nothrow__ , __leaf__));
extern float y1f (float) __attribute__ ((__nothrow__ , __leaf__)); extern float __y1f (float) __attribute__ ((__nothrow__ , __leaf__));
extern float ynf (int, float) __attribute__ ((__nothrow__ , __leaf__)); extern float __ynf (int, float) __attribute__ ((__nothrow__ , __leaf__));

extern float erff (float) __attribute__ ((__nothrow__ , __leaf__)); extern float __erff (float) __attribute__ ((__nothrow__ , __leaf__));
extern float erfcf (float) __attribute__ ((__nothrow__ , __leaf__)); extern float __erfcf (float) __attribute__ ((__nothrow__ , __leaf__));
extern float lgammaf (float) __attribute__ ((__nothrow__ , __leaf__)); extern float __lgammaf (float) __attribute__ ((__nothrow__ , __leaf__));


extern float tgammaf (float) __attribute__ ((__nothrow__ , __leaf__)); extern float __tgammaf (float) __attribute__ ((__nothrow__ , __leaf__));

extern float gammaf (float) __attribute__ ((__nothrow__ , __leaf__)); extern float __gammaf (float) __attribute__ ((__nothrow__ , __leaf__));
extern float lgammaf_r (float, int *__signgamp) __attribute__ ((__nothrow__ , __leaf__)); extern float __lgammaf_r (float, int *__signgamp) __attribute__ ((__nothrow__ , __leaf__));

extern float rintf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __rintf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float nextafterf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern float __nextafterf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern float nexttowardf (float __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern float __nexttowardf (float __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern float remainderf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)); extern float __remainderf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__));
extern float scalbnf (float __x, int __n) __attribute__ ((__nothrow__ , __leaf__)); extern float __scalbnf (float __x, int __n) __attribute__ ((__nothrow__ , __leaf__));
extern int ilogbf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern int __ilogbf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float scalblnf (float __x, long int __n) __attribute__ ((__nothrow__ , __leaf__)); extern float __scalblnf (float __x, long int __n) __attribute__ ((__nothrow__ , __leaf__));
extern float nearbyintf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern float __nearbyintf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float roundf (float __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern float __roundf (float __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern float truncf (float __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern float __truncf (float __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern float remquof (float __x, float __y, int *__quo) __attribute__ ((__nothrow__ , __leaf__)); extern float __remquof (float __x, float __y, int *__quo) __attribute__ ((__nothrow__ , __leaf__));
extern long int lrintf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern long int __lrintf (float __x) __attribute__ ((__nothrow__ , __leaf__));
__extension__
extern long long int llrintf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern long long int __llrintf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern long int lroundf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern long int __lroundf (float __x) __attribute__ ((__nothrow__ , __leaf__));
__extension__
extern long long int llroundf (float __x) __attribute__ ((__nothrow__ , __leaf__)); extern long long int __llroundf (float __x) __attribute__ ((__nothrow__ , __leaf__));
extern float fdimf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)); extern float __fdimf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__));
extern float fmaxf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern float __fmaxf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern float fminf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern float __fminf (float __x, float __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int __fpclassifyf (float __value) __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__const__));
extern int __signbitf (float __value) __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__const__));
extern float fmaf (float __x, float __y, float __z) __attribute__ ((__nothrow__ , __leaf__)); extern float __fmaf (float __x, float __y, float __z) __attribute__ ((__nothrow__ , __leaf__));

extern float scalbf (float __x, float __n) __attribute__ ((__nothrow__ , __leaf__)); extern float __scalbf (float __x, float __n) __attribute__ ((__nothrow__ , __leaf__));

extern long double acosl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __acosl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double asinl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __asinl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double atanl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __atanl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double atan2l (long double __y, long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __atan2l (long double __y, long double __x) __attribute__ ((__nothrow__ , __leaf__));
 extern long double cosl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __cosl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
 extern long double sinl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __sinl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double tanl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __tanl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double coshl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __coshl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double sinhl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __sinhl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double tanhl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __tanhl (long double __x) __attribute__ ((__nothrow__ , __leaf__));


extern long double acoshl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __acoshl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double asinhl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __asinhl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double atanhl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __atanhl (long double __x) __attribute__ ((__nothrow__ , __leaf__));


 extern long double expl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __expl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double frexpl (long double __x, int *__exponent) __attribute__ ((__nothrow__ , __leaf__)); extern long double __frexpl (long double __x, int *__exponent) __attribute__ ((__nothrow__ , __leaf__));
extern long double ldexpl (long double __x, int __exponent) __attribute__ ((__nothrow__ , __leaf__)); extern long double __ldexpl (long double __x, int __exponent) __attribute__ ((__nothrow__ , __leaf__));
 extern long double logl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __logl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double log10l (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __log10l (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double modfl (long double __x, long double *__iptr) __attribute__ ((__nothrow__ , __leaf__)); extern long double __modfl (long double __x, long double *__iptr) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));


extern long double expm1l (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __expm1l (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double log1pl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __log1pl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double logbl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __logbl (long double __x) __attribute__ ((__nothrow__ , __leaf__));


extern long double exp2l (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __exp2l (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double log2l (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __log2l (long double __x) __attribute__ ((__nothrow__ , __leaf__));


 extern long double powl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)); extern long double __powl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__));
extern long double sqrtl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __sqrtl (long double __x) __attribute__ ((__nothrow__ , __leaf__));


extern long double hypotl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)); extern long double __hypotl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__));


extern long double cbrtl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __cbrtl (long double __x) __attribute__ ((__nothrow__ , __leaf__));


extern long double ceill (long double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern long double __ceill (long double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern long double fabsl (long double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern long double __fabsl (long double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern long double floorl (long double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern long double __floorl (long double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern long double fmodl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)); extern long double __fmodl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__));
extern int __isinfl (long double __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int __finitel (long double __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));

extern int isinfl (long double __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int finitel (long double __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern long double dreml (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)); extern long double __dreml (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__));
extern long double significandl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __significandl (long double __x) __attribute__ ((__nothrow__ , __leaf__));

extern long double copysignl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern long double __copysignl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));


extern long double nanl (const char *__tagb) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern long double __nanl (const char *__tagb) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));

extern int __isnanl (long double __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int isnanl (long double __value) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern long double j0l (long double) __attribute__ ((__nothrow__ , __leaf__)); extern long double __j0l (long double) __attribute__ ((__nothrow__ , __leaf__));
extern long double j1l (long double) __attribute__ ((__nothrow__ , __leaf__)); extern long double __j1l (long double) __attribute__ ((__nothrow__ , __leaf__));
extern long double jnl (int, long double) __attribute__ ((__nothrow__ , __leaf__)); extern long double __jnl (int, long double) __attribute__ ((__nothrow__ , __leaf__));
extern long double y0l (long double) __attribute__ ((__nothrow__ , __leaf__)); extern long double __y0l (long double) __attribute__ ((__nothrow__ , __leaf__));
extern long double y1l (long double) __attribute__ ((__nothrow__ , __leaf__)); extern long double __y1l (long double) __attribute__ ((__nothrow__ , __leaf__));
extern long double ynl (int, long double) __attribute__ ((__nothrow__ , __leaf__)); extern long double __ynl (int, long double) __attribute__ ((__nothrow__ , __leaf__));

extern long double erfl (long double) __attribute__ ((__nothrow__ , __leaf__)); extern long double __erfl (long double) __attribute__ ((__nothrow__ , __leaf__));
extern long double erfcl (long double) __attribute__ ((__nothrow__ , __leaf__)); extern long double __erfcl (long double) __attribute__ ((__nothrow__ , __leaf__));
extern long double lgammal (long double) __attribute__ ((__nothrow__ , __leaf__)); extern long double __lgammal (long double) __attribute__ ((__nothrow__ , __leaf__));


extern long double tgammal (long double) __attribute__ ((__nothrow__ , __leaf__)); extern long double __tgammal (long double) __attribute__ ((__nothrow__ , __leaf__));

extern long double gammal (long double) __attribute__ ((__nothrow__ , __leaf__)); extern long double __gammal (long double) __attribute__ ((__nothrow__ , __leaf__));
extern long double lgammal_r (long double, int *__signgamp) __attribute__ ((__nothrow__ , __leaf__)); extern long double __lgammal_r (long double, int *__signgamp) __attribute__ ((__nothrow__ , __leaf__));

extern long double rintl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __rintl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double nextafterl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern long double __nextafterl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern long double nexttowardl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern long double __nexttowardl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern long double remainderl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)); extern long double __remainderl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__));
extern long double scalbnl (long double __x, int __n) __attribute__ ((__nothrow__ , __leaf__)); extern long double __scalbnl (long double __x, int __n) __attribute__ ((__nothrow__ , __leaf__));
extern int ilogbl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern int __ilogbl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double scalblnl (long double __x, long int __n) __attribute__ ((__nothrow__ , __leaf__)); extern long double __scalblnl (long double __x, long int __n) __attribute__ ((__nothrow__ , __leaf__));
extern long double nearbyintl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long double __nearbyintl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double roundl (long double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern long double __roundl (long double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern long double truncl (long double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern long double __truncl (long double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern long double remquol (long double __x, long double __y, int *__quo) __attribute__ ((__nothrow__ , __leaf__)); extern long double __remquol (long double __x, long double __y, int *__quo) __attribute__ ((__nothrow__ , __leaf__));
extern long int lrintl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long int __lrintl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
__extension__
extern long long int llrintl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long long int __llrintl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long int lroundl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long int __lroundl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
__extension__
extern long long int llroundl (long double __x) __attribute__ ((__nothrow__ , __leaf__)); extern long long int __llroundl (long double __x) __attribute__ ((__nothrow__ , __leaf__));
extern long double fdiml (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)); extern long double __fdiml (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__));
extern long double fmaxl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern long double __fmaxl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern long double fminl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)); extern long double __fminl (long double __x, long double __y) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int __fpclassifyl (long double __value) __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__const__));
extern int __signbitl (long double __value) __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__const__));
extern long double fmal (long double __x, long double __y, long double __z) __attribute__ ((__nothrow__ , __leaf__)); extern long double __fmal (long double __x, long double __y, long double __z) __attribute__ ((__nothrow__ , __leaf__));

extern long double scalbl (long double __x, long double __n) __attribute__ ((__nothrow__ , __leaf__)); extern long double __scalbl (long double __x, long double __n) __attribute__ ((__nothrow__ , __leaf__));
extern int signgam;
enum
  {
    FP_NAN =
      0,
    FP_INFINITE =
      1,
    FP_ZERO =
      2,
    FP_SUBNORMAL =
      3,
    FP_NORMAL =
      4
  };
typedef enum
{
  _IEEE_ = -1,
  _SVID_,
  _XOPEN_,
  _POSIX_,
  _ISOC_
} _LIB_VERSION_TYPE;
extern _LIB_VERSION_TYPE _LIB_VERSION;
struct exception
  {
    int type;
    char *name;
    double arg1;
    double arg2;
    double retval;
  };
extern int matherr (struct exception *__exc);

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));
  int a27 = -83;
  int a9 = 3;
  int a14 = -162;
  int a21 = -189;
  int a8 = 7;
 int calculate_output(int input) {
 if((((( a14 <= -148 && a27 <= -78 ) && (a8==6)) && (a9==4)) && a21 <= -178 )){
  error_41: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==4)) && (a9==3)) && ((-144 < a21) && (5 >= a21)) )){
  error_10: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==6)) && (a9==5)) && ((-178 < a21) && (-144 >= a21)) )){
  error_47: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==6)) && (a9==5)) && a21 <= -178 )){
  error_42: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==4)) && (a9==5)) && 5 < a21 )){
  error_17: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==6)) && (a9==6)) && ((-144 < a21) && (5 >= a21)) )){
  error_53: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==4)) && (a9==2)) && 5 < a21 )){
  error_14: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==6)) && (a9==6)) && 5 < a21 )){
  error_58: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==6)) && (a9==3)) && 5 < a21 )){
  error_55: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==5)) && (a9==4)) && a21 <= -178 )){
  error_21: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==4)) && (a9==4)) && ((-144 < a21) && (5 >= a21)) )){
  error_11: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==6)) && (a9==4)) && ((-144 < a21) && (5 >= a21)) )){
  error_51: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==5)) && (a9==4)) && ((-144 < a21) && (5 >= a21)) )){
  error_31: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==5)) && (a9==5)) && ((-144 < a21) && (5 >= a21)) )){
  error_32: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==6)) && (a9==3)) && ((-144 < a21) && (5 >= a21)) )){
  error_50: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==5)) && (a9==2)) && ((-144 < a21) && (5 >= a21)) )){
  error_29: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==6)) && (a9==6)) && a21 <= -178 )){
  error_43: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==5)) && (a9==6)) && ((-178 < a21) && (-144 >= a21)) )){
  error_28: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==5)) && (a9==2)) && a21 <= -178 )){
  error_19: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==7)) && (a9==2)) && a21 <= -178 )){
  error_59: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==5)) && (a9==4)) && ((-178 < a21) && (-144 >= a21)) )){
  error_26: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==5)) && (a9==5)) && ((-178 < a21) && (-144 >= a21)) )){
  error_27: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==4)) && (a9==2)) && a21 <= -178 )){
  globalError: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==5)) && (a9==5)) && a21 <= -178 )){
  error_22: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==4)) && (a9==6)) && 5 < a21 )){
  error_18: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==6)) && (a9==2)) && a21 <= -178 )){
  error_39: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==6)) && (a9==4)) && ((-178 < a21) && (-144 >= a21)) )){
  error_46: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==5)) && (a9==4)) && 5 < a21 )){
  error_36: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==6)) && (a9==2)) && ((-178 < a21) && (-144 >= a21)) )){
  error_44: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==4)) && (a9==6)) && ((-144 < a21) && (5 >= a21)) )){
  error_13: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==5)) && (a9==3)) && ((-178 < a21) && (-144 >= a21)) )){
  error_25: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==4)) && (a9==6)) && ((-178 < a21) && (-144 >= a21)) )){
  error_8: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==5)) && (a9==5)) && 5 < a21 )){
  error_37: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==5)) && (a9==3)) && 5 < a21 )){
  error_35: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==4)) && (a9==3)) && a21 <= -178 )){
  error_0: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==5)) && (a9==6)) && ((-144 < a21) && (5 >= a21)) )){
  error_33: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==6)) && (a9==2)) && ((-144 < a21) && (5 >= a21)) )){
  error_49: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==5)) && (a9==3)) && a21 <= -178 )){
  error_20: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==4)) && (a9==5)) && ((-144 < a21) && (5 >= a21)) )){
  error_12: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==5)) && (a9==2)) && ((-178 < a21) && (-144 >= a21)) )){
  error_24: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==6)) && (a9==3)) && a21 <= -178 )){
  error_40: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==6)) && (a9==3)) && ((-178 < a21) && (-144 >= a21)) )){
  error_45: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==5)) && (a9==3)) && ((-144 < a21) && (5 >= a21)) )){
  error_30: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==4)) && (a9==2)) && ((-144 < a21) && (5 >= a21)) )){
  error_9: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==5)) && (a9==2)) && 5 < a21 )){
  error_34: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==6)) && (a9==4)) && 5 < a21 )){
  error_56: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==5)) && (a9==6)) && a21 <= -178 )){
  error_23: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==4)) && (a9==4)) && 5 < a21 )){
  error_16: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==4)) && (a9==4)) && ((-178 < a21) && (-144 >= a21)) )){
  error_6: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==6)) && (a9==5)) && ((-144 < a21) && (5 >= a21)) )){
  error_52: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==6)) && (a9==5)) && 5 < a21 )){
  error_57: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==4)) && (a9==6)) && a21 <= -178 )){
  error_3: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==4)) && (a9==3)) && 5 < a21 )){
  error_15: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==5)) && (a9==6)) && 5 < a21 )){
  error_38: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==4)) && (a9==3)) && ((-178 < a21) && (-144 >= a21)) )){
  error_5: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==4)) && (a9==5)) && ((-178 < a21) && (-144 >= a21)) )){
  error_7: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==4)) && (a9==2)) && ((-178 < a21) && (-144 >= a21)) )){
  error_4: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==4)) && (a9==4)) && a21 <= -178 )){
  error_1: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==6)) && (a9==2)) && 5 < a21 )){
  error_54: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==6)) && (a9==6)) && ((-178 < a21) && (-144 >= a21)) )){
  error_48: __VERIFIER_assume(0);
  }
  if((((( a14 <= -148 && a27 <= -78 ) && (a8==4)) && (a9==5)) && a21 <= -178 )){
  error_2: __VERIFIER_assume(0);
  }
     if(((( a14 <= -148 && (((input == 2) && a21 <= -178 ) && (a8==4))) && ((100 < a27) && (182 >= a27)) ) && (a9==3))){
      if((a9==6)){
      a27 = (((a27 - 579239) + -16635) - -813300);
      a21 = ((((a21 + 0) * -1)/ 10) - -262318);
       a8 = 6;
       a9 = 2;
      } else{
       a27 = (((a27 - 173) + -1) + 90);
       a21 = (((a21 - -600084) + 8) + 32);
       a8 = 5;
      } return 25;
     } else if((( ((-78 < a27) && (100 >= a27)) && ((((input == 2) && a14 <= -148 ) && (a9==2)) && (a8==4))) && ((-178 < a21) && (-144 >= a21)) )){
      a27 = ((((a27 - -366326) - 844450) * 10)/ 9);
      a21 = (((((a21 - 224703) * 10)/ 9) * 10)/ 9);
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && ( a21 <= -178 && ((a9==2) && (( a27 <= -78 && (input == 6)) && (a8==7)))))){
      if( ((-178 < a21) && (-144 >= a21)) ){
      a14 = (((((a14 + -530871) - 11167) + 1108700) * -1)/ 10);
      a27 = (((((a27 - -152125) % 299908)- -300090) / 5) - -133461);
       a8 = 6;
       a9 = 3;
      } else{
       a14 = ((((a14 * 5) - -433037) - 408099) - 369849);
       a21 = (((((a21 % 74)+ -36) / 5) + 61842) + -61831);
       a8 = 8;
      } return -1;
     } else if(( a27 <= -78 && ((a8==4) && ( ((-148 < a14) && (13 >= a14)) && ((( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ((a9==2) && ((-144 < a21) && (5 >= a21)) )) && (input == 5)))))){
      a14 = (((a14 + 443514) + -776828) * 1);
      a27 = ((((a27 - 0) % 299908)- -300090) * 1);
      a21 = ((((a21 % 74)+ -69) / 5) + -34);
       a8 = 5;
       a9 = 5;
       return 23;
     } else if(( 5 < a21 && ((a8==6) && ( ((-78 < a27) && (100 >= a27)) && ((a9==6) && ( a14 <= -148 && (input == 4))))))){
      a27 = ((((a27 - 250457) - 224278) * 10)/ 9);
      a21 = ((((a21 * 9)/ 10) / 5) + -278361);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a9==2) && ( a14 <= -148 && ( ((100 < a27) && (182 >= a27)) && ((input == 6) && a21 <= -178 )))) && (a8==7))){
      a27 = ((((a27 - 287486) / 5) + 270451) + -433143);
       return -1;
     } else if((((a8==5) && ( 182 < a27 && (((a9==3) && (input == 3)) && a14 <= -148 ))) && ((-178 < a21) && (-144 >= a21)) )){
      a27 = ((((a27 / 5) % 40)+ 121) - -1);
      a21 = ((((a21 - -24894) / 5) + 178914) - 414570);
       a9 = 6;
       return 25;
     } else if((((((((a9==3) || (a9==4)) && (input == 2)) && 5 < a21 ) && a14 <= -148 ) && (a8==8)) && ((-78 < a27) && (100 >= a27)) )){
      a27 = ((((a27 - 18151) - -386650) * 1) - 841345);
      a21 = ((((a21 % 74)- 102) + 362169) + -362206);
       a8 = 7;
       a9 = 2;
       return 25;
     } else if((( a14 <= -148 && ((((((a9==4) || (a9==5)) || (a9==6)) && (input == 2)) && ((-144 < a21) && (5 >= a21)) ) && (a8==5))) && ((100 < a27) && (182 >= a27)) )){
      a27 = (((((a27 * 5) / 5) * 5) * -2)/ 10);
      a21 = (((a21 + -384830) * 1) - 48695);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && (( a21 <= -178 && ((a9==4) && ((input == 2) && (a8==8)))) && a27 <= -78 ))){
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((( ((100 < a27) && (182 >= a27)) && (input == 5)) && a14 <= -148 ) && (a8==4)) && a21 <= -178 ) && (a9==2))){
      a27 = ((((a27 * 10)/ -9) + -124765) * 4);
       return -1;
     } else if(( a14 <= -148 && (((((input == 3) && ((a9==5) || ((a9==3) || (a9==4)))) && ((-78 < a27) && (100 >= a27)) ) && ((-178 < a21) && (-144 >= a21)) ) && (a8==4)))){
      a27 = (((a27 * 5) + -39376) / 5);
      a21 = ((((a21 * 10)/ 8) / 5) - 334528);
       a9 = 2;
       return -1;
     } else if(((a8==7) && ( ((-148 < a14) && (13 >= a14)) && ( a27 <= -78 && ((input == 4) && (( ((-178 < a21) && (-144 >= a21)) && (a9==2)) || (((a9==5) && a21 <= -178 ) || ((a9==6) && a21 <= -178 )))))))){
      a14 = (((a14 + -472372) * 1) - -377912);
      a21 = (((a21 - -600099) + 13) - -29);
       a8 = 4;
       a9 = 6;
       return -1;
     } else if((( ((-78 < a27) && (100 >= a27)) && ( 5 < a21 && ( a14 <= -148 && ((a9==2) && (input == 4))))) && (a8==8))){
      a27 = (((((a27 % 40)+ 141) - 422543) * 1) - -422542);
      a21 = ((((a21 % 299911)- 300088) - 178702) + -12158);
       a8 = 7;
       return 21;
     } else if(( a14 <= -148 && ( ((-78 < a27) && (100 >= a27)) && (( 5 < a21 && ((((a9==4) || (a9==5)) || (a9==6)) && (input == 3))) && (a8==4))))){
      if((a9==3)){
      a27 = (((((a27 % 40)+ 140) * 5) % 40)- -117);
      a21 = (((((((a21 % 74)+ -111) * 10)/ 9) * 5) % 74)- -5);
       a8 = 8;
       a9 = 2;
      } else{
       a8 = 7;
       a9 = 3;
      } return 21;
     } else if(((( a27 <= -78 && ((input == 6) && ((( ((-144 < a21) && (5 >= a21)) && (a9==6)) || ( 5 < a21 && (a9==2))) || ((a9==3) && 5 < a21 )))) && (a8==5)) && ((-148 < a14) && (13 >= a14)) )){
      if((a8==4)){
      a21 = (((((a21 * 9)/ 10) % 16)- 160) + 1);
       a8 = 4;
       a9 = 6;
      } else{
       a14 = (((((a14 + -526418) + -54027) + 1023447) * -1)/ 10);
       a21 = ((((a21 + -567743) % 74)+ -69) / 5);
       a9 = 2;
      } return -1;
     } else if((( a21 <= -178 && (( ((-148 < a14) && (13 >= a14)) && (((a9==4) || ((a9==2) || (a9==3))) && (input == 1))) && a27 <= -78 )) && (a8==5))){
      if( a14 <= -148 ){
      a14 = (((a14 + -356841) / 5) + -197386);
      a27 = ((((a27 % 40)+ 180) + 1) - -1);
      a21 = (((a21 - -600073) / 5) * 5);
       a8 = 8;
       a9 = 3;
      } else{
       a14 = (((a14 - -214411) * 2) + -698183);
       a8 = 8;
       a9 = 5;
      } return -1;
     } else if((((a8==8) && ((a9==4) && ( 5 < a21 && ( a14 <= -148 && (input == 2))))) && ((100 < a27) && (182 >= a27)) )){
      a27 = (((a27 - -420142) * 1) * 1);
      a21 = ((((a21 % 299911)+ -300088) - 88031) / 5);
       a8 = 4;
       a9 = 5;
       return 21;
     } else if(( ((-78 < a27) && (100 >= a27)) && ( a14 <= -148 && ((a8==6) && ((((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ( ((-144 < a21) && (5 >= a21)) && (a9==2))) && (input == 1)))))){
      a27 = (((a27 / 5) + -395053) * 1);
      a21 = ((((a21 - -430011) + -45623) * 10)/ -9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==4) && ( a27 <= -78 && (((input == 1) && ((-148 < a14) && (13 >= a14)) ) && (a9==2)))) && ((-178 < a21) && (-144 >= a21)) )){
      if( 182 < a27 ){
      a14 = (((a14 / 5) - 590758) / 5);
      a27 = (((((a27 * 9)/ 10) % 88)+ 61) + 28);
      a21 = ((((a21 + 537766) * 10)/ -9) / 5);
       a8 = 8;
       a9 = 3;
      } else{
       a14 = (((a14 * 5) - 31569) + -198626);
       a27 = (((((a27 - 0) % 88)- -95) * 9)/ 10);
       a21 = (((a21 - -251956) - -242074) * 1);
       a8 = 7;
       a9 = 5;
      } return -1;
     } else if(( a14 <= -148 && (((a8==8) && ((((a9==4) || (a9==5)) && (input == 2)) && a27 <= -78 )) && ((-144 < a21) && (5 >= a21)) ))){
      a27 = (((((a27 + 0) - 0) + 372672) % 88)- -11);
      a21 = (((((a21 * 5) * 5) * 5) % 16)- 161);
       a8 = 5;
       a9 = 2;
       return 23;
     } else if(((((a9==4) && ((a8==6) && ((input == 4) && a21 <= -178 ))) && ((-148 < a14) && (13 >= a14)) ) && a27 <= -78 )){
      a14 = ((((a14 + -376357) / 5) + 613543) + -922448);
      a27 = (((((a27 - -109700) / 5) * 5) % 299908)+ 300090);
      a21 = ((((((a21 + 431960) % 16)- 160) * 5) % 16)+ -153);
       a8 = 8;
       return -1;
     } else if((( a27 <= -78 && (((a8==6) && (((a9==4) || ((a9==2) || (a9==3))) && (input == 1))) && ((-148 < a14) && (13 >= a14)) )) && ((-178 < a21) && (-144 >= a21)) )){
      a14 = ((((a14 + -539644) * 10)/ 9) * 1);
      a27 = ((((a27 % 40)+ 166) / 5) + 114);
      a21 = ((((a21 + -187793) * 10)/ 9) * 2);
       a8 = 5;
       a9 = 6;
       return -1;
     } else if((( a14 <= -148 && (((a8==6) && ((input == 5) && ((a9==3) || (a9==4)))) && ((-78 < a27) && (100 >= a27)) )) && ((-144 < a21) && (5 >= a21)) )){
      a27 = (((a27 * 5) + 540344) - 1028860);
      a21 = ((((a21 + -486754) * 10)/ 9) + -47115);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a27 <= -78 && ((((a8==8) && (((a9==4) || (a9==5)) && (input == 5))) && ((-144 < a21) && (5 >= a21)) ) && a14 <= -148 ))){
      a21 = (((a21 - 313472) + -146985) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( 5 < a21 && (((((input == 5) && a14 <= -148 ) && (a9==3)) && (a8==6)) && 182 < a27 ))){
      a27 = (((((a27 * 9)/ 10) - -54072) * 1) + -649261);
      a21 = (((a21 / 5) - -233564) + -815080);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( ((100 < a27) && (182 >= a27)) && (( ((-178 < a21) && (-144 >= a21)) && ((input == 3) && ((a9==4) || (a9==5)))) && (a8==7))))){
      a27 = ((((a27 - 269348) * 2) * 10)/ 9);
       a8 = 6;
       a9 = 5;
       return -1;
     } else if(((a9==3) && ( 182 < a27 && ( 5 < a21 && ( a14 <= -148 && ((input == 1) && (a8==6))))))){
       return 25;
     } else if((( a14 <= -148 && ((a8==4) && ( ((-144 < a21) && (5 >= a21)) && ((input == 5) && ((a9==2) || (a9==3)))))) && ((100 < a27) && (182 >= a27)) )){
      a27 = ((((a27 * -8)/ 10) / 5) - 80439);
      a21 = (((a21 - -339578) + -926678) + -10383);
       a9 = 2;
       return -1;
     } else if(((((((input == 3) && (a9==4)) && a27 <= -78 ) && a21 <= -178 ) && (a8==8)) && a14 <= -148 )){
      a27 = (((((a27 % 88)+ 42) - -543065) - 1102846) + 559787);
       a8 = 4;
       a9 = 3;
       return 25;
     } else if(( 5 < a21 && ((( a14 <= -148 && ((input == 1) && (a9==2))) && (a8==4)) && ((-78 < a27) && (100 >= a27)) ))){
      a21 = (((((a21 % 74)+ -82) - 5) * 9)/ 10);
       a8 = 7;
       a9 = 4;
       return 23;
     } else if(( ((-148 < a14) && (13 >= a14)) && (( ((-178 < a21) && (-144 >= a21)) && ((a8==6) && ((input == 5) && (((a9==2) || (a9==3)) || (a9==4))))) && a27 <= -78 ))){
      a14 = (((a14 * 5) + -336075) * 1);
      a21 = ((((a21 * -1)/ 10) + -296144) - -454983);
       a8 = 5;
       a9 = 6;
       return 21;
     } else if((((a8==7) && (( ((100 < a27) && (182 >= a27)) && ((input == 6) && (((a9==3) || (a9==4)) || (a9==5)))) && a21 <= -178 )) && a14 <= -148 )){
      a27 = (((((a27 * 10)/ -9) / 5) / 5) - 115336);
      a21 = ((((((a21 * 9)/ 10) % 74)+ 5) + -174778) - -174719);
       a8 = 4;
       a9 = 4;
       return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && ( a14 <= -148 && ((a8==7) && (((input == 5) && (a9==3)) && 5 < a21 ))))){
      a27 = (((a27 / 5) + -512968) - 79626);
      a21 = (((((a21 % 299911)- 300088) / 5) * 51)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( 182 < a27 && (((input == 2) && ((a9==6) || ((a9==4) || (a9==5)))) && a14 <= -148 )) && ((-144 < a21) && (5 >= a21)) ) && (a8==4))){
      a27 = ((((a27 + -357988) % 88)- -10) + 0);
      a21 = ((((a21 / 5) + 404774) * 10)/ 9);
       a8 = 8;
       a9 = 4;
       return -1;
     } else if((( 182 < a27 && ( a14 <= -148 && ((a8==8) && ((((a9==4) || (a9==5)) || (a9==6)) && (input == 5))))) && a21 <= -178 )){
      a27 = (((a27 - 600171) + -2) * 1);
      a21 = ((((a21 - 0) % 74)- -2) + 1);
       a8 = 6;
       a9 = 2;
       return -1;
     } else if(((( a14 <= -148 && ((a9==5) && ((a8==7) && (input == 1)))) && a21 <= -178 ) && 182 < a27 )){
      a27 = ((((((a27 - 0) * 9)/ 10) - -5851) % 40)+ 131);
      a21 = ((((((a21 / 5) % 74)+ 2) * 5) % 74)+ -69);
       a8 = 4;
       return 21;
     } else if((((( 5 < a21 && ((input == 1) && ((a9==3) || (a9==4)))) && (a8==8)) && ((-78 < a27) && (100 >= a27)) ) && a14 <= -148 )){
      a27 = ((((a27 + -39044) * 10)/ 9) + -228262);
      a21 = ((((a21 + 0) % 299911)+ -300088) - 238095);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a27 <= -78 && (( ((-148 < a14) && (13 >= a14)) && ((input == 6) && ((a9==4) || (a9==5)))) && 5 < a21 )) && (a8==7))){
      a14 = ((((a14 + -67739) + 210314) * 10)/ -9);
      a27 = (((((a27 % 299908)- -300090) * 10)/ 9) - -106347);
      a21 = ((((a21 % 299911)+ -300088) - 33971) + -144100);
       a8 = 5;
       a9 = 6;
       return -1;
     } else if((((((a9==2) && ((input == 5) && ((-144 < a21) && (5 >= a21)) )) && a14 <= -148 ) && a27 <= -78 ) && (a8==7))){
      a21 = (((a21 + -598818) + -1010) * 1);
       a8 = 4;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && ( a21 <= -178 && (( a27 <= -78 && (((a9==4) || ((a9==2) || (a9==3))) && (input == 5))) && (a8==5))))){
      a14 = ((((a14 + -363833) - 170616) * 10)/ 9);
      a21 = ((((((a21 * 9)/ 10) - -364866) * 1) % 74)- 69);
       a8 = 4;
       a9 = 4;
       return -1;
     } else if(( a14 <= -148 && (((((input == 6) && (a8==4)) && 5 < a21 ) && (a9==3)) && ((-78 < a27) && (100 >= a27)) ))){
      a27 = (((a27 * 5) + 509191) + -1088616);
      a21 = ((((a21 % 299911)+ -300088) - 158301) - 14804);
       a9 = 2;
       return -1;
     } else if(((((( ((-78 < a27) && (100 >= a27)) && (input == 3)) && (a9==3)) && 5 < a21 ) && (a8==7)) && a14 <= -148 )){
      a27 = (((a27 - -310764) + 143155) * 1);
      a21 = ((((((a21 % 299911)- 300088) * 10)/ 9) * 10)/ 9);
       a8 = 5;
       return 21;
     } else if((((( ((100 < a27) && (182 >= a27)) && ((input == 1) && ((a9==5) || (a9==6)))) && 5 < a21 ) && (a8==8)) && a14 <= -148 )){
      a27 = (((a27 - 597646) * 1) - 2113);
      a21 = ((((a21 % 299911)+ -300088) + 521271) + -690852);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && ((a8==6) && ( a27 <= -78 && ( ((-178 < a21) && (-144 >= a21)) && ((input == 2) && ((a9==4) || ((a9==2) || (a9==3))))))))){
      a14 = (((a14 / 5) + -351727) * 1);
       a9 = 2;
       return -1;
     } else if(((((a8==5) && (( a21 <= -178 && (input == 2)) && a14 <= -148 )) && (a9==4)) && 182 < a27 )){
      a27 = ((((((a27 % 40)+ 132) * 9)/ 10) * 9)/ 10);
      a21 = (((a21 + 600112) - -36) * 1);
       a8 = 4;
       return 21;
     } else if(((a8==5) && ( 182 < a27 && ((((input == 4) && ((a9==4) || (a9==5))) && a14 <= -148 ) && ((-178 < a21) && (-144 >= a21)) )))){
      a27 = (((a27 - 600149) / 5) * 5);
      a21 = ((((a21 / 5) / 5) * 356)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((((a8==7) && (((a9==4) || ((a9==2) || (a9==3))) && (input == 4))) && ((-78 < a27) && (100 >= a27)) ) && ((-144 < a21) && (5 >= a21)) ) && a14 <= -148 )){
      a27 = (((a27 - 52532) / 5) * 5);
      a21 = (((a21 - 88699) / 5) - 37812);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==7) && ((((a9==3) && ( a21 <= -178 && (input == 2))) && ((-148 < a14) && (13 >= a14)) ) && a27 <= -78 ))){
      a21 = ((((a21 + 0) / 5) % 74)- -2);
       a9 = 5;
       return -1;
     } else if(((((((input == 4) && ((a9==3) || (a9==4))) && a14 <= -148 ) && 5 < a21 ) && (a8==6)) && ((-78 < a27) && (100 >= a27)) )){
      a27 = ((((a27 - 291105) / 5) + 561464) + -733943);
      a21 = ((((a21 % 299911)- 300088) / 5) - 142107);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((((((a9==4) || ((a9==2) || (a9==3))) && (input == 1)) && ((-144 < a21) && (5 >= a21)) ) && (a8==7)) && 182 < a27 ))){
      a27 = (((a27 / 5) + -164328) + -352890);
      a21 = (((a21 - -121590) + -280034) * 3);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && (((a8==7) && ( ((100 < a27) && (182 >= a27)) && ((input == 4) && (((a9==3) || (a9==4)) || (a9==5))))) && a21 <= -178 ))){
      a27 = (((a27 - 193537) - -479973) - 324732);
      a21 = (((((a21 + 0) / 5) - -507158) % 74)+ -133);
       a8 = 6;
       a9 = 4;
       return -1;
     } else if(((a8==7) && ((((((a9==4) || ((a9==2) || (a9==3))) && (input == 4)) && a27 <= -78 ) && ((-144 < a21) && (5 >= a21)) ) && ((-148 < a14) && (13 >= a14)) ))){
      if( 5 < a21 ){
      a14 = (((a14 - 418474) - 28571) - 143516);
      a21 = (((a21 + 550737) - 638962) - 20604);
       a8 = 6;
       a9 = 6;
      } else{
       a14 = ((((a14 - -297838) * -1)/ 10) * 5);
       a27 = (((((a27 % 299908)- -300090) - -72144) * 10)/ 9);
       a21 = (((((a21 % 16)- 161) + 591732) / 5) - 118479);
       a8 = 6;
       a9 = 3;
      } return -1;
     } else if(((a8==6) && (( 182 < a27 && ( ((-178 < a21) && (-144 >= a21)) && ((input == 1) && ((a9==3) || (a9==4))))) && a14 <= -148 ))){
      a27 = ((((a27 * -5)/ 10) - 264819) / 5);
      a21 = (((a21 - 10375) * 5) - 130992);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((-148 < a14) && (13 >= a14)) && (((input == 2) && ((( ((-178 < a21) && (-144 >= a21)) && (a9==5)) || ((a9==6) && ((-178 < a21) && (-144 >= a21)) )) || ( ((-144 < a21) && (5 >= a21)) && (a9==2)))) && (a8==5))) && a27 <= -78 )){
      a14 = (((a14 / 5) + -208748) * 2);
      a27 = (((((a27 - -575434) % 40)- -140) - 458526) + 458527);
      a21 = (((a21 / 5) + -114524) * 5);
       a8 = 7;
       a9 = 2;
       return 23;
     } else if(( a14 <= -148 && ( ((100 < a27) && (182 >= a27)) && ((input == 2) && (((((a9==5) && (a8==4)) && 5 < a21 ) || ( 5 < a21 && ((a8==4) && (a9==6)))) || (((a8==5) && (a9==2)) && a21 <= -178 )))))){
      if((a9==3)){
      a27 = ((((a27 + -52965) * -1)/ 10) * 5);
      a21 = (((a21 / 5) - 295624) - 181035);
       a8 = 7;
       a9 = 6;
      } else{
       a27 = (((a27 * 5) + -75069) + -255530);
       a21 = (((a21 + 0) / 5) - 445782);
       a8 = 8;
       a9 = 4;
      } return 21;
     } else if((((((input == 4) && (((a9==2) && ((-144 < a21) && (5 >= a21)) ) || (( ((-178 < a21) && (-144 >= a21)) && (a9==5)) || ((a9==6) && ((-178 < a21) && (-144 >= a21)) )))) && (a8==5)) && a14 <= -148 ) && ((100 < a27) && (182 >= a27)) )){
      a27 = (((a27 / 5) + -169391) * 3);
      a21 = (((a21 + -182272) + -128986) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && (( ((-78 < a27) && (100 >= a27)) && ((input == 3) && (( a21 <= -178 && (a9==6)) || ((a9==2) && ((-178 < a21) && (-144 >= a21)) )))) && (a8==8)))){
      a27 = ((((a27 + 497611) * 1) * 10)/ -9);
      a21 = ((((a21 % 299911)- 178) - 88023) + -89840);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((( 182 < a27 && (((a9==2) || (a9==3)) && (input == 2))) && (a8==7)) && 5 < a21 ))){
      a27 = ((((a27 - 600180) + -3) + 555260) - 555167);
       a8 = 5;
       a9 = 5;
       return -1;
     } else if(( a14 <= -148 && ((((( 5 < a21 && ((a8==4) && (a9==5))) || (((a8==4) && (a9==6)) && 5 < a21 )) || (((a9==2) && (a8==5)) && a21 <= -178 )) && (input == 3)) && ((100 < a27) && (182 >= a27)) ))){
      a27 = (((((a27 + 475165) * 10)/ -9) * 10)/ 9);
      a21 = (((a21 / 5) + -429847) + -13664);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a27 <= -78 && ((a9==2) && (((a8==7) && ( a21 <= -178 && (input == 5))) && ((-148 < a14) && (13 >= a14)) )))){
      a14 = (((a14 - 204970) + -283491) + -28938);
      a21 = ((((a21 + 0) % 74)+ 3) + 2);
       a8 = 4;
       a9 = 6;
       return -1;
     } else if(((( 5 < a21 && ((((a9==2) || (a9==3)) && (input == 6)) && (a8==7))) && a14 <= -148 ) && 182 < a27 )){
      a27 = (((((a27 % 40)+ 123) / 5) + 171103) + -171009);
      a21 = ((((a21 % 74)- 94) / 5) - -8);
       a8 = 6;
       a9 = 4;
       return -1;
     } else if((( a14 <= -148 && (( ((100 < a27) && (182 >= a27)) && (((a9==5) || (a9==6)) && (input == 1))) && ((-144 < a21) && (5 >= a21)) )) && (a8==7))){
      a27 = ((((a27 * 5) / 5) / 5) - 485737);
      a21 = (((a21 / 5) - 576596) - 4340);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((( a27 <= -78 && ( a21 <= -178 && (input == 2))) && ((-148 < a14) && (13 >= a14)) ) && (a9==5)) && (a8==5))){
      a14 = ((((a14 - 186631) + -319712) * 10)/ 9);
      a27 = ((((a27 % 88)+ 58) + -25) / 5);
      a21 = ((((a21 / 5) % 16)- 157) - -11);
       a8 = 6;
       a9 = 3;
       return -1;
     } else if((( ((-144 < a21) && (5 >= a21)) && ( ((-148 < a14) && (13 >= a14)) && (((input == 2) && ((a9==5) || (a9==6))) && a27 <= -78 ))) && (a8==4))){
      a14 = (((((a14 / 5) - 212292) - -313626) * -1)/ 10);
      a21 = (((a21 / 5) + -189649) / 5);
       a8 = 5;
       a9 = 3;
       return -1;
     } else if(((((a8==7) && (((input == 4) && (a9==2)) && a21 <= -178 )) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 )){
      a27 = (((a27 - 28723) / 5) / 5);
      a21 = ((((((a21 % 16)+ -149) * 5) - -530401) % 16)+ -167);
       a8 = 5;
       a9 = 4;
       return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && ( a14 <= -148 && ( ((-178 < a21) && (-144 >= a21)) && ((((a9==4) || (a9==5)) && (input == 1)) && (a8==8)))))){
       a8 = 4;
       a9 = 6;
       return 23;
     } else if((((( a21 <= -178 && ((a9==3) && (input == 3))) && (a8==5)) && 182 < a27 ) && a14 <= -148 )){
      if((a8==7)){
       a8 = 7;
       a9 = 6;
      } else{
       a27 = (((a27 + 0) + -600122) + -26);
       a8 = 8;
       a9 = 4;
      } return -1;
     } else if(( a14 <= -148 && ( ((-178 < a21) && (-144 >= a21)) && ((a8==4) && (((input == 2) && ((a9==5) || ((a9==3) || (a9==4)))) && ((-78 < a27) && (100 >= a27)) ))))){
      a27 = (((a27 + -588523) * 1) * 1);
      a21 = ((((a21 * 13)/ 10) + -461470) * 1);
       a9 = 2;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && ((((input == 5) && (((a9==6) && a21 <= -178 ) || ( ((-178 < a21) && (-144 >= a21)) && (a9==2)))) && (a8==5)) && a27 <= -78 ))){
      a21 = ((((a21 + 0) % 299911)- 178) + -210847);
       a9 = 2;
       return -1;
     } else if(((a8==5) && ( a14 <= -148 && (((input == 4) && (( ((-144 < a21) && (5 >= a21)) && (a9==6)) || ((a9==2) && 5 < a21 ))) && ((-78 < a27) && (100 >= a27)) )))){
      a27 = (((a27 + -529810) * 1) + -18198);
      a21 = ((((a21 * 9)/ 10) + -546166) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((((input == 6) && (( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ( ((-144 < a21) && (5 >= a21)) && (a9==2)))) && a14 <= -148 ) && ((-78 < a27) && (100 >= a27)) ) && (a8==4))){
      a27 = (((a27 + 598350) + -719497) - 461184);
      a21 = (((a21 + 3746) + -33734) - 177892);
       a9 = 2;
       return -1;
     } else if(((((((( ((-178 < a21) && (-144 >= a21)) && (a9==5)) || ( ((-178 < a21) && (-144 >= a21)) && (a9==6))) || ((a9==2) && ((-144 < a21) && (5 >= a21)) )) && (input == 5)) && (a8==6)) && a27 <= -78 ) && ((-148 < a14) && (13 >= a14)) )){
      a14 = ((((a14 - 70059) * 10)/ 9) - 241528);
      a27 = ((((a27 - 0) % 40)- -180) + -25);
      a21 = ((((a21 + -211190) * 10)/ 9) * 2);
       a8 = 7;
       a9 = 2;
       return -1;
     } else if(( ((-178 < a21) && (-144 >= a21)) && ( a27 <= -78 && (( a14 <= -148 && ((input == 5) && ((a9==5) || ((a9==3) || (a9==4))))) && (a8==8))))){
      a21 = (((((a21 - 28551) * 5) - -593977) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((-178 < a21) && (-144 >= a21)) && (((a8==6) && ((input == 5) && (((a9==3) || (a9==4)) || (a9==5)))) && ((100 < a27) && (182 >= a27)) )) && a14 <= -148 )){
      a27 = (((((a27 * 10)/ -9) - -263394) * 10)/ -9);
      a21 = ((((a21 - 239304) * 10)/ 9) / 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((a8==7) && (((input == 5) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 )) && (a9==4)) && ((-144 < a21) && (5 >= a21)) )){
      a27 = ((((a27 * 10)/ -9) * 5) / 5);
      a21 = (((a21 - 222903) * 2) + -127143);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((-148 < a14) && (13 >= a14)) && (( a27 <= -78 && ((input == 5) && ((a9==3) || (a9==4)))) && (a8==6))) && 5 < a21 )){
      a14 = (((a14 - -145111) + -732697) / 5);
      a21 = ((((((a21 * 9)/ 10) + 50408) / 5) * -1)/ 10);
       a8 = 5;
       a9 = 6;
       return -1;
     } else if(((((a8==6) && ((((a9==2) && ((-178 < a21) && (-144 >= a21)) ) || (((a9==5) && a21 <= -178 ) || ((a9==6) && a21 <= -178 ))) && (input == 6))) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 )){
      a21 = (((((a21 % 299911)+ -178) * 10)/ 9) + -216227);
       a8 = 4;
       a9 = 6;
       return -1;
     } else if((( ((-144 < a21) && (5 >= a21)) && (( a27 <= -78 && ((input == 6) && ((a9==4) || ((a9==2) || (a9==3))))) && (a8==7))) && ((-148 < a14) && (13 >= a14)) )){
      if( a27 <= -78 ){
      a14 = (((a14 + -122526) / 5) + -451735);
      a21 = (((((a21 % 16)- 161) - 296949) - 181680) + 478630);
       a9 = 3;
      } else{
       a14 = (((a14 - 98423) * 5) - 88692);
       a27 = (((((a27 * 9)/ 10) + -50172) % 88)+ 84);
       a21 = ((((a21 % 16)- 160) * 1) + 1);
       a8 = 5;
       a9 = 6;
      } return -1;
     } else if(((a9==3) && (( a21 <= -178 && ((a8==4) && ((input == 1) && ((100 < a27) && (182 >= a27)) ))) && a14 <= -148 ))){
      a27 = (((a27 + -8298) / 5) * 5);
       a9 = 2;
       return -1;
     } else if((( 5 < a21 && ( a14 <= -148 && ( ((100 < a27) && (182 >= a27)) && ((input == 5) && ((a9==5) || (a9==6)))))) && (a8==6))){
      a27 = (((a27 * 5) + -188411) / 5);
      a21 = (((a21 / 5) * 4) + -535843);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((((a8==4) && ((input == 3) && ((a9==5) || (a9==6)))) && ((-144 < a21) && (5 >= a21)) ) && a27 <= -78 ) && ((-148 < a14) && (13 >= a14)) )){
      if((a9==2)){
      a14 = ((((a14 + -555494) - -753150) * 3) + -1077218);
       a8 = 5;
       a9 = 6;
      } else{
       a14 = (((a14 - 249011) * 2) - 47727);
       a21 = (((a21 - -290953) - -237704) - -13887);
       a8 = 5;
       a9 = 6;
      } return -1;
     } else if(((a8==5) && ((a9==5) && ( ((-78 < a27) && (100 >= a27)) && (( ((-144 < a21) && (5 >= a21)) && (input == 2)) && a14 <= -148 ))))){
      a27 = ((((a27 + -373393) + -62325) * 10)/ 9);
      a21 = ((((a21 - 232371) * 10)/ 9) + -261913);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==4) && (( ((-148 < a14) && (13 >= a14)) && ( a27 <= -78 && (((a9==3) || (a9==4)) && (input == 6)))) && ((-178 < a21) && (-144 >= a21)) ))){
      a14 = (((a14 + -564401) * 1) * 1);
      a27 = (((((a27 * 9)/ 10) * 1) % 88)- -80);
       a8 = 6;
       a9 = 6;
       return 23;
     } else if(((((a8==5) && ( a21 <= -178 && ((a9==5) && (input == 4)))) && a27 <= -78 ) && ((-148 < a14) && (13 >= a14)) )){
      if( ((13 < a14) && (182 >= a14)) ){
      a14 = ((((a14 - 21841) * 10)/ 9) / 5);
      a27 = ((((((a27 * 9)/ 10) % 88)- -51) - -569964) + -569918);
      a21 = ((((a21 / 5) / 5) % 16)- 159);
       a9 = 3;
      } else{
       a14 = ((((a14 - 184028) / 5) - -608682) + -842597);
       a27 = ((((a27 % 40)- -147) - -285186) - 285165);
       a21 = ((((a21 * 9)/ 10) + 553782) * 1);
       a8 = 4;
       a9 = 4;
      } return -1;
     } else if(( 5 < a21 && ((( a14 <= -148 && ((input == 1) && (a9==6))) && ((-78 < a27) && (100 >= a27)) ) && (a8==6)))){
      a27 = (((a27 + -117675) / 5) + -132988);
      a21 = (((((a21 + 0) * 9)/ 10) + -523981) - 18184);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((( a21 <= -178 && (input == 4)) && (a8==8)) && a27 <= -78 ) && (a9==6)) && a14 <= -148 )){
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && (((( ((100 < a27) && (182 >= a27)) && (input == 5)) && (a8==7)) && (a9==6)) && ((-178 < a21) && (-144 >= a21)) ))){
      a27 = (((a27 + 479258) - 887825) * 1);
      a21 = ((((a21 - -545484) / 5) - -156570) + -309067);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a27 <= -78 && ((a8==8) && (((a9==6) && ( 5 < a21 && (input == 3))) && a14 <= -148 )))){
      a21 = (((((a21 % 299911)- 300088) + -52922) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==5) && ( a14 <= -148 && ( ((-78 < a27) && (100 >= a27)) && (((input == 4) && (a9==3)) && ((-178 < a21) && (-144 >= a21)) ))))){
      a27 = (((a27 + -378264) + -117302) / 5);
      a21 = (((a21 + 96357) * 5) + -768291);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((((a8==5) && ((input == 1) && ((a9==4) || (a9==5)))) && ((-144 < a21) && (5 >= a21)) ) && a27 <= -78 ) && ((-148 < a14) && (13 >= a14)) )){
      a14 = (((((a14 + 492985) * -1)/ 10) * 10)/ 9);
      a27 = ((((a27 % 299908)+ 300090) - -171007) * 1);
      a21 = (((a21 / 5) - 589821) + 1167128);
       a9 = 2;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && ( a27 <= -78 && ((((input == 1) && ((a9==4) || (a9==5))) && (a8==6)) && ((-144 < a21) && (5 >= a21)) )))){
      a21 = (((((a21 % 16)+ -160) / 5) / 5) + -151);
       a9 = 6;
       return -1;
     } else if(((a8==5) && (((((((a9==5) && ((-144 < a21) && (5 >= a21)) ) || ((a9==6) && ((-144 < a21) && (5 >= a21)) )) || ((a9==2) && 5 < a21 )) && (input == 2)) && 182 < a27 ) && a14 <= -148 ))){
      a27 = ((((a27 - 0) * -5)/ 10) + -294512);
      a21 = (((((a21 % 299911)- 300088) + -2) / 5) + -4677);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==7) && ((((((a9==5) || ((a9==3) || (a9==4))) && (input == 2)) && a27 <= -78 ) && a14 <= -148 ) && ((-144 < a21) && (5 >= a21)) ))){
      a21 = ((((a21 - 499004) + -216) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((( a14 <= -148 && ((input == 1) && ((a9==4) || (a9==5)))) && 5 < a21 ) && ((100 < a27) && (182 >= a27)) ) && (a8==7))){
      a27 = ((((a27 + 578082) + -1025007) * 10)/ 9);
      a21 = ((((a21 - 0) + -245360) % 299911)+ -300088);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==8) && ((a9==6) && ( a21 <= -178 && ( a14 <= -148 && (input == 1))))) && a27 <= -78 )){
      a27 = (((((a27 * 9)/ 10) * 1) % 88)+ 58);
      a21 = ((((a21 % 74)- -2) - -3) + -4);
       a8 = 4;
       a9 = 4;
       return 25;
     } else if(((( ((100 < a27) && (182 >= a27)) && ( a14 <= -148 && ((input == 1) && (((a9==3) || (a9==4)) || (a9==5))))) && (a8==6)) && ((-178 < a21) && (-144 >= a21)) )){
      a27 = ((((a27 + -206334) + -281424) * 10)/ 9);
      a21 = ((((a21 * 10)/ 8) + -472925) - 71198);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((( ((-78 < a27) && (100 >= a27)) && (((a9==3) || (a9==4)) && (input == 5))) && a14 <= -148 ) && (a8==4)) && ((-144 < a21) && (5 >= a21)) )){
      a21 = (((((a21 - -68489) + 391020) / 5) * -1)/ 10);
       a8 = 7;
       a9 = 2;
       return 21;
     } else if(((a8==7) && (((((input == 5) && ((a9==4) || (a9==5))) && a14 <= -148 ) && ((100 < a27) && (182 >= a27)) ) && 5 < a21 ))){
      a27 = ((((a27 * 5) * 10)/ -9) + -461945);
      a21 = ((((a21 - 0) + -537339) % 299911)- 300088);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((a8==5) && ((((a9==4) || (a9==5)) && (input == 5)) && ((100 < a27) && (182 >= a27)) )) && a21 <= -178 ) && a14 <= -148 )){
      a27 = ((((a27 - 85268) + 541040) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==4) && (((input == 3) && (((a9==2) && ((-178 < a21) && (-144 >= a21)) ) || (((a9==5) && a21 <= -178 ) || ( a21 <= -178 && (a9==6))))) && 182 < a27 )) && a14 <= -148 )){
      a27 = (((a27 - 600168) / 5) - 325354);
      a21 = ((((a21 % 299911)- 178) - 135366) - 137780);
       a9 = 2;
       return -1;
     } else if((((( 182 < a27 && ((input == 5) && ((a9==5) || (a9==6)))) && (a8==7)) && a14 <= -148 ) && ((-178 < a21) && (-144 >= a21)) )){
      a27 = (((a27 + -28779) - 571357) + -24);
      a21 = (((a21 / 5) * 5) - 198791);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((( ((100 < a27) && (182 >= a27)) && (input == 3)) && a14 <= -148 ) && a21 <= -178 ) && (a9==2)) && (a8==4))){
      a27 = (((a27 + -541109) + -31128) - 10974);
       return -1;
     } else if(((a8==7) && ( a27 <= -78 && (( a21 <= -178 && ((input == 3) && (a9==2))) && ((-148 < a14) && (13 >= a14)) )))){
      a14 = (((a14 + -144668) * 4) + -18862);
      a21 = ((((a21 - -126413) % 16)+ -161) - 1);
       a8 = 6;
       a9 = 5;
       return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && ( a14 <= -148 && ((a8==6) && (((input == 3) && ((a9==3) || (a9==4))) && 5 < a21 ))))){
      a27 = (((a27 - 488335) / 5) * 5);
      a21 = ((((a21 % 299911)- 300088) - 112580) + -42396);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((-144 < a21) && (5 >= a21)) && ((a8==6) && ( ((100 < a27) && (182 >= a27)) && ((a9==6) && (input == 5))))) && a14 <= -148 )){
      a27 = (((a27 - 258108) + -237028) * 1);
      a21 = (((((a21 + 543499) - -47025) - 116330) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( 182 < a27 && ((( 5 < a21 && ((a9==6) && (a8==5))) || ( a21 <= -178 && ((a8==6) && (a9==2)))) && (input == 3))))){
      a27 = (((a27 - 600177) * 1) + -1);
      a21 = (((((a21 % 299911)- 300088) + -1) / 5) + -95340);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==7) && ((((a9==2) && (input == 1)) && ((-144 < a21) && (5 >= a21)) ) && ((100 < a27) && (182 >= a27)) )) && a14 <= -148 )){
      a27 = (((a27 - 360923) + 578689) - 465541);
      a21 = (((a21 / 5) * 5) - 387337);
       a8 = 4;
       return -1;
     } else if((( 5 < a21 && ((((input == 4) && (a8==8)) && (a9==4)) && a14 <= -148 )) && ((100 < a27) && (182 >= a27)) )){
       a8 = 4;
       a9 = 2;
       return 21;
     } else if(( 182 < a27 && ((a8==6) && ( a14 <= -148 && (((((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ((a9==2) && ((-144 < a21) && (5 >= a21)) )) || ( ((-144 < a21) && (5 >= a21)) && (a9==3))) && (input == 6)))))){
      a27 = ((((a27 - 402338) + -34244) + 341650) + -505158);
      a21 = (((((a21 + 132646) * 10)/ 9) * 10)/ 9);
       a8 = 7;
       a9 = 5;
       return 21;
     } else if(((( a14 <= -148 && ((((a9==2) || (a9==3)) && (input == 5)) && 5 < a21 )) && 182 < a27 ) && (a8==7))){
      if((a9==3)){
      a27 = ((((a27 % 88)+ 8) - 73) + 78);
       a8 = 5;
       a9 = 2;
      } else{
       a27 = (((a27 + -600141) - 26) - 10);
       a21 = (((((a21 % 16)- 159) - 3) + -594756) - -594741);
       a8 = 6;
       a9 = 4;
      } return 21;
     } else if(((((((((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ( ((-144 < a21) && (5 >= a21)) && (a9==2))) || ( ((-144 < a21) && (5 >= a21)) && (a9==3))) && (input == 6)) && 182 < a27 ) && a14 <= -148 ) && (a8==5))){
      a27 = ((((a27 - 0) + 0) % 88)+ 8);
      a21 = (((a21 + 170458) - 183268) * 5);
       a9 = 2;
       return 23;
     } else if(( a14 <= -148 && ( ((-78 < a27) && (100 >= a27)) && ( ((-178 < a21) && (-144 >= a21)) && ((a8==8) && ((input == 5) && ((a9==3) || (a9==4)))))))){
      a27 = (((((a27 - -235050) * 2) + -331088) * -1)/ 10);
      a21 = ((((a21 * 10)/ 8) - -82693) - 209279);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((-144 < a21) && (5 >= a21)) && ( 182 < a27 && ((a8==8) && (((a9==5) || (a9==6)) && (input == 4))))) && a14 <= -148 )){
      a27 = ((((a27 - 0) + -600141) + 86475) + -86436);
      a21 = ((((a21 % 16)+ -159) - 2) + -1);
       a8 = 5;
       a9 = 4;
       return -1;
     } else if((((a9==4) && ( ((-78 < a27) && (100 >= a27)) && ( ((-178 < a21) && (-144 >= a21)) && ((input == 6) && a14 <= -148 )))) && (a8==5))){
      a27 = (((a27 + -533593) / 5) + -349341);
      a21 = ((((a21 + 173692) - 422725) + 643724) + -450232);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-178 < a21) && (-144 >= a21)) && (( a14 <= -148 && ((a8==8) && (((a9==2) || (a9==3)) && (input == 4)))) && 182 < a27 ))){
      if((a8==8)){
      a27 = (((a27 + -600111) * 1) - 48);
       a9 = 5;
      } else{
       a14 = ((((a14 - 0) % 80)+ -66) - 1);
       a27 = ((((a27 + -600175) - -210698) * 1) + -210609);
       a21 = (((a21 / 5) - -512932) * 1);
       a8 = 7;
       a9 = 2;
      } return -1;
     } else if(( ((-178 < a21) && (-144 >= a21)) && (( ((100 < a27) && (182 >= a27)) && ((a8==4) && ((a9==6) && (input == 1)))) && a14 <= -148 ))){
       return 23;
     } else if(((a8==5) && (( ((-148 < a14) && (13 >= a14)) && ((( a21 <= -178 && (a9==6)) || ((a9==2) && ((-178 < a21) && (-144 >= a21)) )) && (input == 4))) && a27 <= -78 ))){
      a14 = (((a14 + 407830) + -800496) + -125857);
      a27 = ((((a27 - -497092) + -249112) % 299908)+ 300090);
      a21 = ((((a21 + 124141) + 417458) % 74)+ -69);
       a8 = 4;
       a9 = 6;
       return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && (((((input == 3) && a14 <= -148 ) && (a8==8)) && (a9==2)) && 5 < a21 ))){
      a27 = (((a27 + -162476) - 165198) * 1);
      a21 = ((((a21 % 299911)+ -300088) / 5) + -78905);
       a8 = 4;
       return -1;
     } else if(((( a14 <= -148 && ((((a9==6) || ((a9==4) || (a9==5))) && (input == 4)) && (a8==7))) && a27 <= -78 ) && ((-178 < a21) && (-144 >= a21)) )){
      a21 = (((a21 * 5) * 5) - 260336);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((((((a9==5) || (a9==6)) && (input == 3)) && a14 <= -148 ) && (a8==8)) && 5 < a21 ) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((a27 + -448132) + -16457) * 1);
      a21 = ((((a21 % 299911)- 300088) - 259736) - 9300);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a9==5) && ( ((-148 < a14) && (13 >= a14)) && (((a8==7) && ( a27 <= -78 && (input == 3))) && ((-144 < a21) && (5 >= a21)) )))){
      a14 = ((((a14 * 5) / 5) * 5) - 502676);
      a27 = (((((a27 % 40)- -157) + -234552) - -299903) + -65336);
       a8 = 8;
       return -1;
     } else if(( a14 <= -148 && (( 182 < a27 && ((input == 2) && ((((a9==5) && a21 <= -178 ) || ( a21 <= -178 && (a9==6))) || ( ((-178 < a21) && (-144 >= a21)) && (a9==2))))) && (a8==6)))){
      a27 = ((((((a27 * -5)/ 10) - -219728) + 93359) * -1)/ 10);
      a21 = (((((a21 % 299911)- 178) + 134968) - 54817) + -299648);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((-178 < a21) && (-144 >= a21)) && ((a9==5) && ( 182 < a27 && ((input == 4) && (a8==6))))) && a14 <= -148 )){
      a27 = (((((a27 * 9)/ 10) % 88)+ 2) / 5);
      a21 = ((((a21 * -1)/ 10) + 156677) * 3);
       a8 = 8;
       a9 = 6;
       return 25;
     } else if(((((a9==4) && (( a14 <= -148 && (input == 2)) && ((-144 < a21) && (5 >= a21)) )) && ((100 < a27) && (182 >= a27)) ) && (a8==7))){
      a27 = ((((((a27 - 50916) * 10)/ 9) + 83069) * -1)/ 10);
      a21 = (((a21 - 416610) * 1) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==7) && (((((a9==6) && ((-144 < a21) && (5 >= a21)) ) || ((a9==2) && 5 < a21 )) && (input == 1)) && a27 <= -78 )) && ((-148 < a14) && (13 >= a14)) )){
      if( ((13 < a14) && (182 >= a14)) ){
      a14 = (((((a14 + -480254) * 10)/ 9) * 10)/ 9);
      a27 = ((((((a27 % 299908)+ 300090) * 1) + -519500) * -1)/ 10);
      a21 = ((((a21 % 299997)- -300002) * 1) + 0);
       a8 = 5;
       a9 = 2;
      } else{
       a14 = (((a14 + -465720) - 29001) / 5);
       a21 = (((((a21 - 313378) % 299997)+ 300002) - 13366) + 13367);
       a8 = 4;
       a9 = 2;
      } return 21;
     } else if(( a14 <= -148 && ( 182 < a27 && (((( 5 < a21 && (a9==2)) || (((a9==5) && ((-144 < a21) && (5 >= a21)) ) || ( ((-144 < a21) && (5 >= a21)) && (a9==6)))) && (input == 4)) && (a8==5))))){
      a27 = (((a27 / 5) - 583537) + 42368);
      a21 = ((((a21 % 299911)- 300088) + 308017) - 308017);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((( a14 <= -148 && ( ((-178 < a21) && (-144 >= a21)) && (input == 5))) && (a8==5)) && (a9==2)) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((a27 - 348312) / 5) - 216480);
      a21 = (((a21 / 5) - 533493) * 1);
       a8 = 4;
       return -1;
     } else if((((a8==4) && ( a21 <= -178 && (( ((-148 < a14) && (13 >= a14)) && (input == 6)) && (a9==6)))) && a27 <= -78 )){
      if((a8==5)){
      a14 = (((a14 + -103407) + -367225) - 25431);
      a21 = (((((a21 * -1)/ 10) + 120927) - 507344) + 757098);
       a8 = 5;
       a9 = 5;
      } else{
       a14 = (((((a14 + -82706) * 5) + 549800) * -1)/ 10);
       a27 = (((((a27 + 521809) % 299908)+ 300090) + -193584) + 193586);
       a21 = (((((a21 % 16)- 155) - 475574) / 5) - -94993);
       a8 = 5;
       a9 = 3;
      } return -1;
     } else if(((((a8==6) && (((input == 6) && 5 < a21 ) && 182 < a27 )) && a14 <= -148 ) && (a9==2))){
      a27 = (((a27 / 5) + -381202) - -251483);
      a21 = (((((a21 + 0) - 484456) - 8825) % 299911)- 300088);
       a8 = 4;
       return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && (( a14 <= -148 && (((a9==4) && (input == 1)) && (a8==8))) && 5 < a21 ))){
      a21 = ((((a21 + -145122) - 319628) % 74)+ -68);
       a8 = 4;
       a9 = 5;
       return 21;
     } else if(((a8==5) && (((((((a9==5) && ((-178 < a21) && (-144 >= a21)) ) || ((a9==6) && ((-178 < a21) && (-144 >= a21)) )) || ( ((-144 < a21) && (5 >= a21)) && (a9==2))) && (input == 6)) && a27 <= -78 ) && ((-148 < a14) && (13 >= a14)) ))){
      a14 = (((a14 - 454358) - -440019) * 5);
      a21 = ((((a21 + 451993) * 10)/ 9) * 1);
       a9 = 5;
       return -1;
     } else if(( 182 < a27 && ((a8==5) && ( a14 <= -148 && ((((a9==2) && ((-178 < a21) && (-144 >= a21)) ) || (( a21 <= -178 && (a9==5)) || ( a21 <= -178 && (a9==6)))) && (input == 4)))))){
      a27 = (((((a27 % 88)- -2) * 9)/ 10) / 5);
      a21 = (((a21 / 5) - -266852) * 2);
       a8 = 8;
       a9 = 6;
       return 25;
     } else if(((a8==8) && (( ((-178 < a21) && (-144 >= a21)) && ( 182 < a27 && ((input == 5) && ((a9==2) || (a9==3))))) && a14 <= -148 ))){
      if((a9==6)){
      a14 = ((((a14 % 80)- 3) - 467933) - -467898);
      a27 = (((a27 / 5) / 5) + -248803);
      a21 = (((a21 + -590404) - 7780) - 497);
       a8 = 7;
       a9 = 6;
      } else{
       a27 = (((a27 / 5) / 5) + -465667);
       a21 = ((((a21 + -298782) - -763044) * 10)/ 9);
       a8 = 4;
       a9 = 2;
      } return -1;
     } else if((( 182 < a27 && ((((input == 4) && (((a9==4) || (a9==5)) || (a9==6))) && a14 <= -148 ) && (a8==6))) && ((-144 < a21) && (5 >= a21)) )){
      a27 = ((((a27 * 9)/ 10) / 5) - 493872);
      a21 = ((((a21 - 163242) / 5) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && (( 182 < a27 && (((input == 4) && ((a9==4) || (a9==5))) && (a8==8))) && ((-178 < a21) && (-144 >= a21)) ))){
      a27 = (((((a27 + -600155) / 5) + 392093) * -1)/ 10);
      a21 = (((((a21 * 10)/ 13) - -33) + -40730) + 40773);
       a8 = 4;
       a9 = 5;
       return 23;
     } else if((((a8==7) && (((input == 1) && ((( ((-144 < a21) && (5 >= a21)) && (a9==5)) || ((a9==6) && ((-144 < a21) && (5 >= a21)) )) || ((a9==2) && 5 < a21 ))) && ((-78 < a27) && (100 >= a27)) )) && a14 <= -148 )){
      a27 = (((a27 + -92138) + -402940) - -198508);
      a21 = ((((a21 % 299911)+ -300088) - 1) - 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( 182 < a27 && (( a21 <= -178 && ((((a9==4) || ((a9==2) || (a9==3))) && (input == 3)) && (a8==4))) && a14 <= -148 ))){
      a27 = (((((((a27 * 9)/ 10) % 40)- -138) / 5) * 38)/ 10);
      a21 = (((((a21 - -247189) % 16)+ -161) / 5) - 133);
       a8 = 5;
       a9 = 6;
       return 21;
     } else if((( 5 < a21 && (((a8==8) && (((a9==5) || (a9==6)) && (input == 6))) && ((100 < a27) && (182 >= a27)) )) && a14 <= -148 )){
      a27 = (((((a27 * 10)/ -9) * 10)/ 9) - 23635);
      a21 = ((((a21 % 299911)+ -300088) + -5422) - 88893);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( 5 < a21 && ((((((a9==6) || ((a9==4) || (a9==5))) && (input == 6)) && a27 <= -78 ) && ((-148 < a14) && (13 >= a14)) ) && (a8==4)))){
      if( ((-144 < a21) && (5 >= a21)) ){
      a14 = (((a14 + -509107) - 63408) * 1);
      a21 = ((((a21 % 299911)+ -300088) - 110303) / 5);
       a8 = 6;
       a9 = 4;
      } else{
       a14 = (((a14 - 122093) + 339452) + -712455);
       a27 = (((((a27 - 0) / 5) - 363880) % 88)- -53);
       a21 = ((((a21 % 16)+ -166) - 83801) - -83805);
       a9 = 4;
      } return -1;
     } else if(((( ((100 < a27) && (182 >= a27)) && (( a14 <= -148 && (input == 5)) && a21 <= -178 )) && (a8==4)) && (a9==4))){
      if( a14 <= -148 ){
      a27 = (((a27 - -275059) + 86321) - -172683);
      a21 = ((((a21 % 16)- 159) - -9) + 1);
       a8 = 7;
       a9 = 6;
      } else{
       a21 = ((((a21 / 5) % 74)- 50) - 15);
       a9 = 6;
      } return 21;
     } else if((( a14 <= -148 && ( ((-178 < a21) && (-144 >= a21)) && ((a9==5) && ((a8==6) && (input == 1))))) && 182 < a27 )){
      a27 = (((a27 / 5) - 567305) * 1);
      a21 = ((((a21 * 10)/ 8) * 5) * 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a27 <= -78 && (((((((a8==7) && (a9==6)) && 5 < a21 ) || (((a8==8) && (a9==2)) && a21 <= -178 )) || ( a21 <= -178 && ((a9==3) && (a8==8)))) && (input == 5)) && a14 <= -148 ))){
      a21 = ((((((a21 * 9)/ 10) % 299911)- 300088) - -465939) - 465939);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && (((a8==7) && (( 5 < a21 && (input == 6)) && (a9==6))) && a14 <= -148 ))){
      a27 = ((((a27 - 110878) * 10)/ 9) + -30278);
      a21 = ((((a21 % 299911)- 300088) - 91726) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((((input == 6) && a21 <= -178 ) && a14 <= -148 ) && ((100 < a27) && (182 >= a27)) ) && (a8==4)) && (a9==4))){
      a27 = (((a27 / 5) * 5) - 177004);
       a9 = 2;
       return -1;
     } else if(((( a27 <= -78 && ( ((-144 < a21) && (5 >= a21)) && ((a8==7) && (input == 2)))) && a14 <= -148 ) && (a9==2))){
      if( ((-78 < a27) && (100 >= a27)) ){
      a27 = ((((a27 % 299908)+ 300090) * 1) - -246957);
      a21 = (((a21 - 467421) + -5630) + -88837);
       a9 = 6;
      } else{
       a21 = (((a21 + -122629) + -228133) * 1);
       a8 = 8;
       a9 = 4;
      } return 21;
     } else if((((a8==5) && ( a21 <= -178 && (((input == 1) && ((a9==2) || (a9==3))) && a14 <= -148 ))) && ((-78 < a27) && (100 >= a27)) )){
       a8 = 8;
       a9 = 2;
       return 23;
     } else if(( ((-148 < a14) && (13 >= a14)) && ((a8==5) && (((( a21 <= -178 && (a9==6)) || ( ((-178 < a21) && (-144 >= a21)) && (a9==2))) && (input == 3)) && a27 <= -78 )))){
      if((a8==5)){
      a14 = ((((a14 * 5) + -505652) * 10)/ 9);
      a27 = ((((a27 / 5) % 88)- -55) - -45);
      a21 = (((((a21 * 9)/ 10) - 16675) % 16)+ -161);
       a8 = 4;
       a9 = 4;
      } else{
       a14 = (((a14 * 5) - 352201) * 1);
       a21 = (((((a21 + 0) % 16)+ -159) + 154049) - 154044);
       a9 = 6;
      } return 23;
     } else if(((a8==6) && ( ((-178 < a21) && (-144 >= a21)) && (( a14 <= -148 && (((a9==3) || (a9==4)) && (input == 6))) && ((-78 < a27) && (100 >= a27)) )))){
      a27 = ((((a27 / 5) / 5) / 5) + -567452);
      a21 = (((a21 + 501794) - 815377) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==5) && ((((input == 4) && ((-144 < a21) && (5 >= a21)) ) && a14 <= -148 ) && (a9==4))) && 182 < a27 )){
      a27 = ((((a27 / 5) / 5) % 40)- -111);
      a21 = (((((a21 + 431246) * 1) + -489697) * -1)/ 10);
       a8 = 6;
       a9 = 5;
       return 21;
     } else if(( a27 <= -78 && ((a8==7) && (((((a9==4) || (a9==5)) && (input == 5)) && ((-148 < a14) && (13 >= a14)) ) && 5 < a21 )))){
      a14 = (((a14 - 203968) / 5) - -31253);
      a21 = ((((((a21 % 16)+ -170) * 5) + 250846) % 16)+ -175);
       a8 = 4;
       a9 = 4;
       return -1;
     } else if((( ((-148 < a14) && (13 >= a14)) && (((a8==4) && ((input == 3) && ((a9==3) || (a9==4)))) && a27 <= -78 )) && ((-144 < a21) && (5 >= a21)) )){
      a14 = (((a14 + -571386) / 5) - 98703);
       a8 = 5;
       a9 = 4;
       return 25;
     } else if((( a21 <= -178 && ((a8==8) && ( ((100 < a27) && (182 >= a27)) && ((((a9==3) || (a9==4)) || (a9==5)) && (input == 1))))) && a14 <= -148 )){
       a8 = 4;
       a9 = 3;
       return -1;
     } else if(((a8==8) && ( a27 <= -78 && ((a9==5) && ( a14 <= -148 && ( 5 < a21 && (input == 4))))))){
      if((a9==4)){
      a27 = (((((a27 % 299908)+ 300090) * 1) * 10)/ 9);
      a21 = ((((((a21 * 9)/ 10) % 16)- 159) * 10)/ 9);
       a8 = 6;
       a9 = 2;
      } else{
       a27 = ((((a27 % 88)+ 89) / 5) / 5);
       a8 = 5;
       a9 = 3;
      } return 25;
     } else if(((input == 4) && ((((( ((-148 < a14) && (13 >= a14)) && a27 <= -78 ) && (a8==4)) && (a9==2)) && a21 <= -178 ) || ((((a9==5) && ((a8==8) && ( a14 <= -148 && 182 < a27 ))) && 5 < a21 ) || (((a9==6) && (( 182 < a27 && a14 <= -148 ) && (a8==8))) && 5 < a21 ))))){
      a14 = ((((a14 % 299926)+ -300073) * 1) + -2);
      a27 = ((((a27 % 299961)- 300038) * 1) - 1);
      a21 = ((((a21 % 299911)+ -300088) + -1) + 0);
       a8 = 6;
       a9 = 6;
       return 23;
     } else if(((a8==7) && ( ((-78 < a27) && (100 >= a27)) && (((((a9==2) && ((-178 < a21) && (-144 >= a21)) ) || (((a9==5) && a21 <= -178 ) || ( a21 <= -178 && (a9==6)))) && (input == 5)) && a14 <= -148 )))){
      a27 = ((((a27 * 5) * 5) / 5) + -421099);
      a21 = ((((a21 % 299911)- 178) * 1) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-178 < a21) && (-144 >= a21)) && ((((((a9==4) || (a9==5)) && (input == 2)) && a14 <= -148 ) && (a8==5)) && 182 < a27 ))){
      a27 = ((((a27 * -5)/ 10) / 5) - 15686);
      a21 = (((((a21 / 5) + 210923) - -185589) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((((input == 3) && (((a9==2) || (a9==3)) || (a9==4))) && a27 <= -78 ) && ((-148 < a14) && (13 >= a14)) ) && (a8==7)) && ((-144 < a21) && (5 >= a21)) )){
      a14 = (((a14 / 5) + -99512) + -18092);
       a9 = 2;
       return -1;
     } else if(( 182 < a27 && ((((input == 5) && ((((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ( ((-144 < a21) && (5 >= a21)) && (a9==2))) || ( ((-144 < a21) && (5 >= a21)) && (a9==3)))) && (a8==6)) && a14 <= -148 ))){
      a27 = (((a27 + 0) + -82039) - 518079);
      a21 = (((a21 / 5) - 570762) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( 182 < a27 && ((((input == 1) && (((a9==3) && ((-144 < a21) && (5 >= a21)) ) || (( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ((a9==2) && ((-144 < a21) && (5 >= a21)) )))) && a14 <= -148 ) && (a8==6)))){
      a27 = (((a27 + -600136) + -8) * 1);
      a21 = (((((a21 - 526378) - -776110) * 2) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==8) && (( ((-178 < a21) && (-144 >= a21)) && (((input == 3) && ((a9==4) || (a9==5))) && 182 < a27 )) && a14 <= -148 ))){
      a27 = (((a27 - 600147) * 1) * 1);
       a8 = 4;
       a9 = 4;
       return 21;
     } else if(( 5 < a21 && (((((((a9==4) || (a9==5)) || (a9==6)) && (input == 4)) && 182 < a27 ) && (a8==7)) && a14 <= -148 ))){
      if((a9==5)){
      a27 = ((((a27 - 0) + 0) * -5)/ 10);
      a21 = (((((a21 % 74)- 88) - -225936) * 2) - 451837);
       a8 = 5;
       a9 = 3;
      } else{
       a27 = (((a27 / 5) - 216531) + -233921);
       a8 = 6;
       a9 = 6;
      } return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && ((a8==7) && ( a14 <= -148 && ((( a21 <= -178 && (a9==6)) || ( ((-178 < a21) && (-144 >= a21)) && (a9==2))) && (input == 1)))))){
      a27 = ((((a27 * -8)/ 10) - 382236) * 1);
      a21 = ((((a21 + 486337) % 74)- 68) + -2);
       a8 = 6;
       a9 = 3;
       return -1;
     } else if((( ((-78 < a27) && (100 >= a27)) && (((((a9==2) || (a9==3)) && (input == 3)) && a14 <= -148 ) && (a8==5))) && a21 <= -178 )){
      a21 = (((a21 / 5) - -11669) + 352089);
       a8 = 7;
       a9 = 6;
       return 25;
     } else if(((((((input == 3) && ((a9==6) || ((a9==4) || (a9==5)))) && 182 < a27 ) && (a8==7)) && 5 < a21 ) && a14 <= -148 )){
      a27 = (((((a27 * 9)/ 10) + -143453) % 40)- -141);
      a21 = ((((a21 * 9)/ 10) + -413835) - 135072);
       a8 = 4;
       a9 = 4;
       return 25;
     } else if((((a8==7) && ( a14 <= -148 && ( ((-144 < a21) && (5 >= a21)) && ((((a9==3) || (a9==4)) || (a9==5)) && (input == 3))))) && a27 <= -78 )){
      a21 = (((a21 + -141122) / 5) / 5);
       a8 = 8;
       a9 = 6;
       return 23;
     } else if((((a8==7) && ( 182 < a27 && (((input == 3) && ((a9==2) || (a9==3))) && a14 <= -148 ))) && 5 < a21 )){
      a27 = ((((a27 + -567331) + 136139) * 1) - 168946);
       a8 = 5;
       a9 = 6;
       return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && ( a14 <= -148 && ( ((-144 < a21) && (5 >= a21)) && (((input == 6) && ((a9==3) || (a9==4))) && (a8==5)))))){
      a27 = (((a27 * 5) - -474051) + -745283);
      a21 = (((a21 + -520594) - 51811) - 27433);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a27 <= -78 && (((((((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ((a9==2) && ((-144 < a21) && (5 >= a21)) )) || ((a9==3) && ((-144 < a21) && (5 >= a21)) )) && (input == 1)) && (a8==8)) && a14 <= -148 ))){
      a27 = (((((a27 / 5) % 88)- -59) + -202715) - -202693);
      a21 = (((a21 / 5) + -273896) + -303296);
       a8 = 5;
       a9 = 6;
       return 23;
     } else if(( ((-178 < a21) && (-144 >= a21)) && (((a8==4) && (( ((-148 < a14) && (13 >= a14)) && (input == 2)) && a27 <= -78 )) && (a9==5)))){
      a14 = (((a14 - 497657) / 5) + -494426);
      a21 = (((a21 - -555931) + -990135) - -434350);
       a9 = 2;
       return 25;
     } else if(( a14 <= -148 && ((a8==7) && ((((input == 2) && a27 <= -78 ) && (a9==3)) && a21 <= -178 )))){
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( 5 < a21 && ((a8==6) && ( ((-78 < a27) && (100 >= a27)) && ( a14 <= -148 && ((input == 3) && (a9==6))))))){
      a27 = ((((a27 - -166439) * -1)/ 10) - 501717);
      a21 = ((((a21 - 0) / 5) / 5) + -135154);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && (( ((-178 < a21) && (-144 >= a21)) && ((a8==4) && ((input == 2) && a14 <= -148 ))) && (a9==6)))){
      a27 = ((((a27 * -8)/ 10) + -462905) + -95574);
      a21 = ((((a21 - 423415) / 5) * 10)/ 9);
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((a9==5) && ( ((-144 < a21) && (5 >= a21)) && (((input == 4) && ((-78 < a27) && (100 >= a27)) ) && (a8==5)))))){
      a21 = (((a21 + 174232) * 3) + 51070);
       a8 = 8;
       return 25;
     } else if((( ((-148 < a14) && (13 >= a14)) && (( a27 <= -78 && (((a9==3) || (a9==4)) && (input == 1))) && (a8==6))) && 5 < a21 )){
      a14 = (((a14 * 5) + -323953) - 120523);
      a27 = (((((a27 % 299908)+ 300090) * 1) - 297455) - -553250);
      a21 = ((((a21 % 16)- 168) + -2) + -6);
       a8 = 4;
       a9 = 3;
       return -1;
     } else if(((((( ((-144 < a21) && (5 >= a21)) && (input == 6)) && a27 <= -78 ) && (a8==6)) && ((-148 < a14) && (13 >= a14)) ) && (a9==3))){
      a14 = (((a14 - 7984) / 5) + -95751);
       return -1;
     } else if(( a21 <= -178 && ((a9==5) && ( a27 <= -78 && ((a8==5) && ( ((-148 < a14) && (13 >= a14)) && (input == 5))))))){
      a14 = ((((((a14 + 345752) * 10)/ -9) - -664850) * -1)/ 10);
      a21 = ((((a21 % 74)+ 2) + -812) + 761);
       a8 = 4;
       a9 = 6;
       return 21;
     } else if((((a8==5) && ( ((100 < a27) && (182 >= a27)) && ( a14 <= -148 && (((a9==6) || ((a9==4) || (a9==5))) && (input == 1))))) && ((-144 < a21) && (5 >= a21)) )){
      a27 = (((a27 / 5) - 201698) + 414132);
      a21 = ((((((a21 % 16)+ -160) + 1) * 5) % 16)- 159);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( ((-178 < a21) && (-144 >= a21)) && ((a9==5) && ((a8==4) && (input == 3)))) && a27 <= -78 ) && ((-148 < a14) && (13 >= a14)) )){
      a14 = (((a14 / 5) - 117630) * 5);
       a9 = 4;
       return -1;
     } else if(((a8==4) && (( a21 <= -178 && (((input == 3) && ((a9==5) || ((a9==3) || (a9==4)))) && ((-148 < a14) && (13 >= a14)) )) && a27 <= -78 ))){
      if((a8==8)){
      a14 = ((((a14 - 353961) / 5) * 10)/ 9);
      a27 = ((((a27 % 88)- -84) - 32) - -43);
      a21 = ((((a21 - 0) % 74)- 12) + 10);
       a8 = 5;
       a9 = 3;
      } else{
       a14 = (((a14 - 367268) / 5) + -385346);
       a21 = (((((a21 % 74)+ 4) + 1) - -429046) + -429117);
       a8 = 5;
       a9 = 2;
      } return 23;
     } else if(((((a8==5) && (((input == 2) && ((-148 < a14) && (13 >= a14)) ) && 5 < a21 )) && a27 <= -78 ) && (a9==5))){
      a21 = ((((((a21 % 74)+ -122) * 10)/ 9) * 9)/ 10);
       a8 = 7;
       return 25;
     } else if(( ((-148 < a14) && (13 >= a14)) && (((((input == 4) && (a9==3)) && (a8==7)) && a27 <= -78 ) && a21 <= -178 ))){
      if((a8==8)){
      a14 = (((a14 * 5) - -167088) - 456837);
      a27 = ((((a27 % 299908)- -300090) - -255510) - -39665);
      a21 = ((((a21 % 74)- -3) - -504995) - 505012);
       a8 = 8;
      } else{
       a14 = (((a14 + -219223) + -307424) - -175107);
       a21 = ((((a21 - 0) % 16)- 146) - 2);
       a8 = 4;
       a9 = 5;
      } return -1;
     } else if(((((( 5 < a21 && (input == 2)) && (a9==3)) && a27 <= -78 ) && ((-148 < a14) && (13 >= a14)) ) && (a8==7))){
      a14 = (((((a14 + -585259) * 1) - -900097) * -1)/ 10);
      a27 = (((((a27 / 5) - 33330) + 65163) % 40)- -142);
      a21 = (((((a21 % 74)- 111) / 5) + 476251) + -476276);
       a8 = 6;
       a9 = 6;
       return -1;
     } else if(( ((-144 < a21) && (5 >= a21)) && ((a9==5) && ((a8==7) && (((input == 1) && ((-148 < a14) && (13 >= a14)) ) && a27 <= -78 ))))){
      if((a8==8)){
      a14 = (((a14 + -560461) * 1) * 1);
      a27 = ((((a27 % 299908)+ 300090) + 255984) - -37520);
      a21 = (((a21 / 5) / 5) + -52445);
       a8 = 8;
       a9 = 2;
      } else{
       a14 = (((a14 - 598182) - 1132) + -164);
       a27 = (((a27 / 5) + 177451) / 5);
       a21 = (((a21 + 578976) * 1) - -1898);
       a8 = 5;
       a9 = 3;
      } return -1;
     } else if((((a8==4) && ( a14 <= -148 && ((((a9==2) && ((-178 < a21) && (-144 >= a21)) ) || (( a21 <= -178 && (a9==5)) || ( a21 <= -178 && (a9==6)))) && (input == 1)))) && 182 < a27 )){
      if((a9==3)){
      a21 = ((((a21 % 16)- 158) + -383837) + 383842);
       a9 = 4;
      } else{
       a27 = ((((a27 / 5) + -426555) % 88)- -56);
       a21 = (((((a21 % 16)- 148) - 10) - -10419) - 10421);
       a8 = 6;
       a9 = 3;
      } return -1;
     } else if(( a14 <= -148 && ((((a8==6) && ((input == 2) && ((a9==3) || (a9==4)))) && 182 < a27 ) && ((-178 < a21) && (-144 >= a21)) ))){
      a27 = ((((a27 - 190339) % 88)+ 11) + -1);
      a21 = (((a21 - -135) + 454687) + -454778);
       a8 = 5;
       a9 = 3;
       return 21;
     } else if(((a8==7) && ((( 182 < a27 && ((input == 5) && (((a9==2) || (a9==3)) || (a9==4)))) && ((-178 < a21) && (-144 >= a21)) ) && a14 <= -148 ))){
      a27 = (((a27 + -600119) - 62) + -2);
      a21 = (((((a21 * 10)/ 8) - 355688) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a14 <= -148 && (((((a9==4) || (a9==5)) && (input == 6)) && (a8==8)) && ((-178 < a21) && (-144 >= a21)) )) && 182 < a27 )){
      a27 = (((a27 + -600176) + -3) - 2);
      a21 = (((a21 + 410959) - -186211) + 1069);
       a8 = 5;
       a9 = 5;
       return -1;
     } else if((( a27 <= -78 && (((input == 4) && (( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ((a9==2) && ((-144 < a21) && (5 >= a21)) ))) && ((-148 < a14) && (13 >= a14)) )) && (a8==4))){
      a14 = (((((a14 - 372953) - -820886) / 5) * -1)/ 10);
      a21 = (((((a21 % 16)+ -160) * 5) % 16)- 158);
       a8 = 6;
       a9 = 4;
       return -1;
     } else if(( a14 <= -148 && (((((input == 3) && (((a9==4) || (a9==5)) || (a9==6))) && a21 <= -178 ) && (a8==8)) && 182 < a27 ))){
      a27 = ((((a27 % 40)- -130) + 110817) - 110827);
       a8 = 7;
       a9 = 6;
       return -1;
     } else if((((( ((100 < a27) && (182 >= a27)) && ((input == 2) && (a9==3))) && a14 <= -148 ) && (a8==8)) && ((-144 < a21) && (5 >= a21)) )){
      a27 = ((((((a27 * -1)/ 10) * 9)/ 10) - 331237) + 331193);
      a21 = ((((((a21 % 16)- 160) - -1) * 5) % 16)+ -160);
       a8 = 5;
       a9 = 2;
       return 23;
     } else if(((((((input == 4) && a14 <= -148 ) && ((-178 < a21) && (-144 >= a21)) ) && ((-78 < a27) && (100 >= a27)) ) && (a8==6)) && (a9==5))){
      a27 = (((((a27 + -398317) + -110567) + 939836) * -1)/ 10);
      a21 = (((a21 - 586455) - 4452) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && (((a8==6) && ((input == 5) && ((( ((-144 < a21) && (5 >= a21)) && (a9==5)) || ((a9==6) && ((-144 < a21) && (5 >= a21)) )) || ( 5 < a21 && (a9==2))))) && ((-78 < a27) && (100 >= a27)) ))){
      a27 = (((a27 + -49941) * 5) + -217804);
      a21 = (((((a21 % 299911)- 300088) * 1) - -442336) - 442336);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((((( 5 < a21 && ((a9==5) && (a8==4))) || (((a9==6) && (a8==4)) && 5 < a21 )) || (((a9==2) && (a8==5)) && a21 <= -178 )) && (input == 5)) && 182 < a27 ))){
      a27 = ((((a27 * 9)/ 10) - 565355) / 5);
      a21 = (((((a21 % 299997)+ 300002) - 0) / 5) - -322605);
       a8 = 8;
       a9 = 6;
       return 21;
     } else if(((a8==7) && ( a21 <= -178 && ( a14 <= -148 && ( ((-78 < a27) && (100 >= a27)) && (((a9==3) || (a9==4)) && (input == 6))))))){
      a27 = (((a27 + -77089) * 5) - 3983);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((((a8==7) && ((input == 5) && ((a9==4) || (a9==5)))) && ((-178 < a21) && (-144 >= a21)) ) && a14 <= -148 ) && ((100 < a27) && (182 >= a27)) )){
      a27 = ((((a27 * -8)/ 10) - 393193) * 1);
      a21 = ((((a21 + 140892) * 10)/ 9) + 107917);
       a8 = 4;
       a9 = 5;
       return -1;
     } else if(((( a14 <= -148 && (((input == 5) && ((a9==4) || (a9==5))) && a27 <= -78 )) && 5 < a21 ) && (a8==7))){
      a21 = (((((a21 % 16)- 164) / 5) * 10)/ 2);
       a8 = 8;
       a9 = 6;
       return 25;
     } else if(( ((100 < a27) && (182 >= a27)) && (( a14 <= -148 && ((input == 4) && (( a21 <= -178 && (a9==6)) || ( ((-178 < a21) && (-144 >= a21)) && (a9==2))))) && (a8==4)))){
      a27 = (((((a27 * -8)/ 10) - -541993) * -1)/ 10);
      a21 = (((((a21 + 116960) % 16)+ -161) + -177804) - -177805);
       a8 = 7;
       a9 = 3;
       return -1;
     } else if(((((input == 3) && ((((a9==2) && (a8==5)) && a21 <= -178 ) || (( 5 < a21 && ((a8==4) && (a9==5))) || ( 5 < a21 && ((a8==4) && (a9==6)))))) && a14 <= -148 ) && 182 < a27 )){
      a27 = ((((((a27 * 9)/ 10) * 1) + -505440) % 88)- -11);
      a21 = (((((a21 + 0) % 299911)- 300088) - -16088) - 16088);
       a8 = 4;
       a9 = 2;
       return 25;
     } else if((( ((-178 < a21) && (-144 >= a21)) && ((((input == 5) && ((a9==5) || ((a9==3) || (a9==4)))) && a27 <= -78 ) && (a8==7))) && ((-148 < a14) && (13 >= a14)) )){
      if((a8==5)){
      a14 = (((a14 * 5) + -514904) * 1);
      a21 = (((a21 * 5) * 5) + -465292);
       a8 = 8;
       a9 = 6;
      } else{
       a14 = (((a14 - 408576) * 1) + -164194);
       a27 = (((((a27 % 88)- -76) - -5) + 57571) + -57553);
       a21 = ((((a21 * 5) * 10)/ -9) / 5);
       a8 = 4;
       a9 = 6;
      } return -1;
     } else if(( a21 <= -178 && ((( a14 <= -148 && ((input == 1) && (a8==7))) && (a9==6)) && 182 < a27 ))){
      a27 = (((a27 - 600083) + -77) + -9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( a21 <= -178 && (((input == 2) && ((-148 < a14) && (13 >= a14)) ) && (a8==4))) && (a9==6)) && a27 <= -78 )){
      if( a21 <= -178 ){
      a14 = (((((a14 - 437625) + 309218) + 548040) * -1)/ 10);
      a27 = (((((a27 % 40)+ 155) / 5) - -86319) + -86174);
      a21 = (((a21 + 600055) - -47) + 46);
       a8 = 5;
      } else{
       a14 = ((((a14 + -491434) - -494736) * 5) + -359682);
       a21 = (((a21 - -600157) + 9) - -3);
       a8 = 7;
       a9 = 2;
      } return -1;
     } else if((( 182 < a27 && (((a9==2) && ((a8==6) && (input == 3))) && 5 < a21 )) && a14 <= -148 )){
      a27 = (((a27 - 600114) + -68) * 1);
      a21 = ((((a21 % 299911)+ -300088) - 199738) + -65053);
       a8 = 4;
       return -1;
     } else if(((((((input == 1) && ((a9==2) || (a9==3))) && a21 <= -178 ) && ((100 < a27) && (182 >= a27)) ) && (a8==6)) && a14 <= -148 )){
      a27 = ((((a27 + 576656) + 20430) / 5) - 545159);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a21 <= -178 && (((((input == 4) && ((a9==4) || ((a9==2) || (a9==3)))) && (a8==4)) && 182 < a27 ) && a14 <= -148 ))){
      a27 = (((((a27 / 5) + 4091) + 92606) * -1)/ 10);
       a9 = 2;
       return -1;
     } else if(((((a8==7) && (((input == 5) && ((100 < a27) && (182 >= a27)) ) && ((-144 < a21) && (5 >= a21)) )) && a14 <= -148 ) && (a9==3))){
      a27 = (((((a27 * -8)/ 10) - -577697) / 5) - 711400);
      a21 = (((a21 - 430880) * 1) - -2736);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((((a9==5) && (input == 3)) && (a8==7)) && 182 < a27 ) && a21 <= -178 ) && a14 <= -148 )){
      a27 = (((a27 - 0) + -600104) - 74);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((( a14 <= -148 && ((input == 2) && ((a9==4) || (a9==5)))) && (a8==8)) && ((-178 < a21) && (-144 >= a21)) ) && ((100 < a27) && (182 >= a27)) )){
       a8 = 4;
       a9 = 2;
       return 23;
     } else if(( 182 < a27 && ( a14 <= -148 && ((a8==4) && ((input == 5) && ((( ((-178 < a21) && (-144 >= a21)) && (a9==5)) || ( ((-178 < a21) && (-144 >= a21)) && (a9==6))) || ( ((-144 < a21) && (5 >= a21)) && (a9==2)))))))){
      a27 = ((((a27 - 600150) - -457159) / 5) - 521696);
      a21 = (((a21 - 221313) + -155963) - 169271);
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( ((-78 < a27) && (100 >= a27)) && (((a9==3) && ((input == 6) && 5 < a21 )) && (a8==7))))){
      a27 = (((a27 / 5) * 5) + -259653);
      a21 = ((((a21 * 9)/ 10) + -554715) - 41237);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a21 <= -178 && ((( ((-78 < a27) && (100 >= a27)) && ((input == 4) && ((a9==3) || (a9==4)))) && a14 <= -148 ) && (a8==7)))){
      a27 = (((a27 + -4653) * 5) * 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((((((a8==6) && (a9==5)) && 5 < a21 ) || ( 5 < a21 && ((a8==6) && (a9==6)))) || ( a21 <= -178 && ((a9==2) && (a8==7)))) && (input == 4)) && a14 <= -148 ) && 182 < a27 )){
      a27 = ((((a27 / 5) / 5) / 5) - 268250);
      a21 = ((((((a21 % 299911)- 300088) - 2) * 9)/ 10) + -22618);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==7) && ((((((a9==3) || (a9==4)) && (input == 3)) && ((-78 < a27) && (100 >= a27)) ) && a21 <= -178 ) && a14 <= -148 ))){
      a27 = (((((a27 * 5) + 306628) - -25808) % 40)- -119);
      a21 = (((((a21 - 0) % 16)+ -144) / 5) - 145);
       a8 = 6;
       a9 = 4;
       return 23;
     } else if(((( 182 < a27 && (((a8==7) && (input == 3)) && a21 <= -178 )) && (a9==6)) && a14 <= -148 )){
      a27 = (((((a27 + 0) / 5) / 5) % 88)- 14);
       a8 = 4;
       a9 = 4;
       return 25;
     } else if(( ((-78 < a27) && (100 >= a27)) && (((((input == 1) && (a9==2)) && a14 <= -148 ) && (a8==4)) && ((-178 < a21) && (-144 >= a21)) ))){
      a27 = (((a27 * 5) * 5) - 464504);
      a21 = (((a21 / 5) + -396717) + 336542);
       return -1;
     } else if(( a21 <= -178 && ((a8==7) && (( a14 <= -148 && ((input == 4) && (((a9==4) || (a9==5)) || (a9==6)))) && a27 <= -78 )))){
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((( ((100 < a27) && (182 >= a27)) && ((input == 2) && ((a9==4) || (a9==5)))) && 5 < a21 ) && (a8==7)))){
      a21 = ((((a21 % 299911)- 300088) - -289650) - 553099);
       a8 = 4;
       a9 = 3;
       return 21;
     } else if((((a8==6) && (((((a9==2) && ((-178 < a21) && (-144 >= a21)) ) || (((a9==5) && a21 <= -178 ) || ((a9==6) && a21 <= -178 ))) && (input == 5)) && a14 <= -148 )) && ((100 < a27) && (182 >= a27)) )){
      a27 = ((((a27 / 5) - -572632) * 1) + -572676);
      a21 = ((((a21 + 142944) % 299911)- 300088) * 1);
       a8 = 7;
       a9 = 2;
       return 21;
     } else if(( 5 < a21 && ( a27 <= -78 && ((a8==4) && ( ((-148 < a14) && (13 >= a14)) && ((input == 2) && (a9==3))))))){
      a14 = (((a14 + 91066) + -635557) * 1);
      a21 = (((a21 / 5) + -381757) / 5);
       a8 = 5;
       a9 = 2;
       return -1;
     } else if(( a21 <= -178 && ((a9==5) && ( ((100 < a27) && (182 >= a27)) && ( a14 <= -148 && ((a8==4) && (input == 1))))))){
      a21 = (((((a21 % 16)+ -158) + -3) + 58528) + -58519);
       a9 = 2;
       return 21;
     }
     return calculate_output2(input);
 }
 int calculate_output2(int input) {
     if(((a9==6) && ( 5 < a21 && (((a8==7) && ((input == 4) && ((-78 < a27) && (100 >= a27)) )) && a14 <= -148 )))){
      a27 = (((a27 - 483864) + -66270) - 38767);
      a21 = ((((a21 % 299911)- 300088) - 235905) + -7587);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a21 <= -178 && (((((((a9==2) || (a9==3)) || (a9==4)) && (input == 1)) && (a8==4)) && ((-78 < a27) && (100 >= a27)) ) && a14 <= -148 ))){
      a27 = (((a27 - 578975) * 1) - 2298);
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( ((-78 < a27) && (100 >= a27)) && (((input == 2) && (((a9==6) && a21 <= -178 ) || ( ((-178 < a21) && (-144 >= a21)) && (a9==2)))) && (a8==8))))){
      a27 = (((((a27 / 5) - -122) * 5) % 40)- -127);
      a21 = ((((a21 + 600098) - 455536) * 1) - -455478);
       a8 = 5;
       a9 = 3;
       return 21;
     } else if((((((a8==6) && (((a9==4) || (a9==5)) && (input == 6))) && ((-144 < a21) && (5 >= a21)) ) && ((-148 < a14) && (13 >= a14)) ) && a27 <= -78 )){
      a14 = (((((a14 - 505722) * 1) - -1017561) * -1)/ 10);
      a27 = ((((((a27 + 0) % 40)+ 161) * 5) % 40)- -107);
      a21 = (((((a21 - 153532) + 350664) - 748425) % 16)+ -156);
       a8 = 7;
       a9 = 3;
       return -1;
     } else if(((( ((-78 < a27) && (100 >= a27)) && ((((a9==3) || (a9==4)) && (input == 4)) && (a8==6))) && ((-178 < a21) && (-144 >= a21)) ) && a14 <= -148 )){
      a27 = ((((a27 % 40)- -141) - 532464) + 532465);
      a21 = (((a21 + -502327) * 1) + 502377);
       a8 = 7;
       a9 = 4;
       return 21;
     } else if(((a9==6) && (((((input == 5) && (a8==8)) && a21 <= -178 ) && a14 <= -148 ) && a27 <= -78 ))){
      a27 = (((((a27 % 88)+ 53) + 44) * 9)/ 10);
      a21 = ((((a21 % 74)- -2) / 5) - -2);
       a8 = 4;
       a9 = 2;
       return 23;
     } else if(( a21 <= -178 && (((a8==5) && ((((a9==4) || ((a9==2) || (a9==3))) && (input == 3)) && a27 <= -78 )) && ((-148 < a14) && (13 >= a14)) ))){
      a14 = (((a14 - 124942) + 333233) - 496335);
      a27 = ((((a27 + 0) % 299908)- -300090) + 271492);
      a21 = (((a21 + 376861) * 1) + 223150);
       a8 = 7;
       a9 = 2;
       return -1;
     } else if(((a8==8) && (( a14 <= -148 && (((( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ((a9==2) && ((-144 < a21) && (5 >= a21)) )) || ((a9==3) && ((-144 < a21) && (5 >= a21)) )) && (input == 2))) && a27 <= -78 ))){
      a21 = (((a21 - 217011) * 2) + -66398);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==4) && (( ((-178 < a21) && (-144 >= a21)) && ((a9==2) && ( a27 <= -78 && (input == 2)))) && ((-148 < a14) && (13 >= a14)) ))){
      a14 = ((((a14 + -377440) * 10)/ 9) - 72117);
      a27 = (((((((a27 * 9)/ 10) % 40)+ 140) * 5) % 40)- -101);
       a8 = 5;
       a9 = 6;
       return -1;
     } else if((((( ((100 < a27) && (182 >= a27)) && ((a8==6) && (input == 6))) && a21 <= -178 ) && (a9==4)) && a14 <= -148 )){
      a21 = ((((a21 * 9)/ 10) - -583781) + 13608);
       a9 = 6;
       return 25;
     } else if(( a21 <= -178 && ( a14 <= -148 && ((a8==5) && (((a9==4) && (input == 3)) && 182 < a27 ))))){
      a27 = (((a27 + -466181) - 49631) - 84351);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a27 <= -78 && (((((((a9==5) && a21 <= -178 ) || ( a21 <= -178 && (a9==6))) || ( ((-178 < a21) && (-144 >= a21)) && (a9==2))) && (input == 3)) && (a8==7)) && ((-148 < a14) && (13 >= a14)) ))){
      a14 = (((a14 * 5) + -507944) * 1);
      a27 = ((((a27 + 345015) % 40)- -141) + -1);
      a21 = (((((a21 % 74)- 28) + -29) * 9)/ 10);
       a9 = 4;
       return -1;
     } else if(((( ((-144 < a21) && (5 >= a21)) && (((input == 6) && (((a9==2) || (a9==3)) || (a9==4))) && a14 <= -148 )) && (a8==7)) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((a27 + -440471) / 5) * 5);
      a21 = (((a21 + -151788) * 3) + -55108);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((100 < a27) && (182 >= a27)) && (( a14 <= -148 && ((input == 4) && (a8==7))) && ((-144 < a21) && (5 >= a21)) )) && (a9==2))){
      a27 = ((((a27 * 10)/ 19) - -5) + -61);
      a21 = ((((a21 + -78751) + 189535) * 10)/ -9);
       a8 = 4;
       a9 = 6;
       return 23;
     } else if((((((input == 1) && (( ((-178 < a21) && (-144 >= a21)) && (a9==2)) || (((a9==5) && a21 <= -178 ) || ((a9==6) && a21 <= -178 )))) && (a8==5)) && a14 <= -148 ) && 182 < a27 )){
      a27 = (((a27 - 600106) + -76) - 0);
      a21 = ((((a21 % 299911)- 178) + -201251) - -91655);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( ((100 < a27) && (182 >= a27)) && (((((a9==3) || (a9==4)) && (input == 4)) && ((-178 < a21) && (-144 >= a21)) ) && (a8==5))))){
      a21 = (((a21 + -198534) * 3) - 2277);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a9==5) && ( a27 <= -78 && (( 5 < a21 && ( ((-148 < a14) && (13 >= a14)) && (input == 3))) && (a8==5))))){
      a14 = (((((a14 + 47070) * 5) * 2) * -1)/ 10);
      a21 = ((((a21 + 0) - 0) / 5) - 378430);
       a8 = 4;
       return -1;
     } else if((( ((-78 < a27) && (100 >= a27)) && ((a8==8) && ((((a9==3) || (a9==4)) && (input == 3)) && 5 < a21 ))) && a14 <= -148 )){
      a27 = ((((a27 - 387237) * 10)/ 9) + -94298);
      a21 = ((((a21 % 299911)- 300088) * 1) + -191697);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && (((a8==6) && ( ((-144 < a21) && (5 >= a21)) && (((a9==4) || (a9==5)) && (input == 2)))) && ((100 < a27) && (182 >= a27)) ))){
      if((a9==6)){
      a27 = ((((a27 - 413134) + -110462) / 5) + 277992);
      a21 = (((a21 - -171820) + 154569) * 1);
       a9 = 5;
      } else{
       a21 = (((a21 + 22880) + 489165) + 23407);
       a8 = 4;
       a9 = 3;
      } return -1;
     } else if(( a27 <= -78 && ((((( ((-144 < a21) && (5 >= a21)) && (a9==2)) || (((a9==5) && ((-178 < a21) && (-144 >= a21)) ) || ((a9==6) && ((-178 < a21) && (-144 >= a21)) ))) && (input == 4)) && (a8==6)) && ((-148 < a14) && (13 >= a14)) ))){
      if((a9==6)){
      a14 = (((a14 + -232668) - 58075) + 67328);
      a27 = (((((a27 % 88)+ 29) - 406153) + 531439) + -125267);
      a21 = ((((a21 % 74)- 69) - -456016) + -456016);
       a9 = 6;
      } else{
       a14 = (((a14 + -199173) * 3) - 824);
       a27 = (((((a27 - 0) / 5) / 5) % 88)+ 68);
       a21 = (((((a21 - -16382) * 10)/ 9) * 10)/ 9);
       a8 = 7;
       a9 = 6;
      } return -1;
     } else if(((a8==6) && ( 5 < a21 && (( a14 <= -148 && ((((a9==2) || (a9==3)) || (a9==4)) && (input == 3))) && ((100 < a27) && (182 >= a27)) )))){
      a27 = ((((a27 + 261773) * -1)/ 10) / 5);
      a21 = ((((a21 + 0) * 9)/ 10) - 540197);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-178 < a21) && (-144 >= a21)) && ( a27 <= -78 && ((a8==7) && ( a14 <= -148 && (((a9==6) || ((a9==4) || (a9==5))) && (input == 1))))))){
      a27 = ((((((a27 % 40)- -145) * 5) + 92657) % 40)- -119);
      a21 = ((((a21 * 5) - 462117) % 74)+ -65);
       a8 = 8;
       a9 = 4;
       return 23;
     } else if(( ((-178 < a21) && (-144 >= a21)) && ( a27 <= -78 && ( ((-148 < a14) && (13 >= a14)) && ((a8==4) && (((a9==3) || (a9==4)) && (input == 2))))))){
      if( a27 <= -78 ){
      a14 = (((a14 + -529108) * 1) - 62048);
      a27 = ((((a27 + 512940) % 88)- -12) / 5);
      a21 = (((((a21 + 59) * 10)/ 9) + -157581) + 157588);
       a9 = 6;
      } else{
       a14 = (((a14 + -20158) + -417262) * 1);
       a27 = (((a27 / 5) - 267279) - -717141);
       a21 = ((((((a21 * -1)/ 10) * 10)/ 9) * 10)/ 9);
       a9 = 6;
      } return 21;
     } else if(( a14 <= -148 && ((((((a9==3) || (a9==4)) && (input == 5)) && 5 < a21 ) && ((-78 < a27) && (100 >= a27)) ) && (a8==5)))){
      a27 = (((a27 / 5) * 5) - 274872);
      a21 = ((((a21 + -172470) % 299911)- 300088) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((-78 < a27) && (100 >= a27)) && (((input == 6) && (((a9==2) && ((-178 < a21) && (-144 >= a21)) ) || (( a21 <= -178 && (a9==5)) || ( a21 <= -178 && (a9==6))))) && a14 <= -148 )) && (a8==7))){
      a27 = (((a27 / 5) + 93312) - 657568);
      a21 = ((((a21 % 299911)- 178) * 1) - 287697);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( 182 < a27 && ( a14 <= -148 && ((((((a9==5) && (a8==4)) && 5 < a21 ) || ( 5 < a21 && ((a9==6) && (a8==4)))) || (((a9==2) && (a8==5)) && a21 <= -178 )) && (input == 6))))){
      a27 = ((((a27 - 600130) + -46) - -415581) - 415512);
      a21 = ((((a21 % 299911)- 300088) - 0) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-144 < a21) && (5 >= a21)) && ((a8==7) && ( a14 <= -148 && ( 182 < a27 && ((((a9==2) || (a9==3)) || (a9==4)) && (input == 3))))))){
      a27 = ((((((a27 % 40)- -116) * 10)/ 9) - -131394) - 131416);
       a8 = 6;
       a9 = 5;
       return 23;
     } else if(( a14 <= -148 && (( ((-78 < a27) && (100 >= a27)) && (((((a9==5) && ((-144 < a21) && (5 >= a21)) ) || ( ((-144 < a21) && (5 >= a21)) && (a9==6))) || ( 5 < a21 && (a9==2))) && (input == 3))) && (a8==7)))){
      a27 = ((((a27 + -159690) * 10)/ 9) + -407997);
      a21 = ((((a21 % 299911)- 300088) + 0) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( 182 < a27 && (( ((-144 < a21) && (5 >= a21)) && ((input == 5) && (a8==8))) && a14 <= -148 )) && (a9==3))){
      a27 = (((a27 - 600093) - 54) - 17);
      a21 = (((a21 - 223943) + -10877) / 5);
       a8 = 4;
       return -1;
     } else if(((( a14 <= -148 && ((a8==4) && ( ((-78 < a27) && (100 >= a27)) && (input == 6)))) && ((-178 < a21) && (-144 >= a21)) ) && (a9==2))){
      a21 = (((a21 * 5) - -511666) - -45494);
       a8 = 6;
       a9 = 3;
       return 25;
     } else if(( 5 < a21 && (( ((100 < a27) && (182 >= a27)) && ( a14 <= -148 && ((input == 2) && ((a9==4) || ((a9==2) || (a9==3)))))) && (a8==6)))){
      a27 = (((a27 - 575665) - 3826) - 17586);
      a21 = ((((a21 % 299911)- 300088) + -189053) - 41850);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((((input == 6) && ((-144 < a21) && (5 >= a21)) ) && (a9==3)) && ((-78 < a27) && (100 >= a27)) ) && (a8==8)) && a14 <= -148 )){
      a27 = (((a27 - 239390) + -125383) * 1);
      a21 = (((a21 / 5) / 5) + 354977);
       a8 = 7;
       a9 = 4;
       return 21;
     } else if(((( ((100 < a27) && (182 >= a27)) && (((input == 3) && ((a9==2) || (a9==3))) && (a8==7))) && a14 <= -148 ) && 5 < a21 )){
      a27 = ((((a27 * -1)/ 10) + -33) / 5);
      a21 = (((((a21 - 8281) - 334928) + 232516) % 16)- 161);
       a8 = 5;
       a9 = 4;
       return 25;
     } else if(((a8==4) && ( a21 <= -178 && ((((input == 3) && (a9==3)) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 )))){
      a21 = ((((a21 % 16)- 144) - 206405) + 206387);
       a8 = 6;
       a9 = 6;
       return 25;
     } else if(((((a8==4) && ( 5 < a21 && (((a9==2) || (a9==3)) && (input == 4)))) && a14 <= -148 ) && ((100 < a27) && (182 >= a27)) )){
      a27 = ((((a27 - 92516) + 616739) * 10)/ -9);
      a21 = (((((a21 % 299911)- 300088) * 1) / 5) + -118600);
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( 182 < a27 && (((a8==8) && (((a9==2) || (a9==3)) && (input == 4))) && a21 <= -178 )))){
      a21 = ((((a21 * 9)/ 10) - -562082) / 5);
       a9 = 3;
       return -1;
     } else if(((( 182 < a27 && ( a14 <= -148 && ((input == 5) && (((a9==4) || (a9==5)) || (a9==6))))) && (a8==4)) && ((-144 < a21) && (5 >= a21)) )){
      a27 = (((a27 + 0) / 5) + -389459);
      a21 = ((((((a21 % 16)- 160) * 5) - 177238) % 16)+ -149);
       a8 = 5;
       a9 = 6;
       return -1;
     } else if((( a14 <= -148 && ((a8==4) && (( ((100 < a27) && (182 >= a27)) && (input == 3)) && 5 < a21 ))) && (a9==4))){
      a27 = ((((a27 - 184267) + -332129) * 10)/ 9);
      a21 = ((((a21 * 9)/ 10) - 541909) / 5);
       a9 = 2;
       return -1;
     } else if(((a9==4) && ( a14 <= -148 && (( a27 <= -78 && ((input == 1) && (a8==8))) && a21 <= -178 )))){
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( ((100 < a27) && (182 >= a27)) && ((((input == 4) && ((a9==6) || ((a9==4) || (a9==5)))) && (a8==4)) && ((-144 < a21) && (5 >= a21)) )))){
       a8 = 7;
       a9 = 2;
       return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && ( a14 <= -148 && ((input == 5) && (((((a8==5) && (a9==5)) && 5 < a21 ) || ( 5 < a21 && ((a9==6) && (a8==5)))) || ( a21 <= -178 && ((a9==2) && (a8==6)))))))){
      a27 = (((((a27 % 40)- -142) * 1) - 214679) + 214677);
      a21 = (((((a21 % 299911)- 300088) + -1) + 562060) + -562059);
       a8 = 4;
       a9 = 5;
       return 23;
     } else if(( a14 <= -148 && ((a8==8) && (( 5 < a21 && ((input == 5) && ((100 < a27) && (182 >= a27)) )) && (a9==3))))){
      a27 = (((a27 - 121) + 366667) - 366703);
      a21 = ((((((a21 * 9)/ 10) % 74)+ -123) * 9)/ 10);
       a8 = 4;
       a9 = 2;
       return 23;
     } else if(((( ((-178 < a21) && (-144 >= a21)) && ((((a9==3) || (a9==4)) && (input == 3)) && ((-148 < a14) && (13 >= a14)) )) && a27 <= -78 ) && (a8==5))){
      if( a14 <= -148 ){
      a14 = (((a14 - 226025) - 137422) * 1);
       a8 = 4;
       a9 = 4;
      } else{
       a14 = (((a14 - 360447) / 5) / 5);
       a27 = (((((a27 / 5) % 40)+ 153) / 5) + 142);
       a21 = (((a21 + 140137) * 4) + 28608);
       a8 = 8;
       a9 = 3;
      } return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && ( a14 <= -148 && ((a8==8) && ((((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ( ((-144 < a21) && (5 >= a21)) && (a9==2))) && (input == 2)))))){
      a27 = (((a27 + -292317) * 2) / 5);
      a21 = (((((a21 - -492853) * 1) + 6264) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a9==3) && ((((input == 3) && a21 <= -178 ) && (a8==8)) && ((-78 < a27) && (100 >= a27)) )) && a14 <= -148 )){
      a27 = (((a27 + -477052) * 1) / 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==4) && ((((input == 4) && ((-78 < a27) && (100 >= a27)) ) && 5 < a21 ) && (a9==3))) && a14 <= -148 )){
      a21 = (((((a21 % 74)+ -72) + 3) + -11689) + 11663);
       a8 = 7;
       a9 = 6;
       return 23;
     } else if(( a14 <= -148 && (((input == 5) && ((((a8==7) && (a9==6)) && 5 < a21 ) || (((a8==8) && (a9==2)) && a21 <= -178 ))) && ((100 < a27) && (182 >= a27)) ))){
      a27 = ((((a27 - 581026) - 5337) - -975277) - 868557);
      a21 = (((((a21 % 299911)- 300088) - 1) / 5) + -103377);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a21 <= -178 && ( a14 <= -148 && ((a8==8) && (((input == 6) && ((a9==5) || ((a9==3) || (a9==4)))) && ((100 < a27) && (182 >= a27)) ))))){
      a27 = (((a27 * 5) + 207748) + -388985);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((-148 < a14) && (13 >= a14)) && ( a27 <= -78 && ((((a9==6) && ((-144 < a21) && (5 >= a21)) ) || ( 5 < a21 && (a9==2))) && (input == 4)))) && (a8==6))){
      a14 = (((a14 - 95939) - 140454) * 2);
      a21 = (((((a21 - 88500) - 419467) - -385467) % 299911)+ -300088);
       a9 = 4;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && ((a8==4) && (( a27 <= -78 && ((((a9==3) || (a9==4)) || (a9==5)) && (input == 6))) && a21 <= -178 )))){
      if( 182 < a14 ){
      a14 = ((((a14 + 442480) - -43608) - -97272) + -971765);
      a21 = ((((a21 / 5) * 4) % 16)- 150);
       a8 = 6;
       a9 = 4;
      } else{
       a14 = (((a14 * 5) * 5) + -59962);
       a27 = ((((((a27 - 0) % 40)- -145) * 5) % 40)+ 122);
       a21 = ((((a21 % 16)+ -151) + 2) * 1);
       a8 = 7;
       a9 = 5;
      } return 23;
     } else if(( 182 < a27 && ( a14 <= -148 && (((input == 1) && ((( ((-144 < a21) && (5 >= a21)) && (a9==5)) || ( ((-144 < a21) && (5 >= a21)) && (a9==6))) || ( 5 < a21 && (a9==2)))) && (a8==5))))){
      a27 = (((a27 + -600168) - 14) + -1);
      a21 = (((((a21 + 0) * 9)/ 10) - 186002) + -367259);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a9==3) && ( 5 < a21 && (((input == 1) && (a8==7)) && ((-78 < a27) && (100 >= a27)) ))) && a14 <= -148 )){
      a27 = ((((a27 + -147572) * 10)/ 9) / 5);
      a21 = (((((a21 + -428495) + -125981) - -189492) % 299911)+ -300088);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((-178 < a21) && (-144 >= a21)) && ((((input == 3) && ((100 < a27) && (182 >= a27)) ) && (a8==7)) && a14 <= -148 )) && (a9==6))){
      a27 = ((((a27 * 5) - -194416) * -1)/ 10);
      a21 = (((a21 - 175515) - 413188) - 10739);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( ((-78 < a27) && (100 >= a27)) && (((input == 1) && ((( ((-178 < a21) && (-144 >= a21)) && (a9==5)) || ((a9==6) && ((-178 < a21) && (-144 >= a21)) )) || ((a9==2) && ((-144 < a21) && (5 >= a21)) ))) && (a8==5))))){
      if( ((-144 < a21) && (5 >= a21)) ){
      a27 = ((((a27 % 40)+ 141) + -1) + 0);
      a21 = (((a21 + 517647) * 1) - -6098);
       a8 = 7;
       a9 = 5;
      } else{
       a21 = (((((a21 + 6179) % 16)- 170) - -557960) + -557949);
       a8 = 8;
       a9 = 6;
      } return 25;
     } else if((((( 182 < a27 && (((a9==5) || (a9==6)) && (input == 3))) && (a8==7)) && a14 <= -148 ) && ((-178 < a21) && (-144 >= a21)) )){
      a27 = ((((a27 * -5)/ 10) - 28466) + -78000);
      a21 = (((a21 * 5) - 297008) / 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==7) && ( ((100 < a27) && (182 >= a27)) && ( a14 <= -148 && ((( a21 <= -178 && (a9==6)) || ( ((-178 < a21) && (-144 >= a21)) && (a9==2))) && (input == 5)))))){
      a27 = ((((a27 - 54652) + -43670) * 10)/ 9);
      a21 = ((((((a21 % 16)+ -156) * 1) * 5) % 16)- 160);
       a8 = 5;
       a9 = 6;
       return -1;
     } else if((((a8==5) && ( a27 <= -78 && ( ((-148 < a14) && (13 >= a14)) && ((input == 3) && ((-144 < a21) && (5 >= a21)) )))) && (a9==3))){
      a14 = (((a14 - 498451) * 1) - 47354);
      a21 = ((((a21 * 5) * 5) + -283605) - -835068);
       a8 = 4;
       a9 = 6;
       return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && ( a14 <= -148 && (((input == 3) && ((((a9==5) && ((-178 < a21) && (-144 >= a21)) ) || ( ((-178 < a21) && (-144 >= a21)) && (a9==6))) || ((a9==2) && ((-144 < a21) && (5 >= a21)) ))) && (a8==5))))){
      a27 = (((a27 - 337750) * 1) * 1);
      a21 = ((((a21 * 5) / 5) * 5) - 52527);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a21 <= -178 && ((a9==3) && (((input == 5) && (a8==5)) && a14 <= -148 ))) && ((100 < a27) && (182 >= a27)) )){
      a27 = (((a27 + -421966) * 1) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==8) && ( a14 <= -148 && ( 182 < a27 && (((input == 2) && ((a9==5) || (a9==6))) && ((-144 < a21) && (5 >= a21)) ))))){
      a27 = (((a27 + -600156) - 25) * 1);
      a21 = (((((a21 % 16)+ -161) + -1) + -26466) - -26468);
       a8 = 6;
       a9 = 4;
       return -1;
     } else if((((a8==5) && ( ((-78 < a27) && (100 >= a27)) && (((input == 2) && ((a9==3) || (a9==4))) && a14 <= -148 ))) && 5 < a21 )){
      a27 = (((((a27 + -38600) + -208101) + 419033) * -1)/ 10);
      a21 = (((((a21 - 522246) / 5) * 5) % 299911)- 300088);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((((a8==5) && ((input == 4) && (a9==3))) && ((100 < a27) && (182 >= a27)) ) && ((-144 < a21) && (5 >= a21)) ) && a14 <= -148 )){
      a27 = (((a27 - 38510) + 418971) - 553190);
      a21 = ((((a21 + 17995) * 5) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( ((100 < a27) && (182 >= a27)) && ((a8==6) && ((input == 1) && ((((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ((a9==2) && ((-144 < a21) && (5 >= a21)) )) || ( ((-144 < a21) && (5 >= a21)) && (a9==3)))))))){
      a27 = ((((((a27 * -8)/ 10) - 425643) + 908682) * -1)/ 10);
      a21 = (((a21 + -522612) - -212336) - 289191);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( 5 < a21 && (((a8==4) && ( ((100 < a27) && (182 >= a27)) && (((a9==2) || (a9==3)) && (input == 5)))) && a14 <= -148 ))){
      a27 = (((a27 - 312570) / 5) - 352385);
      a21 = ((((a21 % 299911)- 300088) - 136061) * 1);
       a9 = 2;
       return -1;
     } else if(( ((-144 < a21) && (5 >= a21)) && ( a14 <= -148 && (((((a9==4) || (a9==5)) && (input == 5)) && ((100 < a27) && (182 >= a27)) ) && (a8==6))))){
      a27 = ((((a27 / 5) * 10)/ -2) * 5);
      a21 = ((((a21 * 5) + 254892) / 5) + -519842);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((((a9==3) && (input == 6)) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 ) && ((-144 < a21) && (5 >= a21)) ) && (a8==8))){
      a27 = (((((a27 * 10)/ 19) - 128) - -157706) - 157637);
      a21 = (((((a21 % 16)- 161) / 5) + -275047) - -274907);
       a8 = 5;
       return 21;
     } else if(((((((input == 3) && ((a9==3) || (a9==4))) && a14 <= -148 ) && ((-78 < a27) && (100 >= a27)) ) && ((-144 < a21) && (5 >= a21)) ) && (a8==5))){
      a27 = (((a27 - 290554) * 2) + -3944);
      a21 = (((a21 - 249279) / 5) + -32429);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a14 <= -148 && (((a9==5) && ( a21 <= -178 && (input == 6))) && (a8==4))) && ((100 < a27) && (182 >= a27)) )){
      a27 = ((((a27 * 5) * 5) * 5) + -483852);
       a9 = 2;
       return -1;
     } else if(((((a8==4) && ((((a9==6) || ((a9==4) || (a9==5))) && (input == 6)) && 5 < a21 )) && a14 <= -148 ) && ((-78 < a27) && (100 >= a27)) )){
      a27 = ((((a27 + -249984) * 10)/ 9) * 2);
      a21 = ((((a21 - 0) / 5) * 4) + -566419);
       a9 = 2;
       return -1;
     } else if(( 5 < a21 && ((a8==6) && ( ((-78 < a27) && (100 >= a27)) && ((((a9==3) || (a9==4)) && (input == 1)) && a14 <= -148 ))))){
      a27 = (((a27 + -538910) + -40854) - 13674);
      a21 = ((((a21 - 340483) * 1) % 299911)- 300088);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((((a9==4) && ((input == 5) && (a8==6))) && 5 < a21 ) && a14 <= -148 ) && 182 < a27 )){
      a27 = ((((a27 - 449255) + -150887) - -228082) + -228095);
      a21 = ((((a21 * 9)/ 10) + -540936) + -48701);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((((((a9==2) || (a9==3)) || (a9==4)) && (input == 3)) && ((-178 < a21) && (-144 >= a21)) ) && (a8==6)) && ((-148 < a14) && (13 >= a14)) ) && a27 <= -78 )){
      a14 = ((((a14 * 5) - 89451) * 10)/ 9);
      a21 = ((((a21 - 350066) * -1)/ 10) + 423382);
       a8 = 5;
       a9 = 5;
       return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && (((((a8==5) && (input == 1)) && (a9==3)) && a14 <= -148 ) && ((-178 < a21) && (-144 >= a21)) ))){
      a27 = ((((a27 + -158667) * 3) * 10)/ 9);
      a21 = (((((a21 * 13)/ 10) + -158410) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a27 <= -78 && (((((input == 4) && ((a9==3) || (a9==4))) && 5 < a21 ) && (a8==8)) && a14 <= -148 ))){
      a21 = ((((a21 * 9)/ 10) + -553258) / 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((( a14 <= -148 && ( 5 < a21 && (input == 1))) && (a9==4)) && 182 < a27 ) && (a8==6))){
      a27 = (((a27 + -450306) - 149857) - 2);
      a21 = ((((a21 % 299911)+ -300088) * 1) + -161680);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a27 <= -78 && (( 5 < a21 && (((a9==3) || (a9==4)) && (input == 3))) && a14 <= -148 )) && (a8==8))){
      a27 = (((((a27 % 40)- -145) * 5) % 40)- -128);
      a21 = (((((a21 % 74)- 73) - 19) * 10)/ 9);
       a8 = 7;
       a9 = 5;
       return 23;
     } else if(((((( ((-148 < a14) && (13 >= a14)) && (input == 2)) && a21 <= -178 ) && (a8==7)) && a27 <= -78 ) && (a9==2))){
      if( ((-144 < a21) && (5 >= a21)) ){
      a14 = ((((a14 - 87258) + -292455) * 10)/ 9);
      a21 = ((((a21 / 5) % 74)+ -62) - 8);
       a8 = 5;
       a9 = 3;
      } else{
       a14 = (((a14 - 206047) + -339446) - 39381);
       a21 = (((((a21 + 18985) * 1) - -317443) % 16)- 161);
       a8 = 5;
       a9 = 3;
      } return 25;
     } else if(((a9==6) && ( a14 <= -148 && ((a8==8) && (( a27 <= -78 && (input == 2)) && a21 <= -178 ))))){
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && (((a8==4) && ( ((-178 < a21) && (-144 >= a21)) && ((((a9==3) || (a9==4)) || (a9==5)) && (input == 5)))) && ((-78 < a27) && (100 >= a27)) ))){
      a21 = (((a21 * 5) - -365385) + 43511);
       a8 = 6;
       a9 = 5;
       return 23;
     } else if(( a27 <= -78 && ((((input == 6) && (((a9==6) && a21 <= -178 ) || ((a9==2) && ((-178 < a21) && (-144 >= a21)) ))) && (a8==5)) && ((-148 < a14) && (13 >= a14)) ))){
      a14 = (((a14 + -468913) - 41903) * 1);
      a21 = ((((((a21 % 74)+ -25) - 26) * 5) % 74)+ 1);
       a9 = 3;
       return 21;
     } else if(( a21 <= -178 && ((((a8==4) && ((((a9==2) || (a9==3)) || (a9==4)) && (input == 5))) && ((-78 < a27) && (100 >= a27)) ) && a14 <= -148 ))){
      a27 = (((a27 - 271468) - 82578) + -59071);
       a9 = 2;
       return -1;
     } else if(((((((input == 4) && a14 <= -148 ) && ((-78 < a27) && (100 >= a27)) ) && (a9==4)) && ((-178 < a21) && (-144 >= a21)) ) && (a8==5))){
      a27 = (((a27 - -103982) + 340138) + -980180);
      a21 = ((((a21 + -526385) * 10)/ 9) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && ( ((-178 < a21) && (-144 >= a21)) && (( a14 <= -148 && ((input == 5) && ((a9==4) || (a9==5)))) && (a8==8))))){
      a27 = (((a27 + -257685) * 2) + -19578);
      a21 = ((((a21 * 5) + 65377) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-144 < a21) && (5 >= a21)) && ( a14 <= -148 && (((((a9==2) || (a9==3)) && (input == 4)) && ((100 < a27) && (182 >= a27)) ) && (a8==4))))){
      a21 = (((a21 + -347955) + -17368) * 1);
       a9 = 3;
       return -1;
     } else if(( a14 <= -148 && ((a9==3) && ( ((100 < a27) && (182 >= a27)) && (((input == 3) && ((-144 < a21) && (5 >= a21)) ) && (a8==7)))))){
      a27 = ((((a27 * 10)/ -9) - 332797) + -24386);
      a21 = ((((a21 - 297457) / 5) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==8) && ( ((-178 < a21) && (-144 >= a21)) && ( a27 <= -78 && ((input == 6) && a14 <= -148 )))) && (a9==2))){
      a21 = (((a21 * 5) * 5) * 5);
       a8 = 4;
       return -1;
     } else if(((a8==8) && ((( 5 < a21 && ((input == 2) && a14 <= -148 )) && a27 <= -78 ) && (a9==6)))){
      a27 = ((((a27 / 5) / 5) % 88)+ 10);
       a8 = 5;
       a9 = 5;
       return 23;
     } else if(( a21 <= -178 && ((a8==8) && ((((input == 1) && ((a9==4) || (a9==5))) && a14 <= -148 ) && ((-78 < a27) && (100 >= a27)) )))){
      a27 = ((((a27 / 5) * 5) / 5) + -379999);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((a9==4) && ( ((100 < a27) && (182 >= a27)) && ( ((-144 < a21) && (5 >= a21)) && (input == 4)))) && a14 <= -148 ) && (a8==8))){
      a27 = ((((((a27 * 10)/ -9) + 126477) - -118633) * -1)/ 10);
      a21 = (((a21 - 95358) - 331795) + -67700);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && (((a8==4) && ( ((-78 < a27) && (100 >= a27)) && ((input == 5) && ((a9==6) || ((a9==4) || (a9==5)))))) && 5 < a21 ))){
      a27 = (((a27 * 5) + -237860) + -133494);
      a21 = (((((a21 - 543427) % 299911)+ -300088) / 5) - 129048);
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((((((a9==6) && (a8==5)) && 5 < a21 ) || ( a21 <= -178 && ((a9==2) && (a8==6)))) && (input == 6)) && 182 < a27 ))){
      a27 = ((((a27 - 600099) - -453618) - 197267) + -256332);
      a21 = ((((((a21 * 9)/ 10) - 16117) * 1) % 16)+ -159);
       a8 = 7;
       a9 = 3;
       return 23;
     } else if((((((((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ( ((-144 < a21) && (5 >= a21)) && (a9==2))) && (input == 2)) && (a8==8)) && a14 <= -148 ) && 182 < a27 )){
      if( a14 <= -148 ){
      a27 = (((a27 + -600133) * 1) + -25);
      a21 = (((a21 + -236822) - -572309) - -199052);
       a8 = 6;
       a9 = 2;
      } else{
       a27 = ((((a27 / 5) - -53789) % 88)+ -45);
       a21 = (((((a21 % 74)+ -68) + -1) + 325828) - 325828);
       a9 = 3;
      } return 21;
     } else if(( a14 <= -148 && (((input == 1) && (( a21 <= -178 && ((a9==2) && (a8==7))) || (( 5 < a21 && ((a9==5) && (a8==6))) || (((a8==6) && (a9==6)) && 5 < a21 )))) && 182 < a27 ))){
      a27 = (((a27 - 600118) + -62) + -2);
      a21 = (((((a21 * 9)/ 10) * 1) % 299911)- 300088);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==4) && ((((((a9==4) || (a9==5)) || (a9==6)) && (input == 1)) && ((-144 < a21) && (5 >= a21)) ) && a14 <= -148 )) && ((100 < a27) && (182 >= a27)) )){
      a27 = (((((a27 * -8)/ 10) + -472661) * 10)/ 9);
      a21 = ((((a21 - -160459) * 3) * 1) + -488073);
       a9 = 2;
       return -1;
     } else if((( 182 < a27 && ((((a8==5) && (input == 6)) && (a9==4)) && a21 <= -178 )) && a14 <= -148 )){
      a27 = (((a27 - 600093) - 5) + -5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((((a9==2) && ((input == 2) && ((-78 < a27) && (100 >= a27)) )) && (a8==8)) && a21 <= -178 ) && a14 <= -148 )){
      a27 = (((a27 / 5) / 5) - 14331);
       a8 = 4;
       return -1;
     } else if((( a27 <= -78 && (((((a9==2) && ((-144 < a21) && (5 >= a21)) ) || (((a9==5) && ((-178 < a21) && (-144 >= a21)) ) || ((a9==6) && ((-178 < a21) && (-144 >= a21)) ))) && (input == 5)) && ((-148 < a14) && (13 >= a14)) )) && (a8==5))){
      if( ((-78 < a27) && (100 >= a27)) ){
      a14 = (((a14 + 172698) / 5) - 424345);
      a21 = (((((a21 * 5) * 5) * 5) % 74)+ -69);
       a9 = 3;
      } else{
       a21 = (((((a21 * 5) * 5) - -582665) % 16)- 164);
       a9 = 3;
      } return -1;
     } else if(( a14 <= -148 && ((((( ((-144 < a21) && (5 >= a21)) && (a9==2)) || (( ((-178 < a21) && (-144 >= a21)) && (a9==5)) || ((a9==6) && ((-178 < a21) && (-144 >= a21)) ))) && (input == 6)) && ((-78 < a27) && (100 >= a27)) ) && (a8==5)))){
      a27 = (((a27 + -313134) + -163605) / 5);
      a21 = (((a21 + -491223) - -805580) - 443420);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && ( a21 <= -178 && ( a14 <= -148 && ((a8==8) && ((a9==2) && (input == 4))))))){
      a27 = ((((a27 * 5) % 40)- -140) + 0);
      a21 = (((a21 + 600066) + -131434) + 131393);
       a8 = 4;
       a9 = 4;
       return 21;
     } else if((((a8==6) && (((( ((-144 < a21) && (5 >= a21)) && (a9==6)) || ( 5 < a21 && (a9==2))) && (input == 3)) && a27 <= -78 )) && ((-148 < a14) && (13 >= a14)) )){
      a14 = (((a14 - 124359) / 5) / 5);
      a21 = (((a21 / 5) + 48797) * 3);
       a8 = 5;
       a9 = 6;
       return -1;
     } else if(((((( 5 < a21 && (input == 5)) && (a9==6)) && (a8==6)) && a14 <= -148 ) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((a27 - 254148) / 5) - 22710);
      a21 = ((((a21 - 121897) % 299911)- 300088) - 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-144 < a21) && (5 >= a21)) && (((((input == 3) && ((a9==5) || (a9==6))) && (a8==7)) && a14 <= -148 ) && 182 < a27 ))){
      a27 = (((a27 - 600146) + -28) - 2);
      a21 = (((a21 - 84317) + 501714) - 832589);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( ((-144 < a21) && (5 >= a21)) && ( ((-148 < a14) && (13 >= a14)) && ((input == 1) && ((a9==5) || (a9==6))))) && a27 <= -78 ) && (a8==4))){
      a14 = (((a14 - 61295) * 5) + -232562);
      a21 = ((((a21 + 85693) + -618566) / 5) + 119313);
       a9 = 2;
       return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && ((a9==6) && ( a14 <= -148 && ( ((-178 < a21) && (-144 >= a21)) && ((a8==4) && (input == 3))))))){
       a8 = 8;
       a9 = 4;
       return -1;
     } else if((( ((-178 < a21) && (-144 >= a21)) && ( ((100 < a27) && (182 >= a27)) && (( a14 <= -148 && (input == 6)) && (a8==7)))) && (a9==6))){
      a27 = (((a27 / 5) - 184577) - -184543);
      a21 = ((((a21 - 370250) * 10)/ 9) * 1);
       a8 = 6;
       a9 = 3;
       return 25;
     } else if(((( a14 <= -148 && ( ((-78 < a27) && (100 >= a27)) && ((input == 1) && ((a9==3) || (a9==4))))) && ((-178 < a21) && (-144 >= a21)) ) && (a8==6))){
      if((a8==5)){
      a27 = (((a27 * 5) - -165966) + 415805);
      a21 = (((a21 + 471876) + 121784) + 3180);
       a8 = 5;
       a9 = 5;
      } else{
       a27 = (((a27 - -422719) + 6022) - -116618);
       a8 = 7;
       a9 = 5;
      } return 21;
     } else if((( ((-78 < a27) && (100 >= a27)) && (((((a9==2) || (a9==3)) && (input == 6)) && (a8==5)) && a14 <= -148 )) && a21 <= -178 )){
      a27 = ((((a27 / 5) / 5) / 5) - 343843);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==7) && ( a14 <= -148 && (( ((-144 < a21) && (5 >= a21)) && (((a9==5) || (a9==6)) && (input == 4))) && ((100 < a27) && (182 >= a27)) )))){
      a27 = ((((a27 + -136) - -39) * 10)/ 9);
      a21 = (((a21 + 417890) + 150614) / 5);
       a8 = 8;
       a9 = 6;
       return 25;
     } else if((((a8==8) && ( a14 <= -148 && (((input == 2) && ((a9==3) || (a9==4))) && ((-178 < a21) && (-144 >= a21)) ))) && ((-78 < a27) && (100 >= a27)) )){
      if( a21 <= -178 ){
      a27 = (((a27 - 269584) / 5) + 54040);
      a21 = ((((a21 + -226987) * 10)/ 9) / 5);
       a9 = 3;
      } else{
       a27 = ((((a27 % 40)+ 140) + 1) + -1);
       a8 = 5;
       a9 = 3;
      } return 21;
     } else if((((((((a9==4) || ((a9==2) || (a9==3))) && (input == 6)) && 182 < a27 ) && ((-178 < a21) && (-144 >= a21)) ) && (a8==7)) && a14 <= -148 )){
      a27 = ((((a27 % 88)+ 2) + 156822) + -156852);
       a8 = 8;
       a9 = 3;
       return 21;
     } else if((( a21 <= -178 && ( a14 <= -148 && (((a9==5) && (input == 4)) && a27 <= -78 ))) && (a8==8))){
      a27 = ((((a27 + 0) % 88)+ 51) + -24);
      a21 = ((((a21 % 16)+ -161) + -399860) - -399868);
       a8 = 4;
       a9 = 4;
       return 25;
     } else if((((((((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ( ((-144 < a21) && (5 >= a21)) && (a9==2))) && (input == 5)) && a14 <= -148 ) && (a8==8)) && ((100 < a27) && (182 >= a27)) )){
      a27 = ((((a27 * -8)/ 10) + -432973) * 1);
      a21 = ((((a21 + -435680) - -743889) * 10)/ -9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==8) && (((a9==3) && ((input == 3) && 5 < a21 )) && ((100 < a27) && (182 >= a27)) )) && a14 <= -148 )){
      a27 = (((((a27 * 10)/ -9) / 5) * 36)/ 10);
      a21 = (((((a21 - 0) * 9)/ 10) * 1) + -562151);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((a9==3) && ( 182 < a27 && (((input == 1) && (a8==5)) && a21 <= -178 ))))){
      a27 = (((((a27 * 9)/ 10) * -5)/ 10) * 2);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-144 < a21) && (5 >= a21)) && (((a9==3) && (( a14 <= -148 && (input == 5)) && (a8==5))) && ((100 < a27) && (182 >= a27)) ))){
      a27 = (((a27 + -71871) * 5) + -84840);
      a21 = (((a21 - 119813) / 5) * 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a9==5) && ( ((-144 < a21) && (5 >= a21)) && ( a27 <= -78 && (((a8==7) && (input == 6)) && ((-148 < a14) && (13 >= a14)) ))))){
      a14 = (((a14 + -394076) - 186083) / 5);
      a27 = (((((a27 + 523987) + -134915) + 37582) % 40)- -141);
      a21 = ((((a21 % 16)+ -161) - 1) * 1);
       a9 = 2;
       return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && ( a14 <= -148 && (((((a9==6) && a21 <= -178 ) || ( ((-178 < a21) && (-144 >= a21)) && (a9==2))) && (input == 5)) && (a8==4))))){
      a27 = ((((((a27 * 10)/ -9) * 10)/ 9) * 10)/ 9);
      a21 = ((((a21 / 5) - -64447) / 5) + -562446);
       a9 = 2;
       return -1;
     } else if(( ((-144 < a21) && (5 >= a21)) && ((((a8==6) && (((a9==4) || (a9==5)) && (input == 4))) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 ))){
      a27 = (((a27 + -86815) * 5) + 350042);
      a21 = (((a21 - 58741) * 5) * 2);
       a8 = 8;
       a9 = 6;
       return -1;
     } else if((((( 182 < a27 && (((a9==6) || ((a9==4) || (a9==5))) && (input == 6))) && a14 <= -148 ) && ((-144 < a21) && (5 >= a21)) ) && (a8==4))){
      a27 = (((((a27 * 9)/ 10) % 40)+ 111) + -9);
      a21 = ((((a21 - 516679) * 10)/ 9) / 5);
       a9 = 3;
       return 25;
     } else if(( 5 < a21 && ((a8==6) && ( ((100 < a27) && (182 >= a27)) && (((((a9==2) || (a9==3)) || (a9==4)) && (input == 4)) && a14 <= -148 ))))){
      a27 = ((((a27 + 436267) / 5) * -1)/ 10);
      a21 = (((((a21 % 299911)- 300088) * 1) - -290714) - 428162);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((((input == 5) && ((a9==3) || (a9==4))) && (a8==4)) && ((-178 < a21) && (-144 >= a21)) ) && ((-148 < a14) && (13 >= a14)) ) && a27 <= -78 )){
      if( ((-144 < a21) && (5 >= a21)) ){
       a9 = 3;
      } else{
       a14 = (((a14 - 149652) - -158139) + -485277);
       a8 = 6;
       a9 = 5;
      } return -1;
     } else if((((a8==7) && ( a14 <= -148 && ((((a9==4) || ((a9==2) || (a9==3))) && (input == 1)) && ((-78 < a27) && (100 >= a27)) ))) && ((-144 < a21) && (5 >= a21)) )){
      a27 = (((a27 / 5) + -343743) + -129206);
      a21 = ((((a21 - -188724) * 10)/ -9) / 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a14 <= -148 && ( ((-178 < a21) && (-144 >= a21)) && ((a8==5) && ( ((-78 < a27) && (100 >= a27)) && (input == 6))))) && (a9==2))){
      a27 = (((a27 + -425967) / 5) / 5);
      a21 = (((a21 + -370202) + -112518) * 1);
       a8 = 4;
       return -1;
     } else if(((a9==5) && ( a14 <= -148 && ( ((-78 < a27) && (100 >= a27)) && (( ((-144 < a21) && (5 >= a21)) && (input == 1)) && (a8==5)))))){
      a27 = (((a27 - 3554) - 536880) - 53811);
      a21 = (((a21 - 210687) - 26300) - 293882);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-144 < a21) && (5 >= a21)) && (((((a9==6) && (input == 3)) && (a8==6)) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 ))){
      a27 = ((((a27 * 5) * 10)/ -9) * 5);
      a21 = (((((a21 % 16)+ -160) + -1) - 313194) + 313195);
       a8 = 7;
       a9 = 2;
       return -1;
     } else if((( a21 <= -178 && (((a8==8) && ((input == 5) && ((a9==4) || (a9==5)))) && a14 <= -148 )) && ((-78 < a27) && (100 >= a27)) )){
      a27 = ((((a27 + 341497) / 5) / 5) + -568011);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( 182 < a27 && ((a8==5) && ( a14 <= -148 && ((input == 2) && ((((a9==5) && a21 <= -178 ) || ( a21 <= -178 && (a9==6))) || ( ((-178 < a21) && (-144 >= a21)) && (a9==2)))))))){
      a27 = (((((a27 / 5) * 4) * 1) * -6)/ 10);
      a21 = ((((a21 % 299911)+ -178) * 1) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a21 <= -178 && ((a9==4) && ( a27 <= -78 && ((input == 5) && (a8==6))))) && ((-148 < a14) && (13 >= a14)) )){
      a14 = (((a14 + -192603) / 5) * 5);
      a21 = ((((a21 + 585778) / 5) % 16)- 160);
       a8 = 4;
       a9 = 6;
       return 23;
     } else if(((((input == 4) && (( 5 < a21 && ((a9==6) && (a8==7))) || ( a21 <= -178 && ((a8==8) && (a9==2))))) && a14 <= -148 ) && ((100 < a27) && (182 >= a27)) )){
      if( 5 < a21 ){
      a27 = (((a27 - -272225) - -158585) + 159481);
      a21 = (((((a21 % 299997)- -300002) - 0) / 5) + 435286);
       a8 = 6;
       a9 = 6;
      } else{
       a21 = ((((((a21 * 9)/ 10) * 1) + 717) % 299997)+ 300002);
       a8 = 4;
       a9 = 2;
      } return 21;
     } else if((((((( ((-144 < a21) && (5 >= a21)) && (a9==6)) || ((a9==2) && 5 < a21 )) && (input == 5)) && ((-78 < a27) && (100 >= a27)) ) && a14 <= -148 ) && (a8==5))){
      a27 = (((a27 + -193865) - 171565) * 1);
      a21 = ((((a21 / 5) + 82495) * 10)/ -9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && (( 182 < a27 && (((input == 3) && ((a9==5) || ((a9==3) || (a9==4)))) && (a8==5))) && 5 < a21 ))){
      a27 = (((a27 / 5) - 308359) * 1);
      a21 = ((((a21 % 299911)- 300088) - -149461) + -262952);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( ((100 < a27) && (182 >= a27)) && ( 5 < a21 && ((a8==7) && (((a9==2) || (a9==3)) && (input == 4))))))){
      a27 = ((((a27 + -353254) * 10)/ 9) + -125686);
      a21 = ((((a21 % 299911)+ -300088) * 1) - 81241);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((( 182 < a27 && (((a9==3) || (a9==4)) && (input == 3))) && a21 <= -178 ) && a14 <= -148 ) && (a8==6))){
      a27 = ((((((a27 % 40)- -105) + 165437) * 3) % 40)- -106);
      a21 = (((((a21 % 16)+ -149) + 3) + 108443) - 108456);
       a8 = 5;
       a9 = 5;
       return 21;
     } else if((( ((100 < a27) && (182 >= a27)) && ( a14 <= -148 && ((( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ( ((-144 < a21) && (5 >= a21)) && (a9==2))) && (input == 4)))) && (a8==8))){
      a27 = (((a27 - 596672) - -754909) + 2733);
      a21 = (((((a21 / 5) + -68) * 5) % 74)- 38);
       a8 = 4;
       a9 = 3;
       return 23;
     } else if(( a21 <= -178 && (((a8==7) && ((a9==5) && ( a14 <= -148 && (input == 5)))) && 182 < a27 ))){
      a27 = ((((a27 + -323152) * 1) + -252230) + -24772);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a9==2) && (((( a14 <= -148 && (input == 5)) && 5 < a21 ) && (a8==8)) && ((-78 < a27) && (100 >= a27)) ))){
      a27 = (((a27 * 5) * 5) + -65844);
      a21 = (((((a21 % 299911)- 300088) * 10)/ 9) + -27777);
       a8 = 4;
       return -1;
     } else if(( ((-178 < a21) && (-144 >= a21)) && ((a8==6) && ( a27 <= -78 && (((input == 6) && ((a9==4) || ((a9==2) || (a9==3)))) && ((-148 < a14) && (13 >= a14)) ))))){
      a14 = (((a14 + -454785) * 1) * 1);
      a27 = ((((((a27 * 9)/ 10) * 1) + -45851) % 40)- -174);
      a21 = (((a21 + -467737) + -123055) * 1);
       a8 = 7;
       a9 = 2;
       return 25;
     } else if((((((input == 1) && (( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ( ((-144 < a21) && (5 >= a21)) && (a9==2)))) && (a8==8)) && a14 <= -148 ) && 182 < a27 )){
      a27 = ((((((a27 - 0) * -5)/ 10) / 5) * 44)/ 10);
      a21 = ((((a21 % 16)+ -161) + -1) + 0);
       a8 = 4;
       a9 = 6;
       return -1;
     } else if((((((input == 4) && (((a9==3) && 5 < a21 ) || (((a9==6) && ((-144 < a21) && (5 >= a21)) ) || ((a9==2) && 5 < a21 )))) && (a8==7)) && a14 <= -148 ) && a27 <= -78 )){
      a21 = ((((a21 * 9)/ 10) / 5) - 323565);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==4) && ( ((100 < a27) && (182 >= a27)) && ( ((-144 < a21) && (5 >= a21)) && ((input == 5) && ((a9==6) || ((a9==4) || (a9==5))))))) && a14 <= -148 )){
      a27 = (((a27 / 5) / 5) - 471305);
      a21 = ((((a21 - 118243) * 10)/ 9) / 5);
       a9 = 2;
       return -1;
     } else if((((a8==8) && ( ((-144 < a21) && (5 >= a21)) && (( a14 <= -148 && (input == 2)) && (a9==4)))) && 182 < a27 )){
      if((a8==7)){
      a27 = (((a27 - 165747) + -434393) * 1);
      a21 = ((((a21 - 274867) % 16)+ -147) + -7);
       a8 = 6;
       a9 = 2;
      } else{
       a27 = ((((a27 + -600128) / 5) * 10)/ 3);
       a8 = 5;
       a9 = 3;
      } return 21;
     } else if(((a9==4) && ((a8==4) && ( a14 <= -148 && ( ((100 < a27) && (182 >= a27)) && ( 5 < a21 && (input == 5))))))){
      a27 = ((((a27 / 5) * 10)/ -2) - 243130);
      a21 = ((((a21 + -110103) % 299911)- 300088) - 1);
       a9 = 2;
       return -1;
     } else if(((a8==4) && ( a14 <= -148 && ( 5 < a21 && ( ((100 < a27) && (182 >= a27)) && (((a9==2) || (a9==3)) && (input == 3))))))){
      if( 182 < a14 ){
      a27 = (((a27 - -32126) * 5) * 3);
      a21 = ((((a21 * 9)/ 10) - 580447) * 1);
       a8 = 7;
       a9 = 6;
      } else{
       a27 = (((((a27 * -8)/ 10) + 191989) * -1)/ 10);
       a21 = ((((a21 % 299911)+ -300088) - 106314) * 1);
       a8 = 8;
       a9 = 4;
      } return 21;
     } else if(( 5 < a21 && ((a9==2) && (( ((-78 < a27) && (100 >= a27)) && ( a14 <= -148 && (input == 1))) && (a8==8))))){
      a27 = (((((a27 - 95065) * 5) * 1) % 40)+ 163);
      a21 = ((((a21 % 299911)- 300088) - 292917) + -3663);
       a8 = 7;
       a9 = 4;
       return 21;
     } else if(((((( a14 <= -148 && (input == 4)) && a21 <= -178 ) && (a9==3)) && ((100 < a27) && (182 >= a27)) ) && (a8==5))){
      a27 = (((a27 * 5) * 5) - 191095);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( 5 < a21 && ((a8==5) && ( 182 < a27 && (((((a9==3) || (a9==4)) || (a9==5)) && (input == 5)) && a14 <= -148 ))))){
      a27 = (((a27 + -600126) * 1) * 1);
      a21 = ((((a21 % 299911)- 300088) - 193458) - -32063);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( 182 < a27 && ((((input == 6) && (( ((-178 < a21) && (-144 >= a21)) && (a9==2)) || (((a9==5) && a21 <= -178 ) || ((a9==6) && a21 <= -178 )))) && (a8==4)) && a14 <= -148 ))){
      if( a27 <= -78 ){
      a21 = (((((a21 % 299911)+ -178) / 5) * 5) - 18375);
       a8 = 7;
       a9 = 5;
      } else{
       a27 = ((((((a27 % 88)- -8) * 5) * 5) % 88)+ -64);
       a21 = ((((a21 % 16)+ -148) / 5) - 135);
       a8 = 6;
       a9 = 3;
      } return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && ((( a27 <= -78 && (((a9==4) || (a9==5)) && (input == 3))) && ((-144 < a21) && (5 >= a21)) ) && (a8==5)))){
      a14 = (((((a14 + 566903) + 24199) - 390557) * -1)/ 10);
      a27 = ((((((a27 * 9)/ 10) / 5) * 5) % 88)- -90);
      a21 = ((((a21 % 16)- 161) / 5) + -121);
       a9 = 2;
       return -1;
     } else if(((((((a8==4) && (input == 2)) && a14 <= -148 ) && (a9==2)) && 5 < a21 ) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((a27 - 199892) * 3) + -54);
      a21 = ((((((a21 % 299911)+ -300088) / 5) + 257684) * -1)/ 10);
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && ( a27 <= -78 && ( a21 <= -178 && ((a8==6) && ((a9==4) && (input == 3))))))){
      a14 = (((a14 + -340660) * 1) * 1);
      a27 = (((((a27 % 299908)- -300090) * 1) - 475687) + 527828);
      a21 = (((a21 - -600055) - -114) - -8);
       a9 = 6;
       return 21;
     } else if(( a21 <= -178 && (((a8==5) && ( ((-148 < a14) && (13 >= a14)) && ((((a9==2) || (a9==3)) || (a9==4)) && (input == 6)))) && a27 <= -78 ))){
      a14 = (((a14 + -101412) * 5) + -19539);
      a27 = ((((((a27 % 88)- -41) * 5) * 5) % 88)+ 10);
      a21 = ((((a21 / 5) + 331466) % 74)+ -111);
       a8 = 8;
       a9 = 4;
       return -1;
     } else if(((a9==4) && ( 5 < a21 && ((a8==6) && (((input == 2) && 182 < a27 ) && a14 <= -148 ))))){
      a27 = (((((a27 / 5) / 5) * 5) % 40)- -120);
      a21 = ((((a21 % 299911)+ -300088) * 1) - 13929);
       a9 = 3;
       return 21;
     } else if(((((((input == 4) && a21 <= -178 ) && (a8==4)) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 ) && (a9==5))){
      a27 = ((((a27 - 232785) - 40308) * 10)/ 9);
       a9 = 2;
       return -1;
     } else if(((a8==7) && ( a14 <= -148 && ( 5 < a21 && ( ((-78 < a27) && (100 >= a27)) && ((input == 4) && ((a9==4) || (a9==5)))))))){
      a27 = (((a27 + -371468) * 1) + -165947);
      a21 = (((a21 / 5) + -439784) - 91879);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a27 <= -78 && (((((input == 1) && ((a9==5) || ((a9==3) || (a9==4)))) && (a8==4)) && a21 <= -178 ) && ((-148 < a14) && (13 >= a14)) ))){
      if( ((-78 < a27) && (100 >= a27)) ){
      a14 = (((a14 + -144725) / 5) + -368268);
      a21 = (((((a21 % 74)- 34) - 225582) / 5) - -45046);
       a9 = 6;
      } else{
       a14 = (((a14 - 260272) - 320547) / 5);
       a27 = (((((a27 * 9)/ 10) - -536006) % 88)+ 12);
       a8 = 8;
       a9 = 2;
      } return -1;
     } else if(( a27 <= -78 && ( a21 <= -178 && (( ((-148 < a14) && (13 >= a14)) && ((input == 2) && ((a9==5) || ((a9==3) || (a9==4))))) && (a8==4))))){
      a14 = ((((a14 / 5) / 5) / 5) - 303817);
      a27 = (((((((a27 % 299908)+ 300090) * 10)/ 9) / 5) * 46)/ 10);
      a21 = (((((a21 - 0) - 0) + 298885) % 74)- 68);
       a8 = 6;
       a9 = 3;
       return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && ((a8==8) && (((((a9==6) && a21 <= -178 ) || ((a9==2) && ((-178 < a21) && (-144 >= a21)) )) && (input == 5)) && a14 <= -148 )))){
      a27 = (((a27 + -344061) - 224966) * 1);
      a21 = ((((a21 * 9)/ 10) - 51945) + -5260);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a27 <= -78 && (((((a9==3) || (a9==4)) && (input == 3)) && ((-148 < a14) && (13 >= a14)) ) && 5 < a21 )) && (a8==6))){
      if((a8==8)){
      a14 = (((a14 + -575139) - 773) + -17784);
       a8 = 4;
       a9 = 5;
      } else{
       a14 = (((a14 - 453633) + -102564) * 1);
       a27 = ((((a27 - -112998) % 299908)+ 300090) * 1);
       a21 = ((((((a21 + 0) % 16)+ -163) / 5) * 51)/ 10);
       a8 = 5;
       a9 = 2;
      } return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && ( 5 < a21 && ((a8==7) && ( a14 <= -148 && ((input == 1) && ((a9==2) || (a9==3)))))))){
      a27 = ((((a27 * -8)/ 10) * 5) + -459453);
      a21 = ((((a21 % 299911)+ -300088) * 1) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==4) && ( ((-144 < a21) && (5 >= a21)) && ((( 182 < a27 && (input == 6)) && a14 <= -148 ) && (a9==3))))){
      a27 = ((((((a27 * -5)/ 10) + -269160) - -697488) * -1)/ 10);
      a21 = (((a21 - 475876) * 1) + -42024);
       a9 = 2;
       return -1;
     } else if(( 182 < a27 && ( a21 <= -178 && ( a14 <= -148 && ((a8==4) && (((a9==4) || ((a9==2) || (a9==3))) && (input == 5))))))){
      a27 = (((a27 + -600079) * 1) - 25);
       a9 = 2;
       return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && (((((input == 4) && (((a9==3) || (a9==4)) || (a9==5))) && (a8==4)) && ((-178 < a21) && (-144 >= a21)) ) && a14 <= -148 ))){
      a21 = ((((a21 * 5) + 213153) * -1)/ 10);
       a9 = 3;
       return -1;
     } else if(((a8==4) && ( 182 < a27 && ((a9==4) && ( a14 <= -148 && ((input == 2) && 5 < a21 )))))){
      a27 = ((((a27 * -5)/ 10) + -122817) * 1);
      a21 = ((((a21 % 299911)- 300088) + -196831) / 5);
       a9 = 2;
       return -1;
     } else if((( ((-78 < a27) && (100 >= a27)) && (((input == 1) && (((a9==6) && a21 <= -178 ) || ( ((-178 < a21) && (-144 >= a21)) && (a9==2)))) && (a8==8))) && a14 <= -148 )){
      a27 = (((a27 - 206833) * 2) / 5);
      a21 = ((((a21 - 0) % 299911)- 178) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==4) && ( ((-78 < a27) && (100 >= a27)) && ( 5 < a21 && ((input == 1) && a14 <= -148 )))) && (a9==3))){
      a27 = ((((a27 - 526774) * 10)/ 9) * 1);
      a21 = (((((a21 - 409680) - -201354) - 235888) % 299911)+ -300088);
       a9 = 2;
       return -1;
     } else if((((((a8==7) && ( ((-178 < a21) && (-144 >= a21)) && (input == 2))) && (a9==6)) && ((-148 < a14) && (13 >= a14)) ) && a27 <= -78 )){
      a21 = (((((a21 + -525630) + -41351) - -584989) * -1)/ 10);
       a9 = 3;
       return -1;
     } else if((( 5 < a21 && (( a14 <= -148 && ((input == 1) && (a8==8))) && a27 <= -78 )) && (a9==5))){
      a21 = (((((a21 % 299911)- 300088) - -521812) * 1) + -732783);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( 5 < a21 && ( ((-148 < a14) && (13 >= a14)) && ( a27 <= -78 && (((a9==5) || (a9==6)) && (input == 1))))) && (a8==6))){
      a14 = ((((a14 + -69919) / 5) * 10)/ 9);
      a27 = ((((a27 % 299908)- -300090) - -19872) - -122571);
      a21 = ((((a21 % 74)- 77) + 9) - 32);
       a8 = 8;
       a9 = 4;
       return 25;
     } else if(( a21 <= -178 && ((a8==7) && ((a9==3) && ( a27 <= -78 && ( a14 <= -148 && (input == 5))))))){
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((-78 < a27) && (100 >= a27)) && (((a8==8) && (((a9==5) || (a9==6)) && (input == 6))) && a14 <= -148 )) && 5 < a21 )){
      a27 = (((a27 + -549458) / 5) / 5);
      a21 = ((((((a21 % 74)+ -89) * 5) + 123087) % 74)+ -96);
       a8 = 7;
       a9 = 2;
       return 25;
     } else if(((a8==7) && (( a14 <= -148 && ((((a9==6) && a21 <= -178 ) || ( ((-178 < a21) && (-144 >= a21)) && (a9==2))) && (input == 6))) && ((100 < a27) && (182 >= a27)) ))){
      a21 = (((((a21 % 299911)- 178) * 1) / 5) + -127803);
       a8 = 4;
       a9 = 3;
       return 25;
     } else if((( a14 <= -148 && ((a8==7) && ( 182 < a27 && (((a9==2) || (a9==3)) && (input == 1))))) && 5 < a21 )){
      a27 = (((a27 - 600142) - 17) * 1);
      a21 = ((((a21 % 16)+ -173) + -420785) - -420787);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((((a8==4) && (((a9==2) || (a9==3)) && (input == 3))) && ((-144 < a21) && (5 >= a21)) ) && ((100 < a27) && (182 >= a27)) ))){
      a27 = ((((a27 * 10)/ -9) / 5) * 5);
      a21 = (((a21 + -303927) * 1) + -261941);
       a9 = 2;
       return -1;
     } else if((((a9==2) && ((a8==5) && (( ((-178 < a21) && (-144 >= a21)) && (input == 4)) && ((-78 < a27) && (100 >= a27)) ))) && a14 <= -148 )){
      a21 = (((a21 / 5) + -175013) + -347568);
       a8 = 8;
       a9 = 6;
       return 23;
     } else if((((a8==4) && ( ((-144 < a21) && (5 >= a21)) && (((input == 3) && ((a9==3) || (a9==4))) && ((-78 < a27) && (100 >= a27)) ))) && a14 <= -148 )){
      a27 = (((a27 / 5) * 5) - 111506);
      a21 = (((a21 + -396154) * 1) - -193476);
       a9 = 2;
       return -1;
     } else if((( 182 < a27 && ((a9==6) && (( a14 <= -148 && (input == 4)) && a21 <= -178 ))) && (a8==7))){
      a27 = (((((((a27 * 9)/ 10) % 88)+ -9) * 5) % 88)- -11);
       a8 = 4;
       return 23;
     } else if((( a14 <= -148 && (((input == 3) && ((( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ( ((-144 < a21) && (5 >= a21)) && (a9==2))) || ( ((-144 < a21) && (5 >= a21)) && (a9==3)))) && (a8==8))) && a27 <= -78 )){
      a21 = (((a21 + -129748) - 310483) - 80676);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( a27 <= -78 && ((input == 4) && (( ((-144 < a21) && (5 >= a21)) && (a9==3)) || (((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ( ((-144 < a21) && (5 >= a21)) && (a9==2)))))) && a14 <= -148 ) && (a8==8))){
      a21 = (((a21 + -397751) / 5) / 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-178 < a21) && (-144 >= a21)) && ( ((-78 < a27) && (100 >= a27)) && ((((input == 2) && (a8==5)) && (a9==3)) && a14 <= -148 )))){
      a27 = (((a27 - 299444) - 76315) - 165980);
      a21 = (((a21 - -569002) + -788175) - 38543);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && ( a27 <= -78 && ((( a21 <= -178 && ((a8==6) && (a9==3))) || ((((a8==5) && (a9==6)) && 5 < a21 ) || ( a21 <= -178 && ((a8==6) && (a9==2))))) && (input == 2))))){
      a14 = (((a14 + -221893) * 2) * 1);
      a21 = ((((a21 % 16)- 161) + 2) - 2);
       a8 = 5;
       a9 = 6;
       return -1;
     } else if((((((input == 4) && ((((a9==5) && a21 <= -178 ) || ( a21 <= -178 && (a9==6))) || ( ((-178 < a21) && (-144 >= a21)) && (a9==2)))) && a14 <= -148 ) && (a8==6)) && ((100 < a27) && (182 >= a27)) )){
      a27 = (((a27 + -336276) / 5) / 5);
      a21 = (((((a21 % 299911)+ -178) - 100902) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((((input == 3) && ((-148 < a14) && (13 >= a14)) ) && (a8==7)) && a27 <= -78 ) && (a9==4)) && a21 <= -178 )){
      a14 = (((a14 / 5) + 458296) - 496867);
      a21 = ((((((a21 % 16)- 146) / 5) / 5) * 289)/ 10);
       a8 = 6;
       a9 = 6;
       return -1;
     } else if((((a9==4) && ( a21 <= -178 && (((a8==4) && (input == 3)) && a14 <= -148 ))) && ((100 < a27) && (182 >= a27)) )){
      a27 = (((a27 - 4456) - -446387) * 1);
       a8 = 5;
       a9 = 3;
       return 25;
     } else if((((a8==5) && ( ((-78 < a27) && (100 >= a27)) && (( a14 <= -148 && (input == 3)) && ((-144 < a21) && (5 >= a21)) ))) && (a9==5))){
      a21 = (((a21 - -8188) - 540916) + 867004);
       a8 = 8;
       a9 = 2;
       return 21;
     } else if(((a8==7) && (( ((-78 < a27) && (100 >= a27)) && (((((a9==5) && a21 <= -178 ) || ( a21 <= -178 && (a9==6))) || ((a9==2) && ((-178 < a21) && (-144 >= a21)) )) && (input == 2))) && a14 <= -148 ))){
      a27 = ((((a27 - 319212) + 743440) * -1)/ 10);
      a21 = ((((((a21 % 299911)- 178) * 10)/ 9) + 73851) + -263459);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((100 < a27) && (182 >= a27)) && (( a21 <= -178 && ((input == 2) && ((a9==5) || ((a9==3) || (a9==4))))) && (a8==8))) && a14 <= -148 )){
      a27 = ((((((a27 - 334102) * 10)/ 9) - -538418) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a9==4) && (((((a8==8) && (input == 1)) && ((-144 < a21) && (5 >= a21)) ) && a14 <= -148 ) && ((100 < a27) && (182 >= a27)) ))){
      a27 = ((((a27 * 5) / 5) / 5) + -159331);
      a21 = (((a21 - 177557) + 39954) + -238081);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( a27 <= -78 && (((input == 2) && ((a9==3) || (a9==4))) && ((-144 < a21) && (5 >= a21)) )) && (a8==4)) && ((-148 < a14) && (13 >= a14)) )){
      a14 = (((a14 - 532016) - 36499) * 1);
      a27 = (((((a27 % 88)+ 79) / 5) + 491004) - 490960);
       a8 = 8;
       a9 = 6;
       return -1;
     } else if(((((((input == 3) && a14 <= -148 ) && (a9==5)) && a21 <= -178 ) && (a8==8)) && a27 <= -78 )){
      a27 = ((((((a27 * 9)/ 10) + -22101) + 512907) % 88)+ 11);
      a21 = ((((a21 + 515487) % 16)+ -159) - 3);
       a8 = 4;
       a9 = 2;
       return 21;
     } else if(((a9==5) && ( ((-178 < a21) && (-144 >= a21)) && ( ((-78 < a27) && (100 >= a27)) && ( a14 <= -148 && ((a8==8) && (input == 5))))))){
      a27 = (((a27 + -535818) + -52916) / 5);
      a21 = ((((a21 * 10)/ 8) - 319110) + -97372);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a21 <= -178 && ((((input == 5) && ((a9==3) || (a9==4))) && a14 <= -148 ) && (a8==7))) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((a27 * 5) - -113614) + -518168);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a9==4) && ( ((-144 < a21) && (5 >= a21)) && ((((a8==5) && (input == 6)) && 182 < a27 ) && a14 <= -148 )))){
      a27 = ((((a27 - 600123) / 5) / 5) + -306576);
      a21 = (((a21 - 51673) * 5) - 324993);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==7) && ( a14 <= -148 && ( a21 <= -178 && (((((a9==4) || (a9==5)) || (a9==6)) && (input == 6)) && a27 <= -78 ))))){
      a21 = ((((a21 % 16)+ -144) - 14) - -9);
       a9 = 6;
       return 25;
     } else if((((a9==5) && ((((input == 4) && ((-148 < a14) && (13 >= a14)) ) && ((-178 < a21) && (-144 >= a21)) ) && (a8==4))) && a27 <= -78 )){
      if( ((100 < a27) && (182 >= a27)) ){
      a14 = (((((a14 + 127089) * 4) * 1) * -1)/ 10);
      a21 = ((((((a21 * 1)/ 10) * 9)/ 10) * 9)/ 10);
       a8 = 6;
       a9 = 3;
      } else{
       a14 = (((a14 - 302315) * 1) / 5);
       a21 = ((((a21 + 544272) + 7767) + -764337) - -704963);
       a8 = 6;
       a9 = 2;
      } return 21;
     } else if((((( ((-78 < a27) && (100 >= a27)) && ((input == 2) && (((a9==4) || (a9==5)) || (a9==6)))) && a14 <= -148 ) && (a8==5)) && a21 <= -178 )){
      a27 = ((((a27 - -138602) * 10)/ -9) / 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( 5 < a21 && ( ((100 < a27) && (182 >= a27)) && ((a9==4) && ((input == 1) && (a8==4))))))){
      if( ((-148 < a14) && (13 >= a14)) ){
      a27 = (((((a27 * 19)/ 10) * 10)/ 9) * 5);
      a21 = ((((a21 % 299911)- 300088) + -280285) / 5);
       a8 = 7;
       a9 = 5;
      } else{
       a27 = ((((a27 * 10)/ 19) - 514153) + 514074);
       a21 = ((((a21 % 16)+ -171) - -8) + 4);
       a8 = 6;
      } return -1;
     } else if((( a14 <= -148 && ((a8==4) && ((((a9==6) || ((a9==4) || (a9==5))) && (input == 4)) && 182 < a27 ))) && ((-144 < a21) && (5 >= a21)) )){
      a27 = (((((a27 * -5)/ 10) * 10)/ 9) + -32401);
       a8 = 5;
       a9 = 2;
       return -1;
     } else if(((a8==6) && ( a14 <= -148 && ( 5 < a21 && ((((a9==4) || ((a9==2) || (a9==3))) && (input == 5)) && ((100 < a27) && (182 >= a27)) ))))){
      a27 = ((((a27 + -310914) / 5) * 10)/ 9);
      a21 = ((((a21 * 9)/ 10) - 547695) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-178 < a21) && (-144 >= a21)) && ( a14 <= -148 && ( ((-78 < a27) && (100 >= a27)) && (((((a9==4) || (a9==5)) || (a9==6)) && (input == 5)) && (a8==7)))))){
      a27 = (((a27 / 5) * 5) + -505787);
      a21 = (((a21 + -160389) - 417813) - 20074);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( ((100 < a27) && (182 >= a27)) && ((((a9==5) || ((a9==3) || (a9==4))) && (input == 5)) && a21 <= -178 )) && (a8==8)) && a14 <= -148 )){
      a27 = (((a27 + -582490) + -8500) - 1465);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a9==5) && ((((input == 6) && ((-78 < a27) && (100 >= a27)) ) && (a8==8)) && ((-178 < a21) && (-144 >= a21)) )) && a14 <= -148 )){
      a27 = (((a27 + 67480) / 5) - 535351);
      a21 = ((((a21 - 314102) + 450313) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a9==3) && (( a14 <= -148 && ((a8==7) && (input == 6))) && a21 <= -178 )) && a27 <= -78 )){
      a21 = ((((((a21 % 16)+ -156) + 2) * 5) % 16)+ -156);
       a9 = 2;
       return 23;
     } else if((((( a14 <= -148 && ((a9==2) && (input == 3))) && ((-78 < a27) && (100 >= a27)) ) && (a8==8)) && a21 <= -178 )){
      a27 = (((a27 + -373149) - 109118) * 1);
       a8 = 4;
       return -1;
     } else if(((a8==5) && ( 5 < a21 && ((((input == 3) && (((a9==4) || (a9==5)) || (a9==6))) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 )))){
      a27 = ((((a27 * -8)/ 10) / 5) - 575292);
      a21 = (((a21 - 535073) / 5) - 470784);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a14 <= -148 && ((( a21 <= -178 && ((a9==2) && (a8==5))) || ((((a8==4) && (a9==5)) && 5 < a21 ) || ( 5 < a21 && ((a9==6) && (a8==4))))) && (input == 1))) && 182 < a27 )){
      a27 = (((a27 + -600162) + -18) * 1);
      a21 = (((a21 / 5) + -323831) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( 5 < a21 && ((a8==8) && (( ((100 < a27) && (182 >= a27)) && (((a9==5) || (a9==6)) && (input == 3))) && a14 <= -148 )))){
      if((a9==3)){
      a27 = ((((a27 * 19)/ 10) + -27902) - -64419);
      a21 = ((((a21 - 0) - 0) % 299911)+ -300088);
       a8 = 5;
       a9 = 5;
      } else{
       a27 = (((a27 + 512082) - 502702) * 5);
       a21 = ((((a21 + 0) % 16)+ -166) + 1);
       a8 = 6;
       a9 = 5;
      } return 23;
     } else if(((((( a14 <= -148 && (input == 1)) && (a9==6)) && (a8==8)) && 5 < a21 ) && a27 <= -78 )){
      a21 = (((a21 - 0) / 5) - 447191);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((100 < a27) && (182 >= a27)) && ((( a14 <= -148 && (input == 5)) && (a9==2)) && a21 <= -178 )) && (a8==7))){
      a27 = (((a27 + -419048) + -71030) * 1);
       a8 = 4;
       return -1;
     } else if(( a14 <= -148 && ((a8==5) && ((((input == 6) && ((a9==3) || (a9==4))) && ((-178 < a21) && (-144 >= a21)) ) && ((100 < a27) && (182 >= a27)) )))){
      a27 = (((((a27 - -91265) * -1)/ 10) * 10)/ 9);
      a21 = ((((a21 + -268906) - -708559) * 1) + -488498);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a27 <= -78 && (((a8==6) && ((input == 6) && (((a9==6) && ((-144 < a21) && (5 >= a21)) ) || ((a9==2) && 5 < a21 )))) && ((-148 < a14) && (13 >= a14)) ))){
      a14 = ((((a14 + -395187) * 10)/ 9) - 66075);
      a27 = ((((((a27 % 299908)+ 300090) / 5) / 5) * 262)/ 10);
      a21 = ((((a21 - 0) * 9)/ 10) - 568943);
       a8 = 7;
       a9 = 6;
       return -1;
     } else if((( a14 <= -148 && ( ((-144 < a21) && (5 >= a21)) && ((((a9==3) || (a9==4)) && (input == 4)) && (a8==4)))) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((a27 + -281463) + -36613) * 1);
      a21 = ((((a21 / 5) - 522439) * 10)/ 9);
       a9 = 2;
       return -1;
     } else if(((a8==4) && (( a21 <= -178 && (((input == 2) && ((100 < a27) && (182 >= a27)) ) && (a9==2))) && a14 <= -148 ))){
      a27 = ((((a27 + -383418) * -1)/ 10) - -209898);
      a21 = (((((a21 - 0) * 9)/ 10) % 74)+ 5);
       a9 = 6;
       return 21;
     } else if(( ((-144 < a21) && (5 >= a21)) && ((a8==4) && ( ((-78 < a27) && (100 >= a27)) && ( a14 <= -148 && ((input == 2) && ((a9==5) || (a9==6)))))))){
      a27 = (((a27 / 5) + -490811) * 1);
      a21 = (((a21 - 382519) + -208499) - 8140);
       a9 = 2;
       return -1;
     } else if(((a8==4) && (( a14 <= -148 && ((a9==4) && ((input == 3) && 182 < a27 ))) && 5 < a21 ))){
      a27 = ((((a27 % 88)+ -20) + 11) + 5);
       a8 = 8;
       a9 = 2;
       return 21;
     } else if(( a27 <= -78 && ( a21 <= -178 && ((a8==7) && (((a9==3) && (input == 1)) && a14 <= -148 ))))){
       a9 = 5;
       return 23;
     } else if((((( a14 <= -148 && ((input == 5) && (a8==7))) && ((-178 < a21) && (-144 >= a21)) ) && (a9==3)) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((a27 - -103352) / 5) + -375741);
      a21 = ((((((a21 * 13)/ 10) * 5) - -331881) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((-78 < a27) && (100 >= a27)) && ( a14 <= -148 && (((input == 1) && ((a9==3) || (a9==4))) && (a8==5)))) && ((-144 < a21) && (5 >= a21)) )){
       a8 = 8;
       a9 = 3;
       return 23;
     } else if(((((a8==8) && ( 5 < a21 && ((input == 1) && a14 <= -148 ))) && (a9==3)) && ((100 < a27) && (182 >= a27)) )){
      a27 = ((((((a27 * -1)/ 10) - 24) * 5) * -1)/ 10);
      a21 = (((((((a21 * 9)/ 10) % 74)- 71) * 5) % 74)+ -69);
       a8 = 4;
       a9 = 4;
       return 25;
     } else if(( a14 <= -148 && (((input == 6) && ((((a8==6) && (a9==2)) && a21 <= -178 ) || (( 5 < a21 && ((a8==5) && (a9==5))) || ( 5 < a21 && ((a9==6) && (a8==5)))))) && ((-78 < a27) && (100 >= a27)) ))){
      a27 = ((((a27 / 5) * 5) / 5) + -495973);
      a21 = (((a21 / 5) + -304170) + -100245);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a9==6) && ( ((100 < a27) && (182 >= a27)) && ((((input == 5) && (a8==4)) && a14 <= -148 ) && ((-178 < a21) && (-144 >= a21)) )))){
      a27 = (((((a27 * -8)/ 10) * 10)/ 9) - 45994);
      a21 = (((a21 * 5) * 5) * 5);
       a9 = 2;
       return -1;
     }
     return calculate_output3(input);
 }
 int calculate_output3(int input) {
     if(((a8==7) && ((( a27 <= -78 && ((input == 2) && ((a9==4) || (a9==5)))) && 5 < a21 ) && a14 <= -148 ))){
      a21 = (((((a21 % 299911)- 300088) / 5) * 5) + -248081);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((((input == 1) && (((a9==4) || (a9==5)) || (a9==6))) && ((-78 < a27) && (100 >= a27)) ) && a21 <= -178 ) && a14 <= -148 ) && (a8==5))){
      a27 = ((((a27 * 5) - -144444) * 10)/ -9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a27 <= -78 && (((((a8==7) && (input == 3)) && (a9==2)) && ((-144 < a21) && (5 >= a21)) ) && a14 <= -148 ))){
      a21 = (((a21 / 5) + -338412) * 1);
       a8 = 8;
       a9 = 5;
       return 23;
     } else if(( 182 < a27 && ( a14 <= -148 && ((input == 2) && (((((a9==5) && (a8==6)) && 5 < a21 ) || ( 5 < a21 && ((a9==6) && (a8==6)))) || (((a9==2) && (a8==7)) && a21 <= -178 )))))){
      a27 = (((a27 / 5) - -474879) + -837272);
      a21 = ((((a21 % 299911)- 300088) - 2) + 0);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a9==6) && ((( a14 <= -148 && (input == 1)) && ((100 < a27) && (182 >= a27)) ) && (a8==7))) && ((-178 < a21) && (-144 >= a21)) )){
      a27 = (((a27 - 357509) - 5092) + -191909);
      a21 = (((a21 * 5) - 316352) + -211936);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a14 <= -148 && ((a8==7) && (((((a9==3) || (a9==4)) || (a9==5)) && (input == 5)) && a27 <= -78 ))) && ((-144 < a21) && (5 >= a21)) )){
      a21 = ((((a21 + -271683) / 5) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((a8==8) && (((input == 1) && ((a9==5) || (a9==6))) && a14 <= -148 )) && 5 < a21 ) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((((a27 - -144105) % 40)+ 133) + 217137) + -217167);
      a21 = ((((((a21 % 74)+ -108) + -18178) * 5) % 74)+ 3);
       a8 = 7;
       a9 = 6;
       return 23;
     } else if(( ((100 < a27) && (182 >= a27)) && ( a14 <= -148 && ((input == 1) && (( 5 < a21 && ((a9==6) && (a8==7))) || ( a21 <= -178 && ((a8==8) && (a9==2)))))))){
      if((a8==4)){
      a27 = (((a27 * 5) / 5) + 589336);
      a21 = ((((a21 / 5) - 150717) - 224629) + 697472);
       a8 = 5;
       a9 = 5;
      } else{
       a21 = ((((a21 % 74)+ -68) - -426901) + -426901);
       a8 = 4;
       a9 = 5;
      } return 21;
     } else if((( ((-178 < a21) && (-144 >= a21)) && ((a9==3) && ( a14 <= -148 && ((a8==5) && (input == 4))))) && 182 < a27 )){
      a27 = (((((a27 * -5)/ 10) * 1) + 123264) + -197900);
      a21 = (((((a21 * 10)/ 8) / 5) * 10)/ 2);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==7) && ( ((-178 < a21) && (-144 >= a21)) && (( ((100 < a27) && (182 >= a27)) && ((input == 1) && ((a9==4) || (a9==5)))) && a14 <= -148 )))){
      a27 = ((((a27 * 5) / 5) / 5) - 356264);
      a21 = (((a21 * 5) + -299062) - 33787);
       a8 = 6;
       a9 = 4;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && ( a27 <= -78 && ((a8==5) && ((input == 3) && (((a9==3) && 5 < a21 ) || (((a9==6) && ((-144 < a21) && (5 >= a21)) ) || ((a9==2) && 5 < a21 )))))))){
      if( a14 <= -148 ){
      a14 = (((a14 + -105663) * 5) * 1);
      a27 = ((((a27 % 40)+ 146) / 5) * 5);
      a21 = ((((a21 - 173408) % 16)+ -159) * 1);
       a8 = 8;
       a9 = 6;
      } else{
       a14 = (((a14 / 5) / 5) - 481267);
       a21 = (((((a21 * 9)/ 10) - 540724) + 454341) + -460775);
       a8 = 6;
       a9 = 6;
      } return -1;
     } else if(((((((input == 3) && 182 < a27 ) && a14 <= -148 ) && (a8==5)) && (a9==4)) && ((-144 < a21) && (5 >= a21)) )){
      a27 = (((((a27 % 40)- -102) * 5) % 40)- -133);
       a8 = 6;
       a9 = 6;
       return 21;
     } else if(( ((-148 < a14) && (13 >= a14)) && ((((((a9==3) || (a9==4)) && (input == 6)) && a27 <= -78 ) && (a8==6)) && 5 < a21 ))){
      a14 = (((a14 / 5) * 5) - 146700);
      a27 = ((((a27 + 443786) % 299908)+ 300090) * 1);
      a21 = ((((a21 * 9)/ 10) + -568455) - 15708);
       a8 = 8;
       a9 = 3;
       return 23;
     } else if(((a8==4) && (( a14 <= -148 && ((((a9==5) || ((a9==3) || (a9==4))) && (input == 1)) && ((100 < a27) && (182 >= a27)) )) && ((-178 < a21) && (-144 >= a21)) ))){
      a27 = (((a27 * 5) + -365309) - 92845);
      a21 = (((a21 + -277404) + -301764) - 5367);
       a9 = 2;
       return -1;
     } else if(( ((-178 < a21) && (-144 >= a21)) && (((((input == 3) && ((a9==6) || ((a9==4) || (a9==5)))) && ((-78 < a27) && (100 >= a27)) ) && a14 <= -148 ) && (a8==7)))){
      if( 182 < a14 ){
      a27 = (((a27 + 339853) + 118718) + 20360);
      a21 = (((a21 + 115934) - -439899) * 1);
       a8 = 6;
       a9 = 3;
      } else{
       a27 = ((((a27 % 40)+ 141) + -50941) - -50941);
       a21 = ((((a21 + 76230) * 10)/ 9) + 205726);
       a8 = 6;
       a9 = 3;
      } return 21;
     } else if(( a14 <= -148 && ( ((100 < a27) && (182 >= a27)) && (((((a8==7) && (a9==6)) && 5 < a21 ) || (((a8==8) && (a9==2)) && a21 <= -178 )) && (input == 2))))){
      a21 = ((((a21 % 299997)- -300002) + 1) + 0);
       a8 = 4;
       a9 = 4;
       return 21;
     } else if((( a14 <= -148 && ( ((-144 < a21) && (5 >= a21)) && (((a9==3) && (input == 1)) && ((100 < a27) && (182 >= a27)) ))) && (a8==7))){
      if( 182 < a27 ){
      a27 = (((a27 / 5) + 52760) - -370951);
      a21 = (((((a21 - -291117) % 16)+ -168) / 5) + -127);
       a9 = 6;
      } else{
       a27 = ((((a27 - -521403) * 10)/ 9) + 19392);
       a21 = (((a21 + 591085) - -4427) - -3650);
       a8 = 5;
       a9 = 4;
      } return 21;
     } else if(((( 182 < a27 && ( a14 <= -148 && ((input == 3) && ((a9==3) || (a9==4))))) && (a8==4)) && ((-178 < a21) && (-144 >= a21)) )){
      a27 = (((a27 + -600116) + -9) - 24);
      a21 = ((((a21 - 121367) - 318952) * 10)/ 9);
       a9 = 2;
       return -1;
     } else if((((( a27 <= -78 && ((((a9==3) || (a9==4)) || (a9==5)) && (input == 4))) && a14 <= -148 ) && ((-144 < a21) && (5 >= a21)) ) && (a8==7))){
      a21 = ((((a21 - 318221) * 1) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( a14 <= -148 && ((input == 6) && ((( ((-144 < a21) && (5 >= a21)) && (a9==5)) || ( ((-144 < a21) && (5 >= a21)) && (a9==6))) || ( 5 < a21 && (a9==2))))) && (a8==8)) && ((100 < a27) && (182 >= a27)) )){
      a27 = ((((a27 + 317492) * -1)/ 10) / 5);
      a21 = ((((a21 * 9)/ 10) - 556883) - 37092);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((( ((-78 < a27) && (100 >= a27)) && ((input == 2) && ((a9==3) || (a9==4)))) && 5 < a21 ) && (a8==6)) && a14 <= -148 )){
      a27 = ((((a27 - 582883) + 598105) * 10)/ -9);
      a21 = (((((a21 % 299911)+ -300088) * 1) - -486223) - 777223);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a9==2) && (((((input == 6) && a14 <= -148 ) && ((-78 < a27) && (100 >= a27)) ) && (a8==8)) && 5 < a21 ))){
      a27 = (((a27 * 5) * 5) - 533408);
      a21 = ((((a21 % 299911)+ -300088) + -258358) * 1);
       a8 = 4;
       return -1;
     } else if(((( ((100 < a27) && (182 >= a27)) && ((((a9==6) || ((a9==4) || (a9==5))) && (input == 3)) && a14 <= -148 )) && ((-144 < a21) && (5 >= a21)) ) && (a8==4))){
      a27 = (((a27 + -376897) + -47562) - 103100);
      a21 = (((((a21 - -584263) + 807) - 519090) * -1)/ 10);
       a9 = 2;
       return -1;
     } else if(((((a8==6) && (((input == 6) && 5 < a21 ) && ((-78 < a27) && (100 >= a27)) )) && (a9==5)) && a14 <= -148 )){
      a27 = (((a27 * 5) - 7181) / 5);
      a21 = ((((a21 / 5) + -452113) - -915881) - 945005);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((((((a9==5) || ((a9==3) || (a9==4))) && (input == 4)) && ((-178 < a21) && (-144 >= a21)) ) && a14 <= -148 ) && ((100 < a27) && (182 >= a27)) ) && (a8==6))){
       a9 = 5;
       return 23;
     } else if((((a8==4) && ( ((-178 < a21) && (-144 >= a21)) && (((input == 4) && (((a9==3) || (a9==4)) || (a9==5))) && ((-78 < a27) && (100 >= a27)) ))) && a14 <= -148 )){
      a27 = (((a27 / 5) - 272320) * 2);
      a21 = (((a21 * 5) - 285612) - -246555);
       a9 = 2;
       return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && ( a14 <= -148 && (((((a9==2) && 5 < a21 ) || (((a9==5) && ((-144 < a21) && (5 >= a21)) ) || ( ((-144 < a21) && (5 >= a21)) && (a9==6)))) && (input == 6)) && (a8==7))))){
      a27 = (((a27 - 357392) + -22593) - 124320);
      a21 = ((((a21 + 0) * 9)/ 10) - 588187);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( ((-178 < a21) && (-144 >= a21)) && ((a9==5) && (( ((-78 < a27) && (100 >= a27)) && (input == 5)) && (a8==6)))))){
      a27 = ((((a27 * 5) - -415071) * 1) + -628777);
      a21 = ((((a21 / 5) * 5) * 10)/ 7);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((a8==7) && (((a9==4) && ( ((-144 < a21) && (5 >= a21)) && (input == 6))) && ((100 < a27) && (182 >= a27)) )))){
      a27 = (((a27 * 5) + -319016) * 1);
      a21 = ((((a21 - 306502) * 1) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==4) && (( 182 < a27 && ((input == 5) && a14 <= -148 )) && (a9==4))) && 5 < a21 )){
      a27 = (((a27 + -306161) + -293966) - 42);
      a21 = ((((a21 % 299911)- 300088) * 1) + -171924);
       a9 = 2;
       return -1;
     } else if((((((((a9==3) || (a9==4)) && (input == 3)) && ((-78 < a27) && (100 >= a27)) ) && ((-144 < a21) && (5 >= a21)) ) && a14 <= -148 ) && (a8==6))){
      a27 = ((((a27 % 40)- -140) + 15084) - 15083);
      a21 = ((((a21 % 16)- 160) * 1) + -1);
       a8 = 5;
       a9 = 5;
       return 21;
     } else if((((((( ((-144 < a21) && (5 >= a21)) && (a9==2)) || (( ((-178 < a21) && (-144 >= a21)) && (a9==5)) || ((a9==6) && ((-178 < a21) && (-144 >= a21)) ))) && (input == 3)) && ((-148 < a14) && (13 >= a14)) ) && (a8==5)) && a27 <= -78 )){
      if( a27 <= -78 ){
      a14 = (((a14 + -595737) + -4098) / 5);
      a21 = (((a21 - 190676) * 3) / 5);
       a8 = 4;
       a9 = 6;
      } else{
       a14 = (((((a14 / 5) / 5) - -560142) * -1)/ 10);
       a27 = ((((a27 + 320355) * 1) % 299908)+ 300090);
       a21 = ((((a21 * 5) * 5) % 74)+ -68);
       a8 = 4;
       a9 = 2;
      } return -1;
     } else if(((a8==7) && ( 5 < a21 && ( a27 <= -78 && ((a9==3) && ( ((-148 < a14) && (13 >= a14)) && (input == 6))))))){
      a14 = ((((a14 / 5) + 527023) * 10)/ -9);
      a27 = ((((((a27 % 40)- -166) + 5) * 5) % 40)- -113);
      a21 = (((a21 / 5) - 404323) - 95398);
       a8 = 5;
       a9 = 4;
       return -1;
     } else if(((a9==2) && ( ((-148 < a14) && (13 >= a14)) && ((( a27 <= -78 && (input == 4)) && ((-178 < a21) && (-144 >= a21)) ) && (a8==4))))){
       return -1;
     } else if((((((a8==7) && (((a9==4) || ((a9==2) || (a9==3))) && (input == 3))) && ((-178 < a21) && (-144 >= a21)) ) && a14 <= -148 ) && 182 < a27 )){
      a27 = ((((a27 + -600117) - -458182) + -257593) - 200594);
      a21 = (((a21 - 61680) * 5) + -18440);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a14 <= -148 && ( a27 <= -78 && (((( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ( ((-144 < a21) && (5 >= a21)) && (a9==2))) || ((a9==3) && ((-144 < a21) && (5 >= a21)) )) && (input == 5)))) && (a8==8))){
      a21 = (((a21 / 5) + -142833) / 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( 182 < a27 && (((a8==7) && ( a14 <= -148 && (((a9==3) || (a9==4)) && (input == 2)))) && a21 <= -178 ))){
      a27 = (((((a27 + 0) * 9)/ 10) % 40)- -103);
      a21 = ((((a21 + 0) % 16)+ -152) * 1);
       a8 = 5;
       a9 = 3;
       return 21;
     } else if((((((input == 5) && (( ((-144 < a21) && (5 >= a21)) && (a9==6)) || ((a9==2) && 5 < a21 ))) && ((-148 < a14) && (13 >= a14)) ) && (a8==7)) && a27 <= -78 )){
      a14 = (((a14 - 437607) - 2367) - 12133);
      a21 = ((((a21 % 299911)- 300088) * 1) + -2);
       a8 = 4;
       a9 = 2;
       return 21;
     } else if((( ((100 < a27) && (182 >= a27)) && (( a14 <= -148 && ((input == 4) && (a8==4))) && (a9==6))) && ((-178 < a21) && (-144 >= a21)) )){
      a27 = ((((a27 * 5) * 10)/ -9) * 5);
      a21 = (((a21 * 5) - 71767) / 5);
       a9 = 2;
       return -1;
     } else if((((a9==3) && ((a8==8) && ( ((-78 < a27) && (100 >= a27)) && ((input == 2) && ((-144 < a21) && (5 >= a21)) )))) && a14 <= -148 )){
      a27 = (((a27 * 5) + -15677) - 116461);
      a21 = (((a21 + -296226) / 5) * 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==5) && (( ((-178 < a21) && (-144 >= a21)) && ( a14 <= -148 && ((input == 5) && (a9==3)))) && 182 < a27 ))){
      a21 = ((((a21 * 10)/ -9) - -419738) * 1);
       a9 = 5;
       return 21;
     } else if(( a21 <= -178 && (((((a9==6) && (input == 6)) && 182 < a27 ) && a14 <= -148 ) && (a8==7)))){
      a27 = ((((a27 / 5) * 10)/ -4) - 183090);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a27 <= -78 && ( ((-148 < a14) && (13 >= a14)) && ((a8==4) && (((input == 1) && ((a9==3) || (a9==4))) && ((-178 < a21) && (-144 >= a21)) ))))){
      if((a8==7)){
      a14 = (((a14 - 73626) - 77687) + -119560);
      a21 = (((a21 - -495950) - 603972) - 299667);
       a9 = 4;
      } else{
       a14 = (((a14 + -89825) * 5) / 5);
       a21 = (((a21 - 117938) - -707215) - -5784);
       a8 = 6;
       a9 = 6;
      } return -1;
     } else if(((a8==7) && (( ((100 < a27) && (182 >= a27)) && (((input == 6) && a14 <= -148 ) && ((-144 < a21) && (5 >= a21)) )) && (a9==3)))){
      a27 = (((a27 / 5) - 270742) + -307691);
      a21 = ((((a21 - -112533) + 119051) / 5) - 172203);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a9==6) && ( a14 <= -148 && ( a27 <= -78 && ( a21 <= -178 && ((a8==8) && (input == 6))))))){
      a27 = (((((a27 - -184339) * 1) * 1) % 88)+ 12);
      a21 = ((((a21 % 74)- 2) / 5) + 1);
       a8 = 4;
       a9 = 5;
       return 21;
     } else if(( ((-144 < a21) && (5 >= a21)) && ((a9==3) && ((( a14 <= -148 && (input == 6)) && ((100 < a27) && (182 >= a27)) ) && (a8==5))))){
      a27 = ((((a27 * -8)/ 10) + 142749) - 143949);
      a21 = ((((a21 + 364899) * 1) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( ((100 < a27) && (182 >= a27)) && ((a8==8) && ((( ((-178 < a21) && (-144 >= a21)) && (a9==3)) || (((a9==6) && a21 <= -178 ) || ((a9==2) && ((-178 < a21) && (-144 >= a21)) ))) && (input == 4)))))){
      a27 = ((((a27 / 5) - 448522) * 10)/ 9);
      a21 = ((((a21 % 299911)- 178) - 151789) + -131625);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==7) && ((((( 5 < a21 && (a9==3)) || (( ((-144 < a21) && (5 >= a21)) && (a9==6)) || ((a9==2) && 5 < a21 ))) && (input == 6)) && a14 <= -148 ) && a27 <= -78 ))){
      a21 = ((((a21 % 299911)+ -300088) / 5) + -277400);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a21 <= -178 && (((a8==7) && ( ((-148 < a14) && (13 >= a14)) && ((input == 1) && (a9==4)))) && a27 <= -78 ))){
      a14 = (((a14 + -217624) + -310562) + -48277);
      a21 = ((((a21 % 74)- -1) - -23110) + -23156);
       a8 = 6;
       a9 = 6;
       return -1;
     } else if((((a8==5) && ( ((-148 < a14) && (13 >= a14)) && ((( ((-144 < a21) && (5 >= a21)) && (a9==2)) || (((a9==5) && ((-178 < a21) && (-144 >= a21)) ) || ( ((-178 < a21) && (-144 >= a21)) && (a9==6)))) && (input == 4)))) && a27 <= -78 )){
      a14 = (((a14 / 5) - 317071) / 5);
      a27 = (((a27 + 0) / 5) + 141124);
      a21 = ((((a21 + 325718) * 10)/ 9) * 1);
       a8 = 4;
       a9 = 3;
       return 21;
     } else if(( ((100 < a27) && (182 >= a27)) && ((( a14 <= -148 && ((input == 1) && (a9==3))) && ((-144 < a21) && (5 >= a21)) ) && (a8==5)))){
      a27 = (((a27 / 5) + 354104) / 5);
      a21 = ((((a21 + -267132) % 16)+ -146) * 1);
       a8 = 4;
       a9 = 6;
       return 21;
     } else if(((a8==5) && ( ((100 < a27) && (182 >= a27)) && ( a14 <= -148 && ((input == 6) && ((((a9==5) && ((-178 < a21) && (-144 >= a21)) ) || ( ((-178 < a21) && (-144 >= a21)) && (a9==6))) || ( ((-144 < a21) && (5 >= a21)) && (a9==2)))))))){
      a27 = ((((a27 + -371883) * 10)/ 9) + -2763);
      a21 = ((((a21 + 140452) * 10)/ -9) + -31914);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((a8==5) && (((a9==3) && (input == 6)) && ((-178 < a21) && (-144 >= a21)) )) && ((-78 < a27) && (100 >= a27)) ) && a14 <= -148 )){
       a8 = 8;
       a9 = 4;
       return 21;
     } else if((( a21 <= -178 && ((( a14 <= -148 && (input == 4)) && (a8==5)) && 182 < a27 )) && (a9==4))){
      a21 = ((((a21 + 600092) + 8) + -266319) + 266299);
       a8 = 6;
       a9 = 5;
       return 21;
     } else if(((a8==4) && (( a27 <= -78 && ((input == 3) && (((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ( ((-144 < a21) && (5 >= a21)) && (a9==2))))) && ((-148 < a14) && (13 >= a14)) ))){
      a14 = (((a14 * 5) * 5) + -225956);
      a21 = ((((a21 + 526707) * 1) % 74)- 123);
       a8 = 6;
       a9 = 4;
       return 21;
     } else if((((( 5 < a21 && ((a8==5) && (input == 4))) && a27 <= -78 ) && ((-148 < a14) && (13 >= a14)) ) && (a9==4))){
      if( a27 <= -78 ){
      a14 = ((((a14 / 5) + 326301) - 283063) + -174541);
      a27 = (((((a27 + 0) % 40)- -140) * 10)/ 9);
       a8 = 7;
       a9 = 3;
      } else{
       a14 = (((a14 / 5) - 413036) * 1);
       a8 = 6;
       a9 = 3;
      } return -1;
     } else if(( a14 <= -148 && ((((( 5 < a21 && ((a8==6) && (a9==5))) || (((a8==6) && (a9==6)) && 5 < a21 )) || (((a9==2) && (a8==7)) && a21 <= -178 )) && (input == 5)) && 182 < a27 ))){
      a27 = (((a27 / 5) + -432466) - 45939);
      a21 = ((((((a21 * 9)/ 10) / 5) * 5) % 299911)- 300088);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a27 <= -78 && (((((a9==3) && (a8==6)) && a21 <= -178 ) || ((((a9==6) && (a8==5)) && 5 < a21 ) || ( a21 <= -178 && ((a9==2) && (a8==6))))) && (input == 1))) && ((-148 < a14) && (13 >= a14)) )){
      if((a9==2)){
      a21 = ((((a21 - 0) - 0) % 299911)- 300088);
       a8 = 7;
       a9 = 2;
      } else{
       a14 = ((((a14 / 5) / 5) - -92760) - 689946);
       a21 = ((((a21 % 299911)- 300088) + -2) - 0);
       a8 = 6;
       a9 = 2;
      } return -1;
     } else if(((( ((-78 < a27) && (100 >= a27)) && ((((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ( ((-144 < a21) && (5 >= a21)) && (a9==2))) && (input == 3))) && (a8==6)) && a14 <= -148 )){
      a27 = (((a27 - 491268) + -50033) - 12370);
      a21 = (((a21 - 356361) * 1) - 182491);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==4) && ( a14 <= -148 && ((a9==3) && ((input == 3) && 5 < a21 )))) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((a27 + -547934) * 1) + -9717);
      a21 = (((((a21 - 0) * 9)/ 10) * 1) + -540975);
       a9 = 2;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && (((a8==4) && ( 5 < a21 && ((input == 3) && (a9==3)))) && a27 <= -78 ))){
      if( ((100 < a27) && (182 >= a27)) ){
      a14 = (((a14 / 5) - 456320) * 1);
       a8 = 6;
       a9 = 5;
      } else{
       a14 = ((((a14 + 14908) * 10)/ -9) + -577536);
       a21 = (((((a21 % 74)- 100) + 562760) + -332669) - 230071);
       a8 = 5;
       a9 = 2;
      } return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && (( 5 < a21 && (((a8==4) && (input == 3)) && (a9==2))) && a14 <= -148 ))){
      a27 = (((((a27 + -80680) - -365650) * 2) * -1)/ 10);
      a21 = (((((a21 % 299911)- 300088) * 10)/ 9) - 145156);
       return -1;
     } else if(((a9==5) && (((((input == 6) && 182 < a27 ) && a21 <= -178 ) && a14 <= -148 ) && (a8==7)))){
      a27 = (((a27 + -600104) + -77) - 2);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((-78 < a27) && (100 >= a27)) && ( ((-178 < a21) && (-144 >= a21)) && ( a14 <= -148 && ((input == 3) && (a8==5))))) && (a9==3))){
      a27 = ((((a27 + -274230) * 2) + 912860) + -604353);
      a21 = ((((a21 - 297730) - -662490) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( a27 <= -78 && ((input == 2) && ((((a9==5) && ((-178 < a21) && (-144 >= a21)) ) || ( ((-178 < a21) && (-144 >= a21)) && (a9==6))) || ((a9==2) && ((-144 < a21) && (5 >= a21)) )))) && (a8==6)) && ((-148 < a14) && (13 >= a14)) )){
      if((a8==6)){
      a14 = (((a14 - -120190) - 359055) * 2);
      a27 = (((((a27 * 9)/ 10) - -469230) % 40)+ 140);
      a21 = (((((a21 % 16)- 160) / 5) * 10)/ 2);
       a8 = 7;
       a9 = 5;
      } else{
       a14 = (((a14 / 5) / 5) - 594946);
       a21 = ((((a21 % 74)- 69) - -1) + -1);
       a8 = 5;
       a9 = 6;
      } return -1;
     } else if(( a14 <= -148 && ((a8==8) && (((a9==5) && ((input == 5) && a21 <= -178 )) && a27 <= -78 )))){
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( 182 < a27 && ( a14 <= -148 && ((((a9==3) && ((-144 < a21) && (5 >= a21)) ) || (( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ((a9==2) && ((-144 < a21) && (5 >= a21)) ))) && (input == 3)))) && (a8==5))){
      a27 = ((((a27 * -5)/ 10) + -83228) + -50073);
      a21 = ((((a21 + -523608) + -9280) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( 182 < a27 && ((a9==4) && ( a14 <= -148 && (((input == 5) && (a8==5)) && a21 <= -178 ))))){
      a27 = (((a27 + -600169) / 5) * 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==6) && (( a21 <= -178 && ( a14 <= -148 && ((input == 3) && ((a9==3) || (a9==4))))) && ((-78 < a27) && (100 >= a27)) ))){
      a27 = (((((a27 % 40)+ 140) + 3) - -263267) - 263267);
      a21 = ((((a21 % 16)- 157) + -4) + 1);
       a8 = 4;
       a9 = 3;
       return 25;
     } else if(( ((-78 < a27) && (100 >= a27)) && ( a14 <= -148 && ((a8==8) && ( a21 <= -178 && (((a9==4) || (a9==5)) && (input == 4))))))){
      a27 = (((a27 - 389836) + 986107) + -771534);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((-178 < a21) && (-144 >= a21)) && (( a27 <= -78 && ((input == 1) && ((a9==2) || (a9==3)))) && (a8==7))) && a14 <= -148 )){
      a21 = ((((((a21 * 10)/ 13) * 9)/ 10) * 5) + 496);
       a9 = 2;
       return 25;
     } else if((((a9==3) && (((a8==8) && ( ((100 < a27) && (182 >= a27)) && (input == 6))) && a14 <= -148 )) && 5 < a21 )){
      a27 = (((((a27 / 5) * 5) * 5) % 88)+ -3);
      a21 = ((((a21 % 74)- 125) + 406583) - 406576);
       a8 = 4;
       a9 = 6;
       return 21;
     } else if(( a14 <= -148 && (((( a21 <= -178 && ((a8==8) && (a9==3))) || (( 5 < a21 && ((a8==7) && (a9==6))) || ( a21 <= -178 && ((a9==2) && (a8==8))))) && (input == 2)) && a27 <= -78 ))){
      if( 182 < a27 ){
      a27 = ((((((a27 % 40)- -168) * 5) - 81988) % 40)- -174);
      a21 = ((((a21 - 0) % 299997)+ 300002) + 0);
       a8 = 8;
       a9 = 5;
      } else{
       a21 = (((((a21 - 0) + 0) + 0) % 299997)- -300002);
       a8 = 8;
       a9 = 3;
      } return 21;
     } else if(( a14 <= -148 && ( ((100 < a27) && (182 >= a27)) && ((( 5 < a21 && ((a9==6) && (a8==7))) || (((a8==8) && (a9==2)) && a21 <= -178 )) && (input == 3))))){
      a27 = ((((a27 - -260122) * 2) * -1)/ 10);
      a21 = ((((((a21 % 299911)- 300088) + -2) * 9)/ 10) - 50821);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==8) && ((((a9==6) && ( a14 <= -148 && (input == 6))) && a27 <= -78 ) && 5 < a21 ))){
      a27 = (((((a27 / 5) - 334204) - 60608) % 88)- -62);
      a21 = ((((a21 % 299911)+ -300088) - 150881) * 1);
       a8 = 6;
       a9 = 3;
       return 25;
     } else if(( a14 <= -148 && ( 182 < a27 && (((( 5 < a21 && ((a8==4) && (a9==5))) || ( 5 < a21 && ((a9==6) && (a8==4)))) || ( a21 <= -178 && ((a9==2) && (a8==5)))) && (input == 4))))){
      a27 = ((((a27 % 88)- 23) + 274783) - 274796);
      a21 = (((((a21 * 9)/ 10) * 1) % 299911)- 300088);
       a8 = 4;
       a9 = 5;
       return 23;
     } else if(((((a8==5) && ( ((-78 < a27) && (100 >= a27)) && (((a9==6) || ((a9==4) || (a9==5))) && (input == 5)))) && a21 <= -178 ) && a14 <= -148 )){
       a8 = 8;
       a9 = 3;
       return 25;
     } else if((((a8==5) && (((( a21 <= -178 && (a9==6)) || ( ((-178 < a21) && (-144 >= a21)) && (a9==2))) && (input == 2)) && a14 <= -148 )) && ((100 < a27) && (182 >= a27)) )){
      if( ((-148 < a14) && (13 >= a14)) ){
      a27 = (((a27 + 45833) * 5) / 5);
      a21 = ((((a21 / 5) * 4) / 5) - 135533);
       a8 = 7;
       a9 = 3;
      } else{
       a27 = ((((a27 + -371555) * 1) + -19397) + 390846);
       a21 = (((((a21 / 5) % 74)+ 2) - -553351) - 553368);
       a8 = 6;
       a9 = 2;
      } return 25;
     } else if(( 182 < a27 && ( 5 < a21 && ((a8==6) && ((a9==2) && ( a14 <= -148 && (input == 1))))))){
      a27 = (((a27 + -600099) + 303710) + -303762);
      a21 = (((((a21 - 0) * 9)/ 10) - 438747) - 149174);
       a8 = 4;
       return -1;
     } else if((( a14 <= -148 && ((a9==3) && (((a8==5) && (input == 5)) && ((-178 < a21) && (-144 >= a21)) ))) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((a27 / 5) * 5) - 517189);
      a21 = (((a21 - 335889) - 256172) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-144 < a21) && (5 >= a21)) && (((a9==2) && (((input == 3) && ((100 < a27) && (182 >= a27)) ) && (a8==7))) && a14 <= -148 ))){
      a27 = ((((a27 + -470751) + 470620) + -541211) + 541232);
      a21 = (((a21 - 364952) + -213517) * 1);
       a8 = 4;
       a9 = 4;
       return 25;
     } else if((((((((a9==6) || ((a9==4) || (a9==5))) && (input == 6)) && (a8==5)) && a21 <= -178 ) && a14 <= -148 ) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((a27 + -214910) - 162004) / 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a21 <= -178 && ((a8==5) && (( ((-78 < a27) && (100 >= a27)) && (((a9==2) || (a9==3)) && (input == 2))) && a14 <= -148 )))){
      a27 = (((a27 - 567411) + -30781) - 1273);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((( 5 < a21 && (((a9==3) || (a9==4)) && (input == 5))) && a14 <= -148 ) && (a8==8)) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((a27 * 5) - 594535) - 2379);
      a21 = ((((a21 * 9)/ 10) / 5) - 253668);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && (((a9==4) && (((input == 4) && (a8==7)) && a21 <= -178 )) && a27 <= -78 ))){
       a8 = 5;
       a9 = 3;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && ((((a8==4) && ((((a9==4) || (a9==5)) || (a9==6)) && (input == 3))) && 5 < a21 ) && a27 <= -78 ))){
      a14 = (((a14 * 5) - 109727) - 30261);
      a21 = ((((a21 % 16)+ -171) / 5) + -122);
       a8 = 5;
       a9 = 2;
       return -1;
     } else if(((( ((-144 < a21) && (5 >= a21)) && ( a14 <= -148 && ((a8==5) && (input == 1)))) && 182 < a27 ) && (a9==4))){
      a27 = ((((((a27 + -16218) % 40)- -140) * 5) % 40)+ 113);
      a21 = ((((a21 / 5) + 181864) * 10)/ 9);
       a8 = 6;
       a9 = 3;
       return 25;
     } else if(((( a14 <= -148 && ( ((100 < a27) && (182 >= a27)) && ((input == 6) && ((a9==4) || (a9==5))))) && ((-144 < a21) && (5 >= a21)) ) && (a8==6))){
      a27 = (((a27 - 122613) - 397388) + -50160);
      a21 = (((a21 - 341416) * 1) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( 5 < a21 && ((((((a9==2) || (a9==3)) && (input == 2)) && a14 <= -148 ) && ((100 < a27) && (182 >= a27)) ) && (a8==4)))){
      a27 = (((a27 + 548171) - 577417) * 5);
      a21 = ((((((a21 % 299911)- 300088) * 1) / 5) * 51)/ 10);
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && (((input == 1) && ((((a8==8) && (a9==3)) && a21 <= -178 ) || ((((a9==6) && (a8==7)) && 5 < a21 ) || (((a8==8) && (a9==2)) && a21 <= -178 )))) && a27 <= -78 ))){
      a21 = (((((a21 % 299911)+ -300088) / 5) * 5) - 3);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((a8==4) && ( ((-144 < a21) && (5 >= a21)) && (((a9==2) || (a9==3)) && (input == 1)))) && a14 <= -148 ) && ((100 < a27) && (182 >= a27)) )){
      a27 = (((a27 - -391718) - 744761) + -121334);
      a21 = (((a21 + -244141) - 297845) + -50897);
       a9 = 2;
       return -1;
     } else if(((((((input == 2) && ((a9==3) || (a9==4))) && ((-144 < a21) && (5 >= a21)) ) && (a8==5)) && a14 <= -148 ) && ((-78 < a27) && (100 >= a27)) )){
       a8 = 8;
       a9 = 5;
       return 21;
     } else if((( a14 <= -148 && ((a8==5) && ( ((-78 < a27) && (100 >= a27)) && ((((a9==4) || (a9==5)) || (a9==6)) && (input == 4))))) && a21 <= -178 )){
       a8 = 8;
       a9 = 4;
       return 25;
     } else if((( ((-78 < a27) && (100 >= a27)) && ((((input == 2) && ((a9==4) || (a9==5))) && (a8==8)) && a14 <= -148 )) && a21 <= -178 )){
      a27 = ((((a27 / 5) - 271591) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((((((a9==6) && ((-144 < a21) && (5 >= a21)) ) || ( 5 < a21 && (a9==2))) || ((a9==3) && 5 < a21 )) && (input == 5)) && a14 <= -148 ) && a27 <= -78 ) && (a8==7))){
      a21 = ((((a21 % 299911)- 300088) * 1) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==4) && ((((input == 4) && ((100 < a27) && (182 >= a27)) ) && a21 <= -178 ) && (a9==4))) && a14 <= -148 )){
      a27 = (((a27 - 364784) + -447) / 5);
       a9 = 2;
       return -1;
     } else if(( ((-144 < a21) && (5 >= a21)) && ((( ((-148 < a14) && (13 >= a14)) && ((a8==6) && (input == 2))) && a27 <= -78 ) && (a9==3)))){
      if( 5 < a21 ){
      a14 = (((a14 - 105367) + -209940) + 113255);
       a8 = 5;
       a9 = 6;
      } else{
       a14 = (((a14 + -11316) + -579259) * 1);
       a21 = (((((a21 % 16)- 161) + 1) + 589728) + -589727);
      } return -1;
     } else if((((a9==6) && ((a8==8) && (( a27 <= -78 && (input == 3)) && a21 <= -178 ))) && a14 <= -148 )){
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( ((-178 < a21) && (-144 >= a21)) && ( 182 < a27 && (((input == 3) && ((a9==3) || (a9==4))) && (a8==6)))))){
      a27 = ((((a27 + 0) / 5) - -428286) + -699722);
      a21 = (((a21 + -111556) * 5) + -38832);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( 182 < a27 && ( 5 < a21 && ( a14 <= -148 && (((a9==4) && (input == 4)) && (a8==6)))))){
      a27 = (((a27 / 5) / 5) + -84536);
      a21 = (((((a21 * 9)/ 10) - 402813) * 1) - 143027);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((((((a9==4) || (a9==5)) || (a9==6)) && (input == 5)) && (a8==7)) && a14 <= -148 ) && a21 <= -178 ) && a27 <= -78 )){
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((((((a9==4) || (a9==5)) && (input == 3)) && a14 <= -148 ) && 5 < a21 ) && (a8==7)) && ((100 < a27) && (182 >= a27)) )){
      a27 = ((((((a27 * -8)/ 10) * 10)/ 9) / 5) + -352548);
      a21 = (((a21 / 5) + -502611) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a27 <= -78 && ((((a9==3) && (input == 3)) && (a8==7)) && ((-148 < a14) && (13 >= a14)) )) && 5 < a21 )){
      a14 = ((((a14 - 337192) - -726283) / 5) - 104789);
      a21 = ((((a21 + -159750) - -109475) % 74)- 69);
       a8 = 5;
       a9 = 5;
       return -1;
     } else if((((a8==6) && ((((input == 1) && ((100 < a27) && (182 >= a27)) ) && a21 <= -178 ) && a14 <= -148 )) && (a9==4))){
      a27 = (((a27 - 45186) * 5) / 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((((input == 4) && (((a9==6) && a21 <= -178 ) || ((a9==2) && ((-178 < a21) && (-144 >= a21)) ))) && (a8==5)) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 )){
      a27 = (((a27 + -177) + 22) + 13);
      a21 = ((((a21 + 284321) - 243960) % 299911)+ -300088);
       a8 = 4;
       a9 = 5;
       return -1;
     } else if(( a21 <= -178 && ((a9==3) && ( ((100 < a27) && (182 >= a27)) && ( a14 <= -148 && ((input == 6) && (a8==5))))))){
      a21 = (((((a21 % 16)+ -151) / 5) * 49)/ 10);
       a8 = 6;
       a9 = 2;
       return 25;
     } else if(((( a14 <= -148 && ((input == 5) && (( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ((a9==2) && ((-144 < a21) && (5 >= a21)) )))) && 182 < a27 ) && (a8==8))){
      a27 = ((((a27 / 5) * 4) % 40)- -126);
      a21 = ((((a21 % 74)- 69) + 27392) - 27392);
       a9 = 3;
       return -1;
     } else if(((input == 3) && (( a21 <= -178 && ((( a27 <= -78 && ((-148 < a14) && (13 >= a14)) ) && (a8==4)) && (a9==2))) || ((((( a14 <= -148 && 182 < a27 ) && (a8==8)) && (a9==5)) && 5 < a21 ) || (((a9==6) && (( 182 < a27 && a14 <= -148 ) && (a8==8))) && 5 < a21 ))))){
      a14 = (((((a14 + 0) % 80)+ -67) + 402171) + -402170);
      a27 = ((((a27 % 299961)+ -300038) / 5) + -175084);
      a21 = (((((a21 % 299911)+ -300088) - 2) / 5) - 306813);
       a8 = 4;
       a9 = 6;
       return -1;
     } else if((( ((-148 < a14) && (13 >= a14)) && (( a27 <= -78 && ((input == 6) && ((a9==3) || (a9==4)))) && (a8==4))) && ((-144 < a21) && (5 >= a21)) )){
      a14 = (((a14 - 533887) + -37968) * 1);
      a27 = (((((a27 * 9)/ 10) % 40)- -142) * 1);
       a8 = 7;
       a9 = 3;
       return -1;
     } else if(( a27 <= -78 && ((a9==3) && ( ((-148 < a14) && (13 >= a14)) && (( a21 <= -178 && (input == 3)) && (a8==7)))))){
      if( ((-144 < a21) && (5 >= a21)) ){
      a14 = (((a14 - 380852) / 5) - 514822);
      a27 = ((((((a27 - 0) % 40)+ 151) / 5) * 49)/ 10);
      a21 = (((a21 + 350605) - -249471) + 64);
       a9 = 6;
      } else{
       a14 = (((((a14 - 525186) * 1) + 537228) * -1)/ 10);
       a21 = (((((a21 % 74)- 7) * 5) % 74)- -5);
       a8 = 6;
      } return -1;
     } else if(((a9==2) && (((a8==7) && ( a14 <= -148 && ((input == 1) && a27 <= -78 ))) && ((-144 < a21) && (5 >= a21)) ))){
      a21 = (((a21 - 568697) + -6490) + -16180);
       a8 = 4;
       return -1;
     } else if((( 182 < a27 && ((((input == 1) && ((a9==4) || ((a9==2) || (a9==3)))) && ((-178 < a21) && (-144 >= a21)) ) && (a8==7))) && a14 <= -148 )){
      a27 = (((((a27 * -5)/ 10) + 451667) - 40084) - 511146);
      a21 = (((a21 + -589246) - 7333) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a27 <= -78 && ((((input == 4) && (((a9==2) || (a9==3)) || (a9==4))) && ((-148 < a14) && (13 >= a14)) ) && a21 <= -178 )) && (a8==5))){
      if( ((-178 < a21) && (-144 >= a21)) ){
      a14 = (((a14 - 249911) - 72116) + -68916);
      a27 = ((((a27 % 299908)- -300090) + -253247) + 397107);
      a21 = (((((a21 % 74)- -4) / 5) + -157273) + 157241);
       a8 = 6;
       a9 = 4;
      } else{
       a14 = (((a14 + -21109) - 486193) + -75514);
       a27 = ((((((a27 / 5) % 40)- -167) / 5) * 45)/ 10);
       a21 = (((((a21 % 74)+ 4) - 66) - -555280) + -555225);
       a8 = 6;
       a9 = 6;
      } return 21;
     } else if(((( a21 <= -178 && ( a27 <= -78 && ((input == 1) && ((a9==5) || (a9==6))))) && ((-148 < a14) && (13 >= a14)) ) && (a8==6))){
      a14 = (((a14 + -258405) + -225013) - 101004);
      a21 = ((((a21 % 16)+ -147) - 1) + -1);
       a9 = 6;
       return 23;
     } else if((( ((-78 < a27) && (100 >= a27)) && ((a9==2) && (( a21 <= -178 && (input == 2)) && (a8==7)))) && a14 <= -148 )){
      a27 = ((((a27 * 5) * 5) - -7566) + -383568);
       a8 = 4;
       return -1;
     } else if(((((((input == 4) && (a8==8)) && (a9==3)) && 5 < a21 ) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 )){
      a27 = ((((a27 * 10)/ -9) - 44488) * 5);
      a21 = (((((a21 - 0) / 5) - -29813) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( a27 <= -78 && ((a8==8) && ( ((-144 < a21) && (5 >= a21)) && (((a9==4) || (a9==5)) && (input == 3))))))){
      a27 = (((((a27 % 88)+ 82) + -28) + 181535) + -181569);
      a21 = ((((a21 % 16)+ -159) * 1) + -1);
       a8 = 5;
       a9 = 4;
       return 25;
     } else if(((((a8==6) && ( a21 <= -178 && ((input == 2) && ((-148 < a14) && (13 >= a14)) ))) && (a9==4)) && a27 <= -78 )){
      a14 = ((((a14 + 518936) * -1)/ 10) / 5);
      a27 = ((((a27 + 242355) + 329377) % 40)- -141);
      a21 = (((((a21 / 5) + 249860) - 556310) * -1)/ 10);
       return 21;
     } else if((((a8==4) && ( 5 < a21 && ((a9==2) && ((input == 5) && ((-148 < a14) && (13 >= a14)) )))) && a27 <= -78 )){
      a21 = (((((a21 / 5) + 87729) - 12770) * -1)/ 10);
       a8 = 7;
       a9 = 6;
       return 21;
     } else if((((((a8==8) && ((input == 3) && ((a9==4) || (a9==5)))) && ((-78 < a27) && (100 >= a27)) ) && a21 <= -178 ) && a14 <= -148 )){
      a21 = ((((a21 - -600122) / 5) - 35944) - -203894);
       a9 = 3;
       return 21;
     } else if(( a27 <= -78 && ((a8==4) && (( ((-178 < a21) && (-144 >= a21)) && ((input == 3) && ((a9==3) || (a9==4)))) && ((-148 < a14) && (13 >= a14)) )))){
      if( a21 <= -178 ){
      a14 = (((a14 + -281835) * 2) / 5);
      a21 = ((((a21 * -1)/ 10) / 5) - -11896);
       a8 = 6;
       a9 = 3;
      } else{
       a8 = 5;
       a9 = 2;
      } return -1;
     } else if((((a8==8) && ( 182 < a27 && ((( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ((a9==2) && ((-144 < a21) && (5 >= a21)) )) && (input == 6)))) && a14 <= -148 )){
      a27 = (((a27 + -600082) + -26) + -50);
      a21 = (((a21 * 5) + 473014) - -122312);
       a8 = 5;
       a9 = 6;
       return -1;
     } else if(((a8==8) && ( ((100 < a27) && (182 >= a27)) && ( a14 <= -148 && ((input == 4) && (( 5 < a21 && (a9==2)) || (( ((-144 < a21) && (5 >= a21)) && (a9==5)) || ((a9==6) && ((-144 < a21) && (5 >= a21)) )))))))){
      a27 = (((a27 - 255018) * 2) / 5);
      a21 = (((((a21 / 5) / 5) + 362003) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( 182 < a27 && ( a14 <= -148 && ((a8==6) && ((input == 3) && (( ((-178 < a21) && (-144 >= a21)) && (a9==2)) || (( a21 <= -178 && (a9==5)) || ( a21 <= -178 && (a9==6))))))))){
      a27 = (((((a27 * 9)/ 10) * 1) * -5)/ 10);
      a21 = ((((a21 * 9)/ 10) + -39222) + -10635);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( a14 <= -148 && ( ((-178 < a21) && (-144 >= a21)) && (((a9==5) || ((a9==3) || (a9==4))) && (input == 1)))) && (a8==8)) && a27 <= -78 )){
      a21 = (((a21 - 389871) + -148376) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a27 <= -78 && (((a8==5) && ((input == 1) && ((( ((-144 < a21) && (5 >= a21)) && (a9==6)) || ( 5 < a21 && (a9==2))) || ( 5 < a21 && (a9==3))))) && ((-148 < a14) && (13 >= a14)) ))){
      a14 = (((a14 - 400430) + -175999) * 1);
      a21 = ((((a21 / 5) / 5) % 16)+ -161);
       a8 = 6;
       a9 = 5;
       return -1;
     } else if((((a8==7) && ( 5 < a21 && ((a9==6) && ( ((-78 < a27) && (100 >= a27)) && (input == 1))))) && a14 <= -148 )){
      a27 = ((((a27 - 65339) + 339121) * -1)/ 10);
      a21 = (((a21 / 5) + -427978) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( a27 <= -78 && ((a9==3) && ((input == 5) && ((-144 < a21) && (5 >= a21)) ))) && ((-148 < a14) && (13 >= a14)) ) && (a8==5))){
      if( a14 <= -148 ){
      a14 = (((((a14 * 5) + -130292) + 616937) * -1)/ 10);
       a8 = 4;
      } else{
       a14 = (((((a14 + 99434) * 5) / 5) * -1)/ 10);
       a8 = 6;
       a9 = 6;
      } return -1;
     } else if(((( ((100 < a27) && (182 >= a27)) && ( a21 <= -178 && (((a9==2) || (a9==3)) && (input == 5)))) && a14 <= -148 ) && (a8==6))){
      a21 = (((((a21 % 16)- 157) * 5) % 16)+ -145);
       a8 = 5;
       a9 = 5;
       return 21;
     } else if(((a8==8) && ( a14 <= -148 && ( ((-144 < a21) && (5 >= a21)) && ((a9==3) && ((input == 3) && 182 < a27 )))))){
      a27 = (((((a27 / 5) / 5) + 273061) * -1)/ 10);
      a21 = ((((a21 - -519974) * -1)/ 10) * 5);
       a8 = 5;
       a9 = 6;
       return 21;
     } else if((( ((-78 < a27) && (100 >= a27)) && ( a14 <= -148 && ((a8==8) && ((input == 6) && ((a9==3) || (a9==4)))))) && 5 < a21 )){
      if( 182 < a27 ){
      a27 = ((((a27 % 40)+ 140) - -3) - 1);
      a21 = (((((a21 % 74)- 77) + -283901) - 310659) + 594496);
       a8 = 7;
       a9 = 5;
      } else{
       a21 = (((((a21 * 9)/ 10) % 74)- 118) + -15);
       a8 = 5;
       a9 = 5;
      } return 23;
     } else if(((((a8==7) && ((input == 1) && ((( ((-144 < a21) && (5 >= a21)) && (a9==6)) || ( 5 < a21 && (a9==2))) || ((a9==3) && 5 < a21 )))) && a27 <= -78 ) && a14 <= -148 )){
      a21 = ((((a21 % 299911)+ -300088) * 1) - 2);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && ((((((a9==4) || (a9==5)) && (input == 2)) && a27 <= -78 ) && (a8==5)) && ((-144 < a21) && (5 >= a21)) ))){
      if((a8==8)){
      a14 = (((a14 * 5) + -129320) + -230640);
      a27 = (((((a27 + 64087) + -13199) * 1) % 299908)+ 300090);
      a21 = (((a21 + -98519) * 5) + -103207);
       a8 = 4;
       a9 = 5;
      } else{
       a14 = (((a14 + -308696) * 1) / 5);
       a27 = (((((a27 + 180120) + 254228) + -207627) % 88)- -11);
       a8 = 4;
       a9 = 5;
      } return -1;
     } else if((( ((-178 < a21) && (-144 >= a21)) && ( a14 <= -148 && (((input == 3) && (a8==6)) && ((-78 < a27) && (100 >= a27)) ))) && (a9==5))){
      a27 = (((((a27 + -147848) % 40)+ 165) - -87675) + -87681);
      a21 = (((a21 - -139716) + -209888) * 5);
       a8 = 5;
       a9 = 3;
       return 23;
     } else if(( a14 <= -148 && ((((a8==8) && (((a9==5) || (a9==6)) && (input == 6))) && ((-144 < a21) && (5 >= a21)) ) && 182 < a27 ))){
      a27 = (((a27 + -600129) / 5) - 35267);
      a21 = (((a21 + 591135) - -5089) + 372);
       a8 = 5;
       a9 = 5;
       return -1;
     } else if(((((((a9==5) && (input == 2)) && 5 < a21 ) && (a8==6)) && ((-78 < a27) && (100 >= a27)) ) && a14 <= -148 )){
      a27 = (((((a27 - 288773) % 40)+ 140) * 10)/ 9);
      a21 = ((((a21 % 299911)- 300088) - -240162) - 443268);
       a9 = 2;
       return 21;
     } else if(((a9==2) && ( a14 <= -148 && ( 182 < a27 && (((input == 2) && 5 < a21 ) && (a8==6)))))){
      a27 = (((a27 - 600094) - -204125) + -204200);
      a21 = (((((a21 % 299911)+ -300088) - 100979) * 10)/ 9);
       a8 = 4;
       return -1;
     } else if((( ((-148 < a14) && (13 >= a14)) && ((((input == 2) && ((a9==4) || (a9==5))) && a27 <= -78 ) && (a8==6))) && ((-144 < a21) && (5 >= a21)) )){
      a14 = (((a14 - 184111) + -733) / 5);
      a21 = (((((a21 % 16)- 159) - 2) / 5) - 133);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( 182 < a27 && (((input == 1) && (( 5 < a21 && ((a9==6) && (a8==5))) || ( a21 <= -178 && ((a8==6) && (a9==2))))) && a14 <= -148 ))){
      a27 = (((a27 - 600172) + -7) + -3);
      a21 = (((((a21 % 299911)- 300088) * 1) - -485931) + -485932);
       a8 = 7;
       a9 = 5;
       return 23;
     } else if((((((input == 4) && (((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ((a9==2) && ((-144 < a21) && (5 >= a21)) ))) && (a8==4)) && a14 <= -148 ) && ((-78 < a27) && (100 >= a27)) )){
      a27 = ((((a27 + -230700) * 10)/ 9) - 242020);
      a21 = ((((a21 / 5) + -234093) + 578536) - 762812);
       a9 = 2;
       return -1;
     } else if(( a27 <= -78 && ((a8==5) && ((( 5 < a21 && (input == 6)) && ((-148 < a14) && (13 >= a14)) ) && (a9==4))))){
      if( a21 <= -178 ){
      a14 = (((a14 - 457873) / 5) * 5);
      a27 = ((((a27 % 88)+ 50) + 78168) + -78127);
      a21 = ((((((a21 * 9)/ 10) % 74)- 131) * 9)/ 10);
       a9 = 3;
      } else{
       a14 = (((((a14 - -233329) * 2) * 1) * -1)/ 10);
       a27 = ((((a27 - 0) / 5) % 88)+ 44);
       a21 = ((((a21 % 16)- 170) + -1) * 1);
       a8 = 6;
       a9 = 2;
      } return -1;
     } else if(((a8==7) && ( ((-144 < a21) && (5 >= a21)) && ((( a27 <= -78 && (input == 4)) && a14 <= -148 ) && (a9==2))))){
      a21 = ((((a21 - 453865) * 1) * 10)/ 9);
       a8 = 4;
       return -1;
     } else if(((( a21 <= -178 && (( a14 <= -148 && (input == 1)) && (a8==8))) && (a9==3)) && ((-78 < a27) && (100 >= a27)) )){
      a27 = ((((a27 + 4235) / 5) * 10)/ -9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((-144 < a21) && (5 >= a21)) && ((((input == 1) && ((a9==4) || (a9==5))) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 )) && (a8==6))){
      a27 = (((a27 - -385507) * 1) / 5);
       a8 = 7;
       a9 = 5;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && (( a27 <= -78 && ((((a9==5) || ((a9==3) || (a9==4))) && (input == 3)) && (a8==7))) && ((-178 < a21) && (-144 >= a21)) ))){
      if( ((13 < a14) && (182 >= a14)) ){
      a14 = ((((a14 - -445156) * 10)/ -9) - 91181);
       a8 = 6;
       a9 = 3;
      } else{
       a14 = (((a14 - 183831) + -367173) * 1);
       a21 = ((((a21 - -515787) - 902051) * 10)/ -9);
       a8 = 8;
       a9 = 5;
      } return -1;
     } else if(((a8==5) && (( ((-78 < a27) && (100 >= a27)) && ((( ((-144 < a21) && (5 >= a21)) && (a9==6)) || ( 5 < a21 && (a9==2))) && (input == 6))) && a14 <= -148 ))){
      a27 = (((a27 - 507686) + -36643) * 1);
      a21 = (((((a21 % 299911)- 300088) + 90416) * 1) - 90417);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a27 <= -78 && ( ((-148 < a14) && (13 >= a14)) && ((a8==5) && ((( ((-144 < a21) && (5 >= a21)) && (a9==2)) || (((a9==5) && ((-178 < a21) && (-144 >= a21)) ) || ((a9==6) && ((-178 < a21) && (-144 >= a21)) ))) && (input == 1)))))){
      a14 = (((a14 + 324195) - -179076) - 948606);
      a21 = ((((a21 + 494664) / 5) + -234710) + 135769);
       a8 = 4;
       a9 = 5;
       return 23;
     } else if(( a14 <= -148 && (((a8==4) && (((input == 2) && ((a9==2) || (a9==3))) && 182 < a27 )) && 5 < a21 ))){
      a27 = ((((a27 % 88)+ 13) + 506886) + -506926);
      a21 = ((((a21 + -427194) / 5) % 74)- 68);
       a8 = 8;
       a9 = 4;
       return 21;
     } else if(( a21 <= -178 && ((a8==8) && ((((input == 4) && (a9==3)) && a14 <= -148 ) && ((-78 < a27) && (100 >= a27)) )))){
      a27 = (((a27 - 65164) / 5) * 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((a8==7) && (( a21 <= -178 && ((input == 1) && ((-78 < a27) && (100 >= a27)) )) && (a9==2))))){
      a27 = (((a27 / 5) + -224989) - 61090);
       a8 = 4;
       return -1;
     } else if(((a8==8) && (( a14 <= -148 && (((((a9==4) || (a9==5)) || (a9==6)) && (input == 1)) && ((-78 < a27) && (100 >= a27)) )) && ((-144 < a21) && (5 >= a21)) ))){
      a27 = ((((a27 * 5) + 22013) * 10)/ 9);
      a21 = ((((a21 * 5) % 16)+ -159) + -2);
       a8 = 4;
       a9 = 2;
       return 25;
     } else if(( ((-178 < a21) && (-144 >= a21)) && ((((((a9==3) || (a9==4)) && (input == 4)) && (a8==5)) && ((-148 < a14) && (13 >= a14)) ) && a27 <= -78 ))){
      if( a27 <= -78 ){
      a14 = ((((a14 * 5) - 396215) - -805609) + -647993);
      a21 = ((((a21 / 5) * 10)/ 1) - 396251);
       a8 = 4;
       a9 = 2;
      } else{
       a14 = (((a14 - 406980) + -92053) + -30994);
       a21 = (((a21 * 5) - 561558) + -9107);
       a9 = 5;
      } return -1;
     } else if(((((a8==6) && ( 5 < a21 && ((input == 6) && 182 < a27 ))) && a14 <= -148 ) && (a9==3))){
      a27 = ((((a27 / 5) - 308956) * 10)/ 9);
      a21 = (((((a21 % 299911)- 300088) + 195889) - -109594) - 557224);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((((input == 5) && a14 <= -148 ) && (a8==7)) && a21 <= -178 ) && ((-78 < a27) && (100 >= a27)) ) && (a9==2))){
      a27 = (((a27 + -134000) + -185996) * 1);
       a8 = 4;
       return -1;
     } else if((((((input == 6) && (( a21 <= -178 && (a9==6)) || ( ((-178 < a21) && (-144 >= a21)) && (a9==2)))) && ((-78 < a27) && (100 >= a27)) ) && (a8==8)) && a14 <= -148 )){
      a27 = ((((a27 + -407744) * 10)/ 9) + -15985);
      a21 = ((((a21 - 0) % 299911)- 178) - 101735);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && (( a27 <= -78 && (((input == 4) && ((a9==4) || ((a9==2) || (a9==3)))) && ((-178 < a21) && (-144 >= a21)) )) && (a8==6)))){
      if( a27 <= -78 ){
      a14 = (((a14 + -360000) - -863225) + -751200);
      a21 = (((a21 - 400361) + -63960) + -5034);
       a8 = 4;
       a9 = 3;
      } else{
       a14 = (((a14 + 46026) - 543440) * 1);
       a21 = ((((a21 + 152524) * -1)/ 10) - 319908);
       a8 = 5;
       a9 = 4;
      } return -1;
     } else if(( ((-144 < a21) && (5 >= a21)) && (( a27 <= -78 && ( a14 <= -148 && ((input == 1) && ((a9==5) || ((a9==3) || (a9==4)))))) && (a8==7)))){
      a21 = (((((a21 + -232889) / 5) - -309668) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( ((-178 < a21) && (-144 >= a21)) && (((input == 1) && ((a9==4) || (a9==5))) && (a8==8))) && a14 <= -148 ) && 182 < a27 )){
      if( 5 < a21 ){
      a27 = ((((a27 * 9)/ 10) - 540451) + -45204);
      a21 = (((((a21 * 5) * 5) / 5) % 74)- -3);
       a8 = 6;
       a9 = 4;
      } else{
       a27 = (((a27 / 5) + -586343) - 11532);
       a8 = 6;
       a9 = 5;
      } return -1;
     } else if(((a8==7) && (((((((a9==3) || (a9==4)) || (a9==5)) && (input == 1)) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 ) && a21 <= -178 ))){
      a27 = ((((((a27 * -1)/ 10) * 10)/ 9) - -378971) + -378952);
      a21 = (((a21 + 600148) * 1) * 1);
       a8 = 8;
       a9 = 5;
       return -1;
     } else if(((( 182 < a27 && (((input == 2) && (((a9==2) || (a9==3)) || (a9==4))) && a21 <= -178 )) && (a8==4)) && a14 <= -148 )){
      a27 = (((a27 - 0) + -600161) + -10);
       a9 = 2;
       return -1;
     } else if((( a14 <= -148 && ((a8==6) && ((( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ((a9==2) && ((-144 < a21) && (5 >= a21)) )) && (input == 2)))) && ((-78 < a27) && (100 >= a27)) )){
      if( a14 <= -148 ){
      a27 = ((((((a27 % 40)- -142) / 5) / 5) * 255)/ 10);
      a21 = (((a21 + -277468) * 2) - -294760);
       a8 = 8;
       a9 = 4;
      } else{
       a27 = (((((a27 % 40)+ 141) + -171777) + 658948) + -487171);
       a21 = (((((a21 * 5) % 16)+ -161) / 5) - 123);
       a8 = 5;
       a9 = 4;
      } return 21;
     } else if(( 182 < a27 && (((input == 3) && (((((a9==5) && (a8==6)) && 5 < a21 ) || ( 5 < a21 && ((a8==6) && (a9==6)))) || ( a21 <= -178 && ((a8==7) && (a9==2))))) && a14 <= -148 ))){
      a27 = (((a27 - 600120) * 1) + -1);
      a21 = (((((a21 * 9)/ 10) % 299911)+ -300088) + -2);
       a8 = 8;
       a9 = 4;
       return 21;
     } else if((((((a8==6) && ((input == 1) && ((a9==3) || (a9==4)))) && ((-78 < a27) && (100 >= a27)) ) && a14 <= -148 ) && a21 <= -178 )){
      a27 = ((((((a27 % 40)- -141) * 1) * 5) % 40)+ 127);
      a21 = ((((((a21 % 16)+ -157) - -7) * 5) % 16)- 146);
       a8 = 4;
       a9 = 6;
       return 23;
     } else if((((((( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ((a9==2) && ((-144 < a21) && (5 >= a21)) )) && (input == 1)) && (a8==4)) && ((-78 < a27) && (100 >= a27)) ) && a14 <= -148 )){
      a27 = (((a27 - 35388) + -187696) + -232042);
      a21 = (((a21 + -437548) * 1) - 124853);
       a9 = 2;
       return -1;
     } else if((((( a14 <= -148 && ( ((-144 < a21) && (5 >= a21)) && (input == 4))) && 182 < a27 ) && (a9==3)) && (a8==8))){
      if( 5 < a21 ){
      a27 = (((a27 / 5) / 5) - 550314);
      a21 = ((((a21 % 16)- 161) - 104990) - -104990);
       a8 = 6;
       a9 = 6;
      } else{
       a14 = ((((a14 % 80)- -7) - 49) / 5);
       a27 = (((((a27 - 0) + -600144) / 5) * 28)/ 10);
       a21 = ((((((a21 % 16)+ -161) + 254976) * 2) % 16)+ -164);
       a8 = 4;
       a9 = 4;
      } return -1;
     } else if(((( a21 <= -178 && ( ((-78 < a27) && (100 >= a27)) && (((a9==3) || (a9==4)) && (input == 5)))) && (a8==6)) && a14 <= -148 )){
      a27 = ((((a27 - -363485) + 24150) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( 182 < a27 && ( ((-144 < a21) && (5 >= a21)) && ((((((a9==2) || (a9==3)) || (a9==4)) && (input == 5)) && a14 <= -148 ) && (a8==7))))){
      a27 = (((((a27 * 9)/ 10) * -5)/ 10) + -290824);
      a21 = (((a21 + -223036) / 5) - 449809);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-178 < a21) && (-144 >= a21)) && ((a8==4) && (((((a9==3) || (a9==4)) && (input == 5)) && 182 < a27 ) && a14 <= -148 )))){
      a27 = ((((a27 + -597756) - -34623) * 1) + -37037);
      a21 = (((((a21 * 13)/ 10) * 10)/ 9) + -242855);
       a9 = 2;
       return -1;
     } else if((((((((a9==2) && ((-178 < a21) && (-144 >= a21)) ) || (( a21 <= -178 && (a9==5)) || ( a21 <= -178 && (a9==6)))) && (input == 3)) && a14 <= -148 ) && ((-78 < a27) && (100 >= a27)) ) && (a8==6))){
      a27 = (((a27 / 5) / 5) + -35498);
      a21 = ((((a21 / 5) / 5) * 5) - 322514);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( a21 <= -178 && ( 182 < a27 && ((((a9==6) || ((a9==4) || (a9==5))) && (input == 6)) && (a8==8)))))){
      if( a27 <= -78 ){
      a27 = ((((a27 / 5) * 4) * 1) - 567015);
      a21 = (((((a21 - 0) / 5) / 5) % 74)+ -25);
       a9 = 5;
      } else{
       a27 = ((((a27 - 272053) * 1) / 5) - 257807);
       a9 = 3;
      } return -1;
     } else if((((( 5 < a21 && ( ((-148 < a14) && (13 >= a14)) && (input == 3))) && (a9==4)) && a27 <= -78 ) && (a8==5))){
      a14 = (((a14 - -175920) / 5) + -234570);
      a27 = ((((a27 % 88)+ 43) - 1) + -14);
      a21 = ((((a21 * 9)/ 10) + -562048) / 5);
       a8 = 7;
       a9 = 2;
       return -1;
     } else if(( 5 < a21 && ( ((-78 < a27) && (100 >= a27)) && ( a14 <= -148 && ((((a9==3) || (a9==4)) && (input == 4)) && (a8==8)))))){
      a27 = ((((a27 % 40)+ 142) - -1) + -1);
      a21 = (((((a21 - 534953) * 1) - 48557) % 74)+ -68);
       a8 = 7;
       a9 = 5;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && ( a27 <= -78 && (((input == 2) && ((((a9==5) && a21 <= -178 ) || ( a21 <= -178 && (a9==6))) || ( ((-178 < a21) && (-144 >= a21)) && (a9==2)))) && (a8==7))))){
      a14 = (((a14 - 409326) * 1) * 1);
      a21 = (((((a21 % 299911)+ -178) / 5) * 5) - 29952);
       a8 = 5;
       a9 = 4;
       return -1;
     } else if((( a14 <= -148 && (((a9==3) && ( ((100 < a27) && (182 >= a27)) && (input == 6))) && ((-178 < a21) && (-144 >= a21)) )) && (a8==7))){
      a27 = ((((a27 * 10)/ -9) * 5) * 5);
      a21 = (((((a21 * 10)/ -9) * 5) - 144944) - -443105);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a9==3) && ((a8==5) && (( ((-144 < a21) && (5 >= a21)) && ( a27 <= -78 && (input == 6))) && ((-148 < a14) && (13 >= a14)) )))){
      a21 = (((a21 - 2997) - 283670) * 2);
       a9 = 6;
       return -1;
     } else if((((a8==8) && (( 182 < a27 && ((input == 4) && (((a9==2) || (a9==3)) || (a9==4)))) && a14 <= -148 )) && 5 < a21 )){
      a27 = (((((a27 * -5)/ 10) * 1) - -252326) + -276177);
      a21 = (((((a21 % 16)+ -167) / 5) * 10)/ 2);
       a8 = 5;
       a9 = 5;
       return -1;
     } else if(((((input == 4) && ((( 5 < a21 && ((a8==4) && (a9==5))) || (((a9==6) && (a8==4)) && 5 < a21 )) || (((a9==2) && (a8==5)) && a21 <= -178 ))) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 )){
      a27 = (((a27 + -255619) - 257310) * 1);
      a21 = ((((((a21 % 299911)+ -300088) + -2) * 9)/ 10) + -11337);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a9==3) && (((a8==5) && ((input == 5) && 182 < a27 )) && a21 <= -178 )) && a14 <= -148 )){
      a27 = ((((a27 * 9)/ 10) - 578775) / 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && (( a21 <= -178 && ( a27 <= -78 && ((input == 1) && (((a9==4) || (a9==5)) || (a9==6))))) && (a8==7)))){
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a14 <= -148 && (((((a9==6) && ((-144 < a21) && (5 >= a21)) ) || ((a9==2) && 5 < a21 )) && (input == 1)) && (a8==8))) && a27 <= -78 )){
      a21 = ((((a21 % 299911)+ -300088) - 1) + -1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==7) && ((((input == 4) && ((-178 < a21) && (-144 >= a21)) ) && (a9==3)) && a14 <= -148 )) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((a27 - 186842) + -17998) / 5);
      a21 = (((a21 - 581608) / 5) - -60205);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( a14 <= -148 && (((input == 6) && (((a9==2) || (a9==3)) || (a9==4))) && (a8==4))) && ((-78 < a27) && (100 >= a27)) ) && a21 <= -178 )){
      a27 = (((a27 - 543497) - 41065) + -1811);
       a9 = 2;
       return -1;
     } else if(((((a9==3) && ( a21 <= -178 && ((a8==5) && (input == 3)))) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 )){
      a27 = ((((a27 * 10)/ -9) * 5) - 39741);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((((input == 1) && (a8==5)) && a14 <= -148 ) && (a9==4)) && a21 <= -178 ) && 182 < a27 )){
      if((a9==6)){
      a21 = (((((a21 % 16)- 151) - -7) + 348608) + -348618);
       a8 = 7;
       a9 = 6;
      } else{
       a27 = (((((a27 / 5) % 40)+ 140) + -203751) + 203714);
       a21 = ((((((a21 * 9)/ 10) - -453867) + -226598) % 74)- 68);
       a8 = 4;
      } return 21;
     } else if(((((((input == 4) && (((a9==3) || (a9==4)) || (a9==5))) && a14 <= -148 ) && ((-178 < a21) && (-144 >= a21)) ) && (a8==8)) && a27 <= -78 )){
      a21 = (((a21 + 183244) + -385997) + -7694);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==5) && ((( 5 < a21 && (((a9==3) || (a9==4)) && (input == 6))) && a14 <= -148 ) && ((-78 < a27) && (100 >= a27)) ))){
      a27 = (((a27 - 577601) + -17723) - 786);
      a21 = ((((a21 % 299911)- 300088) + -256049) + -31726);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a14 <= -148 && ((a9==4) && (( a27 <= -78 && (input == 6)) && (a8==8)))) && a21 <= -178 )){
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && ((a9==4) && ((((input == 2) && a21 <= -178 ) && a14 <= -148 ) && (a8==6))))){
      a27 = (((a27 + -255002) - 113096) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((( a27 <= -78 && ((input == 6) && (((a9==3) || (a9==4)) || (a9==5)))) && ((-148 < a14) && (13 >= a14)) ) && ((-178 < a21) && (-144 >= a21)) ) && (a8==7))){
      a14 = (((a14 * 5) + -562926) + -23352);
      a21 = ((((a21 / 5) * 5) * 5) - -25495);
       a8 = 6;
       a9 = 3;
       return -1;
     } else if(( a14 <= -148 && ((a9==3) && ( 182 < a27 && (((input == 1) && ((-144 < a21) && (5 >= a21)) ) && (a8==4)))))){
      a27 = ((((a27 - 600146) / 5) / 5) - 11449);
      a21 = (((a21 + -543759) - 9367) * 1);
       a9 = 2;
       return -1;
     } else if((( ((-78 < a27) && (100 >= a27)) && (( a14 <= -148 && ((a9==3) && (input == 1))) && ((-144 < a21) && (5 >= a21)) )) && (a8==8))){
      a27 = (((a27 + -164427) / 5) + -26695);
      a21 = ((((a21 - 385204) * 10)/ 9) + -120366);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( ((100 < a27) && (182 >= a27)) && ((( a21 <= -178 && (a9==6)) || ((a9==2) && ((-178 < a21) && (-144 >= a21)) )) && (input == 4))) && (a8==7)) && a14 <= -148 )){
      a27 = ((((a27 * 10)/ -9) * 5) * 5);
      a21 = (((((a21 % 74)- 62) + -462204) + -127644) + 589850);
       a8 = 5;
       a9 = 2;
       return -1;
     } else if((((( 5 < a21 && ((input == 5) && ((a9==2) || (a9==3)))) && ((100 < a27) && (182 >= a27)) ) && (a8==5)) && a14 <= -148 )){
      a27 = ((((((a27 * 10)/ -9) * 5) - -263821) * -1)/ 10);
      a21 = (((((a21 - 15331) % 299911)- 300088) / 5) - 143802);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((((((a9==3) || (a9==4)) && (input == 5)) && (a8==5)) && ((100 < a27) && (182 >= a27)) ) && ((-178 < a21) && (-144 >= a21)) ))){
      a27 = (((((a27 - 183622) / 5) - -496367) * -1)/ 10);
      a21 = (((((a21 - 402896) * 1) + 907656) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a27 <= -78 && ( ((-148 < a14) && (13 >= a14)) && (((((a9==5) && ((-178 < a21) && (-144 >= a21)) ) || ( ((-178 < a21) && (-144 >= a21)) && (a9==6))) || ( ((-144 < a21) && (5 >= a21)) && (a9==2))) && (input == 1)))) && (a8==6))){
      if( 182 < a14 ){
      a14 = (((a14 * 5) * 5) + -218290);
      a27 = ((((a27 % 88)- -47) - 91425) + 91409);
      a21 = (((a21 - -192413) * 3) + 7727);
       a8 = 8;
       a9 = 4;
      } else{
       a14 = (((a14 - 286308) * 2) / 5);
       a21 = (((a21 + -423779) - 137033) - 11517);
       a8 = 5;
       a9 = 3;
      } return -1;
     } else if(((((a8==8) && (((input == 2) && a21 <= -178 ) && (a9==5))) && a27 <= -78 ) && a14 <= -148 )){
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && (( a14 <= -148 && ( a21 <= -178 && ((input == 6) && (a9==3)))) && (a8==4)))){
      a27 = (((a27 + 474072) - 904208) * 1);
       a9 = 2;
       return -1;
     } else if(( ((-144 < a21) && (5 >= a21)) && ( a14 <= -148 && (((a8==7) && (((a9==5) || (a9==6)) && (input == 3))) && ((100 < a27) && (182 >= a27)) )))){
      a27 = (((((a27 * -1)/ 10) + 59) + -595436) - -595407);
      a21 = (((a21 + 437991) - -50460) + 72116);
       a8 = 8;
       a9 = 2;
       return 21;
     } else if(((a8==6) && (( ((-78 < a27) && (100 >= a27)) && ((((a9==2) && 5 < a21 ) || (( ((-144 < a21) && (5 >= a21)) && (a9==5)) || ( ((-144 < a21) && (5 >= a21)) && (a9==6)))) && (input == 3))) && a14 <= -148 ))){
      a27 = ((((a27 * 5) * 5) * 5) - 327573);
      a21 = (((((a21 % 299911)- 300088) - 1) + 404250) + -404249);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( ((-144 < a21) && (5 >= a21)) && ( ((100 < a27) && (182 >= a27)) && (((input == 3) && ((a9==4) || (a9==5))) && (a8==6)))))){
      a27 = (((((a27 / 5) - 397256) + 873711) * -1)/ 10);
      a21 = (((a21 - 65953) - 207917) * 2);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( a27 <= -78 && (((input == 5) && ((a9==5) || (a9==6))) && 5 < a21 )) && (a8==6)) && ((-148 < a14) && (13 >= a14)) )){
      a14 = (((a14 - 495765) / 5) / 5);
      a27 = (((a27 / 5) - -272035) - -301830);
      a21 = (((((a21 * 9)/ 10) / 5) % 16)- 162);
       a8 = 7;
       a9 = 3;
       return -1;
     } else if(( a14 <= -148 && ((((input == 3) && ((( ((-144 < a21) && (5 >= a21)) && (a9==6)) || ( 5 < a21 && (a9==2))) || ( 5 < a21 && (a9==3)))) && (a8==7)) && a27 <= -78 ))){
      a27 = ((((a27 % 299908)- -300090) / 5) - -132145);
      a21 = (((((a21 - 419085) % 16)+ -159) / 5) + -132);
       a8 = 5;
       a9 = 6;
       return 23;
     } else if((( ((-148 < a14) && (13 >= a14)) && ((((input == 4) && ((a9==3) || (a9==4))) && a27 <= -78 ) && ((-178 < a21) && (-144 >= a21)) )) && (a8==4))){
      if( 182 < a14 ){
      a14 = ((((a14 - -591691) * 1) - -4794) + -798965);
       a8 = 6;
       a9 = 6;
      } else{
       a14 = ((((a14 + -476336) * 10)/ 9) - 25154);
       a8 = 6;
       a9 = 5;
      } return -1;
     } else if(( ((-144 < a21) && (5 >= a21)) && ( ((-78 < a27) && (100 >= a27)) && ((((input == 6) && ((a9==3) || (a9==4))) && (a8==6)) && a14 <= -148 )))){
      a27 = (((a27 - 568531) * 1) - 5403);
      a21 = ((((a21 - -506277) + 77008) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && ((a8==6) && (((( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ( ((-144 < a21) && (5 >= a21)) && (a9==2))) && (input == 5)) && a14 <= -148 )))){
      a27 = (((a27 - 584361) * 1) + 558238);
      a21 = (((a21 - 455906) + -116519) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( a14 <= -148 && ((input == 2) && ((((a9==6) && ((-144 < a21) && (5 >= a21)) ) || ( 5 < a21 && (a9==2))) || ((a9==3) && 5 < a21 )))) && a27 <= -78 ) && (a8==7))){
      a21 = ((((a21 % 16)- 159) * 1) + -3);
       a8 = 8;
       a9 = 2;
       return 21;
     } else if((( 5 < a21 && ((a9==3) && (( a14 <= -148 && (input == 4)) && ((-78 < a27) && (100 >= a27)) ))) && (a8==7))){
      a27 = (((a27 - -502656) + 39104) * 1);
      a21 = ((((((a21 * 9)/ 10) * 1) / 5) % 74)- 102);
       a8 = 4;
       return 23;
     } else if(((( a14 <= -148 && ( ((100 < a27) && (182 >= a27)) && ((a9==3) && (input == 5)))) && a21 <= -178 ) && (a8==4))){
      a27 = (((a27 - -315966) + -524622) - 278393);
       a9 = 2;
       return -1;
     } else if(( a21 <= -178 && ( a14 <= -148 && (( ((100 < a27) && (182 >= a27)) && ((a8==4) && (input == 5))) && (a9==5))))){
      if( a21 <= -178 ){
      a21 = (((((a21 % 74)+ 4) + -18) - -419086) - 419112);
       a8 = 7;
       a9 = 4;
      } else{
       a21 = (((a21 + 0) - -600066) - -105);
       a9 = 3;
      } return 21;
     } else if(((((a8==8) && ((a9==4) && ((input == 6) && ((100 < a27) && (182 >= a27)) ))) && a14 <= -148 ) && 5 < a21 )){
      a27 = ((((a27 + -201142) * 10)/ 9) * 2);
      a21 = ((((a21 - 590915) % 299911)- 300088) + -2);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a9==4) && ( a14 <= -148 && ( ((100 < a27) && (182 >= a27)) && (((input == 5) && (a8==8)) && ((-144 < a21) && (5 >= a21)) ))))){
      a27 = ((((a27 * 10)/ -9) * 5) * 5);
      a21 = (((a21 - -454077) / 5) - 382723);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==4) && (( a14 <= -148 && ( a21 <= -178 && (((a9==4) || ((a9==2) || (a9==3))) && (input == 4)))) && ((-78 < a27) && (100 >= a27)) ))){
      a27 = (((((a27 % 40)+ 141) * 1) - -121699) - 121698);
      a21 = (((a21 - -545285) / 5) + 101463);
       a8 = 8;
       a9 = 4;
       return 21;
     } else if((((a8==7) && ( a14 <= -148 && ((a9==4) && ( ((100 < a27) && (182 >= a27)) && (input == 3))))) && ((-144 < a21) && (5 >= a21)) )){
      a27 = ((((a27 * 10)/ 5) - -586728) + 12172);
      a21 = (((a21 * 5) + -156668) - 206299);
       a9 = 6;
       return 21;
     } else if(( ((-178 < a21) && (-144 >= a21)) && ((a8==6) && (( a14 <= -148 && ((input == 3) && ((a9==5) || ((a9==3) || (a9==4))))) && ((100 < a27) && (182 >= a27)) )))){
      a27 = ((((a27 - 493773) + 954901) * 10)/ -9);
      a21 = ((((a21 * 5) / 5) + 590588) + -944153);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a9==2) && (( a14 <= -148 && ( ((100 < a27) && (182 >= a27)) && (input == 1))) && a21 <= -178 )) && (a8==4))){
      a27 = (((a27 / 5) - 374678) + -13323);
       return -1;
     } else if(((((( 5 < a21 && (input == 1)) && ((-148 < a14) && (13 >= a14)) ) && (a8==4)) && a27 <= -78 ) && (a9==2))){
      a21 = (((((a21 % 74)+ -90) - -11) - -200261) - 200290);
       a8 = 7;
       a9 = 3;
       return -1;
     } else if((( ((-144 < a21) && (5 >= a21)) && (( ((-148 < a14) && (13 >= a14)) && ((input == 2) && (((a9==2) || (a9==3)) || (a9==4)))) && a27 <= -78 )) && (a8==7))){
      a14 = (((a14 * 5) + -52128) - 267191);
      a27 = ((((((a27 * 9)/ 10) - -221699) / 5) % 40)- -141);
       a8 = 8;
       a9 = 3;
       return 25;
     } else if(( a14 <= -148 && (( ((100 < a27) && (182 >= a27)) && ((( a21 <= -178 && (a9==6)) || ((a9==2) && ((-178 < a21) && (-144 >= a21)) )) && (input == 5))) && (a8==5)))){
      a27 = (((a27 - 387098) * 1) + -1094);
      a21 = ((((a21 % 299911)- 178) - 131841) + -129102);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((((( a21 <= -178 && (a9==5)) || ((a9==6) && a21 <= -178 )) || ((a9==2) && ((-178 < a21) && (-144 >= a21)) )) && (input == 1)) && a14 <= -148 ) && ((-78 < a27) && (100 >= a27)) ) && (a8==7))){
      if((a9==4)){
      a27 = (((a27 / 5) + 158082) + 334425);
      a21 = (((a21 + 600100) - -6) / 5);
       a8 = 6;
       a9 = 3;
      } else{
       a27 = (((((a27 % 40)- -141) / 5) + 142067) - 141943);
       a21 = (((a21 - -600134) - -6) - -2);
       a8 = 6;
       a9 = 4;
      } return 25;
     } else if(( ((-178 < a21) && (-144 >= a21)) && ((((((a9==3) || (a9==4)) && (input == 1)) && ((-78 < a27) && (100 >= a27)) ) && (a8==8)) && a14 <= -148 ))){
      a27 = (((((a27 / 5) * 5) + 155278) * -1)/ 10);
      a21 = (((a21 + -435046) * 1) + -97634);
       a8 = 4;
       a9 = 2;
       return -1;
     }
     return calculate_output4(input);
 }
 int calculate_output4(int input) {
     if((((((((a9==2) && ((-144 < a21) && (5 >= a21)) ) || (( ((-178 < a21) && (-144 >= a21)) && (a9==5)) || ( ((-178 < a21) && (-144 >= a21)) && (a9==6)))) && (input == 6)) && (a8==6)) && ((-148 < a14) && (13 >= a14)) ) && a27 <= -78 )){
      a14 = (((a14 + -206523) * 2) / 5);
      a21 = (((a21 / 5) + 306224) * 1);
       a8 = 5;
       a9 = 3;
       return -1;
     } else if((( ((-78 < a27) && (100 >= a27)) && ( a21 <= -178 && (((input == 4) && ((a9==5) || (a9==6))) && a14 <= -148 ))) && (a8==4))){
      a27 = (((a27 * 5) - 279033) / 5);
       a9 = 2;
       return -1;
     } else if(( 182 < a27 && ((a8==4) && ( 5 < a21 && ((((a9==2) || (a9==3)) && (input == 5)) && a14 <= -148 ))))){
      a27 = ((((a27 - 0) / 5) * 10)/ -4);
      a21 = ((((a21 / 5) - 413977) * 10)/ 9);
       a9 = 2;
       return -1;
     } else if((((( ((-178 < a21) && (-144 >= a21)) && ( a14 <= -148 && (input == 5))) && ((-78 < a27) && (100 >= a27)) ) && (a8==4)) && (a9==2))){
      a21 = ((((a21 / 5) + -101078) / 5) - -20192);
       a8 = 6;
       a9 = 3;
       return 23;
     } else if(( a27 <= -78 && ( a21 <= -178 && ((((((a9==3) || (a9==4)) || (a9==5)) && (input == 5)) && (a8==4)) && ((-148 < a14) && (13 >= a14)) )))){
      a14 = ((((a14 + -190796) / 5) * 10)/ 9);
      a27 = ((((a27 % 299908)- -300090) - -79548) + 38298);
      a21 = ((((a21 - -524378) / 5) % 74)- 69);
       a9 = 3;
       return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && (((((input == 5) && ((a9==3) || (a9==4))) && ((-178 < a21) && (-144 >= a21)) ) && a14 <= -148 ) && (a8==6)))){
      a27 = (((a27 - 10937) - 457369) / 5);
      a21 = ((((a21 * 5) - 83595) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((((( ((-144 < a21) && (5 >= a21)) && (a9==5)) || ( ((-144 < a21) && (5 >= a21)) && (a9==6))) || ((a9==2) && 5 < a21 )) && (input == 5)) && (a8==8)) && a14 <= -148 ) && ((100 < a27) && (182 >= a27)) )){
      a21 = (((((a21 % 74)+ -69) + -308276) + -289086) + 597361);
       a8 = 4;
       a9 = 5;
       return 21;
     } else if(( ((-78 < a27) && (100 >= a27)) && ((((((a9==5) || (a9==6)) && (input == 5)) && a14 <= -148 ) && a21 <= -178 ) && (a8==4)))){
      a21 = (((((a21 * 9)/ 10) % 16)- 149) * 1);
       a8 = 6;
       a9 = 5;
       return 21;
     } else if(( ((-178 < a21) && (-144 >= a21)) && ( a14 <= -148 && ((a8==7) && ( a27 <= -78 && ((input == 5) && ((a9==2) || (a9==3)))))))){
      a21 = (((a21 - 507491) + -26810) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==7) && (((((((a9==4) || (a9==5)) || (a9==6)) && (input == 3)) && ((-178 < a21) && (-144 >= a21)) ) && a14 <= -148 ) && a27 <= -78 ))){
      a21 = (((a21 + -285139) + 850670) + 12286);
       a9 = 4;
       return 23;
     } else if((( 5 < a21 && ( a27 <= -78 && (((a9==5) && (input == 4)) && ((-148 < a14) && (13 >= a14)) ))) && (a8==5))){
      if( a21 <= -178 ){
      a14 = (((a14 - 38597) + -167600) - 150024);
      } else{
       a14 = (((a14 + 158037) - 575872) * 1);
       a21 = ((((a21 % 16)- 172) * 1) - 4);
       a9 = 4;
      } return 23;
     } else if(( a21 <= -178 && ((a8==6) && ( a14 <= -148 && ( ((100 < a27) && (182 >= a27)) && (((a9==2) || (a9==3)) && (input == 3))))))){
      a27 = (((a27 + -278699) - 258098) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( 5 < a21 && (((((input == 1) && (a8==4)) && 182 < a27 ) && a14 <= -148 ) && (a9==4)))){
      a27 = (((a27 - 600170) / 5) - 20643);
      a21 = ((((a21 * 9)/ 10) - 555967) - 7128);
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( ((100 < a27) && (182 >= a27)) && (((a8==5) && (((a9==6) || ((a9==4) || (a9==5))) && (input == 5))) && ((-144 < a21) && (5 >= a21)) )))){
      a27 = ((((((a27 * 10)/ -9) - -318776) * 1) * -1)/ 10);
      a21 = (((((a21 * 5) / 5) - -96252) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && (((((input == 3) && ((a9==5) || (a9==6))) && ((100 < a27) && (182 >= a27)) ) && (a8==6)) && 5 < a21 ))){
      if( a21 <= -178 ){
      a27 = (((((a27 - -587853) + 2131) - 1104540) * -1)/ 10);
      a21 = (((((a21 % 74)+ -94) * 9)/ 10) + -28);
       a8 = 4;
       a9 = 2;
      } else{
       a21 = ((((((a21 % 74)+ -134) * 9)/ 10) + -500615) + 500639);
       a9 = 3;
      } return -1;
     } else if(( a14 <= -148 && ((a8==7) && ((( a21 <= -178 && (input == 4)) && ((-78 < a27) && (100 >= a27)) ) && (a9==2))))){
      a27 = (((a27 / 5) - -85908) + -317295);
       a8 = 4;
       return -1;
     } else if(((a8==6) && ( 182 < a27 && ( 5 < a21 && ((a9==3) && ( a14 <= -148 && (input == 4))))))){
      a27 = (((a27 - 600181) * 1) - 1);
      a21 = (((((a21 * 9)/ 10) * 1) * 1) - 555749);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( 5 < a21 && ( ((-148 < a14) && (13 >= a14)) && (((a8==5) && (input == 5)) && a27 <= -78 ))) && (a9==5))){
      if( ((-178 < a21) && (-144 >= a21)) ){
      a14 = ((((a14 + -23953) + 360095) + -31786) - 377664);
      a21 = ((((a21 - 19044) % 299911)+ -300088) - 1);
       a8 = 6;
       a9 = 3;
      } else{
       a14 = ((((a14 * 5) / 5) / 5) + -402514);
       a21 = (((((a21 % 74)+ -123) + -80456) - 37600) + 118076);
       a8 = 7;
       a9 = 2;
      } return -1;
     } else if((( a27 <= -78 && (((input == 3) && (( ((-144 < a21) && (5 >= a21)) && (a9==2)) || (((a9==5) && ((-178 < a21) && (-144 >= a21)) ) || ((a9==6) && ((-178 < a21) && (-144 >= a21)) )))) && (a8==6))) && ((-148 < a14) && (13 >= a14)) )){
      if( a21 <= -178 ){
      a14 = ((((a14 / 5) * 5) + 291796) + -638508);
      a21 = ((((((a21 % 16)+ -159) * 5) * 5) % 16)- 157);
       a8 = 5;
       a9 = 2;
      } else{
       a14 = ((((a14 - -508101) / 5) * 10)/ -9);
       a27 = ((((a27 % 88)+ 65) - 42) - -25);
       a21 = (((((a21 % 74)+ -68) * 5) % 74)+ -69);
       a9 = 6;
      } return -1;
     } else if((((( a14 <= -148 && ((input == 3) && ((-178 < a21) && (-144 >= a21)) )) && (a9==3)) && ((100 < a27) && (182 >= a27)) ) && (a8==7))){
      a27 = ((((a27 * 5) * -2)/ 10) * 5);
      a21 = (((a21 - -390313) * 1) - -143756);
       a8 = 6;
       a9 = 6;
       return -1;
     } else if(( ((-178 < a21) && (-144 >= a21)) && ( a14 <= -148 && (((((a9==3) || (a9==4)) && (input == 4)) && (a8==6)) && 182 < a27 )))){
      a27 = ((((a27 % 88)- -6) / 5) + -46);
      a21 = ((((a21 * 1)/ 10) - 164055) + 163946);
       a8 = 5;
       a9 = 2;
       return 21;
     } else if(((( ((-148 < a14) && (13 >= a14)) && (((((a9==4) || (a9==5)) || (a9==6)) && (input == 2)) && (a8==4))) && 5 < a21 ) && a27 <= -78 )){
      if((a9==6)){
      a14 = ((((a14 + -147216) / 5) * 10)/ 9);
      a27 = (((((a27 + 267250) % 40)- -140) + 395749) - 395746);
      a21 = (((((a21 + 0) / 5) / 5) % 16)- 162);
       a8 = 6;
       a9 = 2;
      } else{
       a14 = (((((a14 * 5) + 147495) - -128870) * -1)/ 10);
       a27 = ((((a27 % 40)- -149) + 533299) + -533285);
       a8 = 7;
       a9 = 6;
      } return -1;
     } else if(( ((-178 < a21) && (-144 >= a21)) && ( a27 <= -78 && ((((input == 2) && (((a9==3) || (a9==4)) || (a9==5))) && (a8==8)) && a14 <= -148 )))){
      a21 = (((a21 * 5) * 5) * 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((((((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ((a9==2) && ((-144 < a21) && (5 >= a21)) )) && (input == 3)) && (a8==8)) && 182 < a27 ))){
      a27 = (((a27 / 5) + -233346) / 5);
      a21 = ((((a21 + 141899) * 10)/ 9) * 3);
       a8 = 4;
       a9 = 6;
       return -1;
     } else if((( ((-78 < a27) && (100 >= a27)) && ((((((a9==5) && ((-144 < a21) && (5 >= a21)) ) || ( ((-144 < a21) && (5 >= a21)) && (a9==6))) || ((a9==2) && 5 < a21 )) && (input == 5)) && (a8==7))) && a14 <= -148 )){
      a27 = ((((a27 - 495974) - 10871) * 10)/ 9);
      a21 = ((((((a21 % 16)+ -160) - 2) * 5) % 16)+ -159);
       a9 = 6;
       return 21;
     } else if(( ((-144 < a21) && (5 >= a21)) && (((((input == 6) && ((a9==2) || (a9==3))) && (a8==4)) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 ))){
      a27 = ((((a27 * 5) + 118582) * 5) + -691929);
      a21 = (((a21 * 5) / 5) + -343041);
       a9 = 2;
       return -1;
     } else if((((((((a8==7) && (a9==2)) && a21 <= -178 ) || ((((a8==6) && (a9==5)) && 5 < a21 ) || (((a8==6) && (a9==6)) && 5 < a21 ))) && (input == 6)) && a14 <= -148 ) && 182 < a27 )){
      a27 = (((a27 + -600114) - 53) + -4);
      a21 = (((((a21 % 299911)+ -300088) - 1) / 5) - 272085);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((((input == 6) && (( ((-144 < a21) && (5 >= a21)) && (a9==6)) || ((a9==2) && 5 < a21 ))) && a27 <= -78 ) && (a8==8)))){
      a21 = ((((a21 / 5) + -432485) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((((a8==8) && ( ((-144 < a21) && (5 >= a21)) && (input == 6))) && 182 < a27 ) && a14 <= -148 ) && (a9==3))){
      if( ((-144 < a21) && (5 >= a21)) ){
      a27 = (((((a27 - 0) * 9)/ 10) % 88)- -13);
      a21 = ((((a21 + -188494) % 16)- 152) - -1);
       a8 = 4;
       a9 = 2;
      } else{
       a27 = (((a27 - 0) - 600131) * 1);
       a21 = (((((a21 % 16)+ -159) - 1) - -357483) + -357482);
       a8 = 5;
       a9 = 4;
      } return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && ((a8==8) && (((((a9==3) || (a9==4)) && (input == 3)) && ((-178 < a21) && (-144 >= a21)) ) && a14 <= -148 )))){
      a27 = (((a27 + -439778) + -63190) + -90038);
      a21 = ((((a21 / 5) + 11145) - -241179) + -555989);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( a21 <= -178 && (((input == 1) && ((a9==3) || (a9==4))) && (a8==6))) && a14 <= -148 ) && 182 < a27 )){
      a27 = (((((a27 - 590106) - -426756) / 5) % 40)+ 141);
      a21 = ((((a21 + 178055) % 74)- 69) - 1);
       a8 = 5;
       a9 = 3;
       return 25;
     } else if(( ((-178 < a21) && (-144 >= a21)) && (((((input == 6) && (((a9==4) || (a9==5)) || (a9==6))) && (a8==7)) && a27 <= -78 ) && a14 <= -148 ))){
      a21 = (((a21 - 114693) + -1255) + -44127);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a9==2) && ( ((-78 < a27) && (100 >= a27)) && (((input == 3) && ((-178 < a21) && (-144 >= a21)) ) && (a8==5)))) && a14 <= -148 )){
      a27 = (((((a27 - 315839) - 191654) + 1070639) * -1)/ 10);
      a21 = ((((a21 * 5) + 226085) * 10)/ -9);
       a8 = 4;
       return -1;
     } else if(( ((-178 < a21) && (-144 >= a21)) && ( a14 <= -148 && (((a8==8) && (((a9==2) || (a9==3)) && (input == 1))) && 182 < a27 )))){
      a27 = ((((a27 * 9)/ 10) / 5) + -242443);
      a21 = ((((a21 + 68238) / 5) * 10)/ 9);
       a8 = 5;
       a9 = 6;
       return -1;
     } else if(( 182 < a27 && ( a14 <= -148 && (((input == 4) && (((a9==2) && ((-178 < a21) && (-144 >= a21)) ) || (((a9==5) && a21 <= -178 ) || ( a21 <= -178 && (a9==6))))) && (a8==6))))){
      a27 = (((((a27 % 40)- -114) - 6) - 456054) + 456066);
      a21 = (((a21 / 5) - -419789) - 715824);
       a8 = 4;
       a9 = 3;
       return 21;
     } else if((( a14 <= -148 && ((a9==2) && ( 182 < a27 && ((input == 5) && (a8==6))))) && 5 < a21 )){
      a27 = (((((a27 - 233111) + -367067) / 5) * 23)/ 10);
      a21 = ((((a21 * 9)/ 10) / 5) + -234664);
       a8 = 4;
       return -1;
     } else if(((a8==4) && ( 5 < a21 && (( 182 < a27 && (((a9==2) || (a9==3)) && (input == 3))) && a14 <= -148 )))){
      a27 = (((a27 - 600174) - 3) + -4);
      a21 = ((((((a21 * 9)/ 10) - -57724) + 2087) * -1)/ 10);
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((((a8==4) && (((a9==5) || (a9==6)) && (input == 6))) && ((-78 < a27) && (100 >= a27)) ) && ((-144 < a21) && (5 >= a21)) ))){
      a21 = (((a21 - 340909) * 1) - -224852);
       a8 = 7;
       a9 = 6;
       return 25;
     } else if(((( a21 <= -178 && ( a27 <= -78 && ((a9==3) && (input == 5)))) && ((-148 < a14) && (13 >= a14)) ) && (a8==7))){
      a14 = (((a14 / 5) + -542405) + -6770);
      a27 = ((((a27 % 88)- -20) - 3) - 5);
       a8 = 4;
       a9 = 6;
       return -1;
     } else if(((a8==6) && ( a14 <= -148 && (( ((-78 < a27) && (100 >= a27)) && ((input == 4) && ((a9==3) || (a9==4)))) && ((-144 < a21) && (5 >= a21)) )))){
      a27 = (((((a27 - 195180) + 429882) / 5) * -1)/ 10);
      a21 = (((a21 - -269333) + -36804) + -708623);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((((a9==3) && (input == 5)) && a14 <= -148 ) && (a8==7)) && ((-178 < a21) && (-144 >= a21)) ) && ((100 < a27) && (182 >= a27)) )){
      a27 = (((((a27 * -8)/ 10) * 10)/ 9) - 26124);
      a21 = (((a21 + -343424) * 1) * 1);
       a8 = 5;
       a9 = 4;
       return -1;
     } else if(( a14 <= -148 && (((a8==5) && ( 5 < a21 && ((input == 4) && ((a9==3) || (a9==4))))) && ((-78 < a27) && (100 >= a27)) ))){
      a27 = ((((a27 % 40)- -140) - -1) * 1);
      a21 = (((a21 - 0) / 5) - 483293);
       a8 = 4;
       a9 = 3;
       return 21;
     } else if((((a8==6) && (((( ((-178 < a21) && (-144 >= a21)) && (a9==2)) || (( a21 <= -178 && (a9==5)) || ( a21 <= -178 && (a9==6)))) && (input == 1)) && ((-78 < a27) && (100 >= a27)) )) && a14 <= -148 )){
      a27 = (((a27 - 283881) - 100528) / 5);
      a21 = (((((a21 % 299911)- 178) + -103823) + 699551) + -619151);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==7) && ( a27 <= -78 && (( ((-148 < a14) && (13 >= a14)) && (((a9==4) || (a9==5)) && (input == 4))) && 5 < a21 )))){
      a14 = (((a14 - 26699) - 244272) + -13678);
      a27 = (((((a27 % 299908)+ 300090) * 1) / 5) + 400307);
      a21 = (((((a21 % 16)+ -162) + -346431) - -591909) - 245492);
       a8 = 6;
       a9 = 3;
       return 21;
     } else if(((a9==3) && ( a27 <= -78 && (( 5 < a21 && ((a8==7) && (input == 1))) && ((-148 < a14) && (13 >= a14)) )))){
      if((a9==5)){
      a14 = (((a14 - 588741) + -5284) - 3183);
      a21 = ((((a21 - 215475) % 299911)- 300088) * 1);
       a8 = 4;
       a9 = 2;
      } else{
       a14 = ((((a14 - 90674) - 434102) * 10)/ 9);
       a21 = (((((a21 % 16)+ -169) - 265017) / 5) + 52868);
       a8 = 5;
       a9 = 2;
      } return -1;
     } else if(((a8==4) && ( a14 <= -148 && ( ((-144 < a21) && (5 >= a21)) && ( ((-78 < a27) && (100 >= a27)) && (((a9==5) || (a9==6)) && (input == 3))))))){
      a27 = ((((a27 + -229818) * 10)/ 9) - 84312);
      a21 = (((a21 * 5) + -421511) + 21479);
       a9 = 2;
       return -1;
     } else if((( a27 <= -78 && (((( ((-144 < a21) && (5 >= a21)) && (a9==6)) || ((a9==2) && 5 < a21 )) && (input == 6)) && ((-148 < a14) && (13 >= a14)) )) && (a8==7))){
      a14 = (((a14 - 363079) - 70325) - 86261);
      a27 = ((((((a27 * 9)/ 10) / 5) + -227055) % 40)+ 172);
      a21 = ((((a21 - 155472) % 299911)- 300088) - 1);
       a8 = 4;
       a9 = 4;
       return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && ( a14 <= -148 && (((a9==4) && ((input == 1) && ((-144 < a21) && (5 >= a21)) )) && (a8==7))))){
      a27 = ((((a27 * 5) * 10)/ -9) / 5);
      a21 = (((a21 + -22775) * 5) - 302474);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==4) && (( ((-144 < a21) && (5 >= a21)) && ((input == 6) && ((a9==5) || (a9==6)))) && a27 <= -78 )) && ((-148 < a14) && (13 >= a14)) )){
      a14 = (((a14 + -164519) - 76366) * 2);
      a21 = (((((a21 - -209137) * 2) + -632010) * -1)/ 10);
       a8 = 6;
       a9 = 3;
       return 21;
     } else if(( a14 <= -148 && ((a9==2) && ((((input == 1) && a21 <= -178 ) && (a8==8)) && ((-78 < a27) && (100 >= a27)) )))){
      a27 = ((((a27 - 477223) - 49564) * 10)/ 9);
       a8 = 4;
       return -1;
     } else if(( ((-178 < a21) && (-144 >= a21)) && (( 182 < a27 && ((((a9==3) || (a9==4)) && (input == 5)) && (a8==6))) && a14 <= -148 ))){
      a27 = (((((a27 / 5) * 10)/ -4) / 5) + -106031);
      a21 = (((a21 + -330037) - 258971) - 2143);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && ((((a8==7) && ((input == 5) && (((a9==2) || (a9==3)) || (a9==4)))) && a27 <= -78 ) && ((-144 < a21) && (5 >= a21)) ))){
      if((a9==3)){
       a8 = 6;
       a9 = 4;
      } else{
       a14 = (((a14 * 5) + -431018) / 5);
       a8 = 6;
       a9 = 3;
      } return 25;
     } else if((( 182 < a27 && (((((a9==5) || ((a9==3) || (a9==4))) && (input == 4)) && 5 < a21 ) && (a8==5))) && a14 <= -148 )){
      if((a8==7)){
      a21 = ((((a21 + 0) % 299911)- 300088) * 1);
       a8 = 7;
       a9 = 6;
      } else{
       a27 = (((((a27 * 9)/ 10) - 560870) + 406692) - 435690);
       a21 = (((((a21 + 0) - 18409) + 344) % 299911)- 300088);
       a8 = 8;
       a9 = 4;
      } return -1;
     } else if(( 182 < a27 && ( a14 <= -148 && ((a8==5) && ((input == 5) && ((( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ((a9==2) && ((-144 < a21) && (5 >= a21)) )) || ( ((-144 < a21) && (5 >= a21)) && (a9==3)))))))){
      a27 = (((a27 + 0) - 600109) + -3);
      a21 = (((a21 + -547792) - 29433) / 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((a8==7) && (((input == 4) && ((-148 < a14) && (13 >= a14)) ) && a27 <= -78 )) && (a9==6)) && ((-178 < a21) && (-144 >= a21)) )){
      if( a27 <= -78 ){
      a14 = (((((a14 - -340986) * 1) * 1) * -1)/ 10);
      a21 = ((((a21 * 10)/ 8) / 5) * 5);
       a9 = 2;
      } else{
       a14 = (((a14 - 257308) - 114078) / 5);
       a8 = 5;
       a9 = 3;
      } return -1;
     } else if(( a14 <= -148 && ((( ((100 < a27) && (182 >= a27)) && (((a9==6) || ((a9==4) || (a9==5))) && (input == 5))) && (a8==5)) && 5 < a21 ))){
      a27 = (((a27 / 5) + -160083) + -7331);
      a21 = (((((a21 % 299911)+ -300088) + -26779) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((a8==5) && (((input == 2) && ((((a9==5) && ((-178 < a21) && (-144 >= a21)) ) || ( ((-178 < a21) && (-144 >= a21)) && (a9==6))) || ( ((-144 < a21) && (5 >= a21)) && (a9==2)))) && ((-78 < a27) && (100 >= a27)) )))){
      a27 = (((a27 * 5) + -314291) / 5);
      a21 = (((a21 * 5) - 467721) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( ((-78 < a27) && (100 >= a27)) && ( ((-178 < a21) && (-144 >= a21)) && ((a8==8) && (input == 4)))) && (a9==5)) && a14 <= -148 )){
      a27 = (((a27 - -442389) + -132879) + -800841);
      a21 = (((a21 + -317887) - 117653) + -21643);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==6) && ( a14 <= -148 && ( 5 < a21 && ((a9==5) && ( ((-78 < a27) && (100 >= a27)) && (input == 5))))))){
      a27 = (((((a27 / 5) / 5) + 488247) * -1)/ 10);
      a21 = (((((a21 % 299911)- 300088) * 1) + 246868) + -460237);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-178 < a21) && (-144 >= a21)) && ( ((100 < a27) && (182 >= a27)) && ((a8==4) && ( a14 <= -148 && ((((a9==3) || (a9==4)) || (a9==5)) && (input == 3))))))){
      a27 = ((((a27 * -8)/ 10) + -391337) * 1);
      a21 = ((((a21 / 5) * 64)/ 10) + -275617);
       a9 = 2;
       return -1;
     } else if((( 182 < a27 && ( a14 <= -148 && ( ((-144 < a21) && (5 >= a21)) && ((input == 2) && ((a9==5) || (a9==6)))))) && (a8==7))){
      a27 = ((((a27 / 5) * 4) + 40266) - 558310);
      a21 = (((a21 - 308161) + -286171) - 1189);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((((( a21 <= -178 && (a9==6)) || ( ((-178 < a21) && (-144 >= a21)) && (a9==2))) && (input == 4)) && (a8==8)) && ((-78 < a27) && (100 >= a27)) ) && a14 <= -148 )){
      a27 = (((a27 + -20547) * 5) + -408699);
      a21 = ((((a21 % 299911)+ -178) * 1) * 1);
       a8 = 7;
       a9 = 5;
       return 21;
     } else if(( a14 <= -148 && ( a21 <= -178 && ( ((-78 < a27) && (100 >= a27)) && ((a8==7) && ((input == 2) && ((a9==3) || (a9==4)))))))){
      a27 = (((((a27 % 40)- -142) - -116640) + -313788) + 197147);
      a21 = ((((a21 % 74)+ 2) / 5) + 5);
       a8 = 6;
       a9 = 3;
       return 25;
     } else if((((a8==6) && ( 5 < a21 && ( a27 <= -78 && ((input == 3) && ((a9==5) || (a9==6)))))) && ((-148 < a14) && (13 >= a14)) )){
      a14 = (((a14 + 371250) / 5) + -435138);
      a21 = (((((a21 % 74)+ -93) * 9)/ 10) / 5);
       a9 = 4;
       return -1;
     } else if(( a14 <= -148 && ( ((-178 < a21) && (-144 >= a21)) && ( 182 < a27 && (((input == 3) && ((a9==4) || (a9==5))) && (a8==5)))))){
      a21 = (((a21 + -58643) * 5) + 763705);
       a9 = 4;
       return 25;
     } else if(((( ((-78 < a27) && (100 >= a27)) && (((input == 3) && ((a9==4) || (a9==5))) && (a8==7))) && a14 <= -148 ) && 5 < a21 )){
      a27 = ((((a27 + -493913) * 10)/ 9) * 1);
      a21 = (((a21 / 5) + -1572) + -159867);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==4) && ( a14 <= -148 && ((((input == 3) && ((a9==5) || (a9==6))) && a21 <= -178 ) && ((-78 < a27) && (100 >= a27)) )))){
      a27 = (((a27 * 5) + 9978) * 5);
       a8 = 7;
       a9 = 4;
       return 25;
     } else if(( ((100 < a27) && (182 >= a27)) && ( a14 <= -148 && ((input == 1) && ((( 5 < a21 && ((a9==5) && (a8==4))) || ( 5 < a21 && ((a8==4) && (a9==6)))) || (((a9==2) && (a8==5)) && a21 <= -178 )))))){
      a27 = (((a27 - 450390) - 78329) * 1);
      a21 = ((((a21 % 299911)+ -300088) * 1) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==8) && (( 182 < a27 && ( a14 <= -148 && ((input == 2) && ((a9==4) || (a9==5))))) && ((-178 < a21) && (-144 >= a21)) ))){
      a27 = ((((a27 * -5)/ 10) * 1) + -135973);
      a21 = ((((a21 * 10)/ -9) + 550847) * 1);
       a8 = 5;
       a9 = 2;
       return -1;
     } else if(((a9==3) && ( ((-144 < a21) && (5 >= a21)) && (( a14 <= -148 && ( ((100 < a27) && (182 >= a27)) && (input == 4))) && (a8==7))))){
      if( ((13 < a14) && (182 >= a14)) ){
       a9 = 4;
      } else{
       a21 = ((((a21 + 439076) * 10)/ 9) * 1);
       a8 = 4;
      } return 21;
     } else if((((((a8==5) && ((input == 6) && ((a9==4) || (a9==5)))) && ((-148 < a14) && (13 >= a14)) ) && a27 <= -78 ) && ((-144 < a21) && (5 >= a21)) )){
      a14 = (((((a14 * 5) + -9616) + 389937) * -1)/ 10);
      a21 = (((((a21 % 16)- 161) / 5) / 5) + -147);
       a8 = 4;
       a9 = 5;
       return -1;
     } else if(((((a9==3) && (( ((-78 < a27) && (100 >= a27)) && (input == 5)) && a14 <= -148 )) && (a8==4)) && 5 < a21 )){
      a27 = (((a27 + -281229) * 2) + -11305);
      a21 = ((((a21 * 9)/ 10) + -593388) * 1);
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && (((((input == 3) && ((-78 < a27) && (100 >= a27)) ) && (a9==3)) && (a8==7)) && ((-178 < a21) && (-144 >= a21)) ))){
      a27 = ((((a27 % 40)+ 142) - -1) - 2);
      a21 = ((((a21 - 117874) - 310566) - -603482) - 174927);
       a8 = 4;
       a9 = 4;
       return 25;
     } else if((((((a8==8) && (((a9==5) || (a9==6)) && (input == 2))) && 5 < a21 ) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 )){
      a27 = (((a27 + -95842) * 5) - 29101);
      a21 = (((((a21 % 299911)+ -300088) - 293045) - -301743) + -224034);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==5) && ( ((100 < a27) && (182 >= a27)) && ( a14 <= -148 && ((input == 3) && ((a9==2) || (a9==3)))))) && 5 < a21 )){
      a27 = (((a27 - -261727) - 573677) * 1);
      a21 = (((a21 / 5) - 566635) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((( a14 <= -148 && ((((a9==3) || (a9==4)) || (a9==5)) && (input == 2))) && ((100 < a27) && (182 >= a27)) ) && a21 <= -178 ) && (a8==7))){
      a21 = (((((a21 - 0) + 312193) - 207781) % 16)+ -161);
       a9 = 5;
       return 25;
     } else if(((( ((100 < a27) && (182 >= a27)) && ((a8==5) && ((input == 6) && (((a9==4) || (a9==5)) || (a9==6))))) && ((-144 < a21) && (5 >= a21)) ) && a14 <= -148 )){
      a27 = ((((a27 / 5) * 5) * 5) - 572398);
      a21 = ((((a21 * 5) - 146040) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((a9==2) && ( a21 <= -178 && ((a8==8) && ( ((-78 < a27) && (100 >= a27)) && (input == 5))))))){
      a27 = ((((((a27 % 40)+ 142) * 5) * 5) % 40)- -112);
       a8 = 4;
       return 21;
     } else if(((((a8==7) && ( ((100 < a27) && (182 >= a27)) && ((input == 4) && ((a9==4) || (a9==5))))) && ((-178 < a21) && (-144 >= a21)) ) && a14 <= -148 )){
       a8 = 4;
       a9 = 6;
       return 21;
     } else if(( a14 <= -148 && (( ((100 < a27) && (182 >= a27)) && ( 5 < a21 && (((a9==2) || (a9==3)) && (input == 6)))) && (a8==7)))){
      a27 = (((a27 + 279554) - 155308) * 4);
      a21 = ((((((a21 % 16)- 163) - 8) * 5) % 16)+ -159);
       a9 = 2;
       return 21;
     } else if(( ((-144 < a21) && (5 >= a21)) && ( a14 <= -148 && ((a8==8) && ((((a9==5) || (a9==6)) && (input == 1)) && 182 < a27 ))))){
      a14 = (((((a14 % 80)+ -22) * 5) % 80)+ 7);
      a27 = (((((a27 / 5) * 10)/ -4) - -389854) + -640891);
      a21 = (((a21 / 5) - 147) - 1);
       a8 = 4;
       a9 = 4;
       return -1;
     } else if((((a9==3) && ( 182 < a27 && (((input == 2) && (a8==8)) && ((-144 < a21) && (5 >= a21)) ))) && a14 <= -148 )){
      if((a8==5)){
      a27 = (((a27 - 600128) * 1) * 1);
      a21 = (((a21 / 5) / 5) - 475400);
       a8 = 5;
       a9 = 2;
      } else{
       a27 = ((((a27 * -5)/ 10) + -12840) + -4903);
       a21 = (((((a21 % 16)+ -161) + 203588) + -298559) - -94972);
       a8 = 6;
       a9 = 4;
      } return -1;
     } else if((( ((-78 < a27) && (100 >= a27)) && ((((((a8==5) && (a9==5)) && 5 < a21 ) || (((a8==5) && (a9==6)) && 5 < a21 )) || ( a21 <= -178 && ((a8==6) && (a9==2)))) && (input == 1))) && a14 <= -148 )){
      a27 = ((((a27 + 159018) / 5) * 5) + -423743);
      a21 = ((((a21 % 299911)- 300088) * 1) + -1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a21 <= -178 && ((( ((100 < a27) && (182 >= a27)) && ((input == 3) && ((a9==5) || ((a9==3) || (a9==4))))) && a14 <= -148 ) && (a8==7)))){
      a27 = (((((a27 - -439565) * -1)/ 10) - -356621) + -692285);
      a21 = (((((a21 % 74)+ 5) - 25) * 9)/ 10);
       a8 = 5;
       a9 = 4;
       return -1;
     } else if(( ((-144 < a21) && (5 >= a21)) && (((((((a9==4) || (a9==5)) || (a9==6)) && (input == 1)) && (a8==4)) && a14 <= -148 ) && 182 < a27 ))){
      a27 = (((a27 - 600142) * 1) * 1);
       a8 = 6;
       a9 = 3;
       return -1;
     } else if(((a8==5) && ( 5 < a21 && (( ((-148 < a14) && (13 >= a14)) && ((a9==5) && (input == 1))) && a27 <= -78 )))){
      a14 = ((((a14 + -232728) * 10)/ 9) + 113715);
       a8 = 4;
       a9 = 6;
       return -1;
     } else if(((((a9==5) && ( a21 <= -178 && ((input == 1) && (a8==8)))) && a27 <= -78 ) && a14 <= -148 )){
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==4) && ( a14 <= -148 && ( ((100 < a27) && (182 >= a27)) && ((( a21 <= -178 && (a9==6)) || ((a9==2) && ((-178 < a21) && (-144 >= a21)) )) && (input == 1)))))){
      a27 = (((a27 + -1496) * 5) - 111101);
      a21 = ((((((a21 % 299911)- 178) * 1) + 583818) * -1)/ 10);
       a9 = 2;
       return -1;
     } else if((((a8==5) && ( 182 < a27 && (((input == 1) && (((a9==3) || (a9==4)) || (a9==5))) && 5 < a21 ))) && a14 <= -148 )){
      a27 = ((((a27 * 9)/ 10) + -405698) + -161168);
      a21 = (((((a21 % 299911)+ -300088) * 10)/ 9) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( 5 < a21 && ((a8==6) && (( 182 < a27 && (input == 3)) && (a9==3)))))){
      a27 = (((a27 - 600155) * 1) - 20);
      a21 = (((((a21 % 299911)- 300088) / 5) * 51)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( ((-144 < a21) && (5 >= a21)) && ((((a9==5) || (a9==6)) && (input == 4)) && 182 < a27 )) && (a8==7)) && a14 <= -148 )){
      a27 = (((((a27 - 81382) - -34952) + -87709) % 40)+ 140);
      a21 = ((((a21 + -153766) - -202044) / 5) - 241721);
       a8 = 4;
       a9 = 3;
       return -1;
     } else if(( a14 <= -148 && ((((a9==6) && ((input == 5) && (a8==8))) && a27 <= -78 ) && 5 < a21 ))){
      a21 = ((((a21 - 392694) % 299911)+ -300088) + -2);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( ((100 < a27) && (182 >= a27)) && ((a8==4) && (((input == 6) && ((-178 < a21) && (-144 >= a21)) ) && (a9==6)))))){
       return 23;
     } else if((( 182 < a27 && ( a21 <= -178 && ( a14 <= -148 && ((a8==7) && (input == 5))))) && (a9==6))){
      a27 = ((((((a27 * -5)/ 10) * 1) / 5) * 44)/ 10);
      a21 = (((a21 - -600057) * 1) + 25);
       a8 = 8;
       return 21;
     } else if(((a8==5) && (( a27 <= -78 && ((((a9==6) && a21 <= -178 ) || ( ((-178 < a21) && (-144 >= a21)) && (a9==2))) && (input == 1))) && ((-148 < a14) && (13 >= a14)) ))){
      a21 = ((((a21 / 5) % 16)+ -145) + 1);
       a9 = 5;
       return -1;
     } else if((( a14 <= -148 && (((input == 2) && (((a9==6) && ((-144 < a21) && (5 >= a21)) ) || ((a9==2) && 5 < a21 ))) && (a8==5))) && ((-78 < a27) && (100 >= a27)) )){
      a27 = ((((a27 * 5) % 40)+ 140) * 1);
      a21 = ((((a21 % 299911)- 300088) - 1) - 1);
       a8 = 4;
       a9 = 2;
       return 25;
     } else if((( ((100 < a27) && (182 >= a27)) && ( a21 <= -178 && (((input == 2) && a14 <= -148 ) && (a9==4)))) && (a8==4))){
      if( ((-78 < a27) && (100 >= a27)) ){
      a27 = (((a27 + 75187) - -516296) - -1670);
       a8 = 7;
       a9 = 6;
      } else{
       a27 = (((((a27 * -8)/ 10) + 132947) * 10)/ -9);
       a8 = 8;
      } return 21;
     } else if(((((((((a9==2) || (a9==3)) || (a9==4)) && (input == 2)) && (a8==7)) && a14 <= -148 ) && ((-144 < a21) && (5 >= a21)) ) && 182 < a27 )){
      a27 = (((((a27 + 0) * -5)/ 10) * 10)/ 9);
      a21 = ((((a21 - 236567) - 406) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==8) && ( a14 <= -148 && ((((input == 6) && ((a9==4) || ((a9==2) || (a9==3)))) && 5 < a21 ) && 182 < a27 )))){
      a27 = (((a27 + -376581) + -135835) - 87742);
       a8 = 5;
       a9 = 2;
       return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && (((a8==4) && ( a14 <= -148 && ((input == 6) && ((a9==5) || ((a9==3) || (a9==4)))))) && ((-178 < a21) && (-144 >= a21)) ))){
      a27 = (((((a27 - 414477) - -707009) / 5) * -1)/ 10);
      a21 = (((((a21 * 10)/ 8) * 10)/ 9) + -167121);
       a9 = 2;
       return -1;
     } else if((((((input == 1) && (((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ((a9==2) && ((-144 < a21) && (5 >= a21)) ))) && ((-148 < a14) && (13 >= a14)) ) && a27 <= -78 ) && (a8==4))){
      a14 = (((((a14 + 419959) * 10)/ -9) + 595794) - 444743);
      a21 = ((((a21 + 122234) - 306523) * -1)/ 10);
       a9 = 4;
       return -1;
     } else if((( ((-78 < a27) && (100 >= a27)) && (((((a9==3) || (a9==4)) && (input == 4)) && ((-178 < a21) && (-144 >= a21)) ) && (a8==8))) && a14 <= -148 )){
      a27 = ((((a27 + -164941) - 100084) + 280240) - 364990);
      a21 = (((((a21 / 5) - -471993) * 1) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((((( ((-144 < a21) && (5 >= a21)) && (a9==6)) || ((a9==2) && 5 < a21 )) && (input == 2)) && (a8==8)) && a27 <= -78 ))){
      if((a9==5)){
      a27 = ((((a27 + 0) % 299908)+ 300090) + 102079);
      a21 = (((((a21 % 299997)+ 300002) - 206472) * 1) + 206473);
       a8 = 4;
       a9 = 3;
      } else{
       a27 = (((((a27 - -481914) * 1) / 5) % 88)+ 12);
       a21 = ((((a21 % 74)- 69) - -1) - 1);
       a8 = 5;
       a9 = 3;
      } return 21;
     } else if((((a8==7) && (( a14 <= -148 && ((input == 2) && ((-144 < a21) && (5 >= a21)) )) && ((100 < a27) && (182 >= a27)) )) && (a9==3))){
      a21 = (((a21 - -150633) * 3) * 1);
       a8 = 4;
       a9 = 4;
       return 21;
     } else if(( a14 <= -148 && ( ((-78 < a27) && (100 >= a27)) && ((a8==4) && ((input == 3) && (( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ((a9==2) && ((-144 < a21) && (5 >= a21)) ))))))){
      a21 = (((a21 + 452144) * 1) * 1);
       a8 = 6;
       a9 = 6;
       return 23;
     } else if(((((a8==4) && ( a21 <= -178 && ((a9==6) && (input == 1)))) && ((-148 < a14) && (13 >= a14)) ) && a27 <= -78 )){
      if((a9==5)){
      a14 = (((a14 + -101790) - 11048) + -188732);
       a8 = 6;
       a9 = 3;
      } else{
       a14 = ((((a14 + -482775) - 52273) * 10)/ 9);
       a21 = ((((a21 - -451543) + 148546) + -570415) + 570413);
       a8 = 6;
       a9 = 4;
      } return 21;
     } else if(( 182 < a27 && ((( ((-178 < a21) && (-144 >= a21)) && (((a9==4) || (a9==5)) && (input == 1))) && a14 <= -148 ) && (a8==5)))){
      a27 = ((((a27 % 40)- -117) + 79343) - 79342);
      a21 = ((((a21 * 1)/ 10) - 4) - 8);
       a8 = 6;
       a9 = 6;
       return 25;
     } else if(( 5 < a21 && ( a14 <= -148 && (((a8==4) && ((a9==2) && (input == 5))) && ((-78 < a27) && (100 >= a27)) )))){
      a21 = ((((a21 % 16)+ -171) - -5) + 3);
       a8 = 7;
       a9 = 4;
       return 25;
     } else if((( a14 <= -148 && (((((a9==6) || ((a9==4) || (a9==5))) && (input == 5)) && (a8==7)) && 5 < a21 )) && 182 < a27 )){
      a27 = (((a27 - 600125) - 16) + -10);
      a21 = ((((a21 % 299911)+ -300088) + -84755) + -203145);
       a8 = 6;
       a9 = 2;
       return -1;
     } else if(((a8==7) && ( a27 <= -78 && (((((a9==4) || (a9==5)) && (input == 3)) && 5 < a21 ) && a14 <= -148 )))){
      a21 = (((((a21 + -311396) * 1) - -281473) % 299911)+ -300088);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==6) && ((( 182 < a27 && ((input == 3) && a14 <= -148 )) && ((-178 < a21) && (-144 >= a21)) ) && (a9==5)))){
      a27 = (((((a27 - 42424) % 88)- -12) - -182850) + -182851);
      a21 = ((((((a21 * -1)/ 10) * 10)/ 9) * 10)/ 9);
       a8 = 8;
       a9 = 2;
       return 21;
     } else if(((( 182 < a27 && ( a14 <= -148 && ((a8==8) && (input == 6)))) && ((-144 < a21) && (5 >= a21)) ) && (a9==4))){
      if((a8==8)){
      a27 = ((((a27 * -5)/ 10) + -274300) * 1);
      a21 = ((((a21 - 521847) * 10)/ 9) * 1);
       a8 = 5;
       a9 = 6;
      } else{
       a27 = ((((a27 + -600104) * 1) + 577693) + -577707);
       a21 = ((((a21 - -574023) / 5) * 10)/ 9);
       a8 = 5;
       a9 = 5;
      } return -1;
     } else if(( a27 <= -78 && ( ((-148 < a14) && (13 >= a14)) && ( a21 <= -178 && (((a9==5) && (input == 1)) && (a8==5)))))){
      a14 = (((a14 - 191332) - -164095) + -205627);
      a27 = ((((a27 % 299908)+ 300090) - -48393) - -134300);
      a21 = (((a21 - -600167) / 5) * 5);
       a8 = 7;
       a9 = 4;
       return 25;
     } else if((((a8==5) && ( a14 <= -148 && ( ((-144 < a21) && (5 >= a21)) && ((input == 6) && (a9==5))))) && ((-78 < a27) && (100 >= a27)) )){
      a21 = ((((a21 - -430272) / 5) * 10)/ 9);
       a8 = 8;
       a9 = 3;
       return 21;
     } else if(( 182 < a27 && ((a8==7) && ( ((-178 < a21) && (-144 >= a21)) && ((((a9==4) || ((a9==2) || (a9==3))) && (input == 2)) && a14 <= -148 ))))){
      a27 = (((a27 - 284880) + -254850) + -60366);
      a21 = (((a21 / 5) / 5) + -323597);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((a8==8) && ((input == 1) && (( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ( ((-144 < a21) && (5 >= a21)) && (a9==2))))) && ((-78 < a27) && (100 >= a27)) ) && a14 <= -148 )){
      a27 = (((a27 / 5) * 5) + -223265);
      a21 = ((((a21 + -449415) * 10)/ 9) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==4) && (((((a9==2) || (a9==3)) && (input == 6)) && ((100 < a27) && (182 >= a27)) ) && 5 < a21 )) && a14 <= -148 )){
      a27 = ((((a27 / 5) * 10)/ -2) + -454712);
      a21 = ((((a21 + -2485) + -131655) % 299911)- 300088);
       a9 = 2;
       return -1;
     } else if((((a8==6) && ( a27 <= -78 && ( 5 < a21 && ((input == 4) && ((a9==5) || (a9==6)))))) && ((-148 < a14) && (13 >= a14)) )){
      if((a9==3)){
      a14 = (((a14 + -477914) + -84287) + -4964);
      a21 = (((((a21 % 299911)- 300088) * 1) - -209330) - 210553);
       a8 = 7;
       a9 = 2;
      } else{
       a14 = (((a14 - 244733) * 2) * 1);
       a21 = ((((a21 % 299911)+ -300088) - 79549) + 48267);
       a8 = 5;
       a9 = 3;
      } return -1;
     } else if(( 182 < a27 && ( a14 <= -148 && ((a8==6) && ((((a9==3) && ((-144 < a21) && (5 >= a21)) ) || (( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ((a9==2) && ((-144 < a21) && (5 >= a21)) ))) && (input == 2)))))){
      a27 = (((((a27 * -5)/ 10) / 5) * 10)/ 2);
      a21 = ((((a21 - 366878) * 10)/ 9) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a9==3) && ((( a14 <= -148 && (input == 3)) && ((-144 < a21) && (5 >= a21)) ) && (a8==5))) && ((100 < a27) && (182 >= a27)) )){
      a27 = (((a27 + -114190) - 454205) + -3303);
      a21 = ((((a21 + -428649) - -820172) / 5) + -203489);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( 182 < a27 && ((a9==3) && (((input == 5) && ((-144 < a21) && (5 >= a21)) ) && (a8==4)))))){
      a27 = (((a27 + -600155) * 1) + -23);
      a21 = (((a21 + -125956) / 5) - 572051);
       a9 = 2;
       return -1;
     } else if((( 182 < a27 && (( ((-144 < a21) && (5 >= a21)) && ((input == 3) && (a8==8))) && (a9==4))) && a14 <= -148 )){
      a27 = (((a27 + -600101) - -346598) + -346629);
      a21 = (((a21 * 5) - -296733) * 2);
       a8 = 6;
       a9 = 5;
       return 25;
     } else if(((((a8==7) && (( ((-78 < a27) && (100 >= a27)) && (input == 3)) && (a9==6))) && 5 < a21 ) && a14 <= -148 )){
      a27 = (((((a27 % 40)- -140) / 5) / 5) - -171);
      a21 = ((((((a21 / 5) % 16)+ -170) * 5) % 16)- 156);
       a8 = 6;
       a9 = 5;
       return 25;
     } else if((((a8==5) && ((a9==4) && ( a14 <= -148 && ( ((-144 < a21) && (5 >= a21)) && (input == 2))))) && 182 < a27 )){
      a27 = (((a27 - 600092) / 5) - 147263);
      a21 = (((a21 * 5) - 301065) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((((a8==7) && ((input == 1) && ((a9==3) || (a9==4)))) && a14 <= -148 ) && a21 <= -178 ) && 182 < a27 )){
      a27 = (((((a27 - 600103) / 5) - -149692) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( 182 < a27 && (((((input == 6) && (a8==6)) && ((-178 < a21) && (-144 >= a21)) ) && (a9==5)) && a14 <= -148 ))){
      a27 = (((((a27 * 9)/ 10) + 14470) % 88)+ -73);
      a21 = (((a21 / 5) - -207132) * 2);
       a8 = 8;
       a9 = 3;
       return 21;
     } else if(((((a8==6) && ((((a9==5) || (a9==6)) && (input == 2)) && ((100 < a27) && (182 >= a27)) )) && 5 < a21 ) && a14 <= -148 )){
      a27 = (((((a27 / 5) + 480482) * 1) * -1)/ 10);
      a21 = ((((a21 * 9)/ 10) + -547045) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && ( a14 <= -148 && ((a8==8) && (((( a21 <= -178 && (a9==6)) || ((a9==2) && ((-178 < a21) && (-144 >= a21)) )) || ((a9==3) && ((-178 < a21) && (-144 >= a21)) )) && (input == 6)))))){
      a27 = (((a27 - -289134) + -289224) / 5);
      a21 = ((((((a21 + 0) * 9)/ 10) / 5) % 16)- 152);
       a8 = 5;
       a9 = 3;
       return 21;
     } else if((((a8==7) && ((((( a21 <= -178 && (a9==5)) || ( a21 <= -178 && (a9==6))) || ( ((-178 < a21) && (-144 >= a21)) && (a9==2))) && (input == 1)) && ((-148 < a14) && (13 >= a14)) )) && a27 <= -78 )){
      a14 = (((a14 - 526354) * 1) * 1);
      a21 = (((((a21 + 8095) % 299911)+ -300088) - -104945) + -104945);
       a8 = 5;
       a9 = 6;
       return 23;
     } else if((((a8==6) && (((input == 4) && (( ((-144 < a21) && (5 >= a21)) && (a9==3)) || (((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ( ((-144 < a21) && (5 >= a21)) && (a9==2))))) && ((100 < a27) && (182 >= a27)) )) && a14 <= -148 )){
      a27 = (((a27 * 5) - 505366) - 60204);
      a21 = ((((a21 % 74)- 69) - -1) + -1);
       a8 = 7;
       a9 = 3;
       return 25;
     } else if((((( 5 < a21 && ((input == 6) && ((a9==4) || (a9==5)))) && a14 <= -148 ) && (a8==7)) && a27 <= -78 )){
      if((a9==6)){
      a27 = ((((a27 % 40)- -181) - -518396) + -518403);
      a21 = (((((a21 * 9)/ 10) - 45474) % 74)+ -68);
       a8 = 8;
       a9 = 3;
      } else{
       a21 = ((((a21 - 0) % 74)+ -111) / 5);
       a8 = 8;
       a9 = 4;
      } return 25;
     } else if(( ((-178 < a21) && (-144 >= a21)) && ( a27 <= -78 && ( ((-148 < a14) && (13 >= a14)) && ((a9==2) && ((input == 6) && (a8==4))))))){
      a14 = (((a14 - 184311) * 3) - 40866);
       a8 = 6;
       a9 = 6;
       return 23;
     } else if(( ((100 < a27) && (182 >= a27)) && (((((((a9==3) || (a9==4)) || (a9==5)) && (input == 5)) && (a8==7)) && a21 <= -178 ) && a14 <= -148 ))){
      a27 = (((((a27 * 10)/ -9) / 5) * 10)/ 2);
      a21 = ((((a21 - 0) % 74)- -2) / 5);
       a8 = 5;
       a9 = 5;
       return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && ((((((a9==2) && 5 < a21 ) || (( ((-144 < a21) && (5 >= a21)) && (a9==5)) || ((a9==6) && ((-144 < a21) && (5 >= a21)) ))) && (input == 6)) && a14 <= -148 ) && (a8==6)))){
      a27 = (((a27 * 5) - 251432) * 2);
      a21 = ((((a21 - 146882) * 1) % 299911)+ -300088);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && (( 5 < a21 && (( a14 <= -148 && (input == 3)) && (a8==8))) && (a9==4)))){
      a27 = (((a27 - -258854) + 87012) - 577750);
      a21 = (((((a21 % 299911)- 300088) / 5) * 51)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((((input == 1) && (((a9==4) || (a9==5)) || (a9==6))) && a27 <= -78 ) && (a8==4)) && 5 < a21 ) && ((-148 < a14) && (13 >= a14)) )){
      a21 = ((((a21 * 9)/ 10) + 59910) - 611500);
       a9 = 2;
       return -1;
     } else if(( 182 < a27 && (((( 5 < a21 && ((a9==6) && (a8==5))) || ( a21 <= -178 && ((a8==6) && (a9==2)))) && (input == 4)) && a14 <= -148 ))){
      a27 = (((((a27 * -5)/ 10) * 1) + 184577) + -426082);
      a21 = ((((a21 % 299911)- 300088) - 1) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a27 <= -78 && ((((input == 4) && (((a9==6) && ((-144 < a21) && (5 >= a21)) ) || ((a9==2) && 5 < a21 ))) && (a8==7)) && ((-148 < a14) && (13 >= a14)) ))){
      a14 = ((((a14 - -91256) * -1)/ 10) + -70405);
      a21 = (((((a21 - 594476) / 5) * 5) % 74)+ -69);
       a8 = 4;
       a9 = 3;
       return 21;
     } else if((((a9==5) && ((( ((-78 < a27) && (100 >= a27)) && (input == 2)) && ((-178 < a21) && (-144 >= a21)) ) && (a8==6))) && a14 <= -148 )){
      a27 = (((a27 * 5) + -84054) * 5);
      a21 = ((((a21 * 10)/ 8) - 582280) + -7870);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-144 < a21) && (5 >= a21)) && (((a8==4) && ( ((-78 < a27) && (100 >= a27)) && (((a9==3) || (a9==4)) && (input == 1)))) && a14 <= -148 ))){
      a27 = (((((a27 - 528618) / 5) - -611145) * -1)/ 10);
      a21 = (((a21 + -17377) + -148696) - 105359);
       a9 = 2;
       return -1;
     } else if((( ((-148 < a14) && (13 >= a14)) && (( a27 <= -78 && ((input == 1) && (a9==3))) && (a8==7))) && a21 <= -178 )){
      a14 = (((a14 - 201260) + -229990) - 101921);
      a27 = (((((a27 + 0) % 40)+ 181) - 231521) + 231510);
      a21 = (((a21 - -600100) * 1) + 76);
       a8 = 5;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( ((-78 < a27) && (100 >= a27)) && ((a8==8) && ((((a9==3) || (a9==4)) && (input == 6)) && ((-178 < a21) && (-144 >= a21)) ))))){
      a27 = ((((a27 - -78374) * 10)/ -9) - 253250);
      a21 = (((a21 + -526203) - -346542) * 3);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a21 <= -178 && (( 182 < a27 && ((a8==8) && (((a9==2) || (a9==3)) && (input == 3)))) && a14 <= -148 ))){
      if( ((-178 < a21) && (-144 >= a21)) ){
      a27 = (((a27 + -600085) * 1) * 1);
      a21 = (((a21 - -600052) + -419910) - -419961);
       a8 = 4;
       a9 = 5;
      } else{
       a27 = ((((((a27 - 329934) % 40)+ 141) * 5) % 40)- -106);
       a8 = 5;
       a9 = 3;
      } return -1;
     } else if((((((input == 4) && ((( ((-144 < a21) && (5 >= a21)) && (a9==5)) || ((a9==6) && ((-144 < a21) && (5 >= a21)) )) || ( 5 < a21 && (a9==2)))) && a14 <= -148 ) && (a8==7)) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((a27 - 36017) * 5) * 3);
      a21 = ((((a21 % 299911)+ -300088) / 5) - 197534);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( ((100 < a27) && (182 >= a27)) && ((a8==8) && (((a9==5) || (a9==6)) && (input == 5)))) && a14 <= -148 ) && 5 < a21 )){
      a27 = ((((a27 + -256142) / 5) * 10)/ 9);
      a21 = (((((a21 % 299911)- 300088) * 1) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==6) && (( a14 <= -148 && ((input == 1) && (((a9==2) && ((-178 < a21) && (-144 >= a21)) ) || (((a9==5) && a21 <= -178 ) || ( a21 <= -178 && (a9==6)))))) && ((100 < a27) && (182 >= a27)) ))){
      a27 = (((a27 * 5) * 5) + -464871);
      a21 = ((((a21 % 299911)- 178) + -236701) - 54803);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a9==3) && (((( a14 <= -148 && (input == 4)) && (a8==8)) && ((-144 < a21) && (5 >= a21)) ) && ((-78 < a27) && (100 >= a27)) ))){
      a27 = (((a27 - -91588) + 221375) + -517904);
      a21 = (((a21 - 565772) - 9492) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && (( ((-144 < a21) && (5 >= a21)) && ( a27 <= -78 && ((input == 3) && (a8==6)))) && (a9==3)))){
      a14 = (((a14 - 210337) - 150207) / 5);
      a21 = ((((a21 * 5) / 5) % 16)+ -161);
       a8 = 5;
       a9 = 5;
       return 21;
     } else if((( a14 <= -148 && (((a8==5) && ((input == 4) && ((a9==4) || (a9==5)))) && a21 <= -178 )) && ((100 < a27) && (182 >= a27)) )){
      a27 = ((((a27 - 127) - -582552) - -6129) - 588665);
      a21 = (((((a21 % 16)+ -155) + -3) - -523652) - 523645);
       a8 = 6;
       a9 = 5;
       return 21;
     } else if(( ((-148 < a14) && (13 >= a14)) && (((a8==5) && ( ((-144 < a21) && (5 >= a21)) && (((a9==4) || (a9==5)) && (input == 4)))) && a27 <= -78 ))){
      if((a8==6)){
      a14 = (((a14 + 487299) * 1) - 756399);
       a9 = 6;
      } else{
       a14 = (((a14 + -69803) * 5) + -21428);
       a21 = ((((a21 * 5) % 16)- 159) * 1);
       a8 = 6;
       a9 = 3;
      } return -1;
     } else if(( a14 <= -148 && ((( ((-78 < a27) && (100 >= a27)) && ((input == 4) && ((a9==5) || (a9==6)))) && (a8==8)) && 5 < a21 ))){
      a27 = (((a27 * 5) + -28679) * 5);
      a21 = ((((a21 % 299911)- 300088) + -39254) + -166596);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((a8==6) && ((input == 1) && ((( ((-144 < a21) && (5 >= a21)) && (a9==5)) || ( ((-144 < a21) && (5 >= a21)) && (a9==6))) || ((a9==2) && 5 < a21 )))) && a14 <= -148 ) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((a27 + -3196) - 56388) / 5);
      a21 = (((((a21 + -587209) % 299911)+ -300088) - -325306) - 325307);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((-178 < a21) && (-144 >= a21)) && ((a8==7) && ((((a9==2) || (a9==3)) && (input == 4)) && a14 <= -148 ))) && a27 <= -78 )){
      a21 = (((a21 / 5) + 567417) + -567393);
       a9 = 3;
       return 25;
     } else if(( ((-78 < a27) && (100 >= a27)) && ((a8==5) && ( a14 <= -148 && ((input == 5) && (((a9==2) && ((-144 < a21) && (5 >= a21)) ) || (((a9==5) && ((-178 < a21) && (-144 >= a21)) ) || ((a9==6) && ((-178 < a21) && (-144 >= a21)) )))))))){
      a27 = ((((a27 + -131858) * 10)/ 9) * 4);
      a21 = ((((a21 / 5) + 62425) / 5) + -557869);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==5) && ( a14 <= -148 && (((input == 1) && ((a9==2) || (a9==3))) && 5 < a21 ))) && ((100 < a27) && (182 >= a27)) )){
      a27 = (((((a27 * 10)/ 19) + 3) - 177307) - -177193);
      a21 = (((((a21 + -217892) % 16)+ -159) - -591137) + -591138);
       a8 = 4;
       a9 = 2;
       return 21;
     } else if((((a8==7) && (((((a9==6) && a21 <= -178 ) || ((a9==2) && ((-178 < a21) && (-144 >= a21)) )) && (input == 3)) && a14 <= -148 )) && ((100 < a27) && (182 >= a27)) )){
      a27 = (((a27 + -248494) * 2) + -6842);
      a21 = ((((a21 % 299911)- 178) - 118260) * 1);
       a8 = 6;
       a9 = 6;
       return -1;
     } else if((((a8==5) && (((input == 3) && ((( a21 <= -178 && (a9==5)) || ((a9==6) && a21 <= -178 )) || ((a9==2) && ((-178 < a21) && (-144 >= a21)) ))) && a14 <= -148 )) && 182 < a27 )){
      a27 = ((((a27 - 0) / 5) % 88)- -12);
      a21 = ((((a21 / 5) - -519017) + -902946) + 801663);
       a8 = 8;
       a9 = 2;
       return 21;
     } else if(( ((-148 < a14) && (13 >= a14)) && ((((input == 5) && (((a9==6) && ((-144 < a21) && (5 >= a21)) ) || ((a9==2) && 5 < a21 ))) && (a8==6)) && a27 <= -78 ))){
      if( 5 < a21 ){
      a14 = (((a14 / 5) * 5) + -17081);
      a21 = ((((a21 + -478006) * 1) % 299911)+ -300088);
       a8 = 7;
       a9 = 3;
      } else{
       a14 = (((a14 * 5) + -534544) - 39506);
       a27 = ((((((a27 % 88)- -61) - 32081) * 5) % 88)- -65);
       a21 = ((((a21 % 299911)- 300088) / 5) - 244460);
       a8 = 7;
       a9 = 2;
      } return 23;
     } else if((( a27 <= -78 && ( 5 < a21 && (((a9==5) && (input == 6)) && ((-148 < a14) && (13 >= a14)) ))) && (a8==5))){
      a14 = (((a14 - 163680) * 3) - 92065);
      a21 = (((((a21 % 74)+ -102) / 5) * 9)/ 10);
       a8 = 4;
       a9 = 3;
       return -1;
     } else if((((( a14 <= -148 && ((input == 4) && ((100 < a27) && (182 >= a27)) )) && (a8==7)) && (a9==3)) && ((-178 < a21) && (-144 >= a21)) )){
      a21 = (((a21 - -244945) + 37975) - -150966);
       a8 = 6;
       a9 = 2;
       return 23;
     } else if((((a9==6) && ( a27 <= -78 && (((a8==4) && (input == 3)) && ((-148 < a14) && (13 >= a14)) ))) && a21 <= -178 )){
      if( a21 <= -178 ){
      a14 = (((a14 / 5) + -523454) - 17733);
      a21 = (((a21 - -420320) - -179731) - -2);
       a8 = 6;
      } else{
       a14 = ((((a14 + 429603) * -1)/ 10) + -303207);
       a27 = ((((a27 % 40)- -179) / 5) - -90);
       a21 = (((((a21 - 0) * 9)/ 10) % 16)+ -160);
       a8 = 6;
       a9 = 3;
      } return -1;
     } else if(((((a8==5) && ( ((100 < a27) && (182 >= a27)) && ((input == 6) && ((a9==4) || (a9==5))))) && a21 <= -178 ) && a14 <= -148 )){
      a27 = (((a27 + 185646) + -715924) / 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==8) && ( ((100 < a27) && (182 >= a27)) && ( ((-178 < a21) && (-144 >= a21)) && (((a9==4) || (a9==5)) && (input == 6))))) && a14 <= -148 )){
      a27 = (((a27 * 5) - 182832) - 335005);
      a21 = (((((a21 * 13)/ 10) / 5) / 5) - 285165);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && (( a27 <= -78 && ( ((-144 < a21) && (5 >= a21)) && (((a9==4) || (a9==5)) && (input == 6)))) && (a8==8)))){
      a27 = ((((a27 % 299908)- -300090) / 5) - -343907);
      a21 = (((a21 / 5) + -146) + -2);
       a8 = 7;
       a9 = 4;
       return 21;
     } else if(( a14 <= -148 && (( 5 < a21 && ( ((100 < a27) && (182 >= a27)) && (((a9==2) || (a9==3)) && (input == 1)))) && (a8==4)))){
      a27 = (((a27 / 5) * 5) + -111082);
      a21 = ((((a21 % 299911)- 300088) - 283134) - 14605);
       a9 = 2;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && ( ((-178 < a21) && (-144 >= a21)) && (( a27 <= -78 && ((input == 5) && (a9==6))) && (a8==7))))){
      a21 = (((a21 / 5) / 5) - 11);
       a8 = 4;
       a9 = 3;
       return 21;
     } else if(((a9==6) && (((a8==7) && ( ((-178 < a21) && (-144 >= a21)) && ((input == 2) && a14 <= -148 ))) && ((100 < a27) && (182 >= a27)) ))){
      a27 = ((((a27 * 10)/ 19) - -2) - -2);
      a21 = (((a21 * 5) - -348574) + 237846);
       a8 = 5;
       a9 = 5;
       return 23;
     } else if((( a21 <= -178 && ( ((-78 < a27) && (100 >= a27)) && ( a14 <= -148 && (((a9==3) || (a9==4)) && (input == 1))))) && (a8==7))){
      a27 = ((((a27 % 40)- -141) - 1) + 0);
      a21 = (((((a21 % 74)+ 1) + 4) + 88329) + -88330);
       a8 = 6;
       a9 = 5;
       return 21;
     } else if(( ((-148 < a14) && (13 >= a14)) && ((((a9==2) && ( a27 <= -78 && (input == 4))) && 5 < a21 ) && (a8==4)))){
      a14 = (((((a14 + -553116) + 569023) * 5) * -1)/ 10);
      a27 = ((((a27 % 299908)+ 300090) - -252698) / 5);
      a21 = (((((a21 % 16)+ -170) - 2) / 5) - 136);
       a8 = 7;
       return -1;
     } else if(((((((((a9==5) && ((-144 < a21) && (5 >= a21)) ) || ( ((-144 < a21) && (5 >= a21)) && (a9==6))) || ( 5 < a21 && (a9==2))) && (input == 6)) && (a8==5)) && a14 <= -148 ) && 182 < a27 )){
      a27 = ((((a27 - 600117) + -10) / 5) - 87370);
      a21 = (((((a21 % 299911)- 300088) - -415498) * 1) + -415499);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((((((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ((a9==2) && ((-144 < a21) && (5 >= a21)) )) && (input == 6)) && a27 <= -78 ) && ((-148 < a14) && (13 >= a14)) ) && (a8==4))){
      a14 = (((((a14 * 5) * 5) - -347605) * -1)/ 10);
      a21 = (((a21 - 420645) * 1) + -164537);
       a8 = 5;
       a9 = 5;
       return -1;
     } else if((((( ((-178 < a21) && (-144 >= a21)) && ((input == 3) && a14 <= -148 )) && ((-78 < a27) && (100 >= a27)) ) && (a8==5)) && (a9==4))){
      a27 = (((a27 - 507535) / 5) / 5);
      a21 = ((((a21 - 98583) * 10)/ 9) * 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((a8==4) && (( ((100 < a27) && (182 >= a27)) && ((input == 6) && (a9==2))) && a21 <= -178 )))){
      a27 = (((a27 - 112238) - -112128) + 1);
      a21 = ((((a21 * 9)/ 10) - -581477) * 1);
       a8 = 8;
       a9 = 4;
       return 23;
     } else if(((((((input == 1) && (((a9==2) || (a9==3)) || (a9==4))) && a27 <= -78 ) && ((-144 < a21) && (5 >= a21)) ) && (a8==7)) && ((-148 < a14) && (13 >= a14)) )){
      a14 = ((((a14 + 462367) / 5) - -477142) - 1167260);
      a21 = ((((a21 + -587720) + 59401) - 67745) + 734540);
       a8 = 6;
       a9 = 2;
       return 23;
     } else if(( ((-148 < a14) && (13 >= a14)) && (((((a8==4) && (input == 5)) && (a9==3)) && a27 <= -78 ) && 5 < a21 ))){
      if( a14 <= -148 ){
      a14 = (((a14 * 5) / 5) - 504958);
      a21 = ((((((a21 % 74)- 112) * 10)/ 9) + 168909) + -168877);
       a8 = 5;
       a9 = 2;
      } else{
       a14 = (((a14 * 5) / 5) + -572458);
       a27 = ((((((a27 % 40)+ 154) * 10)/ 9) - 144336) + 144332);
       a21 = ((((a21 % 299911)+ -300088) / 5) + -58946);
       a9 = 4;
      } return 21;
     } else if(((a8==5) && ( ((-178 < a21) && (-144 >= a21)) && ((( 182 < a27 && (input == 1)) && (a9==3)) && a14 <= -148 )))){
      a27 = (((a27 - 600140) - 35) - 8);
      a21 = ((((a21 + 304760) * 1) * 10)/ -9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((((input == 4) && ((((a9==6) && ((-144 < a21) && (5 >= a21)) ) || ((a9==2) && 5 < a21 )) || ( 5 < a21 && (a9==3)))) && (a8==5)) && a27 <= -78 ) && ((-148 < a14) && (13 >= a14)) )){
      if((a9==5)){
      a14 = (((a14 - 107493) - -229361) + -391263);
      a21 = (((((a21 / 5) + 430837) * 1) % 74)+ -96);
       a8 = 4;
       a9 = 3;
      } else{
       a14 = ((((a14 - -286677) + -368427) + 567673) + -650816);
       a27 = (((((a27 % 40)- -154) * 5) % 40)- -108);
       a21 = ((((((a21 * 9)/ 10) % 74)- 68) - 287045) + 287043);
       a8 = 4;
       a9 = 2;
      } return -1;
     } else if(( a14 <= -148 && ((a9==4) && ((a8==4) && (( 182 < a27 && (input == 4)) && 5 < a21 ))))){
      a27 = ((((((a27 % 88)+ 4) + -73) * 5) % 88)- -11);
       a8 = 8;
       a9 = 5;
       return 25;
     } else if(( a14 <= -148 && (((a8==7) && ( a21 <= -178 && ((a9==3) && (input == 3)))) && a27 <= -78 ))){
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( a14 <= -148 && (((input == 6) && ((a9==5) || (a9==6))) && 182 < a27 )) && ((-178 < a21) && (-144 >= a21)) ) && (a8==7))){
      a27 = ((((a27 - 82626) % 88)- -11) + -1);
      a21 = ((((a21 - 25711) * -1)/ 10) * 5);
       a8 = 8;
       a9 = 4;
       return -1;
     } else if((( ((-144 < a21) && (5 >= a21)) && (((((a9==3) || (a9==4)) && (input == 6)) && ((-78 < a27) && (100 >= a27)) ) && a14 <= -148 )) && (a8==4))){
      a27 = ((((a27 + 579002) * 1) + 9739) - 1120860);
      a21 = (((a21 - 424955) / 5) - 393166);
       a9 = 2;
       return -1;
     } else if(( a27 <= -78 && ((a8==7) && ( a14 <= -148 && ( 5 < a21 && (((a9==4) || (a9==5)) && (input == 1))))))){
      a21 = ((((a21 % 299911)+ -300088) / 5) - 161457);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a9==5) && (( ((-144 < a21) && (5 >= a21)) && ((a8==7) && (input == 4))) && a27 <= -78 )) && ((-148 < a14) && (13 >= a14)) )){
      a14 = (((a14 / 5) - 580922) + -12563);
      a27 = (((((a27 / 5) * 4) + -80074) % 40)+ 167);
      a21 = (((a21 - -567350) - -21945) + 2047);
       a8 = 8;
       a9 = 3;
       return -1;
     } else if((((( ((-144 < a21) && (5 >= a21)) && ((input == 4) && ((a9==4) || (a9==5)))) && ((-148 < a14) && (13 >= a14)) ) && a27 <= -78 ) && (a8==6))){
      a14 = ((((a14 + -66933) - 313712) - -829316) - 969511);
      a27 = ((((a27 % 88)+ 53) - -16) + -31);
      a21 = (((a21 - -558798) + 5473) / 5);
       a9 = 5;
       return -1;
     } else if((( a14 <= -148 && ( ((100 < a27) && (182 >= a27)) && ((( a21 <= -178 && (a9==6)) || ( ((-178 < a21) && (-144 >= a21)) && (a9==2))) && (input == 2)))) && (a8==7))){
      a27 = (((((a27 * -1)/ 10) + 267041) - 390323) - -123353);
      a21 = ((((a21 - -600029) - 353264) * 1) - -353264);
       a8 = 8;
       a9 = 4;
       return -1;
     } else if((( ((-78 < a27) && (100 >= a27)) && (((((a9==5) || (a9==6)) && (input == 2)) && (a8==8)) && 5 < a21 )) && a14 <= -148 )){
      if( ((-148 < a14) && (13 >= a14)) ){
      a27 = (((((a27 % 40)- -141) + 2) / 5) - -104);
      a21 = ((((((a21 % 74)- 106) * 10)/ 9) * 10)/ 9);
       a8 = 7;
       a9 = 5;
      } else{
       a27 = (((a27 - -536580) + 14739) + -501558);
       a8 = 4;
       a9 = 4;
      } return 23;
     } else if((( ((-144 < a21) && (5 >= a21)) && ((a9==6) && (((input == 4) && (a8==6)) && ((100 < a27) && (182 >= a27)) ))) && a14 <= -148 )){
       return -1;
     } else if((( 5 < a21 && (((a8==4) && ((input == 2) && (((a9==4) || (a9==5)) || (a9==6)))) && a14 <= -148 )) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((a27 + -462350) - 130261) - 340);
      a21 = (((((a21 + 0) * 9)/ 10) - 491227) - 73786);
       a9 = 2;
       return -1;
     } else if((( 182 < a27 && ( a14 <= -148 && ((input == 6) && ((( a21 <= -178 && (a9==5)) || ( a21 <= -178 && (a9==6))) || ( ((-178 < a21) && (-144 >= a21)) && (a9==2)))))) && (a8==5))){
      a27 = (((((a27 + 0) / 5) * 4) % 88)- -2);
      a21 = (((((a21 * 9)/ 10) * 1) * -1)/ 10);
       a8 = 8;
       a9 = 4;
       return 21;
     } else if(((((((( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ((a9==2) && ((-144 < a21) && (5 >= a21)) )) || ((a9==3) && ((-144 < a21) && (5 >= a21)) )) && (input == 3)) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 ) && (a8==6))){
      a21 = (((a21 / 5) + -233565) * 2);
       a8 = 4;
       a9 = 3;
       return -1;
     } else if((((( ((-144 < a21) && (5 >= a21)) && (((a9==4) || (a9==5)) && (input == 5))) && a27 <= -78 ) && ((-148 < a14) && (13 >= a14)) ) && (a8==5))){
      if( ((13 < a14) && (182 >= a14)) ){
      a14 = (((a14 + -345896) + -210970) + -2947);
       a8 = 6;
       a9 = 6;
      } else{
       a14 = (((a14 + -473468) + -44243) * 1);
       a8 = 6;
       a9 = 3;
      } return -1;
     } else if((((((((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ((a9==2) && ((-144 < a21) && (5 >= a21)) )) && (input == 6)) && (a8==6)) && ((-78 < a27) && (100 >= a27)) ) && a14 <= -148 )){
      a27 = (((a27 - 472368) * 1) + -78877);
      a21 = (((a21 + -234097) - 71016) - 208744);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((a8==5) && (( ((-78 < a27) && (100 >= a27)) && ((input == 5) && ((a9==3) || (a9==4)))) && ((-144 < a21) && (5 >= a21)) )))){
      a27 = ((((a27 - 167597) * 10)/ 9) - 224636);
      a21 = (((a21 + -570466) + -9579) + -11574);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==6) && ( 182 < a27 && ((input == 5) && ((((a9==5) && a21 <= -178 ) || ( a21 <= -178 && (a9==6))) || ((a9==2) && ((-178 < a21) && (-144 >= a21)) ))))) && a14 <= -148 )){
      a27 = (((a27 + -600168) - 3) * 1);
      a21 = ((((a21 % 299911)+ -178) - 75702) + -58584);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((-148 < a14) && (13 >= a14)) && (((a8==7) && ((input == 4) && a27 <= -78 )) && 5 < a21 )) && (a9==3))){
      if( ((100 < a27) && (182 >= a27)) ){
      a14 = (((a14 - 394838) - 59903) * 1);
       a8 = 5;
       a9 = 2;
      } else{
       a14 = (((a14 * 5) + -173342) * 3);
       a21 = ((((((a21 % 74)- 82) * 9)/ 10) - 30629) + 30587);
       a8 = 6;
      } return 21;
     } else if(( a27 <= -78 && ( a14 <= -148 && (( a21 <= -178 && ((input == 3) && (((a9==4) || (a9==5)) || (a9==6)))) && (a8==7))))){
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==7) && ( a14 <= -148 && ( ((-78 < a27) && (100 >= a27)) && ((((a9==2) && ((-178 < a21) && (-144 >= a21)) ) || (((a9==5) && a21 <= -178 ) || ( a21 <= -178 && (a9==6)))) && (input == 4)))))){
      a27 = (((a27 / 5) / 5) - -104);
      a21 = ((((a21 * 9)/ 10) - -121232) + 434303);
       a8 = 6;
       a9 = 6;
       return 21;
     } else if(( 5 < a21 && ((((((a9==4) || (a9==5)) && (input == 2)) && ((-78 < a27) && (100 >= a27)) ) && a14 <= -148 ) && (a8==7)))){
      a27 = (((a27 - 357996) + -42433) * 1);
      a21 = ((((a21 * 9)/ 10) / 5) - 208864);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( 182 < a27 && (((((a9==6) && (a8==5)) && 5 < a21 ) || (((a9==2) && (a8==6)) && a21 <= -178 )) && (input == 5))))){
      a27 = (((((a27 - 0) * 9)/ 10) * -5)/ 10);
      a21 = (((((a21 % 299911)- 300088) * 1) + 107506) - 107506);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==6) && (( a21 <= -178 && ( a14 <= -148 && (((a9==2) || (a9==3)) && (input == 6)))) && ((100 < a27) && (182 >= a27)) ))){
      a27 = (((a27 / 5) / 5) + -365545);
      a21 = (((((a21 % 16)+ -145) / 5) / 5) - 167);
       a8 = 7;
       a9 = 3;
       return 25;
     } else if(( a14 <= -148 && ((((a8==8) && ((((a9==2) || (a9==3)) || (a9==4)) && (input == 1))) && 5 < a21 ) && 182 < a27 ))){
      a27 = ((((a27 % 88)- 29) / 5) + -58);
      a21 = (((((a21 * 9)/ 10) + -282472) % 16)+ -161);
       a8 = 5;
       a9 = 2;
       return -1;
     } else if(((a8==5) && ( a14 <= -148 && ( 5 < a21 && (((input == 6) && ((a9==2) || (a9==3))) && ((100 < a27) && (182 >= a27)) ))))){
      a21 = (((((a21 * 9)/ 10) + -362076) % 16)- 161);
       a8 = 4;
       a9 = 6;
       return -1;
     } else if((( ((-178 < a21) && (-144 >= a21)) && ((a9==2) && (((input == 1) && a14 <= -148 ) && a27 <= -78 ))) && (a8==8))){
      a27 = (((((((a27 * 9)/ 10) % 88)- -13) * 5) % 88)+ 12);
      a21 = ((((a21 + -248552) * -1)/ 10) * 5);
       a8 = 4;
       return 21;
     } else if((((( ((-148 < a14) && (13 >= a14)) && ((input == 4) && ((-144 < a21) && (5 >= a21)) )) && (a8==5)) && (a9==3)) && a27 <= -78 )){
      a21 = ((((((a21 + 174935) % 16)- 173) / 5) * 49)/ 10);
       a8 = 7;
       a9 = 6;
       return 21;
     } else if((( ((100 < a27) && (182 >= a27)) && ((input == 6) && (( a21 <= -178 && ((a8==5) && (a9==2))) || (( 5 < a21 && ((a8==4) && (a9==5))) || (((a9==6) && (a8==4)) && 5 < a21 ))))) && a14 <= -148 )){
      a27 = (((a27 * 5) - 552091) - 32227);
      a21 = (((((a21 * 9)/ 10) - 13604) / 5) - 249746);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && ((a8==4) && ((( a21 <= -178 && (input == 4)) && (a9==3)) && a14 <= -148 )))){
      a27 = (((a27 * 5) * 5) + -271157);
      a21 = (((a21 + 570530) - -29604) - -25);
       a8 = 8;
       a9 = 5;
       return 25;
     } else if(( ((-78 < a27) && (100 >= a27)) && ( a21 <= -178 && ( a14 <= -148 && (((input == 3) && (((a9==2) || (a9==3)) || (a9==4))) && (a8==4)))))){
      a27 = (((a27 + -193396) - -630161) - 511706);
       a9 = 2;
       return -1;
     } else if(((a8==6) && ( ((-78 < a27) && (100 >= a27)) && ( a14 <= -148 && ((input == 4) && (( 5 < a21 && (a9==2)) || (((a9==5) && ((-144 < a21) && (5 >= a21)) ) || ( ((-144 < a21) && (5 >= a21)) && (a9==6))))))))){
      a27 = (((((a27 * 5) % 40)- -142) / 5) + 118);
      a21 = ((((a21 % 74)+ -69) / 5) - -2);
       a8 = 5;
       a9 = 5;
       return 23;
     } else if(((( a14 <= -148 && ( a21 <= -178 && ((input == 6) && ((a9==3) || (a9==4))))) && (a8==6)) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((a27 + -466420) * 1) - 48106);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a27 <= -78 && ( ((-148 < a14) && (13 >= a14)) && (((( 5 < a21 && ((a8==5) && (a9==6))) || (((a9==2) && (a8==6)) && a21 <= -178 )) || (((a8==6) && (a9==3)) && a21 <= -178 )) && (input == 4))))){
      a14 = (((a14 + -48374) + -57215) * 5);
      a27 = (((((a27 * 9)/ 10) + 456321) * 1) + 112001);
      a21 = ((((a21 % 74)+ -68) + -1) - -1);
       a8 = 5;
       a9 = 6;
       return -1;
     } else if(( a14 <= -148 && ( ((100 < a27) && (182 >= a27)) && (((( ((-144 < a21) && (5 >= a21)) && (a9==2)) || (((a9==5) && ((-178 < a21) && (-144 >= a21)) ) || ( ((-178 < a21) && (-144 >= a21)) && (a9==6)))) && (input == 2)) && (a8==5))))){
      a27 = (((a27 * 5) + -347497) * 1);
      a21 = (((a21 - 409199) - 105846) - 53996);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((100 < a27) && (182 >= a27)) && ((((input == 2) && ((a9==4) || (a9==5))) && a14 <= -148 ) && (a8==7))) && ((-178 < a21) && (-144 >= a21)) )){
      a27 = (((((a27 * -8)/ 10) - -284497) / 5) + -195304);
      a21 = (((a21 + -32947) * 5) * 3);
       a8 = 6;
       a9 = 5;
       return -1;
     } else if((((( ((-144 < a21) && (5 >= a21)) && (((a9==3) || (a9==4)) && (input == 2))) && a14 <= -148 ) && ((-78 < a27) && (100 >= a27)) ) && (a8==6))){
      a27 = (((a27 * 5) - 420711) * 1);
      a21 = (((a21 + -232437) * 2) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a21 <= -178 && ((((a8==8) && (((a9==2) || (a9==3)) && (input == 2))) && a14 <= -148 ) && 182 < a27 ))){
      a27 = ((((a27 + 0) + -353399) * 1) + -246690);
       a8 = 6;
       a9 = 3;
       return 23;
     } else if(((a8==7) && ((( ((-148 < a14) && (13 >= a14)) && ((input == 6) && a21 <= -178 )) && (a9==4)) && a27 <= -78 ))){
      if( 182 < a14 ){
      a14 = ((((a14 - -586035) - -4886) - 446160) - 645991);
      a21 = ((((a21 + 0) + 0) % 16)- 157);
       a8 = 5;
      } else{
       a14 = ((((a14 + 455602) * -1)/ 10) * 5);
       a27 = (((((((a27 % 40)+ 164) * 10)/ 9) * 5) % 40)- -139);
       a8 = 4;
       a9 = 3;
      } return 21;
     } else if((((( 5 < a21 && ((( 182 < a27 && a14 <= -148 ) && (a8==8)) && (a9==5))) || (((a9==6) && (( a14 <= -148 && 182 < a27 ) && (a8==8))) && 5 < a21 )) || ( a21 <= -178 && (((a8==4) && ( a27 <= -78 && ((-148 < a14) && (13 >= a14)) )) && (a9==2)))) && (input == 2))){
      a14 = ((((a14 % 299926)+ -300073) - 1) + -1);
      a27 = ((((a27 % 299961)+ -300038) + 0) - 2);
      a21 = (((((a21 + 0) * 9)/ 10) % 16)+ -161);
       a8 = 5;
       a9 = 2;
       return -1;
     } else if(( a21 <= -178 && ((( a14 <= -148 && ((input == 5) && a27 <= -78 )) && (a8==8)) && (a9==4)))){
      a27 = ((((a27 % 40)- -151) - -368972) - 368949);
      a21 = ((((a21 - 0) - -150097) % 16)- 160);
       a8 = 7;
       a9 = 6;
       return 21;
     } else if(((( a21 <= -178 && ((a9==2) && ((a8==4) && ( a27 <= -78 && ((-148 < a14) && (13 >= a14)) )))) || (( 5 < a21 && ((( 182 < a27 && a14 <= -148 ) && (a8==8)) && (a9==5))) || ( 5 < a21 && ((a9==6) && (( 182 < a27 && a14 <= -148 ) && (a8==8)))))) && (input == 6))){
      a14 = (((((a14 * 9)/ 10) + 3980) % 80)+ -67);
      a27 = (((((a27 + 0) * 9)/ 10) % 299961)- 300038);
      a21 = (((((a21 + 0) / 5) / 5) % 74)- 69);
       a8 = 4;
       a9 = 4;
       return -1;
     } else if((((a8==4) && ((a9==2) && (( a14 <= -148 && (input == 4)) && 5 < a21 ))) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((a27 / 5) + 196173) * 3);
      a21 = ((((a21 - 320377) / 5) % 16)+ -160);
       a8 = 5;
       a9 = 5;
       return 21;
     } else if(((((a8==4) && ( ((-148 < a14) && (13 >= a14)) && (((a9==3) || (a9==4)) && (input == 1)))) && ((-144 < a21) && (5 >= a21)) ) && a27 <= -78 )){
      a14 = ((((a14 + 97256) * -1)/ 10) / 5);
      a27 = ((((a27 + 0) / 5) / 5) - -523284);
      a21 = (((((a21 % 16)+ -159) / 5) - 519675) - -519556);
       a8 = 5;
       a9 = 3;
       return -1;
     }
     return calculate_output5(input);
 }
 int calculate_output5(int input) {
     if((((( a14 <= -148 && ((((a9==4) || (a9==5)) || (a9==6)) && (input == 6))) && (a8==7)) && 5 < a21 ) && 182 < a27 )){
      if( ((-144 < a21) && (5 >= a21)) ){
      a27 = ((((a27 + -291743) * 1) % 88)- -11);
      a21 = ((((a21 - 398497) % 299911)- 300088) + -1);
       a8 = 4;
       a9 = 5;
      } else{
       a27 = ((((a27 + 0) - 0) % 40)- -118);
       a21 = (((((a21 % 74)- 135) - -14) - -441618) - 441581);
       a8 = 4;
       a9 = 2;
      } return -1;
     } else if(( a14 <= -148 && ((((input == 4) && ((( ((-178 < a21) && (-144 >= a21)) && (a9==5)) || ((a9==6) && ((-178 < a21) && (-144 >= a21)) )) || ((a9==2) && ((-144 < a21) && (5 >= a21)) ))) && (a8==4)) && 182 < a27 ))){
      a27 = (((((a27 * 9)/ 10) * -5)/ 10) * 2);
      a21 = ((((a21 % 74)+ -69) + 359841) + -359841);
       a8 = 7;
       a9 = 4;
       return 25;
     } else if(((a8==7) && ( ((-148 < a14) && (13 >= a14)) && ( a27 <= -78 && ((input == 5) && ((( a21 <= -178 && (a9==5)) || ( a21 <= -178 && (a9==6))) || ((a9==2) && ((-178 < a21) && (-144 >= a21)) ))))))){
      a14 = ((((a14 - 184571) + -135284) * 10)/ 9);
      a27 = (((((a27 % 88)- -21) + 445962) - 680992) - -235081);
      a21 = (((a21 + 600093) + 9) - -25);
       a8 = 5;
       a9 = 3;
       return -1;
     } else if(( 182 < a27 && (((((((a9==4) || (a9==5)) || (a9==6)) && (input == 2)) && (a8==7)) && 5 < a21 ) && a14 <= -148 ))){
      if( ((-78 < a27) && (100 >= a27)) ){
      a27 = ((((a27 / 5) * 10)/ -4) * 1);
      a21 = ((((a21 / 5) % 16)- 167) + -9);
       a8 = 4;
       a9 = 3;
      } else{
       a21 = (((((a21 % 74)+ -84) + -11) - -441728) - 441746);
       a8 = 8;
       a9 = 3;
      } return -1;
     } else if((( a14 <= -148 && ((((input == 6) && (((a9==4) || (a9==5)) || (a9==6))) && (a8==7)) && ((-78 < a27) && (100 >= a27)) )) && ((-178 < a21) && (-144 >= a21)) )){
      a27 = ((((a27 + -241632) + 384359) * -1)/ 10);
      a21 = (((((a21 * 13)/ 10) - 432303) * 10)/ 9);
       a8 = 5;
       a9 = 5;
       return -1;
     } else if(( a14 <= -148 && ((a8==8) && ((((input == 4) && 5 < a21 ) && (a9==6)) && a27 <= -78 )))){
      a21 = ((((a21 * 9)/ 10) + -556805) / 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( ((-144 < a21) && (5 >= a21)) && ( ((-78 < a27) && (100 >= a27)) && ((a8==6) && (((a9==3) || (a9==4)) && (input == 1))))))){
      a27 = ((((((a27 % 40)- -140) * 5) + -67106) % 40)- -141);
       a8 = 5;
       a9 = 3;
       return 25;
     } else if((((a8==5) && ( a14 <= -148 && ((((a9==3) || (a9==4)) && (input == 2)) && ((-178 < a21) && (-144 >= a21)) ))) && ((100 < a27) && (182 >= a27)) )){
      a27 = (((a27 - 48407) + -270227) / 5);
      a21 = ((((a21 - 341445) - -688512) / 5) + -152263);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a9==3) && (( ((-148 < a14) && (13 >= a14)) && ((a8==4) && ( a27 <= -78 && (input == 4)))) && 5 < a21 ))){
      if( ((13 < a14) && (182 >= a14)) ){
      a14 = (((a14 - -62813) + -547288) + -59093);
      a21 = ((((((a21 * 9)/ 10) * 1) - 504085) % 16)- 161);
      } else{
       a14 = ((((a14 - 438932) * 1) * 10)/ 9);
       a21 = (((((a21 - 0) % 74)- 91) + -352311) - -352296);
       a9 = 5;
      } return 23;
     } else if((((a8==7) && (( 182 < a27 && ((input == 2) && (a9==5))) && a14 <= -148 )) && a21 <= -178 )){
      a27 = (((((a27 + -147604) % 40)+ 141) + -40578) + 40577);
      a21 = ((((a21 * -1)/ 10) + 122534) - -379839);
       a8 = 4;
       a9 = 4;
       return 21;
     } else if(( ((-144 < a21) && (5 >= a21)) && ( a27 <= -78 && ((a8==6) && (((input == 3) && ((a9==4) || (a9==5))) && ((-148 < a14) && (13 >= a14)) ))))){
      a14 = (((a14 + -75060) - 340104) + -157155);
      a21 = ((((((a21 - 220470) % 16)+ -156) * 5) % 16)+ -145);
       a8 = 4;
       a9 = 6;
       return -1;
     } else if(( ((-178 < a21) && (-144 >= a21)) && (( a27 <= -78 && ((((a9==6) || ((a9==4) || (a9==5))) && (input == 2)) && (a8==7))) && a14 <= -148 ))){
      a21 = (((a21 * 5) * 5) + -243705);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( a14 <= -148 && (((input == 2) && (a8==7)) && (a9==3))) && ((-78 < a27) && (100 >= a27)) ) && 5 < a21 )){
      a27 = (((a27 + -129682) + 113676) * 5);
      a21 = ((((a21 * 9)/ 10) + -555566) + -8255);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a14 <= -148 && ( 182 < a27 && ((a8==4) && (((a9==3) || (a9==4)) && (input == 6))))) && ((-178 < a21) && (-144 >= a21)) )){
      a27 = (((((a27 - 600094) + -43) / 5) * 29)/ 10);
      a21 = ((((a21 * 10)/ 8) * 5) / 5);
       a9 = 2;
       return -1;
     } else if((( a27 <= -78 && ( ((-178 < a21) && (-144 >= a21)) && ( ((-148 < a14) && (13 >= a14)) && ((a8==4) && (input == 5))))) && (a9==5))){
      a14 = (((a14 * 5) - 504056) - 65277);
      a27 = ((((((a27 - -249402) % 40)+ 141) * 5) % 40)+ 122);
      a21 = (((a21 / 5) - 66993) + -174504);
       a8 = 6;
       a9 = 3;
       return -1;
     } else if(((a9==5) && (( a21 <= -178 && ( ((100 < a27) && (182 >= a27)) && ((input == 3) && a14 <= -148 ))) && (a8==4)))){
      a27 = (((((a27 * 10)/ -9) * 10)/ 9) - 21434);
       a9 = 2;
       return -1;
     } else if((( a14 <= -148 && ( 182 < a27 && ((a8==8) && (((a9==2) || (a9==3)) && (input == 1))))) && a21 <= -178 )){
      a14 = ((((((a14 % 80)- 14) * 10)/ 9) * 10)/ 9);
      a27 = ((((a27 - 600130) - -148490) * 1) - 148479);
      a21 = (((((a21 + 0) / 5) * 4) * -1)/ 10);
       a8 = 6;
       a9 = 2;
       return 21;
     } else if(( a14 <= -148 && ((a9==3) && ((((input == 4) && a21 <= -178 ) && (a8==5)) && 182 < a27 )))){
      a27 = ((((((a27 % 88)- -12) * 9)/ 10) - 573347) + 573289);
       a8 = 4;
       a9 = 6;
       return -1;
     } else if(( ((-178 < a21) && (-144 >= a21)) && ((( a27 <= -78 && ((input == 1) && (((a9==3) || (a9==4)) || (a9==5)))) && (a8==7)) && ((-148 < a14) && (13 >= a14)) ))){
      if( 182 < a27 ){
      a14 = (((a14 - 280341) * 2) * 1);
      a27 = (((((a27 % 40)+ 178) * 5) % 40)- -106);
      a21 = (((a21 - 276422) / 5) * 5);
       a8 = 8;
       a9 = 2;
      } else{
       a14 = (((a14 + 74616) / 5) - 366659);
       a21 = (((a21 + -20958) - 444332) - 23355);
       a8 = 4;
       a9 = 2;
      } return -1;
     } else if(((a8==6) && ( a27 <= -78 && (( 5 < a21 && ((input == 4) && ((a9==3) || (a9==4)))) && ((-148 < a14) && (13 >= a14)) )))){
      if( ((100 < a27) && (182 >= a27)) ){
      a14 = (((a14 - -140240) + 270841) - 574890);
      a27 = ((((a27 % 299908)- -300090) - -124980) * 1);
       a8 = 8;
       a9 = 6;
      } else{
       a14 = (((a14 + -300057) / 5) - 276500);
       a21 = ((((a21 % 299911)+ -300088) * 1) + -297551);
       a8 = 4;
       a9 = 5;
      } return -1;
     } else if((( ((-178 < a21) && (-144 >= a21)) && ((((a8==4) && (input == 6)) && a27 <= -78 ) && (a9==5))) && ((-148 < a14) && (13 >= a14)) )){
      a14 = (((a14 / 5) / 5) - 381009);
      a21 = ((((a21 + 67) * 10)/ 9) + 87);
       a8 = 5;
       return 21;
     } else if(( a14 <= -148 && ( ((100 < a27) && (182 >= a27)) && ((a8==5) && ((input == 6) && (( a21 <= -178 && (a9==6)) || ( ((-178 < a21) && (-144 >= a21)) && (a9==2)))))))){
      a27 = ((((a27 * 5) * -2)/ 10) - 480041);
      a21 = ((((a21 + 452978) % 299911)- 300088) + -2);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((((input == 5) && (a9==2)) && ((-144 < a21) && (5 >= a21)) ) && a14 <= -148 ) && ((100 < a27) && (182 >= a27)) ) && (a8==7))){
      a27 = (((a27 + 60646) + -192265) / 5);
      a21 = (((a21 - -310294) * 1) * 1);
       a8 = 8;
       a9 = 6;
       return 21;
     } else if(( ((100 < a27) && (182 >= a27)) && (((a8==5) && ((input == 3) && (( a21 <= -178 && (a9==6)) || ((a9==2) && ((-178 < a21) && (-144 >= a21)) )))) && a14 <= -148 ))){
      if((a8==8)){
      a27 = ((((a27 + -200985) / 5) + -287784) - -793089);
      a21 = (((a21 + 61891) / 5) - -555828);
       a8 = 4;
       a9 = 5;
      } else{
       a27 = (((((a27 + 395704) + 101649) - -23624) * -1)/ 10);
       a21 = (((((a21 % 299911)+ -178) - -313247) * -1)/ 10);
       a8 = 8;
       a9 = 4;
      } return -1;
     } else if(( a27 <= -78 && ( ((-178 < a21) && (-144 >= a21)) && ((a8==7) && ( ((-148 < a14) && (13 >= a14)) && ((((a9==3) || (a9==4)) || (a9==5)) && (input == 2))))))){
      a14 = (((a14 * 5) + -8623) / 5);
       a8 = 4;
       a9 = 5;
       return 21;
     } else if(( ((-148 < a14) && (13 >= a14)) && (( a27 <= -78 && (((input == 2) && (a9==2)) && (a8==4))) && 5 < a21 ))){
      a14 = (((a14 - 149296) - 263416) * 1);
      a21 = ((((a21 % 299911)+ -300088) - 40161) + 35049);
       a8 = 5;
       a9 = 4;
       return -1;
     } else if((((((((a9==2) || (a9==3)) && (input == 6)) && a14 <= -148 ) && ((-178 < a21) && (-144 >= a21)) ) && (a8==7)) && a27 <= -78 )){
      a21 = (((a21 + -570451) * 1) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==4) && ((a9==4) && (( a14 <= -148 && ((input == 6) && ((100 < a27) && (182 >= a27)) )) && 5 < a21 )))){
      if( 5 < a21 ){
      a27 = (((a27 - -65636) * 5) * 1);
      a21 = ((((a21 + -61917) % 299911)- 300088) + -1);
       a8 = 7;
       a9 = 5;
      } else{
       a27 = (((a27 + -239620) / 5) + 47977);
       a21 = ((((a21 - 593302) / 5) % 16)- 159);
       a8 = 6;
       a9 = 3;
      } return -1;
     } else if(((( a14 <= -148 && ((input == 2) && ((((a9==5) && ((-178 < a21) && (-144 >= a21)) ) || ( ((-178 < a21) && (-144 >= a21)) && (a9==6))) || ( ((-144 < a21) && (5 >= a21)) && (a9==2))))) && (a8==4)) && 182 < a27 )){
      a27 = ((((a27 + -600132) - -139354) + -91825) + -47511);
      a21 = ((((a21 + 555168) * -1)/ 10) - 314537);
       a9 = 2;
       return -1;
     } else if(((((a8==6) && ((((a9==2) && ((-178 < a21) && (-144 >= a21)) ) || (((a9==5) && a21 <= -178 ) || ((a9==6) && a21 <= -178 ))) && (input == 6))) && 182 < a27 ) && a14 <= -148 )){
      a27 = ((((a27 + -600125) + -50) - -457687) + -457647);
      a21 = ((((a21 * 9)/ 10) + -12669) / 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((a8==6) && ( ((100 < a27) && (182 >= a27)) && ( ((-144 < a21) && (5 >= a21)) && (input == 1)))) && a14 <= -148 ) && (a9==6))){
      a27 = ((((a27 - -57500) / 5) / 5) + -574178);
      a21 = ((((a21 + -155844) + 859) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==6) && ( ((-178 < a21) && (-144 >= a21)) && ( 182 < a27 && ((input == 6) && ((a9==3) || (a9==4)))))) && a14 <= -148 )){
      a27 = (((a27 - 0) - 600085) - 22);
      a21 = (((a21 - 320678) - 51601) - -137965);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((( ((100 < a27) && (182 >= a27)) && (((a9==5) || ((a9==3) || (a9==4))) && (input == 2))) && ((-178 < a21) && (-144 >= a21)) ) && (a8==6)))){
      a27 = (((a27 + -187311) * 3) * 1);
      a21 = ((((a21 + 228352) * -1)/ 10) - 395261);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((((input == 2) && (((a9==2) || (a9==3)) || (a9==4))) && a21 <= -178 ) && a27 <= -78 ) && (a8==5)) && ((-148 < a14) && (13 >= a14)) )){
      a14 = (((a14 + -18611) * 5) / 5);
      a21 = (((((a21 % 16)- 152) * 5) % 16)+ -145);
       a8 = 6;
       a9 = 3;
       return -1;
     } else if((((((((a9==3) || (a9==4)) && (input == 5)) && a27 <= -78 ) && (a8==5)) && ((-148 < a14) && (13 >= a14)) ) && ((-178 < a21) && (-144 >= a21)) )){
       a8 = 6;
       a9 = 5;
       return -1;
     } else if((((( ((-148 < a14) && (13 >= a14)) && ((a8==7) && (input == 1))) && (a9==6)) && a27 <= -78 ) && ((-178 < a21) && (-144 >= a21)) )){
      a14 = (((a14 + -252330) - 217375) / 5);
      a21 = (((((a21 + -77409) + 530938) - 436466) * -1)/ 10);
       a8 = 6;
       return 23;
     } else if((((a9==3) && ( a27 <= -78 && (((input == 5) && ((-144 < a21) && (5 >= a21)) ) && ((-148 < a14) && (13 >= a14)) ))) && (a8==6))){
      a14 = ((((a14 / 5) / 5) / 5) - 93183);
      a21 = (((a21 - -598671) + 907) + -439821);
       a8 = 4;
       a9 = 4;
       return -1;
     } else if(((a8==8) && (( ((100 < a27) && (182 >= a27)) && ((input == 2) && ((((a9==5) && ((-144 < a21) && (5 >= a21)) ) || ((a9==6) && ((-144 < a21) && (5 >= a21)) )) || ( 5 < a21 && (a9==2))))) && a14 <= -148 ))){
      a27 = (((a27 - -474985) - -23546) + -79300);
      a21 = (((((a21 + 0) % 299911)- 300088) - -575437) - 575437);
       a8 = 7;
       a9 = 6;
       return 21;
     } else if(((a8==7) && ( a14 <= -148 && (( 182 < a27 && ((input == 5) && ((a9==3) || (a9==4)))) && a21 <= -178 )))){
      a27 = (((a27 / 5) - 394305) - 155705);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==8) && ( a14 <= -148 && ( ((-144 < a21) && (5 >= a21)) && (((a9==6) || ((a9==4) || (a9==5))) && (input == 2))))) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((a27 + -466567) * 1) / 5);
      a21 = (((((a21 - 152531) * 10)/ 9) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( ((100 < a27) && (182 >= a27)) && ((input == 5) && (( ((-144 < a21) && (5 >= a21)) && (a9==3)) || (((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ( ((-144 < a21) && (5 >= a21)) && (a9==2)))))) && a14 <= -148 ) && (a8==6))){
      a27 = ((((a27 * 10)/ -9) * 5) / 5);
      a21 = (((a21 + -236169) * 2) / 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a14 <= -148 && ( 5 < a21 && ((a8==4) && ( ((100 < a27) && (182 >= a27)) && (input == 2))))) && (a9==4))){
      a21 = (((((a21 % 299911)+ -300088) * 10)/ 9) + -358);
       a9 = 6;
       return -1;
     } else if(( a27 <= -78 && ((((a9==4) && ((input == 5) && (a8==5))) && 5 < a21 ) && ((-148 < a14) && (13 >= a14)) ))){
      a14 = (((a14 + -384408) - -7489) - 65430);
      a21 = (((((a21 % 299911)- 300088) / 5) + 283129) - 558615);
       a8 = 8;
       a9 = 6;
       return -1;
     } else if(((input == 1) && (( a21 <= -178 && ((( a27 <= -78 && ((-148 < a14) && (13 >= a14)) ) && (a8==4)) && (a9==2))) || ((((a9==5) && ((a8==8) && ( 182 < a27 && a14 <= -148 ))) && 5 < a21 ) || ((((a8==8) && ( a14 <= -148 && 182 < a27 )) && (a9==6)) && 5 < a21 ))))){
      a14 = (((a14 + 0) / 5) - 237151);
      a27 = ((((((a27 * 9)/ 10) / 5) + -354377) * -1)/ 10);
      a21 = ((((((a21 % 16)+ -161) * 5) - 341492) % 16)+ -152);
       a8 = 4;
       a9 = 2;
       return 25;
     } else if((( 182 < a27 && ((((((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ((a9==2) && ((-144 < a21) && (5 >= a21)) )) || ( ((-144 < a21) && (5 >= a21)) && (a9==3))) && (input == 1)) && (a8==5))) && a14 <= -148 )){
      a27 = (((a27 + -390734) * 1) + -209418);
      a21 = (((a21 + -79168) - 172535) + -249021);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( 5 < a21 && ( ((100 < a27) && (182 >= a27)) && (( a14 <= -148 && (input == 5)) && (a9==4)))) && (a8==8))){
      a27 = (((a27 + -555179) - 10598) - 33745);
      a21 = ((((a21 - 228489) * 1) % 299911)+ -300088);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((( a14 <= -148 && (((a9==4) || (a9==5)) && (input == 2))) && a21 <= -178 ) && (a8==5)) && ((100 < a27) && (182 >= a27)) )){
      a27 = (((((a27 - 12092) * 5) + 106136) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((-78 < a27) && (100 >= a27)) && ( a14 <= -148 && ((a8==7) && ((input == 5) && ((a9==4) || (a9==5)))))) && 5 < a21 )){
      a27 = ((((((a27 - -291611) % 40)- -141) * 5) % 40)+ 119);
      a21 = (((((a21 * 9)/ 10) % 74)- 124) + -16);
       a8 = 5;
       a9 = 2;
       return 21;
     } else if((((a8==5) && (((( ((-178 < a21) && (-144 >= a21)) && (a9==2)) || (( a21 <= -178 && (a9==5)) || ( a21 <= -178 && (a9==6)))) && (input == 5)) && a14 <= -148 )) && 182 < a27 )){
      a27 = (((a27 + -600100) + -66) - 0);
      a21 = ((((a21 % 299911)+ -178) * 1) + -79279);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((((((a9==6) || ((a9==4) || (a9==5))) && (input == 5)) && a27 <= -78 ) && ((-178 < a21) && (-144 >= a21)) ) && (a8==7)))){
      a21 = (((((a21 / 5) * 10)/ 1) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((( ((-178 < a21) && (-144 >= a21)) && (((a9==2) || (a9==3)) && (input == 6))) && a14 <= -148 ) && (a8==8)) && 182 < a27 )){
      if( ((-148 < a14) && (13 >= a14)) ){
      a27 = (((a27 - 269119) + -330974) - 28);
      a21 = (((a21 - -229108) + -229034) - -54);
       a8 = 5;
       a9 = 6;
      } else{
       a27 = ((((a27 - 600105) + -30) - -534266) - 534229);
       a21 = ((((a21 / 5) - -273656) - 571552) + 822893);
       a8 = 4;
       a9 = 2;
      } return -1;
     } else if((((((input == 3) && (( ((-144 < a21) && (5 >= a21)) && (a9==6)) || ( 5 < a21 && (a9==2)))) && ((-148 < a14) && (13 >= a14)) ) && a27 <= -78 ) && (a8==7))){
      a14 = (((a14 - 212981) - 327890) + -10902);
      a21 = ((((((a21 % 299911)- 300088) + -2) * 9)/ 10) - 47405);
       a9 = 6;
       return -1;
     } else if(((( a21 <= -178 && (((input == 1) && (a9==4)) && a14 <= -148 )) && (a8==4)) && ((100 < a27) && (182 >= a27)) )){
      a27 = (((a27 - 179774) / 5) + -216469);
       a9 = 2;
       return -1;
     } else if(((( ((-178 < a21) && (-144 >= a21)) && ( a14 <= -148 && ((a8==8) && (input == 3)))) && (a9==5)) && ((-78 < a27) && (100 >= a27)) )){
       a8 = 5;
       a9 = 4;
       return 25;
     } else if((((a8==6) && ((((((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ((a9==2) && ((-144 < a21) && (5 >= a21)) )) || ((a9==3) && ((-144 < a21) && (5 >= a21)) )) && (input == 4)) && a14 <= -148 )) && 182 < a27 )){
      a27 = (((a27 + -600084) + 165903) + -165975);
      a21 = (((a21 - 41856) / 5) / 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((((((a9==2) || (a9==3)) && (input == 2)) && (a8==5)) && ((100 < a27) && (182 >= a27)) ) && 5 < a21 ))){
      a27 = (((((a27 * 10)/ 19) * 5) % 88)+ 1);
      a21 = (((((a21 % 16)- 171) + 8) - -526447) + -526458);
       a8 = 4;
       a9 = 2;
       return 21;
     } else if((( a14 <= -148 && ((((input == 1) && ((a9==6) || ((a9==4) || (a9==5)))) && (a8==5)) && ((100 < a27) && (182 >= a27)) )) && 5 < a21 )){
      a21 = ((((a21 % 16)- 166) + -4) * 1);
       a9 = 5;
       return -1;
     } else if((( a21 <= -178 && (((a8==8) && (((a9==4) || (a9==5)) && (input == 6))) && a14 <= -148 )) && ((-78 < a27) && (100 >= a27)) )){
      if( ((-148 < a14) && (13 >= a14)) ){
      a27 = ((((a27 - 188111) - 200966) % 40)- -171);
      a21 = (((((a21 - -390102) + 34582) / 5) % 74)+ -68);
       a8 = 7;
       a9 = 4;
      } else{
       a27 = (((((a27 * 5) - -33906) / 5) % 40)+ 129);
       a21 = (((a21 / 5) * 4) - -517685);
       a8 = 4;
       a9 = 2;
      } return 21;
     } else if(( a14 <= -148 && ((((a9==6) && ( ((-178 < a21) && (-144 >= a21)) && (input == 4))) && (a8==7)) && ((100 < a27) && (182 >= a27)) ))){
      a27 = ((((a27 / 5) * 10)/ -2) + -415706);
      a21 = (((((a21 * 13)/ 10) * 5) + 556881) + -888760);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((( a14 <= -148 && ( ((-178 < a21) && (-144 >= a21)) && (input == 2))) && a27 <= -78 ) && (a9==2)) && (a8==8))){
      a27 = ((((a27 % 88)- -97) + -580853) - -580809);
      a21 = ((((a21 * -1)/ 10) * 5) - -586763);
       a8 = 4;
       a9 = 3;
       return 21;
     } else if(((a8==5) && ( 182 < a27 && ( a14 <= -148 && ( ((-178 < a21) && (-144 >= a21)) && (((a9==4) || (a9==5)) && (input == 6))))))){
      a27 = (((a27 + -600086) + -39) * 1);
      a21 = (((a21 * 5) + 24218) + -62780);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((((( 5 < a21 && (a9==2)) || (( ((-144 < a21) && (5 >= a21)) && (a9==5)) || ((a9==6) && ((-144 < a21) && (5 >= a21)) ))) && (input == 1)) && ((100 < a27) && (182 >= a27)) ) && (a8==8)))){
      a27 = (((a27 / 5) / 5) - 561412);
      a21 = ((((a21 % 299911)+ -300088) * 1) - 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((a9==2) && ( ((-178 < a21) && (-144 >= a21)) && ( a14 <= -148 && (input == 3)))) && ((-78 < a27) && (100 >= a27)) ) && (a8==4))){
      a21 = ((((a21 + 483749) - 524661) * 5) - -631792);
       a8 = 6;
       return 25;
     } else if(( a27 <= -78 && ((( ((-148 < a14) && (13 >= a14)) && (((a9==5) || (a9==6)) && (input == 6))) && a21 <= -178 ) && (a8==6)))){
      a14 = (((a14 + -216373) * 2) * 1);
      a27 = ((((a27 % 40)+ 144) + -590007) + 590021);
       a8 = 7;
       a9 = 3;
       return 25;
     } else if(((((( a21 <= -178 && ((a9==2) && (a8==6))) || (( 5 < a21 && ((a9==5) && (a8==5))) || ( 5 < a21 && ((a8==5) && (a9==6))))) && (input == 3)) && a14 <= -148 ) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((a27 + -109345) * 5) / 5);
      a21 = (((a21 / 5) + -220138) - 147933);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((-78 < a27) && (100 >= a27)) && (((input == 5) && ((( a21 <= -178 && (a9==5)) || ( a21 <= -178 && (a9==6))) || ((a9==2) && ((-178 < a21) && (-144 >= a21)) ))) && a14 <= -148 )) && (a8==6))){
      a27 = (((a27 - 67242) - 413751) * 1);
      a21 = ((((((a21 % 299911)+ -178) - -444367) * 1) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((((((a9==6) || ((a9==4) || (a9==5))) && (input == 1)) && 5 < a21 ) && a14 <= -148 ) && 182 < a27 ) && (a8==7))){
      a27 = ((((a27 % 88)+ -57) / 5) / 5);
      a21 = ((((((a21 % 74)- 88) * 10)/ 9) + -104167) + 104142);
       a8 = 5;
       a9 = 2;
       return 21;
     } else if(( ((-148 < a14) && (13 >= a14)) && ((a8==6) && ( 5 < a21 && ((((a9==5) || (a9==6)) && (input == 2)) && a27 <= -78 ))))){
      a14 = (((a14 + -73953) * 5) - 86284);
      a27 = ((((a27 % 88)- -95) / 5) + -68);
      a21 = ((((((a21 * 9)/ 10) + -130848) + -249422) % 16)+ -160);
       a8 = 7;
       a9 = 4;
       return -1;
     } else if(((a8==6) && (((((input == 4) && ((a9==2) || (a9==3))) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 ) && a21 <= -178 ))){
      a27 = (((a27 - -494881) + -428552) - 66495);
      a21 = (((a21 + 600090) - -4) * 1);
       a8 = 8;
       a9 = 6;
       return 25;
     } else if((( a14 <= -148 && (((( 5 < a21 && ((a9==6) && (a8==7))) || (((a9==2) && (a8==8)) && a21 <= -178 )) || ( a21 <= -178 && ((a8==8) && (a9==3)))) && (input == 6))) && a27 <= -78 )){
      a21 = (((((a21 * 9)/ 10) % 299997)+ 300002) + 0);
       a8 = 8;
       a9 = 5;
       return 21;
     } else if(((( a14 <= -148 && ( 5 < a21 && ((a9==5) && (input == 2)))) && (a8==8)) && a27 <= -78 )){
      a21 = (((a21 / 5) - 180026) + -156657);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && ((a8==4) && (( a14 <= -148 && ((a9==2) && (input == 4))) && ((-178 < a21) && (-144 >= a21)) )))){
      a27 = (((a27 + -166610) - 362387) + -31082);
      a21 = (((a21 - 547783) - 1616) + -29745);
       return -1;
     } else if(( a14 <= -148 && ((a8==8) && (( 182 < a27 && ((input == 2) && ((a9==2) || (a9==3)))) && ((-178 < a21) && (-144 >= a21)) )))){
      if( ((100 < a27) && (182 >= a27)) ){
      a27 = ((((a27 - 600129) - 52) / 5) - 376795);
       a8 = 4;
       a9 = 6;
      } else{
       a27 = (((a27 + -600180) * 1) * 1);
       a21 = (((a21 - -541968) + 9851) + -551718);
       a8 = 5;
       a9 = 6;
      } return 25;
     } else if(((a8==6) && ( ((100 < a27) && (182 >= a27)) && (( 5 < a21 && ((input == 6) && ((a9==5) || (a9==6)))) && a14 <= -148 )))){
      a27 = (((((a27 * 5) * -2)/ 10) / 5) - 149208);
      a21 = ((((a21 % 299911)- 300088) - -597537) + -717492);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( 5 < a21 && (( a27 <= -78 && ((a8==8) && ((input == 5) && (a9==5)))) && a14 <= -148 ))){
      a21 = (((((a21 - 586586) % 299911)- 300088) + 130759) + -130760);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && ((a8==7) && ((a9==2) && ( a14 <= -148 && ((input == 6) && a21 <= -178 )))))){
      a27 = ((((a27 % 40)- -140) - 0) + 0);
      a21 = (((((a21 - -476208) % 16)+ -159) - -177554) + -177556);
       a8 = 6;
       return 21;
     } else if((( ((-148 < a14) && (13 >= a14)) && ( a27 <= -78 && (((input == 2) && ((a9==5) || (a9==6))) && a21 <= -178 ))) && (a8==6))){
      a14 = (((a14 + -259102) * 2) * 1);
       a8 = 5;
       a9 = 2;
       return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && ((((input == 2) && (( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ((a9==2) && ((-144 < a21) && (5 >= a21)) ))) && (a8==8)) && a14 <= -148 ))){
      a27 = ((((a27 % 40)+ 142) / 5) - -144);
      a21 = (((a21 - 34772) + -178431) - 136620);
       a8 = 4;
       a9 = 3;
       return 21;
     } else if(( a14 <= -148 && ((((((a9==2) && ((-178 < a21) && (-144 >= a21)) ) || (((a9==5) && a21 <= -178 ) || ((a9==6) && a21 <= -178 ))) && (input == 1)) && (a8==6)) && 182 < a27 ))){
      a27 = (((a27 + -600100) - -265201) + -265187);
      a21 = (((a21 / 5) / 5) - 571813);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && ((a8==5) && (( a21 <= -178 && ((input == 3) && ((a9==6) || ((a9==4) || (a9==5))))) && a14 <= -148 )))){
      a27 = (((a27 * 5) * 5) + -243486);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==5) && ( 182 < a27 && ((input == 2) && (((a9==3) && ((-144 < a21) && (5 >= a21)) ) || (( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ( ((-144 < a21) && (5 >= a21)) && (a9==2))))))) && a14 <= -148 )){
      a27 = (((a27 / 5) + -311372) * 1);
      a21 = (((a21 * 5) + -158206) + -336495);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( 182 < a27 && (( a21 <= -178 && ((input == 6) && (((a9==2) || (a9==3)) || (a9==4)))) && a14 <= -148 )) && (a8==4))){
      a27 = ((((a27 - 600132) - 5) - -497322) + -497328);
       a9 = 2;
       return -1;
     } else if(( a21 <= -178 && (( a14 <= -148 && ( ((-78 < a27) && (100 >= a27)) && (((a9==5) || (a9==6)) && (input == 6)))) && (a8==4)))){
      a27 = (((a27 * 5) - -63256) + -171101);
       a9 = 2;
       return -1;
     } else if(((((( ((-148 < a14) && (13 >= a14)) && (input == 3)) && (a9==2)) && (a8==4)) && a27 <= -78 ) && ((-178 < a21) && (-144 >= a21)) )){
      if( ((-178 < a21) && (-144 >= a21)) ){
      a14 = (((a14 + -592192) - 2854) * 1);
      a21 = (((((a21 * 1)/ 10) * 9)/ 10) * 5);
       a8 = 6;
       a9 = 6;
      } else{
       a14 = (((a14 + 201896) + -676471) + -52594);
       a9 = 3;
      } return -1;
     } else if((((a9==3) && (( 182 < a27 && ((input == 2) && ((-178 < a21) && (-144 >= a21)) )) && a14 <= -148 )) && (a8==5))){
      a21 = (((a21 - 251142) - 344617) / 5);
       a8 = 7;
       a9 = 6;
       return 21;
     } else if(( a14 <= -148 && (((a8==4) && ( ((-78 < a27) && (100 >= a27)) && ((a9==2) && (input == 6)))) && 5 < a21 ))){
      a27 = (((a27 - 426685) / 5) - 451675);
      a21 = ((((a21 - 0) / 5) * 4) + -542109);
       return -1;
     } else if((((a9==2) && (( a27 <= -78 && ( a14 <= -148 && (input == 4))) && ((-178 < a21) && (-144 >= a21)) )) && (a8==8))){
      a21 = (((a21 + -313639) * 1) * 1);
       a8 = 4;
       return -1;
     } else if((((a9==5) && ( a21 <= -178 && (((a8==5) && (input == 6)) && ((-148 < a14) && (13 >= a14)) ))) && a27 <= -78 )){
      a14 = (((a14 - -546948) - 706592) + -254133);
      a27 = ((((a27 % 40)+ 140) + -246682) + 246696);
      a21 = (((a21 + 600114) + 21) * 1);
       a8 = 4;
       a9 = 4;
       return -1;
     } else if(( 182 < a27 && ( a14 <= -148 && ( a21 <= -178 && (((input == 1) && ((a9==4) || ((a9==2) || (a9==3)))) && (a8==4)))))){
      a27 = (((((((a27 * 9)/ 10) % 40)- -109) * 5) % 40)+ 127);
      a21 = ((((((a21 % 74)- 10) * 10)/ 9) * 10)/ 9);
       a8 = 5;
       a9 = 3;
       return 25;
     } else if(((((a8==7) && ( a21 <= -178 && (((a9==3) || (a9==4)) && (input == 6)))) && 182 < a27 ) && a14 <= -148 )){
      a27 = (((a27 / 5) + -332165) + -5219);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==7) && (( a14 <= -148 && ( ((-78 < a27) && (100 >= a27)) && ((input == 4) && ((a9==6) || ((a9==4) || (a9==5)))))) && ((-178 < a21) && (-144 >= a21)) ))){
      a27 = (((((a27 * 5) + 147174) + 283507) * -1)/ 10);
      a21 = (((a21 - -181935) * 3) - -19836);
       a8 = 4;
       a9 = 6;
       return -1;
     } else if((( a21 <= -178 && ( a14 <= -148 && ((a8==6) && ((input == 5) && ((a9==3) || (a9==4)))))) && 182 < a27 )){
      a27 = (((a27 / 5) + -331275) + -2156);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((((a8==4) && ((input == 3) && 5 < a21 )) && ((-148 < a14) && (13 >= a14)) ) && a27 <= -78 ) && (a9==2))){
      if( ((13 < a14) && (182 >= a14)) ){
      a14 = (((a14 - 389174) + -74122) * 1);
      a27 = ((((a27 % 40)+ 178) / 5) + 129);
      a21 = ((((a21 / 5) + 54183) % 16)+ -176);
       a8 = 5;
       a9 = 3;
      } else{
       a14 = ((((a14 / 5) / 5) / 5) + -124091);
       a21 = (((((a21 * 9)/ 10) - 207344) - 224824) - 127981);
       a8 = 5;
      } return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && (((a8==7) && ((a9==6) && ( 5 < a21 && (input == 5)))) && a14 <= -148 ))){
      a27 = (((a27 / 5) + -562305) + -2252);
      a21 = (((((a21 % 299911)+ -300088) * 10)/ 9) - 77523);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && (((input == 2) && ((((a8==6) && (a9==2)) && a21 <= -178 ) || ((((a9==5) && (a8==5)) && 5 < a21 ) || ( 5 < a21 && ((a9==6) && (a8==5)))))) && a14 <= -148 ))){
      a27 = (((a27 - 334068) - -667555) + -334199);
      a21 = ((((a21 % 299911)+ -300088) - 0) + -1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((( ((-178 < a21) && (-144 >= a21)) && ((input == 1) && (a9==2))) && a14 <= -148 ) && (a8==5)) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((((a27 - -123907) * -1)/ 10) * 10)/ 9);
      a21 = ((((a21 * 5) - 394866) * 10)/ 9);
       a8 = 4;
       return -1;
     } else if((((a9==3) && ((( a14 <= -148 && (input == 6)) && (a8==7)) && ((-178 < a21) && (-144 >= a21)) )) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((((a27 + 528580) / 5) * 5) * -1)/ 10);
      a21 = (((a21 - 586658) * 1) - 994);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((((input == 3) && ((a9==3) || (a9==4))) && ((100 < a27) && (182 >= a27)) ) && ((-178 < a21) && (-144 >= a21)) ) && a14 <= -148 ) && (a8==5))){
      a27 = ((((a27 - 360665) * 1) * 10)/ 9);
      a21 = (((a21 - 185438) / 5) * 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((( 5 < a21 && ((input == 4) && ((a9==2) || (a9==3)))) && (a8==5)) && ((100 < a27) && (182 >= a27)) ))){
      a27 = (((a27 - 59229) / 5) * 5);
      a21 = ((((a21 % 299911)+ -300088) - 200488) + -27182);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a14 <= -148 && ((a9==5) && ( 5 < a21 && ((input == 3) && a27 <= -78 )))) && (a8==8))){
      a21 = ((((a21 * 9)/ 10) - 576094) / 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( ((-78 < a27) && (100 >= a27)) && ((input == 4) && (((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ((a9==2) && ((-144 < a21) && (5 >= a21)) )))) && a14 <= -148 ) && (a8==6))){
      a27 = (((((a27 % 40)+ 142) - -1) / 5) + 142);
      a21 = (((((a21 - -567999) + -882955) - -508891) * -1)/ 10);
       a8 = 5;
       a9 = 6;
       return 25;
     } else if(((( ((100 < a27) && (182 >= a27)) && ((( a21 <= -178 && (a9==6)) || ((a9==2) && ((-178 < a21) && (-144 >= a21)) )) && (input == 2))) && (a8==4)) && a14 <= -148 )){
      a27 = (((a27 + 489329) - 581050) + -413239);
      a21 = ((((a21 % 299911)- 178) - -284488) + -574341);
       a9 = 2;
       return -1;
     } else if(((((a9==4) && (((input == 1) && a21 <= -178 ) && ((-148 < a14) && (13 >= a14)) )) && a27 <= -78 ) && (a8==6))){
      a14 = (((a14 - 591875) * 1) - 6276);
      a27 = ((((a27 % 299908)- -300090) - -195530) + 77995);
      a21 = (((((a21 * 9)/ 10) % 16)+ -156) - 6);
       a8 = 8;
       a9 = 6;
       return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && (((((input == 1) && ((a9==4) || (a9==5))) && a21 <= -178 ) && (a8==5)) && a14 <= -148 ))){
      a27 = (((a27 * 5) * 5) - 405705);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==8) && (( ((-78 < a27) && (100 >= a27)) && ( ((-178 < a21) && (-144 >= a21)) && ( a14 <= -148 && (input == 2)))) && (a9==5)))){
      a27 = (((a27 / 5) / 5) + -302211);
      a21 = (((a21 * 5) * 5) * 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==6) && (((((input == 4) && ((a9==3) || (a9==4))) && a21 <= -178 ) && ((-78 < a27) && (100 >= a27)) ) && a14 <= -148 ))){
      a27 = (((a27 + -340849) * 1) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( a14 <= -148 && (((input == 6) && ((a9==5) || ((a9==3) || (a9==4)))) && (a8==4))) && ((100 < a27) && (182 >= a27)) ) && ((-178 < a21) && (-144 >= a21)) )){
      a27 = (((a27 + -81801) - 438715) - 52455);
      a21 = (((((((a21 * 13)/ 10) * 10)/ 9) / 5) * 44)/ 10);
       a9 = 2;
       return -1;
     } else if(((((( a14 <= -148 && (input == 6)) && a21 <= -178 ) && ((-78 < a27) && (100 >= a27)) ) && (a9==2)) && (a8==8))){
      a27 = ((((a27 % 40)+ 141) - 1) + 0);
      a21 = ((((a21 - 0) - -600178) - 108602) + 108437);
       a8 = 6;
       a9 = 6;
       return 23;
     } else if((( a14 <= -148 && ( 182 < a27 && (((input == 4) && (((a9==4) || (a9==5)) || (a9==6))) && a21 <= -178 ))) && (a8==8))){
      a27 = ((((a27 % 40)- -130) - -8) - 2);
      a21 = ((((a21 / 5) * 10)/ -9) * 4);
       a8 = 7;
       a9 = 5;
       return 25;
     } else if((((a8==5) && ((((input == 1) && ((a9==3) || (a9==4))) && ((-148 < a14) && (13 >= a14)) ) && a27 <= -78 )) && ((-178 < a21) && (-144 >= a21)) )){
      if( ((-78 < a27) && (100 >= a27)) ){
      a14 = (((a14 - 98139) * 5) + -106311);
      a21 = ((((a21 - -48) * 9)/ 10) + -24);
       a9 = 4;
      } else{
       a14 = ((((a14 / 5) * 5) * 5) + -417270);
       a21 = (((a21 - 544250) + -45556) + -317);
       a8 = 4;
       a9 = 5;
      } return -1;
     } else if(( a27 <= -78 && ( ((-148 < a14) && (13 >= a14)) && ((((((a8==5) && (a9==6)) && 5 < a21 ) || (((a8==6) && (a9==2)) && a21 <= -178 )) || ( a21 <= -178 && ((a8==6) && (a9==3)))) && (input == 5))))){
      if((a9==5)){
      a14 = (((a14 + -114067) * 5) / 5);
      a21 = (((((a21 % 299911)+ -300088) * 1) + 594360) - 594360);
       a8 = 7;
       a9 = 2;
      } else{
       a14 = (((a14 * 5) + -291031) / 5);
       a27 = ((((a27 + 0) - -216147) % 299908)+ 300090);
       a21 = ((((a21 % 299911)- 300088) - 1) * 1);
       a8 = 6;
       a9 = 4;
      } return 25;
     } else if(((((((input == 6) && 5 < a21 ) && (a9==4)) && 182 < a27 ) && (a8==6)) && a14 <= -148 )){
      a27 = (((a27 - 600133) + -20) * 1);
      a21 = ((((a21 % 299911)- 300088) * 1) + -146414);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && (((a8==5) && ((input == 5) && ((( ((-144 < a21) && (5 >= a21)) && (a9==6)) || ( 5 < a21 && (a9==2))) || ((a9==3) && 5 < a21 )))) && a27 <= -78 ))){
      a14 = (((a14 + -238742) - 89559) + -94510);
      a21 = ((((a21 * 9)/ 10) / 5) - -377487);
       a9 = 6;
       return -1;
     } else if((((a8==4) && (((( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ( ((-144 < a21) && (5 >= a21)) && (a9==2))) && (input == 2)) && a14 <= -148 )) && ((-78 < a27) && (100 >= a27)) )){
      a27 = ((((a27 + 460177) + -976302) * 10)/ 9);
      a21 = (((a21 + -445056) + -3949) * 1);
       a9 = 2;
       return -1;
     } else if(( ((-144 < a21) && (5 >= a21)) && ((( a27 <= -78 && ((a8==7) && (input == 5))) && ((-148 < a14) && (13 >= a14)) ) && (a9==5)))){
      if( ((-148 < a14) && (13 >= a14)) ){
      a14 = (((a14 * 5) - 503367) + -9212);
       a8 = 6;
       a9 = 4;
      } else{
       a14 = (((a14 - 83907) + -349411) * 1);
       a21 = (((((a21 - -22866) + -206603) - -223872) * -1)/ 10);
       a8 = 4;
       a9 = 4;
      } return 25;
     } else if(( ((-78 < a27) && (100 >= a27)) && ((((((a9==6) || ((a9==4) || (a9==5))) && (input == 5)) && ((-144 < a21) && (5 >= a21)) ) && (a8==8)) && a14 <= -148 ))){
      a27 = (((a27 - -379705) - 751360) * 1);
      a21 = (((a21 + -514821) + -38850) + -24638);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==7) && (( 182 < a27 && ( ((-178 < a21) && (-144 >= a21)) && ((input == 1) && ((a9==5) || (a9==6))))) && a14 <= -148 ))){
      a27 = ((((a27 - 600083) - -33788) + 182962) - 216830);
      a21 = ((((a21 * 13)/ 10) + -393743) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((a8==8) && (( ((100 < a27) && (182 >= a27)) && (input == 2)) && (a9==4))) && a14 <= -148 ) && ((-144 < a21) && (5 >= a21)) )){
      a27 = (((a27 + 364621) - 935511) + 331174);
      a21 = (((((a21 % 16)+ -161) * 5) % 16)+ -149);
       a9 = 2;
       return 21;
     } else if(((a9==4) && ((a8==5) && ( ((-144 < a21) && (5 >= a21)) && ( a14 <= -148 && ( 182 < a27 && (input == 5))))))){
      a27 = ((((((a27 / 5) * 10)/ -4) / 5) * 44)/ 10);
      a21 = (((a21 * 5) - 191934) + 63338);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && (((input == 6) && (((((a8==5) && (a9==6)) && 5 < a21 ) || ( a21 <= -178 && ((a8==6) && (a9==2)))) || (((a8==6) && (a9==3)) && a21 <= -178 ))) && a27 <= -78 ))){
      if((a8==8)){
      a14 = (((a14 - 422284) * 1) * 1);
      a21 = ((((a21 * 9)/ 10) / 5) + 121636);
       a8 = 7;
       a9 = 3;
      } else{
       a14 = ((((a14 * 5) - 149595) + 377891) - 394386);
       a27 = (((((a27 + 0) % 88)+ 40) + -59716) - -59698);
       a21 = ((((a21 % 16)- 159) + 322371) + -322373);
       a8 = 6;
       a9 = 2;
      } return 23;
     } else if((( ((-78 < a27) && (100 >= a27)) && ((a8==8) && ((((a9==5) || (a9==6)) && (input == 5)) && 5 < a21 ))) && a14 <= -148 )){
      a27 = ((((a27 / 5) - 43596) + 46397) - 540779);
      a21 = ((((a21 % 299911)+ -300088) + -207882) - 74329);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-144 < a21) && (5 >= a21)) && (((((input == 1) && (a9==3)) && (a8==8)) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 ))){
      a27 = ((((a27 * -8)/ 10) - 323408) + -264222);
      a21 = ((((a21 - 300984) / 5) + 334258) + -450516);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((-144 < a21) && (5 >= a21)) && (((a8==4) && ((input == 5) && ((a9==3) || (a9==4)))) && a27 <= -78 )) && ((-148 < a14) && (13 >= a14)) )){
      if( a14 <= -148 ){
      a14 = (((((a14 - 353848) + 689353) + 25398) * -1)/ 10);
      a27 = (((((a27 * 9)/ 10) - -251083) % 88)- -11);
      a21 = ((((a21 - -188890) * 3) % 16)- 164);
       a8 = 6;
       a9 = 4;
      } else{
       a14 = (((a14 - 474018) - -87966) - 188890);
       a27 = (((((((a27 * 9)/ 10) % 88)+ 75) * 5) % 88)+ 10);
       a21 = (((((a21 % 16)- 159) - -124695) / 5) + -25072);
       a8 = 7;
       a9 = 5;
      } return 25;
     } else if(((((a9==4) && ((a8==6) && ( a14 <= -148 && (input == 5)))) && a21 <= -178 ) && ((100 < a27) && (182 >= a27)) )){
      a27 = (((a27 / 5) / 5) + -473387);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && ((a8==4) && ( a14 <= -148 && ((( a21 <= -178 && (a9==6)) || ((a9==2) && ((-178 < a21) && (-144 >= a21)) )) && (input == 6)))))){
      a21 = ((((a21 % 74)+ 4) + 1) - 5);
       a8 = 7;
       a9 = 2;
       return -1;
     } else if(( ((-178 < a21) && (-144 >= a21)) && ( a14 <= -148 && (( 182 < a27 && (((a9==5) || (a9==6)) && (input == 4))) && (a8==7))))){
      a27 = ((((a27 * 9)/ 10) - 583351) * 1);
      a21 = ((((a21 - -258226) + 47320) * -1)/ 10);
       a8 = 8;
       a9 = 4;
       return -1;
     } else if(( ((-144 < a21) && (5 >= a21)) && ((a8==7) && ( a14 <= -148 && (((((a9==2) || (a9==3)) || (a9==4)) && (input == 6)) && 182 < a27 ))))){
      a27 = (((a27 + -600135) + -48) - 0);
      a21 = (((((a21 - 104334) * 10)/ 9) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a14 <= -148 && (((( a21 <= -178 && (a9==6)) || ( ((-178 < a21) && (-144 >= a21)) && (a9==2))) && (input == 1)) && ((100 < a27) && (182 >= a27)) )) && (a8==5))){
      a27 = ((((a27 * 10)/ -9) * 5) + -576311);
      a21 = (((a21 / 5) * 4) + -86756);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( 5 < a21 && ((((input == 5) && (((a9==4) || (a9==5)) || (a9==6))) && ((-148 < a14) && (13 >= a14)) ) && a27 <= -78 )) && (a8==4))){
      a14 = (((a14 * 5) + -516463) * 1);
      a21 = ((((a21 + 0) % 74)+ -87) + 16);
       a9 = 4;
       return 25;
     } else if(((( ((-148 < a14) && (13 >= a14)) && ( 5 < a21 && ((input == 6) && (a8==4)))) && a27 <= -78 ) && (a9==2))){
      a14 = (((a14 / 5) - 513635) * 1);
      a27 = ((((a27 - -297766) + -292080) % 88)+ 12);
       a8 = 6;
       a9 = 6;
       return 25;
     } else if(( ((-78 < a27) && (100 >= a27)) && (((( a21 <= -178 && ((a8==6) && (a9==2))) || (( 5 < a21 && ((a9==5) && (a8==5))) || ( 5 < a21 && ((a9==6) && (a8==5))))) && (input == 4)) && a14 <= -148 ))){
      a27 = ((((a27 / 5) / 5) + -21707) - -21850);
      a21 = (((((a21 * 9)/ 10) % 299997)+ 300002) * 1);
       a8 = 8;
       a9 = 2;
       return 25;
     } else if(( a14 <= -148 && ((a8==7) && (( a27 <= -78 && ((((a9==3) || (a9==4)) || (a9==5)) && (input == 6))) && ((-144 < a21) && (5 >= a21)) )))){
      a21 = (((a21 - 328409) * 1) + -38247);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((((input == 6) && (((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ((a9==2) && ((-144 < a21) && (5 >= a21)) ))) && ((100 < a27) && (182 >= a27)) ) && (a8==8)))){
      a27 = ((((a27 + -539712) * 1) * 10)/ 9);
      a21 = ((((a21 - 14780) + 81722) * 10)/ -9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==6) && ( 182 < a27 && ( a14 <= -148 && (((a9==6) || ((a9==4) || (a9==5))) && (input == 3))))) && ((-144 < a21) && (5 >= a21)) )){
      a27 = ((((a27 + 0) * 9)/ 10) - 555974);
      a21 = (((((a21 + 409154) / 5) * 5) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==7) && (( 182 < a27 && (((input == 2) && (a9==6)) && a14 <= -148 )) && a21 <= -178 ))){
      a27 = (((a27 + -600163) * 1) - 8);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && ( a14 <= -148 && (( ((-178 < a21) && (-144 >= a21)) && (((a9==5) || ((a9==3) || (a9==4))) && (input == 2))) && (a8==4))))){
      a27 = (((a27 + -425561) + 66895) * 1);
      a21 = ((((a21 + -45555) * 10)/ 9) * 5);
       a9 = 2;
       return -1;
     } else if(( ((-144 < a21) && (5 >= a21)) && ((a8==7) && ((((((a9==2) || (a9==3)) || (a9==4)) && (input == 4)) && a14 <= -148 ) && 182 < a27 )))){
      a27 = ((((a27 - 0) % 88)+ -62) / 5);
      a21 = ((((a21 + 108659) % 16)+ -170) * 1);
       a8 = 6;
       a9 = 5;
       return 21;
     } else if(( ((-78 < a27) && (100 >= a27)) && ( ((-178 < a21) && (-144 >= a21)) && ( a14 <= -148 && ((((a9==3) || (a9==4)) && (input == 3)) && (a8==6)))))){
      a27 = (((a27 / 5) + -493626) + -29231);
      a21 = (((a21 + -125505) + -53236) * 3);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==5) && (((input == 4) && ((( ((-178 < a21) && (-144 >= a21)) && (a9==5)) || ((a9==6) && ((-178 < a21) && (-144 >= a21)) )) || ((a9==2) && ((-144 < a21) && (5 >= a21)) ))) && ((-78 < a27) && (100 >= a27)) )) && a14 <= -148 )){
      a27 = (((a27 + -359023) * 1) + -73064);
      a21 = (((a21 / 5) - 555849) - 38750);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && ((((a8==4) && ((input == 1) && a27 <= -78 )) && (a9==5)) && ((-178 < a21) && (-144 >= a21)) ))){
      if( a27 <= -78 ){
      a14 = (((a14 - 492533) + -11036) - 15692);
      a21 = ((((a21 - -43) * 9)/ 10) + 4);
       a8 = 6;
       a9 = 2;
      } else{
       a14 = ((((a14 / 5) - 119781) * 10)/ 9);
       a27 = (((((a27 * 9)/ 10) * 1) % 88)+ 10);
       a21 = ((((a21 + 69) + 11) + -129908) + 129900);
       a8 = 6;
       a9 = 3;
      } return -1;
     } else if(( a21 <= -178 && ((a8==8) && ( ((100 < a27) && (182 >= a27)) && ( a14 <= -148 && ((input == 4) && (((a9==3) || (a9==4)) || (a9==5)))))))){
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && (((a8==4) && ( ((-78 < a27) && (100 >= a27)) && (((a9==5) || ((a9==3) || (a9==4))) && (input == 1)))) && ((-178 < a21) && (-144 >= a21)) ))){
      a27 = (((a27 - 278043) + -243786) / 5);
      a21 = ((((a21 * 13)/ 10) / 5) - 182593);
       a9 = 2;
       return -1;
     } else if(( a27 <= -78 && ((a8==4) && (((a9==3) && ( 5 < a21 && (input == 6))) && ((-148 < a14) && (13 >= a14)) )))){
      a14 = (((a14 - 443068) - 8229) + -59812);
       return -1;
     } else if(((( a21 <= -178 && (((input == 2) && (a8==5)) && (a9==3))) && 182 < a27 ) && a14 <= -148 )){
       a8 = 7;
       return 25;
     } else if(((a8==6) && ( a27 <= -78 && (( a21 <= -178 && (((a9==5) || (a9==6)) && (input == 3))) && ((-148 < a14) && (13 >= a14)) )))){
      if( 5 < a21 ){
      a14 = (((((a14 + -172034) / 5) - -177051) * -1)/ 10);
      a21 = ((((((a21 * 9)/ 10) * 1) + 407414) % 16)- 161);
       a9 = 3;
      } else{
       a14 = (((a14 - 119785) + -330303) * 1);
       a27 = ((((a27 % 88)+ 96) + 3) + -27);
       a21 = ((((a21 + 0) - 0) % 74)+ -62);
       a8 = 5;
       a9 = 4;
      } return -1;
     } else if((((a8==5) && ( ((100 < a27) && (182 >= a27)) && ( 5 < a21 && (((a9==6) || ((a9==4) || (a9==5))) && (input == 6))))) && a14 <= -148 )){
      a27 = ((((a27 * -8)/ 10) - 342746) / 5);
      a21 = (((((a21 % 299911)- 300088) * 10)/ 9) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((( ((-148 < a14) && (13 >= a14)) && (input == 1)) && (a8==4)) && (a9==3)) && a27 <= -78 ) && 5 < a21 )){
      a14 = (((a14 + -470975) * 1) / 5);
      a27 = ((((((a27 - 0) - 0) * 9)/ 10) % 40)+ 155);
      a21 = ((((((a21 * 9)/ 10) / 5) * 5) % 16)- 163);
       a8 = 8;
       a9 = 6;
       return 25;
     } else if(((a8==4) && (( ((100 < a27) && (182 >= a27)) && ( a14 <= -148 && ((a9==2) && (input == 4)))) && a21 <= -178 ))){
      a27 = ((((a27 * 5) * 10)/ -9) / 5);
      a21 = (((((a21 * 9)/ 10) % 16)- 148) + -13);
       a8 = 7;
       a9 = 3;
       return -1;
     } else if(( a14 <= -148 && (( ((-144 < a21) && (5 >= a21)) && ( ((100 < a27) && (182 >= a27)) && ((a9==6) && (input == 6)))) && (a8==6)))){
      a27 = (((a27 - 286620) / 5) - 251602);
      a21 = ((((a21 - 65686) / 5) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( 5 < a21 && ( ((-78 < a27) && (100 >= a27)) && ((input == 5) && ((a9==3) || (a9==4))))) && (a8==6)) && a14 <= -148 )){
      a27 = (((((a27 * 5) % 40)+ 140) - 374839) + 374839);
       a8 = 5;
       a9 = 2;
       return 21;
     } else if(((a9==3) && ((a8==8) && ( a14 <= -148 && ( 5 < a21 && ((input == 2) && ((100 < a27) && (182 >= a27)) )))))){
      a27 = ((((a27 * 5) * -2)/ 10) * 5);
      a21 = ((((a21 - 0) + 0) % 299911)- 300088);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( 182 < a27 && (( ((-144 < a21) && (5 >= a21)) && (((a9==5) || (a9==6)) && (input == 5))) && a14 <= -148 )) && (a8==7))){
      a27 = ((((a27 - 600113) * 1) - -556833) - 556901);
      a21 = (((a21 + -148358) * 4) - 819);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((a8==5) && (((input == 3) && (( ((-144 < a21) && (5 >= a21)) && (a9==6)) || ( 5 < a21 && (a9==2)))) && ((-78 < a27) && (100 >= a27)) )))){
      a27 = (((a27 - 255206) * 2) - 51597);
      a21 = (((a21 / 5) + -541572) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a14 <= -148 && (((input == 6) && (( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ((a9==2) && ((-144 < a21) && (5 >= a21)) ))) && ((-78 < a27) && (100 >= a27)) )) && (a8==8))){
      a27 = ((((a27 - 227897) * 2) * 10)/ 9);
      a21 = ((((a21 / 5) / 5) + 474457) + -1057562);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && (((((input == 3) && ((a9==2) || (a9==3))) && 182 < a27 ) && (a8==8)) && ((-178 < a21) && (-144 >= a21)) ))){
      a27 = ((((a27 * -5)/ 10) + -244666) - 16737);
      a21 = ((((a21 * 10)/ 13) * 5) / 5);
       a8 = 4;
       a9 = 4;
       return -1;
     } else if(( a14 <= -148 && ( ((-78 < a27) && (100 >= a27)) && ((a8==4) && ((input == 5) && (((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ((a9==2) && ((-144 < a21) && (5 >= a21)) ))))))){
      a27 = ((((a27 - -359696) * 10)/ -9) - 65001);
      a21 = (((a21 + -99281) - 430126) * 1);
       a9 = 2;
       return -1;
     } else if(((a8==6) && (( a14 <= -148 && ((( ((-178 < a21) && (-144 >= a21)) && (a9==2)) || (((a9==5) && a21 <= -178 ) || ((a9==6) && a21 <= -178 ))) && (input == 3))) && ((100 < a27) && (182 >= a27)) ))){
      a27 = (((a27 + -226209) + 69747) * 3);
      a21 = (((((a21 % 299911)+ -178) * 10)/ 9) + -118320);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==6) && ( a14 <= -148 && (((( ((-178 < a21) && (-144 >= a21)) && (a9==2)) || (( a21 <= -178 && (a9==5)) || ( a21 <= -178 && (a9==6)))) && (input == 6)) && ((-78 < a27) && (100 >= a27)) )))){
      a27 = ((((((a27 % 40)- -141) / 5) / 5) * 255)/ 10);
      a21 = ((((a21 % 74)+ -63) - 7) - 0);
       a8 = 4;
       a9 = 3;
       return 25;
     } else if(( a21 <= -178 && ((a9==3) && ( a14 <= -148 && ((a8==5) && ((input == 6) && 182 < a27 )))))){
      a27 = ((((a27 - 600168) * 1) / 5) + -107123);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && ((a8==4) && ( a27 <= -78 && (((input == 4) && ((a9==5) || ((a9==3) || (a9==4)))) && a21 <= -178 ))))){
      a14 = (((a14 - 473437) / 5) - 265455);
      a27 = ((((((a27 % 40)- -163) * 9)/ 10) + -371091) + 371122);
      a21 = ((((((a21 % 74)+ 1) - 81639) * 5) % 74)- 35);
       a8 = 7;
       a9 = 2;
       return 23;
     } else if((( 5 < a21 && (((((a9==4) || (a9==5)) && (input == 6)) && ((-78 < a27) && (100 >= a27)) ) && a14 <= -148 )) && (a8==7))){
      a27 = (((a27 - 159933) + -118548) * 2);
      a21 = ((((a21 + -126212) * 1) % 299911)- 300088);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((( 182 < a27 && ((input == 3) && (a9==4))) && (a8==6)) && 5 < a21 ))){
      a27 = (((((a27 * 9)/ 10) / 5) + 480436) + -649333);
      a21 = (((((a21 * 9)/ 10) / 5) + 269243) + -812701);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((( ((100 < a27) && (182 >= a27)) && ((input == 2) && ((a9==5) || (a9==6)))) && ((-144 < a21) && (5 >= a21)) ) && (a8==7)) && a14 <= -148 )){
      a27 = ((((a27 + -39768) - 94609) - -704307) + -1146924);
      a21 = (((((a21 + 31371) * -1)/ 10) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==8) && (((a9==2) && ((input == 3) && ((-178 < a21) && (-144 >= a21)) )) && a14 <= -148 )) && a27 <= -78 )){
      a27 = ((((a27 + 354924) % 299908)- -300090) - -1);
      a21 = (((a21 - 489788) - -489875) - -18);
       a8 = 4;
       a9 = 3;
       return 23;
     } else if((( 182 < a27 && ((((((a9==4) || (a9==5)) || (a9==6)) && (input == 1)) && a14 <= -148 ) && (a8==8))) && a21 <= -178 )){
      if((a8==6)){
      a27 = (((a27 - 600091) / 5) - 217264);
      a21 = (((a21 - -600059) - -114) + 0);
       a8 = 5;
       a9 = 6;
      } else{
       a27 = ((((a27 % 88)+ -28) - -1) - 39);
       a8 = 7;
       a9 = 4;
      } return -1;
     } else if(( ((-178 < a21) && (-144 >= a21)) && ((( a14 <= -148 && ((((a9==3) || (a9==4)) || (a9==5)) && (input == 3))) && a27 <= -78 ) && (a8==8)))){
      a21 = ((((a21 * 10)/ 8) - -347375) + -823965);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( 182 < a27 && ( a14 <= -148 && ((input == 2) && ((((a9==6) && (a8==5)) && 5 < a21 ) || ( a21 <= -178 && ((a8==6) && (a9==2)))))))){
      a27 = (((a27 / 5) * 4) + -527022);
      a21 = ((((a21 % 299911)- 300088) - 2) + 0);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && ( a21 <= -178 && (( a14 <= -148 && (((a9==5) || (a9==6)) && (input == 1))) && (a8==4))))){
      a27 = ((((a27 + -337804) - -519225) * 10)/ -9);
       a9 = 2;
       return -1;
     } else if(( a21 <= -178 && ((a9==2) && ( ((100 < a27) && (182 >= a27)) && ((a8==7) && ((input == 1) && a14 <= -148 )))))){
      a27 = ((((a27 - -279779) * 10)/ -9) * 1);
       a8 = 5;
       return -1;
     } else if(((a8==5) && (( a21 <= -178 && ( a27 <= -78 && ( ((-148 < a14) && (13 >= a14)) && (input == 3)))) && (a9==5)))){
      a14 = ((((a14 - -55543) * 10)/ -9) + -199400);
      a27 = ((((a27 - 0) % 88)+ 43) / 5);
      a21 = (((((a21 - -530820) / 5) / 5) % 74)+ -68);
       a9 = 3;
       return -1;
     } else if((( a14 <= -148 && ((a9==2) && (((input == 2) && a21 <= -178 ) && (a8==7)))) && ((100 < a27) && (182 >= a27)) )){
      a21 = (((((a21 % 16)- 161) / 5) - 553895) + 553780);
       a9 = 3;
       return 21;
     } else if(( 5 < a21 && ((( ((100 < a27) && (182 >= a27)) && (((a9==4) || ((a9==2) || (a9==3))) && (input == 6))) && a14 <= -148 ) && (a8==6)))){
      a27 = (((a27 / 5) + -492620) * 1);
      a21 = (((a21 / 5) - -404300) + -556457);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && (( 5 < a21 && ((a8==7) && ((input == 1) && ((a9==4) || (a9==5))))) && ((-78 < a27) && (100 >= a27)) ))){
      a27 = (((a27 + 221778) - 623142) / 5);
      a21 = (((((a21 + 0) % 299911)- 300088) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-144 < a21) && (5 >= a21)) && (((a8==4) && (((input == 1) && ((a9==5) || (a9==6))) && ((-78 < a27) && (100 >= a27)) )) && a14 <= -148 ))){
      a27 = (((a27 - 301409) * 1) * 1);
      a21 = (((a21 - 568502) - 2375) * 1);
       a9 = 2;
       return -1;
     } else if((( ((-78 < a27) && (100 >= a27)) && ((a8==5) && (((a9==4) && (input == 2)) && ((-178 < a21) && (-144 >= a21)) ))) && a14 <= -148 )){
       a8 = 8;
       a9 = 5;
       return 21;
     } else if(( 182 < a27 && (((a8==8) && ( 5 < a21 && ((input == 5) && ((a9==4) || ((a9==2) || (a9==3)))))) && a14 <= -148 ))){
      if( ((-78 < a27) && (100 >= a27)) ){
      a27 = ((((a27 % 40)- -127) + -23) * 1);
      a21 = (((a21 / 5) + -593168) / 5);
       a8 = 5;
       a9 = 3;
      } else{
       a27 = (((a27 - 600181) + -2) - 0);
       a21 = ((((((a21 + 0) % 16)+ -169) * 5) % 16)+ -145);
       a8 = 4;
       a9 = 5;
      } return 23;
     } else if(( a14 <= -148 && ( 182 < a27 && ((a8==8) && ((a9==4) && ((input == 1) && ((-144 < a21) && (5 >= a21)) )))))){
      a27 = (((a27 - 293758) - 306342) + -78);
      a21 = (((a21 - -552933) + 39134) * 1);
       a9 = 6;
       return -1;
     } else if(( a27 <= -78 && ((a8==6) && (((((a9==3) || (a9==4)) && (input == 2)) && ((-148 < a14) && (13 >= a14)) ) && 5 < a21 )))){
      if((a8==4)){
      a14 = (((a14 * 5) + -434788) + -35465);
      a21 = ((((a21 * 9)/ 10) - 251117) - 293004);
       a8 = 5;
       a9 = 5;
      } else{
       a14 = (((a14 + -167026) + -193563) + -156646);
       a27 = ((((((a27 + 0) * 9)/ 10) / 5) % 88)+ 91);
       a21 = (((a21 / 5) / 5) - 31764);
       a8 = 7;
       a9 = 2;
      } return -1;
     } else if((((((((a9==2) || (a9==3)) && (input == 5)) && a21 <= -178 ) && (a8==5)) && ((-78 < a27) && (100 >= a27)) ) && a14 <= -148 )){
      a27 = (((a27 + -22053) * 5) - 464829);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-178 < a21) && (-144 >= a21)) && (( a27 <= -78 && ((a9==2) && ((input == 5) && (a8==4)))) && ((-148 < a14) && (13 >= a14)) ))){
      a14 = ((((a14 / 5) - 457899) * 10)/ 9);
       a8 = 6;
       a9 = 3;
       return -1;
     } else if(((a9==4) && ( ((-144 < a21) && (5 >= a21)) && ((a8==8) && ( 182 < a27 && ((input == 5) && a14 <= -148 )))))){
      a27 = (((a27 / 5) - 583131) * 1);
      a21 = ((((((a21 * 5) % 16)+ -161) * 5) % 16)+ -156);
       a8 = 5;
       return -1;
     } else if((((a8==8) && ((((input == 3) && ((a9==5) || ((a9==3) || (a9==4)))) && a14 <= -148 ) && ((100 < a27) && (182 >= a27)) )) && a21 <= -178 )){
      a27 = (((((a27 * -8)/ 10) + 31594) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( 182 < a27 && ( 5 < a21 && (((input == 6) && ((a9==2) || (a9==3))) && (a8==4)))) && a14 <= -148 )){
      a27 = (((a27 + -52495) - 547640) * 1);
      a21 = ((((((a21 % 299911)+ -300088) + -247336) - -571852) * -1)/ 10);
       a9 = 2;
       return -1;
     } else if((( a27 <= -78 && (((( a21 <= -178 && (a9==6)) || ((a9==2) && ((-178 < a21) && (-144 >= a21)) )) && (input == 2)) && ((-148 < a14) && (13 >= a14)) )) && (a8==5))){
      if((a8==5)){
      a21 = (((((((a21 * 9)/ 10) * -1)/ 10) + -224629) * -1)/ 10);
       a8 = 4;
       a9 = 4;
      } else{
       a14 = (((a14 + -491658) + -107182) * 1);
       a21 = (((((a21 * 9)/ 10) % 16)- 145) + -8);
       a9 = 5;
      } return -1;
     } else if((( 182 < a27 && ( ((-178 < a21) && (-144 >= a21)) && ((((a9==3) || (a9==4)) && (input == 4)) && a14 <= -148 ))) && (a8==4))){
      a27 = (((((a27 % 40)+ 137) / 5) / 5) + 108);
      a21 = ((((a21 - 481321) * 10)/ -9) - -59564);
       a9 = 2;
       return 21;
     } else if(( a14 <= -148 && ((a8==4) && ( 182 < a27 && ((((a9==2) || (a9==3)) && (input == 4)) && 5 < a21 ))))){
      a27 = ((((a27 * 9)/ 10) * 1) + -588523);
      a21 = ((((a21 % 299911)+ -300088) - 207032) * 1);
       a9 = 2;
       return -1;
     } else if((( 182 < a27 && (((((a9==3) || (a9==4)) && (input == 2)) && a14 <= -148 ) && a21 <= -178 )) && (a8==6))){
      a27 = (((a27 - 600123) / 5) + -158321);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==7) && (( a21 <= -178 && ( ((-148 < a14) && (13 >= a14)) && ((a9==4) && (input == 5)))) && a27 <= -78 ))){
      a14 = (((a14 - 185288) * 3) - 23131);
       a8 = 6;
       a9 = 5;
       return -1;
     } else if(((( ((100 < a27) && (182 >= a27)) && ((input == 3) && ((((a9==5) && ((-144 < a21) && (5 >= a21)) ) || ( ((-144 < a21) && (5 >= a21)) && (a9==6))) || ( 5 < a21 && (a9==2))))) && (a8==8)) && a14 <= -148 )){
      a27 = ((((a27 + -455376) * -1)/ 10) / 5);
      a21 = ((((a21 % 299911)- 300088) - 1) * 1);
       a8 = 5;
       a9 = 3;
       return 25;
     } else if((((a8==8) && (( ((-144 < a21) && (5 >= a21)) && ((input == 4) && ((a9==4) || (a9==5)))) && a27 <= -78 )) && a14 <= -148 )){
      a21 = (((a21 + -17593) * 5) - 303697);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a27 <= -78 && ((((input == 3) && ((-178 < a21) && (-144 >= a21)) ) && (a8==7)) && ((-148 < a14) && (13 >= a14)) )) && (a9==6))){
      a14 = (((a14 / 5) + -95988) * 5);
      a21 = ((((a21 * 10)/ 8) - -237118) - 314483);
       a8 = 5;
       a9 = 4;
       return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && ( a14 <= -148 && (( ((-178 < a21) && (-144 >= a21)) && (((a9==6) || ((a9==4) || (a9==5))) && (input == 2))) && (a8==7))))){
      a27 = ((((a27 - 219432) * 10)/ 9) / 5);
      a21 = (((a21 - 440919) * 1) + -153838);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((a9==4) && ((a8==4) && ((input == 6) && a14 <= -148 ))) && 5 < a21 ) && 182 < a27 )){
      a27 = (((((a27 * 9)/ 10) - -25637) % 88)- -9);
       a8 = 8;
       a9 = 3;
       return 21;
     } else if(( ((-144 < a21) && (5 >= a21)) && (( a14 <= -148 && (((a9==3) && (input == 1)) && 182 < a27 )) && (a8==8)))){
      a27 = ((((a27 % 88)- -13) + 78672) - 78723);
      a21 = (((((a21 % 16)- 161) * 5) % 16)+ -155);
       a8 = 5;
       a9 = 2;
       return 25;
     } else if((( ((-144 < a21) && (5 >= a21)) && ( ((-78 < a27) && (100 >= a27)) && (((input == 2) && ((a9==3) || (a9==4))) && (a8==4)))) && a14 <= -148 )){
      a27 = (((((a27 + -289802) * 10)/ 9) * 10)/ 9);
      a21 = ((((a21 * 5) / 5) / 5) - 182624);
       a9 = 2;
       return -1;
     } else if(( a21 <= -178 && ( a14 <= -148 && ( ((100 < a27) && (182 >= a27)) && ((a8==6) && ((input == 4) && (a9==4))))))){
      a27 = (((((a27 * 10)/ -9) * 10)/ 9) - 30856);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a27 <= -78 && ( ((-144 < a21) && (5 >= a21)) && (( ((-148 < a14) && (13 >= a14)) && (((a9==5) || (a9==6)) && (input == 5))) && (a8==4))))){
      if( ((100 < a27) && (182 >= a27)) ){
      a14 = ((((((a14 + -147030) * 10)/ 9) + 644017) * -1)/ 10);
      a21 = (((a21 / 5) * 5) + 82771);
       a8 = 6;
       a9 = 4;
      } else{
       a14 = ((((a14 / 5) - -287393) * 2) + -1017993);
       a8 = 6;
       a9 = 4;
      } return 23;
     } else if(((a8==6) && (((((input == 6) && ((a9==3) || (a9==4))) && a14 <= -148 ) && a21 <= -178 ) && 182 < a27 ))){
      a27 = ((((a27 + -600103) * 1) - -43820) + -43818);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==8) && ( a14 <= -148 && ((((((a9==4) || (a9==5)) || (a9==6)) && (input == 3)) && ((-144 < a21) && (5 >= a21)) ) && ((-78 < a27) && (100 >= a27)) )))){
      a27 = (((a27 + -271418) - 155543) * 1);
      a21 = (((a21 - 313165) + -16565) + 212462);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==8) && ( 182 < a27 && (( a14 <= -148 && ((input == 3) && (((a9==2) || (a9==3)) || (a9==4)))) && 5 < a21 )))){
      if((a9==4)){
      a27 = (((((a27 % 40)- -115) - -363293) * 1) - 363275);
       a9 = 6;
      } else{
       a27 = (((a27 + -218454) + -381684) - 10);
       a21 = (((((a21 % 299911)- 300088) * 1) / 5) + -142282);
       a8 = 5;
       a9 = 5;
      } return -1;
     } else if((( a14 <= -148 && (( ((100 < a27) && (182 >= a27)) && ((input == 6) && ((a9==6) || ((a9==4) || (a9==5))))) && ((-144 < a21) && (5 >= a21)) )) && (a8==4))){
      a27 = (((a27 - -110136) - 110277) + 53);
      a21 = (((a21 + 345877) - -236094) + 5301);
       a8 = 8;
       a9 = 3;
       return -1;
     } else if(( a14 <= -148 && ((((a9==3) && ((a8==5) && (input == 2))) && ((100 < a27) && (182 >= a27)) ) && a21 <= -178 ))){
      a27 = (((((a27 * 10)/ -9) + -255450) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( 182 < a27 && (((((input == 6) && ((a9==2) || (a9==3))) && (a8==8)) && a21 <= -178 ) && a14 <= -148 ))){
      a14 = (((((a14 - -341197) * 1) + 72498) % 80)+ -67);
      a27 = (((((a27 - 600157) + -23) / 5) * 22)/ 10);
      a21 = (((((a21 + 0) / 5) * 4) % 16)- 152);
       a8 = 5;
       a9 = 4;
       return 25;
     } else if((((((input == 1) && (( ((-144 < a21) && (5 >= a21)) && (a9==2)) || (((a9==5) && ((-178 < a21) && (-144 >= a21)) ) || ( ((-178 < a21) && (-144 >= a21)) && (a9==6))))) && (a8==4)) && a14 <= -148 ) && 182 < a27 )){
      a27 = (((((a27 * -5)/ 10) * 10)/ 9) + -47291);
      a21 = (((a21 - 78480) / 5) * 5);
       a9 = 2;
       return -1;
     } else if((((((((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ((a9==2) && ((-144 < a21) && (5 >= a21)) )) && (input == 1)) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 ) && (a8==8))){
      a27 = ((((((a27 * 10)/ -9) * 5) + 321895) * -1)/ 10);
      a21 = (((a21 + -358638) * 1) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a27 <= -78 && (( a14 <= -148 && ( a21 <= -178 && ((((a9==4) || (a9==5)) || (a9==6)) && (input == 2)))) && (a8==7)))){
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((-78 < a27) && (100 >= a27)) && ( a14 <= -148 && (((((a9==5) && ((-144 < a21) && (5 >= a21)) ) || ((a9==6) && ((-144 < a21) && (5 >= a21)) )) || ((a9==2) && 5 < a21 )) && (input == 2)))) && (a8==7))){
      a27 = (((a27 * 5) - 480511) - 109440);
      a21 = ((((a21 % 16)- 159) / 5) + -124);
       a9 = 5;
       return 21;
     } else if(((a8==8) && (((((input == 6) && a14 <= -148 ) && (a9==5)) && a27 <= -78 ) && a21 <= -178 ))){
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==5) && (((((input == 6) && (a9==3)) && a14 <= -148 ) && 182 < a27 ) && ((-178 < a21) && (-144 >= a21)) ))){
      a27 = ((((a27 * 9)/ 10) * 1) + -560493);
      a21 = (((a21 - 92206) * 5) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && ((a8==8) && ( a14 <= -148 && ((((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ( ((-144 < a21) && (5 >= a21)) && (a9==2))) && (input == 3)))))){
      a27 = ((((a27 + 492625) * -1)/ 10) * 5);
      a21 = (((((a21 * 5) - 206492) - -223190) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a27 <= -78 && ( ((-148 < a14) && (13 >= a14)) && ((a8==5) && (((input == 6) && ((a9==3) || (a9==4))) && ((-178 < a21) && (-144 >= a21)) ))))){
      a14 = (((a14 + 262134) * 2) - 656939);
      a21 = (((a21 - -111) / 5) + -71);
       a8 = 6;
       a9 = 3;
       return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && ( a14 <= -148 && (((a8==5) && ((input == 3) && (((a9==4) || (a9==5)) || (a9==6)))) && ((-144 < a21) && (5 >= a21)) )))){
      a21 = (((a21 / 5) - 521234) + -63864);
       a8 = 4;
       a9 = 3;
       return -1;
     } else if((( a21 <= -178 && ((( ((100 < a27) && (182 >= a27)) && (input == 2)) && (a8==4)) && a14 <= -148 )) && (a9==5))){
      a27 = (((a27 / 5) + -103015) / 5);
       a9 = 2;
       return -1;
     } else if(((input == 5) && (( a21 <= -178 && ((( ((-148 < a14) && (13 >= a14)) && a27 <= -78 ) && (a8==4)) && (a9==2))) || ((((a9==5) && ((a8==8) && ( 182 < a27 && a14 <= -148 ))) && 5 < a21 ) || (((a9==6) && ((a8==8) && ( 182 < a27 && a14 <= -148 ))) && 5 < a21 ))))){
      if( 182 < a27 ){
      a14 = ((((a14 % 299926)+ -300073) - 2) - 0);
      a27 = (((a27 / 5) / 5) - 170190);
      a21 = ((((a21 % 299911)- 300088) * 1) * 1);
       a8 = 6;
       a9 = 2;
      } else{
       a14 = ((((a14 % 299926)- 300073) - 2) + 0);
       a27 = ((((a27 * 9)/ 10) / 5) + -338165);
       a21 = ((((((a21 * 9)/ 10) * 1) - -52990) % 299997)+ 300002);
       a8 = 6;
       a9 = 2;
      } return -1;
     } else if(( a27 <= -78 && (((a8==8) && ( a14 <= -148 && ((input == 6) && (((a9==3) || (a9==4)) || (a9==5))))) && ((-178 < a21) && (-144 >= a21)) ))){
      a27 = ((((((a27 * 9)/ 10) % 88)+ 92) * 9)/ 10);
      a21 = (((a21 - 291770) + 89141) * 2);
       a8 = 5;
       a9 = 3;
       return 23;
     } else if(((( ((-148 < a14) && (13 >= a14)) && ((((a9==5) || (a9==6)) && (input == 5)) && a21 <= -178 )) && (a8==6)) && a27 <= -78 )){
      a21 = ((((((a21 + 0) * 9)/ 10) - -542921) % 16)+ -175);
       a8 = 4;
       a9 = 6;
       return -1;
     } else if(( a21 <= -178 && ( a14 <= -148 && (((((a9==2) || (a9==3)) && (input == 5)) && (a8==8)) && 182 < a27 )))){
      if((a9==5)){
      a27 = ((((a27 + 0) * 9)/ 10) + -587179);
      a21 = (((a21 - -600026) * 1) - -63);
       a8 = 5;
       a9 = 2;
      } else{
       a27 = (((((a27 + 0) * 9)/ 10) + -444973) - 96765);
       a21 = ((((a21 / 5) % 74)- -4) + 1);
       a8 = 5;
       a9 = 3;
      } return 25;
     } else if(( ((-178 < a21) && (-144 >= a21)) && ( 182 < a27 && ( a14 <= -148 && ((((a9==4) || (a9==5)) && (input == 5)) && (a8==5)))))){
      a27 = ((((a27 + 0) / 5) + 217589) - 793174);
      a21 = (((a21 * 5) * 5) - 281812);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==8) && ((( ((100 < a27) && (182 >= a27)) && (((a9==4) || (a9==5)) && (input == 4))) && a14 <= -148 ) && ((-178 < a21) && (-144 >= a21)) ))){
      a27 = (((a27 / 5) + -201130) * 2);
      a21 = (((a21 - -67302) - 402131) / 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && (( a27 <= -78 && ((((a9==5) || (a9==6)) && (input == 4)) && ((-144 < a21) && (5 >= a21)) )) && (a8==4)))){
      a14 = (((a14 / 5) + -95841) + -340046);
      a27 = ((((a27 + 146797) / 5) % 40)+ 140);
       a8 = 8;
       a9 = 6;
       return 25;
     }
     return calculate_output6(input);
 }
 int calculate_output6(int input) {
     if(((( 182 < a27 && ( 5 < a21 && ((((a9==2) || (a9==3)) || (a9==4)) && (input == 2)))) && (a8==8)) && a14 <= -148 )){
      a27 = (((a27 - 66592) - 533552) + -18);
      a21 = (((a21 / 5) + -432059) - 129147);
       a8 = 5;
       a9 = 4;
       return -1;
     } else if((( a14 <= -148 && ((a9==5) && ( 182 < a27 && ((a8==7) && (input == 4))))) && a21 <= -178 )){
      a27 = (((((a27 + 0) % 40)+ 123) * 10)/ 9);
      a21 = (((a21 - -569111) * 1) - -31067);
       a8 = 4;
       a9 = 3;
       return 21;
     } else if(( ((-144 < a21) && (5 >= a21)) && ((((((a9==6) || ((a9==4) || (a9==5))) && (input == 1)) && 182 < a27 ) && a14 <= -148 ) && (a8==6)))){
      a27 = (((a27 + -398378) - 201733) * 1);
      a21 = (((a21 * 5) + -345413) + -103187);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && (( a27 <= -78 && (((a8==7) && (input == 6)) && (a9==3))) && a21 <= -178 ))){
      a14 = ((((a14 + -63661) + 645647) / 5) - 427795);
      a27 = (((((a27 % 40)- -179) + -39) - 511989) - -512024);
       a8 = 6;
       a9 = 4;
       return -1;
     } else if((((((((a9==2) || (a9==3)) && (input == 2)) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 ) && 5 < a21 ) && (a8==7))){
      a27 = ((((a27 * 5) - 92361) % 88)- -22);
      a21 = (((((a21 + 0) * 9)/ 10) % 16)- 159);
       a8 = 5;
       a9 = 2;
       return 23;
     } else if((( a14 <= -148 && (((((a9==5) || (a9==6)) && (input == 5)) && ((-144 < a21) && (5 >= a21)) ) && ((-78 < a27) && (100 >= a27)) )) && (a8==4))){
      a27 = ((((a27 + -224796) - -420778) * 10)/ -9);
      a21 = (((a21 / 5) / 5) + -45858);
       a9 = 2;
       return -1;
     } else if((( 182 < a27 && ((a8==4) && ((( ((-144 < a21) && (5 >= a21)) && (a9==2)) || (((a9==5) && ((-178 < a21) && (-144 >= a21)) ) || ( ((-178 < a21) && (-144 >= a21)) && (a9==6)))) && (input == 6)))) && a14 <= -148 )){
      a27 = (((((a27 * 9)/ 10) * -5)/ 10) * 2);
      a21 = (((a21 + -352031) - -25843) + -224998);
       a9 = 2;
       return -1;
     } else if(((a9==5) && ((a8==6) && ((( 5 < a21 && (input == 1)) && ((-78 < a27) && (100 >= a27)) ) && a14 <= -148 )))){
      a27 = (((a27 - 82475) * 5) * 1);
      a21 = ((((a21 % 299911)+ -300088) + -62011) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a9==4) && ((( a14 <= -148 && (input == 4)) && (a8==8)) && 182 < a27 )) && ((-144 < a21) && (5 >= a21)) )){
      if( ((13 < a14) && (182 >= a14)) ){
      a27 = ((((a27 + 0) % 88)+ -56) + -7);
      a21 = ((((a21 + -433645) % 16)+ -151) - -3);
       a8 = 5;
       a9 = 2;
      } else{
       a27 = ((((((a27 + 0) % 40)+ 123) / 5) * 45)/ 10);
       a21 = (((((a21 % 16)+ -159) + 232065) / 5) - 46535);
       a8 = 7;
       a9 = 6;
      } return -1;
     } else if((((a8==4) && ( ((-148 < a14) && (13 >= a14)) && ((((a9==6) || ((a9==4) || (a9==5))) && (input == 4)) && a27 <= -78 ))) && 5 < a21 )){
      if( a21 <= -178 ){
      a14 = ((((a14 + -178358) * 10)/ 9) * 3);
       a8 = 5;
       a9 = 6;
      } else{
       a14 = ((((a14 + 104455) * 10)/ -9) * 5);
       a21 = (((((a21 - 0) * 9)/ 10) * 1) + -560952);
       a8 = 6;
       a9 = 4;
      } return -1;
     } else if(((( a27 <= -78 && ((((a9==4) || (a9==5)) && (input == 1)) && ((-148 < a14) && (13 >= a14)) )) && (a8==7)) && 5 < a21 )){
      a14 = (((a14 - -106697) - -470703) + -604918);
      a27 = ((((((a27 + 488573) % 88)- -11) * 5) % 88)- -12);
      a21 = (((((a21 * 9)/ 10) / 5) % 16)+ -164);
       a8 = 8;
       a9 = 5;
       return -1;
     } else if(((((a8==4) && ( ((-178 < a21) && (-144 >= a21)) && ((input == 5) && (((a9==3) || (a9==4)) || (a9==5))))) && a14 <= -148 ) && ((100 < a27) && (182 >= a27)) )){
      a27 = (((a27 + -35258) / 5) - 227439);
      a21 = (((a21 / 5) - -344117) + 199318);
       a8 = 8;
       a9 = 6;
       return 21;
     } else if(( ((-148 < a14) && (13 >= a14)) && ( a27 <= -78 && ((((( ((-144 < a21) && (5 >= a21)) && (a9==6)) || ( 5 < a21 && (a9==2))) || ( 5 < a21 && (a9==3))) && (input == 2)) && (a8==5))))){
      if( a27 <= -78 ){
      a14 = (((a14 - 563154) - -581435) - 23970);
      a21 = (((a21 / 5) / 5) - -104473);
       a8 = 6;
       a9 = 4;
      } else{
       a14 = ((((a14 + -6030) * 5) * 10)/ 9);
       a21 = ((((a21 % 299997)- -300002) * 1) - 0);
       a8 = 4;
       a9 = 5;
      } return 21;
     } else if(( ((-178 < a21) && (-144 >= a21)) && (((a8==6) && (((input == 6) && (((a9==3) || (a9==4)) || (a9==5))) && ((100 < a27) && (182 >= a27)) )) && a14 <= -148 ))){
      a27 = ((((a27 * -8)/ 10) * 5) * 5);
      a21 = (((a21 * 5) * 5) * 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==6) && ((((((a9==2) && ((-178 < a21) && (-144 >= a21)) ) || (((a9==5) && a21 <= -178 ) || ( a21 <= -178 && (a9==6)))) && (input == 4)) && ((-78 < a27) && (100 >= a27)) ) && a14 <= -148 ))){
      a27 = (((a27 - 590564) - 7158) + -577);
      a21 = (((((a21 + 0) % 299911)+ -178) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( 5 < a21 && (((((input == 4) && ((a9==4) || (a9==5))) && (a8==7)) && a27 <= -78 ) && a14 <= -148 ))){
      a27 = ((((a27 % 299908)+ 300090) + 248624) + 6712);
      a21 = ((((a21 % 16)- 163) - 452836) + 452836);
       a8 = 6;
       a9 = 4;
       return 21;
     } else if(((a8==5) && ((((( ((-144 < a21) && (5 >= a21)) && (a9==6)) || ((a9==2) && 5 < a21 )) && (input == 1)) && ((-78 < a27) && (100 >= a27)) ) && a14 <= -148 ))){
      a27 = (((a27 + -275770) + -95239) / 5);
      a21 = (((((a21 % 299911)+ -300088) + -2) - -367333) + -367332);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((-78 < a27) && (100 >= a27)) && (( 5 < a21 && ((input == 2) && a14 <= -148 )) && (a8==8))) && (a9==2))){
      a27 = (((a27 + -543747) * 1) * 1);
      a21 = ((((a21 % 299911)- 300088) * 1) + -218469);
       a8 = 4;
       return -1;
     } else if(((a8==4) && ( a14 <= -148 && ((((input == 1) && ((a9==3) || (a9==4))) && 182 < a27 ) && ((-178 < a21) && (-144 >= a21)) )))){
      a21 = ((((a21 + 117652) * 10)/ 9) / 5);
       a8 = 5;
       a9 = 4;
       return 21;
     } else if((( a14 <= -148 && ((a8==7) && ( 182 < a27 && ((input == 4) && ((a9==3) || (a9==4)))))) && a21 <= -178 )){
      a27 = ((((a27 + 0) / 5) % 40)- -121);
      a21 = ((((a21 + 0) % 16)- 158) - -13);
       a8 = 5;
       a9 = 2;
       return 25;
     } else if(((((((input == 3) && ((a9==4) || (a9==5))) && (a8==5)) && a21 <= -178 ) && a14 <= -148 ) && ((100 < a27) && (182 >= a27)) )){
      a21 = (((((a21 % 74)+ -8) * 5) % 74)+ -5);
       a8 = 6;
       a9 = 5;
       return 23;
     } else if((( 5 < a21 && ((((input == 4) && (((a9==4) || (a9==5)) || (a9==6))) && (a8==4)) && ((-78 < a27) && (100 >= a27)) )) && a14 <= -148 )){
      a27 = ((((a27 * 5) / 5) * 5) + 303550);
       a8 = 5;
       a9 = 2;
       return 23;
     } else if((((( ((100 < a27) && (182 >= a27)) && (((a9==6) || ((a9==4) || (a9==5))) && (input == 4))) && 5 < a21 ) && (a8==5)) && a14 <= -148 )){
      a27 = (((a27 + 192068) / 5) - 496164);
      a21 = ((((a21 * 9)/ 10) - 597394) / 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-178 < a21) && (-144 >= a21)) && (((a8==6) && (((input == 5) && (a9==5)) && 182 < a27 )) && a14 <= -148 ))){
      a27 = (((a27 - 600159) * 1) * 1);
      a21 = ((((a21 * 5) - -485416) / 5) + -504012);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( ((-144 < a21) && (5 >= a21)) && ((a9==4) && ( ((100 < a27) && (182 >= a27)) && ((a8==8) && (input == 3))))))){
      a27 = (((a27 + 133264) / 5) + 278842);
       a8 = 5;
       a9 = 2;
       return 23;
     } else if((((a8==8) && (( ((-178 < a21) && (-144 >= a21)) && ( a14 <= -148 && (input == 5))) && a27 <= -78 )) && (a9==2))){
      a21 = (((a21 - 232798) / 5) - 50493);
       a8 = 4;
       return -1;
     } else if(((((((input == 1) && ((a9==5) || (a9==6))) && 5 < a21 ) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 ) && (a8==6))){
      a27 = ((((((a27 * 10)/ -9) / 5) / 5) * 195)/ 10);
      a21 = (((((a21 % 299911)- 300088) * 10)/ 9) - 45082);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && ( a27 <= -78 && (((( ((-144 < a21) && (5 >= a21)) && (a9==6)) || ( 5 < a21 && (a9==2))) && (input == 2)) && (a8==7))))){
      if( 182 < a27 ){
      a14 = ((((a14 + -449659) * 10)/ 9) * 1);
      a27 = ((((a27 % 299908)- -300090) + 110222) - -150497);
      a21 = ((((a21 % 299911)- 300088) * 1) - 1);
       a8 = 6;
       a9 = 4;
      } else{
       a14 = (((a14 + -421172) + -167503) + -2626);
       a21 = ((((((a21 % 74)- 68) - 2) * 5) % 74)+ -68);
       a9 = 4;
      } return -1;
     } else if(((a8==7) && (((( a21 <= -178 && (input == 2)) && (a9==4)) && a27 <= -78 ) && ((-148 < a14) && (13 >= a14)) ))){
      a14 = ((((a14 + 439901) - 607488) + 183941) - 412847);
      a21 = ((((a21 % 74)+ -16) + 4) + -49);
       a8 = 6;
       return -1;
     } else if((((((((a9==3) || (a9==4)) && (input == 1)) && (a8==5)) && a14 <= -148 ) && ((100 < a27) && (182 >= a27)) ) && ((-178 < a21) && (-144 >= a21)) )){
      a21 = (((a21 * 5) * 5) + -508874);
       a8 = 4;
       a9 = 3;
       return -1;
     } else if((((a9==4) && (( a27 <= -78 && ( ((-148 < a14) && (13 >= a14)) && (input == 2))) && 5 < a21 )) && (a8==5))){
      a14 = ((((a14 - 73083) - -2106) * 10)/ 9);
      a21 = (((((a21 % 16)- 161) * 5) % 16)+ -154);
       a8 = 4;
       a9 = 6;
       return 21;
     } else if(((a9==4) && (((((input == 3) && a21 <= -178 ) && (a8==6)) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 ))){
      a27 = ((((a27 * -8)/ 10) + -302336) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && (( 5 < a21 && (((input == 6) && (a9==6)) && (a8==6))) && ((-78 < a27) && (100 >= a27)) ))){
      a27 = (((((a27 * 5) % 40)- -142) - 449901) + 449900);
      a21 = (((((a21 % 299911)- 300088) / 5) * 5) - 244991);
       a9 = 4;
       return 21;
     } else if(( a21 <= -178 && ( ((-148 < a14) && (13 >= a14)) && ((a8==6) && ( a27 <= -78 && ((input == 4) && ((a9==5) || (a9==6)))))))){
      if( ((-148 < a14) && (13 >= a14)) ){
      a14 = (((((a14 - 260349) * 10)/ 9) * 10)/ 9);
      a27 = (((((a27 % 40)- -162) + 9326) + 484360) + -493701);
      a21 = ((((a21 / 5) % 74)- 63) + -4);
       a8 = 7;
       a9 = 3;
      } else{
       a8 = 7;
       a9 = 2;
      } return -1;
     } else if((((((input == 1) && (((a9==6) && ((-144 < a21) && (5 >= a21)) ) || ((a9==2) && 5 < a21 ))) && (a8==6)) && ((-148 < a14) && (13 >= a14)) ) && a27 <= -78 )){
      if( a27 <= -78 ){
      a14 = (((a14 + -521473) * 1) * 1);
      a21 = (((((a21 % 16)+ -160) / 5) - 458950) + 458827);
       a8 = 5;
       a9 = 2;
      } else{
       a14 = (((a14 + 107339) * 5) - 928473);
       a21 = (((((a21 % 299911)+ -300088) - 1) + 498922) + -498921);
       a9 = 4;
      } return -1;
     } else if((( a14 <= -148 && ((a9==2) && (( ((-144 < a21) && (5 >= a21)) && (input == 6)) && (a8==7)))) && ((100 < a27) && (182 >= a27)) )){
      a27 = ((((a27 * 10)/ -9) - 560749) / 5);
      a21 = (((a21 - 526275) * 1) / 5);
       a8 = 4;
       return -1;
     } else if(((a8==6) && ((((((a9==2) || (a9==3)) && (input == 2)) && a14 <= -148 ) && a21 <= -178 ) && ((100 < a27) && (182 >= a27)) ))){
      a27 = ((((a27 + -43618) * 5) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( 5 < a21 && ((a8==7) && ( a14 <= -148 && (((a9==4) || (a9==5)) && (input == 6))))) && ((100 < a27) && (182 >= a27)) )){
      a27 = ((((a27 * 5) * 5) * 5) + -26864);
      a21 = ((((a21 % 299911)+ -300088) + 598386) - 885249);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==7) && ( a14 <= -148 && (((input == 3) && (((a9==2) || (a9==3)) || (a9==4))) && ((-144 < a21) && (5 >= a21)) ))) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((a27 / 5) / 5) - -126);
       a8 = 6;
       a9 = 2;
       return 21;
     } else if(( 182 < a27 && ( a21 <= -178 && ((a8==6) && ((((a9==3) || (a9==4)) && (input == 4)) && a14 <= -148 ))))){
      a27 = ((((a27 / 5) + 193310) * 10)/ -9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((-178 < a21) && (-144 >= a21)) && ((a9==4) && ( a14 <= -148 && ((input == 5) && ((-78 < a27) && (100 >= a27)) )))) && (a8==5))){
      a27 = (((a27 - 262613) - 3506) / 5);
      a21 = ((((a21 - 18511) + 431110) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==6) && (( a27 <= -78 && ( ((-148 < a14) && (13 >= a14)) && (((a9==5) || (a9==6)) && (input == 6)))) && 5 < a21 ))){
      if( a27 <= -78 ){
      a14 = (((a14 - -261639) + 243092) - 561929);
      a27 = ((((a27 - -133132) % 40)- -140) - 0);
      a21 = ((((a21 % 16)+ -176) - -15) + -16);
       a9 = 6;
      } else{
       a14 = ((((a14 + -164262) + 84776) + 95667) - 237858);
       a27 = ((((a27 / 5) + -81117) % 88)- -81);
       a21 = ((((a21 % 16)+ -171) * 5) / 5);
       a8 = 4;
       a9 = 2;
      } return -1;
     } else if(((( a14 <= -148 && ((input == 3) && ((( a21 <= -178 && (a9==6)) || ((a9==2) && ((-178 < a21) && (-144 >= a21)) )) || ( ((-178 < a21) && (-144 >= a21)) && (a9==3))))) && (a8==8)) && ((100 < a27) && (182 >= a27)) )){
      a27 = ((((a27 / 5) * 5) * 10)/ 18);
      a21 = (((((a21 + 264542) % 16)- 159) + -368153) - -368152);
       a8 = 5;
       a9 = 4;
       return 25;
     } else if(((((a8==5) && ( a21 <= -178 && ((input == 4) && ((a9==2) || (a9==3))))) && ((-78 < a27) && (100 >= a27)) ) && a14 <= -148 )){
      a27 = (((a27 + -582687) * 1) + -6526);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && ( ((-144 < a21) && (5 >= a21)) && ( a14 <= -148 && (((a9==4) && (input == 4)) && (a8==7)))))){
      a27 = ((((a27 - -32929) * 5) * -1)/ 10);
      a21 = (((a21 + -547391) / 5) / 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((a8==6) && ( a14 <= -148 && ((input == 6) && ((a9==3) || (a9==4))))) && ((-78 < a27) && (100 >= a27)) ) && 5 < a21 )){
      a27 = ((((a27 % 40)+ 141) * 5) / 5);
       a8 = 5;
       a9 = 4;
       return 25;
     } else if(( ((-148 < a14) && (13 >= a14)) && ((( a21 <= -178 && ((a9==4) && (input == 6))) && a27 <= -78 ) && (a8==6)))){
      if((a8==5)){
      a14 = ((((a14 - 384256) * 1) * 10)/ 9);
      a27 = ((((((a27 % 40)- -180) * 9)/ 10) * 9)/ 10);
      a21 = ((((a21 - 0) + 0) % 74)+ -60);
       a8 = 7;
       a9 = 3;
      } else{
       a14 = (((a14 + -470715) * 1) * 1);
       a21 = (((((a21 * 9)/ 10) % 74)- 65) / 5);
       a8 = 5;
      } return -1;
     } else if((( a14 <= -148 && ((a8==7) && (((input == 3) && ((a9==2) || (a9==3))) && ((-178 < a21) && (-144 >= a21)) ))) && a27 <= -78 )){
      a21 = (((a21 + -479356) - -574088) - 599630);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( ((-148 < a14) && (13 >= a14)) && (((( a21 <= -178 && (a9==5)) || ( a21 <= -178 && (a9==6))) || ((a9==2) && ((-178 < a21) && (-144 >= a21)) )) && (input == 6))) && (a8==7)) && a27 <= -78 )){
      a14 = ((((a14 + -206977) + -91514) + 682831) + -449381);
      a21 = (((((a21 / 5) + 413101) * 1) * -1)/ 10);
       a8 = 4;
       a9 = 3;
       return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && ( 5 < a21 && (((a8==6) && ((input == 1) && ((a9==4) || ((a9==2) || (a9==3))))) && a14 <= -148 )))){
       a9 = 2;
       return 25;
     } else if(( ((-78 < a27) && (100 >= a27)) && ((a8==7) && ( a14 <= -148 && ( ((-178 < a21) && (-144 >= a21)) && (((a9==6) || ((a9==4) || (a9==5))) && (input == 1))))))){
      a27 = ((((((a27 % 40)+ 140) * 5) - -426114) % 40)+ 113);
       a8 = 6;
       a9 = 3;
       return 21;
     } else if(((( 5 < a21 && ((a9==2) && ((input == 4) && a14 <= -148 ))) && 182 < a27 ) && (a8==6))){
      a27 = (((((a27 % 40)+ 133) + -4) + -294721) + 294730);
      a21 = ((((a21 % 299911)+ -300088) - 153417) - 73428);
       a8 = 4;
       a9 = 3;
       return 21;
     } else if(((a8==4) && ( a14 <= -148 && (((((a9==6) || ((a9==4) || (a9==5))) && (input == 1)) && 5 < a21 ) && ((-78 < a27) && (100 >= a27)) )))){
      a27 = (((a27 + -431781) * 1) * 1);
      a21 = ((((a21 % 299911)+ -300088) / 5) + -299344);
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && (((((a9==5) && (input == 5)) && ((-78 < a27) && (100 >= a27)) ) && (a8==5)) && ((-144 < a21) && (5 >= a21)) ))){
      a27 = (((a27 * 5) + -35226) + -229784);
      a21 = (((a21 - 122775) + -463407) + 413114);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a9==3) && (((( ((-144 < a21) && (5 >= a21)) && (input == 4)) && a14 <= -148 ) && ((100 < a27) && (182 >= a27)) ) && (a8==8)))){
      a27 = (((a27 + -187654) + -101140) * 2);
      a21 = (((((a21 * 5) + -135023) + 211965) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a9==3) && ( 182 < a27 && (((input == 2) && (a8==4)) && a14 <= -148 ))) && ((-144 < a21) && (5 >= a21)) )){
      a27 = ((((a27 + 0) + -600156) - -41470) - 41481);
      a21 = (((a21 - 598146) - 433) * 1);
       a9 = 2;
       return -1;
     } else if((( a14 <= -148 && (( 182 < a27 && ((input == 2) && (((a9==4) || (a9==5)) || (a9==6)))) && (a8==8))) && a21 <= -178 )){
      if((a9==4)){
      a27 = ((((a27 - 349438) + -250679) - -351335) + -351316);
      a21 = ((((((a21 % 74)- 29) * 5) - 543733) % 74)+ -61);
       a8 = 5;
       a9 = 5;
      } else{
       a27 = ((((a27 % 88)- 41) + 2) + -9);
       a21 = ((((a21 + 284052) / 5) + -527650) + 946064);
       a9 = 5;
      } return -1;
     } else if(((a8==6) && ( ((100 < a27) && (182 >= a27)) && (((input == 2) && ((( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ((a9==2) && ((-144 < a21) && (5 >= a21)) )) || ((a9==3) && ((-144 < a21) && (5 >= a21)) ))) && a14 <= -148 )))){
      a27 = ((((a27 - 112876) + -22072) + 621980) + -537112);
      a21 = ((((a21 + 208030) / 5) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && ((((( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ((a9==2) && ((-144 < a21) && (5 >= a21)) )) && (input == 5)) && (a8==8)) && a14 <= -148 ))){
      a27 = (((((a27 - 359617) - -468925) - -359496) * -1)/ 10);
      a21 = (((a21 + -566093) * 1) / 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( ((-144 < a21) && (5 >= a21)) && ((a9==3) && ((a8==8) && ((input == 3) && ((100 < a27) && (182 >= a27)) )))))){
      a27 = ((((a27 - -529667) - 529811) + -181145) - -181199);
      a21 = ((((a21 % 16)+ -159) + -2) - 1);
       a8 = 5;
       a9 = 4;
       return 25;
     } else if(( ((-144 < a21) && (5 >= a21)) && ((((a8==6) && ( ((-148 < a14) && (13 >= a14)) && (input == 1))) && a27 <= -78 ) && (a9==3)))){
      if((a8==6)){
      a14 = (((a14 / 5) - 166358) + -431370);
       a8 = 5;
       a9 = 4;
      } else{
       a14 = (((a14 - 74238) * 5) + -3640);
       a21 = (((((a21 % 16)- 159) + 143499) / 5) - 28817);
       a8 = 4;
       a9 = 5;
      } return -1;
     } else if((( a14 <= -148 && ((((input == 5) && ((a9==4) || (a9==5))) && (a8==8)) && ((-178 < a21) && (-144 >= a21)) )) && 182 < a27 )){
      if( 182 < a14 ){
      a27 = ((((a27 + -600083) - 34) / 5) - 421854);
      a21 = ((((a21 * 5) - -483352) - 742016) - -423819);
       a9 = 3;
      } else{
       a27 = ((((((a27 * 9)/ 10) / 5) - 387625) % 88)+ 77);
       a8 = 6;
       a9 = 5;
      } return -1;
     } else if((( ((-144 < a21) && (5 >= a21)) && (((((a9==5) || (a9==6)) && (input == 4)) && ((-78 < a27) && (100 >= a27)) ) && (a8==4))) && a14 <= -148 )){
      a21 = ((((a21 + 524239) + -739786) * 10)/ 9);
       a8 = 7;
       a9 = 4;
       return 25;
     } else if((((((a8==5) && ((input == 2) && (((a9==3) || (a9==4)) || (a9==5)))) && a14 <= -148 ) && 5 < a21 ) && 182 < a27 )){
      a27 = (((((a27 * -5)/ 10) * 1) * 10)/ 9);
      a21 = (((((a21 + 0) % 299911)+ -300088) / 5) + -437742);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( a21 <= -178 && ((a8==4) && ((((a9==2) || (a9==3)) || (a9==4)) && (input == 2)))) && a14 <= -148 ) && ((-78 < a27) && (100 >= a27)) )){
       a8 = 6;
       a9 = 5;
       return 23;
     } else if(( ((-78 < a27) && (100 >= a27)) && (((a8==6) && ( a14 <= -148 && ((input == 4) && (a9==5)))) && 5 < a21 ))){
      a27 = (((a27 + -123910) + -400016) - 19636);
      a21 = (((((a21 % 299911)- 300088) + -236635) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a14 <= -148 && ( ((-78 < a27) && (100 >= a27)) && (((input == 1) && ((a9==3) || (a9==4))) && (a8==5)))) && 5 < a21 )){
      a27 = (((a27 * 5) * 5) - 358510);
      a21 = ((((a21 + -278652) * 1) / 5) - 447946);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==8) && (( a14 <= -148 && ((input == 4) && (((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ( ((-144 < a21) && (5 >= a21)) && (a9==2))))) && 182 < a27 ))){
      a27 = (((((a27 * 9)/ 10) / 5) % 40)+ 107);
      a21 = (((a21 / 5) + -544237) + 648888);
       a8 = 7;
       a9 = 6;
       return -1;
     } else if(((a8==8) && ((a9==3) && ( a21 <= -178 && (( ((-78 < a27) && (100 >= a27)) && (input == 5)) && a14 <= -148 ))))){
      a27 = ((((a27 - -28691) * 5) % 40)+ 110);
      a21 = ((((((a21 % 16)+ -148) * 5) + 122018) % 16)- 162);
       a8 = 5;
       a9 = 5;
       return 21;
     } else if(( ((-144 < a21) && (5 >= a21)) && (( a14 <= -148 && (((input == 6) && ((a9==6) || ((a9==4) || (a9==5)))) && (a8==6))) && 182 < a27 ))){
      a27 = ((((a27 * 9)/ 10) - 550252) - 19507);
      a21 = (((a21 - -516708) + 62235) * 1);
       a8 = 7;
       a9 = 4;
       return 21;
     } else if(((( a14 <= -148 && ( ((100 < a27) && (182 >= a27)) && (((a9==5) || (a9==6)) && (input == 4)))) && (a8==6)) && 5 < a21 )){
      a27 = (((a27 - 469331) + 469170) / 5);
      a21 = ((((a21 / 5) % 74)- 117) + 8);
       a8 = 4;
       a9 = 6;
       return 21;
     } else if(( a27 <= -78 && (( a14 <= -148 && ((((a9==3) || (a9==4)) && (input == 5)) && 5 < a21 )) && (a8==8)))){
      a21 = ((((a21 % 299911)- 300088) - 156978) - 10177);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((( a14 <= -148 && ( a21 <= -178 && (input == 3))) && (a9==2)) && ((-78 < a27) && (100 >= a27)) ) && (a8==7))){
      a27 = (((a27 - 520367) + 4463) / 5);
       a8 = 4;
       return -1;
     } else if(((((a8==4) && ((( ((-178 < a21) && (-144 >= a21)) && (a9==2)) || (( a21 <= -178 && (a9==5)) || ( a21 <= -178 && (a9==6)))) && (input == 2))) && 182 < a27 ) && a14 <= -148 )){
      a27 = (((((a27 - 137200) + -221152) * 1) % 40)+ 141);
      a21 = ((((a21 % 299911)+ -178) + -244958) * 1);
       a9 = 6;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && (( ((-144 < a21) && (5 >= a21)) && (((input == 2) && (a8==5)) && a27 <= -78 )) && (a9==3)))){
      a14 = (((a14 * 5) - 311341) * 1);
      a27 = (((((a27 * 9)/ 10) - -547487) + -213162) - -253180);
       a8 = 4;
       return -1;
     } else if(( ((-144 < a21) && (5 >= a21)) && ( a14 <= -148 && ((a8==4) && ( 182 < a27 && (((a9==6) || ((a9==4) || (a9==5))) && (input == 3))))))){
      a27 = (((a27 - 600084) - 78) + -15);
      a21 = (((((a21 / 5) * 5) + 244213) * -1)/ 10);
       a8 = 6;
       a9 = 6;
       return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && (((((((a9==6) && a21 <= -178 ) || ( ((-178 < a21) && (-144 >= a21)) && (a9==2))) || ( ((-178 < a21) && (-144 >= a21)) && (a9==3))) && (input == 5)) && (a8==8)) && a14 <= -148 ))){
      a27 = (((((a27 * 5) + 210210) / 5) * -1)/ 10);
      a21 = ((((a21 % 299911)- 178) - 275213) / 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a9==3) && ( a27 <= -78 && ((( ((-148 < a14) && (13 >= a14)) && (input == 5)) && 5 < a21 ) && (a8==7))))){
      a21 = (((((a21 % 74)- 104) * 10)/ 9) / 5);
       a8 = 5;
       return -1;
     } else if(((a8==7) && ( ((-178 < a21) && (-144 >= a21)) && ((((input == 6) && ((a9==4) || (a9==5))) && a14 <= -148 ) && ((100 < a27) && (182 >= a27)) )))){
      a27 = ((((((a27 * -8)/ 10) - 22865) - -485738) * -1)/ 10);
      a21 = ((((a21 - 188799) * 3) / 5) - -113273);
       a8 = 4;
       a9 = 3;
       return -1;
     } else if(((a8==7) && ( a27 <= -78 && ( a14 <= -148 && ( ((-144 < a21) && (5 >= a21)) && ((a9==2) && (input == 6))))))){
      a21 = (((a21 + 100391) * 5) + 78481);
       a9 = 6;
       return 25;
     } else if((( a14 <= -148 && ( ((-178 < a21) && (-144 >= a21)) && ((a8==4) && (((a9==3) || (a9==4)) && (input == 2))))) && 182 < a27 )){
      a27 = ((((a27 + -448098) % 40)- -142) + -1);
      a21 = ((((a21 - 290780) * 2) * 1) - -623093);
       a9 = 4;
       return 21;
     } else if(( ((100 < a27) && (182 >= a27)) && (( a14 <= -148 && ( ((-144 < a21) && (5 >= a21)) && ((input == 6) && (a8==8)))) && (a9==4)))){
      a27 = ((((a27 * -8)/ 10) + -296106) * 2);
      a21 = (((a21 + -580757) - 19029) - -69893);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a9==4) && ( ((100 < a27) && (182 >= a27)) && (( 5 < a21 && ((input == 4) && (a8==4))) && a14 <= -148 )))){
      a27 = (((a27 - 528922) * 1) * 1);
      a21 = (((((a21 % 299911)- 300088) - 227154) * 10)/ 9);
       a9 = 2;
       return -1;
     } else if((((( a21 <= -178 && (((a9==5) || (a9==6)) && (input == 2))) && (a8==4)) && ((-78 < a27) && (100 >= a27)) ) && a14 <= -148 )){
      a27 = (((a27 - 254274) * 2) * 1);
       a9 = 2;
       return -1;
     } else if((((( a14 <= -148 && ((input == 2) && (a8==5))) && ((100 < a27) && (182 >= a27)) ) && ((-144 < a21) && (5 >= a21)) ) && (a9==3))){
      a27 = (((a27 / 5) * 5) + -460068);
      a21 = (((a21 + -35314) / 5) * 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( ((-148 < a14) && (13 >= a14)) && ( ((-178 < a21) && (-144 >= a21)) && ((input == 6) && (a8==7)))) && a27 <= -78 ) && (a9==6))){
      a14 = (((a14 - 341477) * 1) / 5);
      a27 = ((((((a27 - 0) - 0) * 9)/ 10) % 40)+ 161);
      a21 = (((a21 / 5) + -347700) - 15787);
       a8 = 4;
       a9 = 3;
       return -1;
     } else if(((a9==3) && (((((input == 3) && (a8==4)) && 182 < a27 ) && ((-144 < a21) && (5 >= a21)) ) && a14 <= -148 ))){
      a27 = ((((((a27 % 88)- -3) * 5) + 263960) % 88)+ 6);
      a21 = (((a21 + 480441) * 1) + 94331);
       a8 = 7;
       return 21;
     } else if(( ((-148 < a14) && (13 >= a14)) && (((((a9==4) && (input == 1)) && (a8==5)) && a27 <= -78 ) && 5 < a21 ))){
      a14 = (((a14 + -101542) * 5) - 51359);
      a21 = (((a21 / 5) + -231501) * 2);
       a9 = 5;
       return -1;
     } else if(( a27 <= -78 && (((input == 3) && (((((a9==6) && (a8==7)) && 5 < a21 ) || (((a9==2) && (a8==8)) && a21 <= -178 )) || ( a21 <= -178 && ((a9==3) && (a8==8))))) && a14 <= -148 ))){
      a21 = ((((a21 - 0) % 299911)- 300088) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((((((a9==5) || (a9==6)) && (input == 5)) && (a8==7)) && ((100 < a27) && (182 >= a27)) ) && ((-144 < a21) && (5 >= a21)) ) && a14 <= -148 )){
      a27 = ((((a27 / 5) * 5) - -307584) - 900245);
      a21 = (((a21 * 5) + -482678) - 50505);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a14 <= -148 && ( ((-78 < a27) && (100 >= a27)) && ((input == 2) && (((a9==2) && ((-178 < a21) && (-144 >= a21)) ) || (((a9==5) && a21 <= -178 ) || ( a21 <= -178 && (a9==6))))))) && (a8==6))){
      a27 = ((((a27 - 186424) + 120966) * 10)/ 9);
      a21 = ((((a21 % 299911)+ -178) - 96643) - 130613);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==5) && ( ((100 < a27) && (182 >= a27)) && (( a14 <= -148 && ((input == 4) && ((a9==6) || ((a9==4) || (a9==5))))) && ((-144 < a21) && (5 >= a21)) )))){
      a27 = ((((a27 + -64695) / 5) - -354998) - 416310);
      a21 = ((((a21 / 5) * 5) % 16)- 161);
       a8 = 7;
       a9 = 2;
       return 25;
     } else if(( ((100 < a27) && (182 >= a27)) && ( a14 <= -148 && (((a8==7) && (((a9==4) || (a9==5)) && (input == 4))) && 5 < a21 )))){
      a27 = (((((a27 + 165984) / 5) / 5) * -1)/ 10);
      a21 = ((((a21 * 9)/ 10) + -566647) / 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==4) && (((((a9==2) || (a9==3)) && (input == 2)) && ((100 < a27) && (182 >= a27)) ) && ((-144 < a21) && (5 >= a21)) )) && a14 <= -148 )){
      a27 = ((((a27 + 190978) + -461241) * 10)/ 9);
      a21 = ((((a21 / 5) - 341422) * 10)/ 9);
       a9 = 2;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && ((a8==6) && ( a27 <= -78 && ( ((-144 < a21) && (5 >= a21)) && ((input == 5) && ((a9==4) || (a9==5)))))))){
      a14 = (((a14 - 565865) + -5921) / 5);
      a27 = (((((a27 - 0) / 5) / 5) % 40)+ 149);
      a21 = (((a21 - -353471) / 5) + -70839);
       a8 = 8;
       a9 = 4;
       return -1;
     } else if((((((a8==8) && ((input == 2) && a14 <= -148 )) && (a9==3)) && a21 <= -178 ) && ((-78 < a27) && (100 >= a27)) )){
      a27 = ((((a27 + -471144) - -732032) - -3285) - 803297);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a27 <= -78 && ( ((-148 < a14) && (13 >= a14)) && ((a8==5) && (( ((-144 < a21) && (5 >= a21)) && (input == 1)) && (a9==3)))))){
      if( ((-148 < a14) && (13 >= a14)) ){
      a14 = ((((a14 - 412875) * 10)/ 9) + 186262);
      a27 = (((a27 / 5) + 213975) * 2);
      a21 = ((((a21 % 16)- 159) + -1) + -1);
       a8 = 7;
       a9 = 4;
      } else{
       a14 = (((a14 + -157792) * 3) / 5);
       a21 = (((((a21 % 16)+ -161) * 5) % 16)- 150);
       a8 = 4;
       a9 = 2;
      } return -1;
     } else if((( a14 <= -148 && ((a8==8) && ((((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ( ((-144 < a21) && (5 >= a21)) && (a9==2))) && (input == 4)))) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((((a27 + 121397) * 10)/ -9) + 240938) - 158949);
      a21 = (((((a21 + -234437) + -219766) + 606404) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((( ((-78 < a27) && (100 >= a27)) && ((a8==6) && (input == 1))) && ((-178 < a21) && (-144 >= a21)) ) && (a9==5)))){
      a27 = ((((a27 * 5) / 5) / 5) + 140);
      a21 = ((((a21 * 10)/ 8) - 461884) * 1);
       a8 = 5;
       a9 = 2;
       return 23;
     } else if(((a8==8) && ((((input == 3) && (((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ( ((-144 < a21) && (5 >= a21)) && (a9==2)))) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 ))){
      if( ((-144 < a21) && (5 >= a21)) ){
      a27 = (((a27 * 5) + 321291) / 5);
      a21 = (((a21 - 29473) + -260016) / 5);
       a8 = 5;
       a9 = 3;
      } else{
       a21 = ((((a21 - -587423) / 5) % 16)- 162);
       a8 = 5;
       a9 = 2;
      } return 21;
     } else if(((( ((-144 < a21) && (5 >= a21)) && ( ((-148 < a14) && (13 >= a14)) && ( a27 <= -78 && (input == 4)))) && (a8==6)) && (a9==3))){
      if( ((-178 < a21) && (-144 >= a21)) ){
      a14 = (((a14 - -524545) - 1082601) + -33023);
      a21 = ((((a21 - 416331) + -42459) - -829820) - 835753);
       a8 = 8;
       a9 = 4;
      } else{
       a14 = (((a14 - -385286) - 434992) * 5);
       a21 = (((a21 / 5) - -81890) - 486359);
       a8 = 5;
       a9 = 2;
      } return -1;
     } else if((( a14 <= -148 && ((a8==6) && (((( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ( ((-144 < a21) && (5 >= a21)) && (a9==2))) || ((a9==3) && ((-144 < a21) && (5 >= a21)) )) && (input == 3)))) && 182 < a27 )){
      a27 = (((a27 / 5) / 5) + -319696);
      a21 = (((a21 - -471707) * 1) + -671533);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==4) && ((( a14 <= -148 && ((input == 1) && ((a9==2) || (a9==3)))) && 5 < a21 ) && 182 < a27 ))){
      if( 182 < a14 ){
      a21 = ((((((a21 / 5) % 74)- 135) * 5) % 74)- 4);
       a8 = 6;
       a9 = 2;
      } else{
       a21 = ((((a21 + -582502) % 74)- 69) + -1);
       a8 = 6;
       a9 = 5;
      } return 23;
     } else if(( ((-144 < a21) && (5 >= a21)) && ( 182 < a27 && ((a8==7) && ( a14 <= -148 && (((a9==5) || (a9==6)) && (input == 6))))))){
      a27 = ((((a27 + -600110) + 525486) - -43267) - 568794);
      a21 = (((a21 - 41279) * 5) * 2);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((((input == 1) && (a9==5)) && ((-78 < a27) && (100 >= a27)) ) && (a8==8)) && a14 <= -148 ) && ((-178 < a21) && (-144 >= a21)) )){
      a27 = ((((a27 * 5) % 40)+ 140) - 0);
      a21 = ((((a21 * 5) * 5) % 74)- 2);
       a8 = 6;
       a9 = 6;
       return 21;
     } else if(((a9==3) && (( ((100 < a27) && (182 >= a27)) && (((input == 1) && ((-178 < a21) && (-144 >= a21)) ) && (a8==7))) && a14 <= -148 ))){
      a27 = (((((a27 * 10)/ -9) * 10)/ 9) * 5);
      a21 = (((((a21 * 10)/ 13) - -31) + -200497) - -200536);
       a8 = 6;
       a9 = 6;
       return -1;
     } else if(((((input == 3) && (((((a9==6) && (a8==5)) && 5 < a21 ) || ( a21 <= -178 && ((a9==2) && (a8==6)))) || (((a8==6) && (a9==3)) && a21 <= -178 ))) && ((-148 < a14) && (13 >= a14)) ) && a27 <= -78 )){
      a14 = (((a14 + 472038) - 634000) - 336176);
      a21 = ((((((a21 % 74)- 69) - 1) * 5) % 74)+ -69);
       a8 = 6;
       a9 = 3;
       return -1;
     } else if(((( ((100 < a27) && (182 >= a27)) && (((( a21 <= -178 && (a9==6)) || ( ((-178 < a21) && (-144 >= a21)) && (a9==2))) || ((a9==3) && ((-178 < a21) && (-144 >= a21)) )) && (input == 2))) && (a8==8)) && a14 <= -148 )){
      a27 = (((a27 / 5) + 9) / 5);
      a21 = (((((a21 - -565496) % 16)+ -159) / 5) - 142);
       a8 = 5;
       a9 = 2;
       return 23;
     } else if(((a9==2) && ( ((100 < a27) && (182 >= a27)) && ( a21 <= -178 && (( a14 <= -148 && (input == 3)) && (a8==7)))))){
      a27 = (((a27 - 454385) * 1) / 5);
      a21 = (((((a21 % 16)- 154) - 5) + 214084) - 214081);
       a8 = 5;
       a9 = 5;
       return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && ((((a9==6) && ( ((-144 < a21) && (5 >= a21)) && (input == 2))) && a14 <= -148 ) && (a8==6)))){
      a27 = (((a27 + -575564) + -13967) + -6228);
      a21 = ((((a21 % 16)+ -161) - 1) - 0);
       a8 = 7;
       a9 = 3;
       return -1;
     } else if(((( a14 <= -148 && ((((a9==2) && 5 < a21 ) || (((a9==5) && ((-144 < a21) && (5 >= a21)) ) || ( ((-144 < a21) && (5 >= a21)) && (a9==6)))) && (input == 2))) && (a8==6)) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((a27 - 174002) - -83964) - 155258);
      a21 = ((((a21 * 9)/ 10) - 543242) - 15496);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==5) && ( a14 <= -148 && ((((a9==3) || (a9==4)) && (input == 4)) && ((-144 < a21) && (5 >= a21)) ))) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((a27 + -175974) * 3) - 786);
      a21 = (((a21 / 5) * 5) - 10825);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a9==2) && (( ((-144 < a21) && (5 >= a21)) && ( ((100 < a27) && (182 >= a27)) && (input == 2))) && (a8==7))) && a14 <= -148 )){
      a27 = (((a27 + -112796) + -55457) - 27873);
      a21 = (((a21 + -202086) - 226814) * 1);
       a8 = 4;
       return -1;
     } else if((((a8==8) && ( ((-144 < a21) && (5 >= a21)) && (((input == 5) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 ))) && (a9==3))){
      a27 = (((((a27 - -215963) + 301637) / 5) * -1)/ 10);
      a21 = (((a21 * 5) - 180356) + -101492);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==4) && ( a21 <= -178 && ((a9==6) && (( a27 <= -78 && (input == 4)) && ((-148 < a14) && (13 >= a14)) ))))){
      if( ((-148 < a14) && (13 >= a14)) ){
      a14 = ((((((a14 - 10515) * 10)/ 9) - -580985) * -1)/ 10);
       a8 = 6;
      } else{
       a14 = (((a14 - 235835) + -208620) + -54151);
       a27 = (((((a27 % 299908)+ 300090) / 5) * 51)/ 10);
       a21 = (((((a21 - -228470) + 256921) * 1) % 16)+ -159);
       a8 = 8;
       a9 = 5;
      } return -1;
     } else if((((((((a9==2) || (a9==3)) && (input == 4)) && (a8==7)) && 5 < a21 ) && a14 <= -148 ) && 182 < a27 )){
      if( 182 < a27 ){
      a27 = (((((a27 + 0) * -5)/ 10) * 10)/ 9);
       a8 = 4;
       a9 = 2;
      } else{
       a27 = (((a27 + -600145) - 21) + -12);
       a21 = ((((a21 - 0) / 5) % 74)- 85);
       a8 = 6;
       a9 = 3;
      } return -1;
     } else if((( a14 <= -148 && ((((a8==5) && (input == 1)) && (a9==3)) && a21 <= -178 )) && ((100 < a27) && (182 >= a27)) )){
      a27 = (((((a27 * 10)/ -9) + -263470) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( ((-144 < a21) && (5 >= a21)) && (((input == 5) && ((a9==5) || (a9==6))) && 182 < a27 )) && (a8==8)) && a14 <= -148 )){
      if((a9==4)){
      a27 = (((((a27 % 88)+ 2) * 10)/ 9) + -53);
       a8 = 7;
       a9 = 3;
      } else{
       a21 = (((((a21 - 326238) * 1) / 5) * -1)/ 10);
       a9 = 3;
      } return -1;
     } else if((((( 182 < a27 && ((input == 2) && ((-178 < a21) && (-144 >= a21)) )) && a14 <= -148 ) && (a8==6)) && (a9==5))){
      a27 = (((a27 - 600148) + -25) * 1);
      a21 = (((a21 / 5) + -166670) * 3);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ((a8==8) && ( a27 <= -78 && (((input == 1) && ((a9==4) || (a9==5))) && ((-144 < a21) && (5 >= a21)) ))))){
      a21 = ((((a21 / 5) + 75005) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( 5 < a21 && ( ((-78 < a27) && (100 >= a27)) && ((a9==5) && ((a8==6) && ((input == 3) && a14 <= -148 )))))){
      a27 = (((((a27 - -234448) + 197914) * 1) * -1)/ 10);
      a21 = ((((a21 / 5) * 4) - 80965) + -402609);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((((a9==6) && ((input == 2) && (a8==6))) && a14 <= -148 ) && 5 < a21 ) && ((-78 < a27) && (100 >= a27)) )){
      a27 = (((a27 + -193980) * 3) + -4362);
      a21 = ((((a21 + 0) % 299911)- 300088) - 299800);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==7) && ( ((-148 < a14) && (13 >= a14)) && (((a9==2) && ((input == 4) && a27 <= -78 )) && a21 <= -178 )))){
      if( 182 < a14 ){
      a14 = (((a14 + -523669) * 1) / 5);
      a27 = (((((a27 / 5) - -495590) - -62155) % 40)+ 109);
      a21 = (((a21 + 600121) - 194049) - -193952);
       a8 = 8;
       a9 = 3;
      } else{
       a14 = ((((a14 - 467867) + -77415) - -1033220) - 583607);
       a21 = (((a21 + 600147) + 24) * 1);
       a8 = 4;
       a9 = 3;
      } return -1;
     } else if(( a14 <= -148 && ( ((-78 < a27) && (100 >= a27)) && ((a8==8) && ( ((-144 < a21) && (5 >= a21)) && (((a9==6) || ((a9==4) || (a9==5))) && (input == 4))))))){
      a27 = (((a27 - 249053) * 2) * 1);
      a21 = (((a21 / 5) + -132803) * 4);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==6) && (( a14 <= -148 && ((input == 6) && (((a9==3) && ((-144 < a21) && (5 >= a21)) ) || (((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ((a9==2) && ((-144 < a21) && (5 >= a21)) ))))) && ((100 < a27) && (182 >= a27)) ))){
      a27 = (((a27 / 5) + -34426) - 104732);
      a21 = (((a21 - 468782) - 7283) + -65139);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && ( a14 <= -148 && (((( ((-144 < a21) && (5 >= a21)) && (a9==2)) || (((a9==5) && ((-178 < a21) && (-144 >= a21)) ) || ( ((-178 < a21) && (-144 >= a21)) && (a9==6)))) && (input == 5)) && (a8==5))))){
      a27 = ((((a27 * -1)/ 10) * 5) - -76);
      a21 = ((((a21 + -122927) % 74)- -3) - 7);
       a8 = 6;
       a9 = 4;
       return -1;
     } else if((( a14 <= -148 && ((input == 5) && (( a21 <= -178 && ((a8==5) && (a9==2))) || ((((a8==4) && (a9==5)) && 5 < a21 ) || (((a8==4) && (a9==6)) && 5 < a21 ))))) && ((100 < a27) && (182 >= a27)) )){
      a27 = (((a27 - 579488) / 5) / 5);
      a21 = ((((a21 % 299911)- 300088) * 1) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((( 182 < a27 && ((((a9==4) || (a9==5)) || (a9==6)) && (input == 2))) && a14 <= -148 ) && (a8==6)) && ((-144 < a21) && (5 >= a21)) )){
      a27 = (((a27 + -600109) + -45) + -18);
      a21 = (((a21 + -185425) - 212820) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((100 < a27) && (182 >= a27)) && ((a8==8) && ((((a9==5) || (a9==6)) && (input == 4)) && a14 <= -148 ))) && 5 < a21 )){
      a27 = ((((a27 * 10)/ -9) * 5) + -226809);
      a21 = ((((((a21 * 9)/ 10) + 42053) * 1) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((((input == 4) && (((a9==2) && ((-178 < a21) && (-144 >= a21)) ) || (( a21 <= -178 && (a9==5)) || ((a9==6) && a21 <= -178 )))) && 182 < a27 ) && a14 <= -148 ) && (a8==4))){
      a27 = ((((a27 - 600091) - -559466) * 1) + -559490);
      a21 = ((((a21 + 276975) % 299911)- 300088) - 2);
       a9 = 2;
       return -1;
     } else if(( ((-148 < a14) && (13 >= a14)) && ( a21 <= -178 && ((a9==6) && ((a8==4) && ((input == 5) && a27 <= -78 )))))){
      if( a27 <= -78 ){
      a14 = (((a14 / 5) + -73329) * 5);
      a27 = ((((a27 % 88)- -70) / 5) * 5);
       a8 = 5;
      } else{
       a14 = (((a14 * 5) + -161972) * 3);
       a21 = (((a21 - -600157) - -13) / 5);
       a9 = 5;
      } return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && (((a8==6) && ((input == 2) && (((a9==2) && ((-178 < a21) && (-144 >= a21)) ) || (( a21 <= -178 && (a9==5)) || ( a21 <= -178 && (a9==6)))))) && a14 <= -148 ))){
      a27 = (((a27 - 503901) - -79154) + 11931);
      a21 = ((((a21 * 9)/ 10) - 2291) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a14 <= -148 && (((a8==7) && ((input == 6) && ((a9==5) || (a9==6)))) && ((100 < a27) && (182 >= a27)) )) && ((-144 < a21) && (5 >= a21)) )){
      a27 = (((((a27 - -411543) + -411695) * 5) % 88)+ 11);
      a21 = (((a21 - -563159) - -1267) + 35162);
       a8 = 8;
       a9 = 3;
       return 21;
     } else if(((a8==6) && ((((((a9==3) || (a9==4)) && (input == 2)) && a21 <= -178 ) && ((-78 < a27) && (100 >= a27)) ) && a14 <= -148 ))){
      a27 = ((((a27 + -512505) % 40)+ 181) + -16);
       a8 = 4;
       a9 = 6;
       return 23;
     } else if((( a14 <= -148 && ((((input == 6) && (a9==3)) && ((-78 < a27) && (100 >= a27)) ) && a21 <= -178 )) && (a8==8))){
      a27 = (((a27 * 5) - 192850) * 3);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((((input == 3) && (((a9==6) && ((-144 < a21) && (5 >= a21)) ) || ( 5 < a21 && (a9==2)))) && a27 <= -78 ) && a14 <= -148 ) && (a8==8))){
      a21 = ((((a21 % 299911)+ -300088) - 0) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( a27 <= -78 && ((a9==4) && ((input == 4) && (a8==8)))) && a21 <= -178 ) && a14 <= -148 )){
      a27 = (((((a27 % 88)- -39) - -44) - -592069) + -592113);
       a8 = 4;
       a9 = 6;
       return 23;
     } else if(( ((100 < a27) && (182 >= a27)) && ((a8==4) && ( a14 <= -148 && ((input == 3) && (((a9==6) && a21 <= -178 ) || ( ((-178 < a21) && (-144 >= a21)) && (a9==2)))))))){
      a21 = ((((a21 % 299911)+ -178) + -149957) * 1);
       a9 = 3;
       return 25;
     } else if(( ((-148 < a14) && (13 >= a14)) && ( a27 <= -78 && (((((a9==4) || (a9==5)) && (input == 2)) && (a8==7)) && 5 < a21 )))){
      if((a9==5)){
      a14 = (((a14 - 484747) - 22947) + -70606);
       a8 = 4;
       a9 = 4;
      } else{
       a14 = (((((a14 / 5) * 5) - -515691) * -1)/ 10);
       a8 = 4;
       a9 = 3;
      } return -1;
     } else if((( a14 <= -148 && ((a8==5) && ((input == 5) && (( 5 < a21 && (a9==2)) || (((a9==5) && ((-144 < a21) && (5 >= a21)) ) || ( ((-144 < a21) && (5 >= a21)) && (a9==6))))))) && 182 < a27 )){
      a27 = (((((a27 + -48617) / 5) - -124657) % 40)+ 141);
      a21 = (((((a21 * 9)/ 10) - -59096) % 16)+ -171);
       a9 = 6;
       return 21;
     } else if((((a8==8) && ( ((-144 < a21) && (5 >= a21)) && ( a14 <= -148 && (((a9==5) || (a9==6)) && (input == 3))))) && 182 < a27 )){
      a27 = (((a27 + -600149) - -382119) - 382097);
      a21 = (((a21 - -81768) + 294814) - -132116);
       a9 = 4;
       return 21;
     } else if((((a8==7) && (( ((-148 < a14) && (13 >= a14)) && ((input == 4) && (((a9==3) || (a9==4)) || (a9==5)))) && a27 <= -78 )) && ((-178 < a21) && (-144 >= a21)) )){
      a14 = (((a14 - -368656) + -572527) + 120225);
      a21 = (((a21 - 161134) + -359907) - -191610);
       a8 = 6;
       a9 = 4;
       return -1;
     } else if(( ((-178 < a21) && (-144 >= a21)) && (( a14 <= -148 && (((input == 2) && ((100 < a27) && (182 >= a27)) ) && (a9==3))) && (a8==7)))){
      a27 = ((((a27 * 5) * -2)/ 10) * 5);
      a21 = ((((a21 * 10)/ -9) / 5) / 5);
       a8 = 6;
       return -1;
     } else if(((a8==6) && ( a14 <= -148 && ((((input == 2) && 5 < a21 ) && (a9==3)) && 182 < a27 )))){
      a27 = ((((a27 / 5) / 5) / 5) + -427768);
      a21 = ((((a21 % 299911)- 300088) / 5) - 510883);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-178 < a21) && (-144 >= a21)) && ((((((a9==3) || (a9==4)) && (input == 2)) && ((-148 < a14) && (13 >= a14)) ) && a27 <= -78 ) && (a8==5)))){
      a14 = (((a14 + -527219) * 1) * 1);
      a21 = ((((a21 / 5) / 5) - -586790) - 586876);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==7) && (( a27 <= -78 && ( ((-148 < a14) && (13 >= a14)) && (((a9==4) || (a9==5)) && (input == 3)))) && 5 < a21 ))){
      a14 = (((a14 * 5) - 75343) * 5);
      a21 = (((((a21 % 16)- 162) + 2) + 579242) - 579258);
       a8 = 5;
       a9 = 3;
       return -1;
     } else if(( a14 <= -148 && (( ((100 < a27) && (182 >= a27)) && ((a8==4) && ((input == 2) && ((a9==6) || ((a9==4) || (a9==5)))))) && ((-144 < a21) && (5 >= a21)) ))){
      a27 = (((a27 + -340716) + -177272) * 1);
      a21 = ((((a21 + -356101) * 1) * 10)/ 9);
       a9 = 2;
       return -1;
     } else if(((((((input == 1) && (a9==3)) && a14 <= -148 ) && ((-178 < a21) && (-144 >= a21)) ) && (a8==7)) && ((-78 < a27) && (100 >= a27)) )){
      a27 = ((((a27 % 40)+ 141) / 5) + 115);
      a21 = ((((a21 - -110936) / 5) - -345538) - 367831);
       a8 = 6;
       a9 = 6;
       return 25;
     } else if(((a9==3) && (((((input == 2) && (a8==7)) && a14 <= -148 ) && ((-78 < a27) && (100 >= a27)) ) && ((-178 < a21) && (-144 >= a21)) ))){
      a27 = (((a27 - 146150) - -675307) + -547558);
      a21 = ((((a21 * 10)/ 8) + -597948) + -904);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==5) && (( ((100 < a27) && (182 >= a27)) && ((input == 3) && (( ((-144 < a21) && (5 >= a21)) && (a9==2)) || (((a9==5) && ((-178 < a21) && (-144 >= a21)) ) || ((a9==6) && ((-178 < a21) && (-144 >= a21)) ))))) && a14 <= -148 ))){
      a21 = (((((a21 % 16)+ -159) * 5) % 16)+ -149);
       a8 = 4;
       a9 = 4;
       return -1;
     } else if(( ((-144 < a21) && (5 >= a21)) && ((( a14 <= -148 && ((input == 5) && (((a9==2) || (a9==3)) || (a9==4)))) && ((-78 < a27) && (100 >= a27)) ) && (a8==7)))){
      a27 = (((((a27 % 40)- -142) / 5) + -39478) + 39578);
       a8 = 5;
       a9 = 2;
       return 21;
     } else if((((a8==8) && ( a14 <= -148 && ((input == 1) && ((( a21 <= -178 && (a9==6)) || ((a9==2) && ((-178 < a21) && (-144 >= a21)) )) || ( ((-178 < a21) && (-144 >= a21)) && (a9==3)))))) && ((100 < a27) && (182 >= a27)) )){
      a27 = ((((((a27 * -8)/ 10) - -486883) * 1) * -1)/ 10);
      a21 = ((((a21 + 190246) % 299911)+ -300088) + -2);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-178 < a21) && (-144 >= a21)) && (((((input == 2) && ((-78 < a27) && (100 >= a27)) ) && (a8==5)) && (a9==2)) && a14 <= -148 ))){
      a27 = (((a27 - 178423) - 119687) * 2);
      a21 = (((a21 - 490621) - 13072) + -17329);
       a8 = 4;
       return -1;
     } else if((((a9==3) && ( ((-78 < a27) && (100 >= a27)) && (((input == 2) && a14 <= -148 ) && 5 < a21 ))) && (a8==4))){
      a27 = (((a27 - 439906) - 124074) / 5);
      a21 = ((((((a21 % 299911)+ -300088) / 5) / 5) * 255)/ 10);
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( a27 <= -78 && ((a8==7) && ( ((-178 < a21) && (-144 >= a21)) && (((a9==2) || (a9==3)) && (input == 2))))))){
      a21 = ((((a21 * 13)/ 10) + -225891) - -217524);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a27 <= -78 && ((a8==8) && ( a14 <= -148 && (((( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ((a9==2) && ((-144 < a21) && (5 >= a21)) )) || ((a9==3) && ((-144 < a21) && (5 >= a21)) )) && (input == 6)))))){
      a21 = (((a21 - 326594) + -257213) / 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((((input == 3) && (( 5 < a21 && (a9==2)) || (( ((-144 < a21) && (5 >= a21)) && (a9==5)) || ( ((-144 < a21) && (5 >= a21)) && (a9==6))))) && a14 <= -148 ) && 182 < a27 ) && (a8==5))){
      a27 = ((((a27 - 600105) - 54) + 76175) - 76140);
      a21 = ((((a21 % 299911)+ -300088) - 1) + -1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( a14 <= -148 && ((input == 4) && ((( 5 < a21 && ((a8==7) && (a9==6))) || ( a21 <= -178 && ((a8==8) && (a9==2)))) || (((a8==8) && (a9==3)) && a21 <= -178 )))) && a27 <= -78 )){
      a21 = (((((a21 % 299911)- 300088) - 2) / 5) - 479603);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==8) && (( a14 <= -148 && (((input == 2) && ((a9==3) || (a9==4))) && a27 <= -78 )) && 5 < a21 ))){
      a21 = ((((a21 * 9)/ 10) + -541487) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((-148 < a14) && (13 >= a14)) && ( a27 <= -78 && (((a8==7) && (input == 1)) && (a9==2)))) && a21 <= -178 )){
      a14 = (((a14 - -307166) - 49185) + -291887);
      a27 = ((((a27 - -92418) % 299908)+ 300090) - 0);
      a21 = ((((a21 - -600113) + -73115) + 48705) + 24362);
       a8 = 5;
       a9 = 6;
       return -1;
     } else if(((a8==5) && ( 5 < a21 && ( ((100 < a27) && (182 >= a27)) && (((input == 2) && (((a9==4) || (a9==5)) || (a9==6))) && a14 <= -148 ))))){
      a27 = ((((a27 / 5) + -531227) * 10)/ 9);
      a21 = (((a21 / 5) + -592891) - 698);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==4) && (((( ((-178 < a21) && (-144 >= a21)) && (a9==2)) || (((a9==5) && a21 <= -178 ) || ( a21 <= -178 && (a9==6)))) && (input == 5)) && a14 <= -148 )) && 182 < a27 )){
      a27 = (((a27 - 600122) * 1) + -6);
      a21 = (((((a21 * 9)/ 10) / 5) / 5) + -553055);
       a9 = 2;
       return -1;
     } else if(( 182 < a27 && ((a8==7) && (( a21 <= -178 && (((a9==3) || (a9==4)) && (input == 3))) && a14 <= -148 )))){
      a27 = ((((a27 - 600079) - -575920) + -275525) + -300470);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((100 < a27) && (182 >= a27)) && ((a8==8) && ( a14 <= -148 && ((((a9==4) || (a9==5)) && (input == 3)) && ((-178 < a21) && (-144 >= a21)) ))))){
       a8 = 4;
       a9 = 3;
       return 25;
     } else if(((a8==8) && ((((((a9==6) && ((-144 < a21) && (5 >= a21)) ) || ( 5 < a21 && (a9==2))) && (input == 4)) && a27 <= -78 ) && a14 <= -148 ))){
      a27 = (((((a27 % 88)+ 21) + 52) - -591300) - 591338);
      a21 = ((((a21 % 16)+ -159) + -3) * 1);
       a8 = 5;
       a9 = 5;
       return 21;
     } else if(( 182 < a27 && ((a8==7) && ( a14 <= -148 && ((((a9==4) || ((a9==2) || (a9==3))) && (input == 4)) && ((-178 < a21) && (-144 >= a21)) ))))){
      a27 = (((a27 - 600124) - 29) - 19);
      a21 = ((((a21 * 13)/ 10) - 220262) * 2);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==8) && (( 5 < a21 && ((((a9==3) || (a9==4)) && (input == 6)) && a27 <= -78 )) && a14 <= -148 ))){
      a21 = ((((a21 % 299911)+ -300088) - -188218) - 432691);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((((input == 1) && ((-178 < a21) && (-144 >= a21)) ) && (a9==4)) && ((-78 < a27) && (100 >= a27)) ) && a14 <= -148 ) && (a8==5))){
      a27 = (((a27 - 422455) - 105104) / 5);
      a21 = ((((a21 - 576126) - 15067) + 673911) - 437192);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((( ((-148 < a14) && (13 >= a14)) && ( a27 <= -78 && ((input == 2) && (( ((-144 < a21) && (5 >= a21)) && (a9==6)) || ( 5 < a21 && (a9==2)))))) && (a8==6))){
      a21 = ((((((a21 * 9)/ 10) % 74)- 69) - -401021) + -401020);
       a8 = 7;
       a9 = 5;
       return 21;
     } else if(((a8==6) && ((a9==5) && ( a14 <= -148 && (((input == 6) && ((-78 < a27) && (100 >= a27)) ) && ((-178 < a21) && (-144 >= a21)) ))))){
      a27 = ((((a27 % 40)+ 140) + 0) * 1);
      a21 = ((((((a21 + -487552) * 10)/ 9) + 763828) * -1)/ 10);
       a8 = 5;
       a9 = 4;
       return 25;
     } else if(((a8==6) && ( a14 <= -148 && (( ((-78 < a27) && (100 >= a27)) && ((input == 2) && ((a9==3) || (a9==4)))) && ((-178 < a21) && (-144 >= a21)) )))){
      a27 = ((((a27 + 80415) / 5) * 10)/ 9);
      a21 = ((((a21 * 5) * 5) + 100418) - 227741);
       a8 = 4;
       a9 = 5;
       return 21;
     } else if(((( ((100 < a27) && (182 >= a27)) && ((input == 1) && (((a9==2) && ((-144 < a21) && (5 >= a21)) ) || (( ((-178 < a21) && (-144 >= a21)) && (a9==5)) || ( ((-178 < a21) && (-144 >= a21)) && (a9==6)))))) && (a8==5)) && a14 <= -148 )){
      a27 = ((((a27 * 5) / 5) - -98392) + -98501);
      a21 = ((((a21 % 16)+ -160) - 432040) + 432038);
       a8 = 4;
       a9 = 2;
       return 21;
     } else if(( ((-148 < a14) && (13 >= a14)) && (((a8==4) && ((input == 2) && (((a9==6) && ((-178 < a21) && (-144 >= a21)) ) || ((a9==2) && ((-144 < a21) && (5 >= a21)) )))) && a27 <= -78 ))){
      a14 = (((a14 + -187554) - 278882) + -8849);
      a27 = ((((a27 - 0) % 40)- -143) * 1);
      a21 = ((((((a21 % 16)+ -159) - 3) * 5) % 16)- 158);
       a9 = 5;
       return -1;
     } else if(( ((-144 < a21) && (5 >= a21)) && ((a8==4) && ((((input == 4) && ((a9==3) || (a9==4))) && ((-148 < a14) && (13 >= a14)) ) && a27 <= -78 )))){
      a14 = (((a14 - 418732) * 1) * 1);
      a21 = ((((a21 + 294959) % 16)+ -162) - -2);
       a9 = 3;
       return 21;
     } else if(( a27 <= -78 && (( a14 <= -148 && (((input == 1) && ((a9==3) || (a9==4))) && 5 < a21 )) && (a8==8)))){
      a21 = ((((a21 * 9)/ 10) / 5) + -170644);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && ( a14 <= -148 && ( 5 < a21 && ((a8==5) && ((input == 3) && ((a9==3) || (a9==4)))))))){
      a27 = (((a27 - 304966) - 173321) * 1);
      a21 = (((((a21 % 299911)- 300088) / 5) * 5) + -207313);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((( a14 <= -148 && ((input == 6) && (((a9==3) || (a9==4)) || (a9==5)))) && 5 < a21 ) && (a8==5)) && 182 < a27 )){
      a27 = (((((a27 % 88)- 12) + -49) + 178542) + -178492);
       a8 = 8;
       a9 = 4;
       return -1;
     } else if(((a8==7) && ( a14 <= -148 && ( 5 < a21 && ((a9==6) && ( ((-78 < a27) && (100 >= a27)) && (input == 2))))))){
      a27 = (((a27 + -322070) * 1) - 93610);
      a21 = (((((((a21 % 299911)+ -300088) * 10)/ 9) / 5) * 46)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-144 < a21) && (5 >= a21)) && ((( a14 <= -148 && ((input == 6) && ((a9==6) || ((a9==4) || (a9==5))))) && (a8==8)) && ((-78 < a27) && (100 >= a27)) ))){
      a27 = (((a27 / 5) / 5) + -465283);
      a21 = ((((a21 + 223503) + -727942) * 10)/ 9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a14 <= -148 && ( 182 < a27 && (((((a8==5) && (a9==2)) && a21 <= -178 ) || (( 5 < a21 && ((a8==4) && (a9==5))) || ( 5 < a21 && ((a8==4) && (a9==6))))) && (input == 2))))){
      a27 = (((a27 + -188035) / 5) - 254566);
      a21 = ((((a21 % 299911)+ -300088) / 5) - 136210);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((a8==5) && ( a14 <= -148 && (((input == 4) && (((a9==3) && ((-144 < a21) && (5 >= a21)) ) || (( ((-178 < a21) && (-144 >= a21)) && (a9==6)) || ((a9==2) && ((-144 < a21) && (5 >= a21)) )))) && 182 < a27 )))){
      a27 = ((((((a27 * -5)/ 10) * 1) / 5) * 44)/ 10);
      a21 = (((a21 - 284965) * 2) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-78 < a27) && (100 >= a27)) && (((a8==8) && (( a14 <= -148 && (input == 5)) && ((-144 < a21) && (5 >= a21)) )) && (a9==3)))){
      a27 = ((((a27 - 414316) + 700207) * 10)/ -9);
      a21 = (((((a21 - 34785) + -42142) + 141831) * -1)/ 10);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a21 <= -178 && (((a8==7) && (( a14 <= -148 && (input == 4)) && a27 <= -78 )) && (a9==3)))){
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( 5 < a21 && ( a14 <= -148 && (((((a9==2) || (a9==3)) && (input == 5)) && (a8==7)) && ((100 < a27) && (182 >= a27)) )))){
      a27 = ((((a27 * 5) * 10)/ -9) - 176048);
      a21 = ((((a21 % 299911)+ -300088) + 471741) + -573725);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((((((a9==5) && ((-178 < a21) && (-144 >= a21)) ) || ((a9==6) && ((-178 < a21) && (-144 >= a21)) )) || ( ((-144 < a21) && (5 >= a21)) && (a9==2))) && (input == 3)) && (a8==4)) && a14 <= -148 ) && 182 < a27 )){
      a27 = (((((a27 % 40)- -137) / 5) * 10)/ 2);
      a21 = (((a21 - 315888) - 127730) * 1);
       a9 = 3;
       return -1;
     } else if(((( a14 <= -148 && ( 182 < a27 && ((input == 5) && ((a9==6) || ((a9==4) || (a9==5)))))) && ((-144 < a21) && (5 >= a21)) ) && (a8==6))){
      a27 = ((((a27 * -5)/ 10) + -228840) * 1);
      a21 = ((((a21 - 56480) - -212549) * 10)/ -9);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( ((-144 < a21) && (5 >= a21)) && (( ((-78 < a27) && (100 >= a27)) && (input == 3)) && (a8==8))) && (a9==3)) && a14 <= -148 )){
      a27 = (((((a27 - 261167) * 10)/ 9) * 10)/ 9);
      a21 = (((a21 - 290849) / 5) + -271877);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( ((-144 < a21) && (5 >= a21)) && ( a14 <= -148 && (( 182 < a27 && (((a9==5) || (a9==6)) && (input == 1))) && (a8==7))))){
      a27 = ((((a27 * -5)/ 10) - -98076) - 345332);
      a21 = (((a21 + -15400) / 5) - -200);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if((((a8==7) && ( 182 < a27 && (((input == 2) && ((a9==5) || (a9==6))) && ((-178 < a21) && (-144 >= a21)) ))) && a14 <= -148 )){
      a27 = (((((a27 * -5)/ 10) * 10)/ 9) - 73480);
      a21 = (((a21 + -545010) - 16935) * 1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((((a8==4) && (input == 4)) && a14 <= -148 ) && (a9==3)) && 182 < a27 ) && ((-144 < a21) && (5 >= a21)) )){
       a8 = 5;
       a9 = 5;
       return 23;
     } else if((((( ((-144 < a21) && (5 >= a21)) && (((a9==4) || ((a9==2) || (a9==3))) && (input == 2))) && a14 <= -148 ) && (a8==7)) && ((-78 < a27) && (100 >= a27)) )){
      a27 = ((((a27 - 437026) / 5) * 10)/ 9);
      a21 = (((a21 - 233728) / 5) * 5);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(( a27 <= -78 && ((a8==7) && (( ((-148 < a14) && (13 >= a14)) && ((input == 2) && (a9==5))) && ((-144 < a21) && (5 >= a21)) )))){
      a14 = ((((a14 + -92086) + 458013) * -1)/ 10);
      a21 = ((((((a21 - -69534) % 16)+ -166) * 5) % 16)+ -156);
       a8 = 5;
       a9 = 3;
       return -1;
     } else if(( a27 <= -78 && ((a9==5) && ((a8==8) && ( a14 <= -148 && ((input == 6) && 5 < a21 )))))){
      a27 = (((((a27 % 88)+ 59) * 5) % 88)+ 11);
       a8 = 5;
       a9 = 2;
       return 25;
     } else if(((((a8==8) && ((input == 5) && (( ((-144 < a21) && (5 >= a21)) && (a9==6)) || ( 5 < a21 && (a9==2))))) && a14 <= -148 ) && a27 <= -78 )){
      a21 = (((a21 - 0) / 5) - 431053);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((((input == 6) && ((((a9==6) && (a8==7)) && 5 < a21 ) || ( a21 <= -178 && ((a9==2) && (a8==8))))) && ((100 < a27) && (182 >= a27)) ) && a14 <= -148 )){
      a27 = (((a27 / 5) + -42786) + -547619);
      a21 = ((((a21 % 299911)+ -300088) - 1) + -1);
       a8 = 4;
       a9 = 2;
       return -1;
     } else if(((( a14 <= -148 && ((( ((-178 < a21) && (-144 >= a21)) && (a9==2)) || (( a21 <= -178 && (a9==5)) || ( a21 <= -178 && (a9==6)))) && (input == 3))) && ((-78 < a27) && (100 >= a27)) ) && (a8==7))){
      a27 = ((((((a27 % 40)+ 141) - 1) / 5) * 51)/ 10);
      a21 = ((((((a21 % 74)+ -24) * 5) * 5) % 74)- 4);
       a8 = 6;
       a9 = 6;
       return 21;
     }
     return -2;
 }
int input, output;
int main()
{
    output = -1;
    while(1)
    {
        input = __VERIFIER_nondet_int();
  __VERIFIER_assume(input >= 1 && input <= 6);
        output = calculate_output(input);
    }
}
