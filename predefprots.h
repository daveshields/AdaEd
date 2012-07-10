/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

/* predef1 */
void predef();
void predef_raise(int, char *);

/* predef2 */
void calendar();

/* predef3 */
int *get_argument_ptr(int);
void get_string_value(int);
char *make_string();
int get_argument_value(int);
float get_float_argument_value(int);
long get_long_argument_value(int);
void get_filenum();
void get_file_argument_or_default();
void return_string(char *, int);

/* predef4 */
void initialize_predef();
void check_opened_ok();
void check_file_open();
void check_status(int);
void open_textio(char);
void load_look_ahead();
void close_textio();
char get_char();
void skip_line();
void put_blanks(int);
void put_char(char);
void put_line();
void put_page();
void put_string(char *);
void put_buffer(char *, int, char);
void open_seq_io(int);
void open_dir_io(int);
void close_file();
void predef_term();
char *predef_alloc(int);
void predef_free(char *);
#ifdef IBM_PC
FILE *fopen_bin(char *, char *);
FILE *fopen_txt(char *, char *);
#endif

/* predef5 */
void scan_enum();
void scan_enum_string(int *);
int scan_integer(int *, int);
int scan_integer_string(int *, int *);
long scan_fixed(int *, int);
long scan_fixed_string(int *, int *);
float scan_float(int *, int);
float scan_float_string(int *, int *);
int enum_ord(int *, int, int);

/* predef6 */

void image_integer(int, int);
void image_fixed (long, int *, int, int, int);
void image_float (float, int, int, int);
void image_enum(int, int *);
