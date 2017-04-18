#define INT 1
#define CHAR 2
#define VAR_LENGTH_STR 3
#define CONST_LENGTH_STR 4
#define VAR_INT_ARR 5
#define CONST_INT_ARR 6
#define VAR_STR_ARR 7
#define CONST_STR_ARR 8

extern int  _mark_int( int addr);
extern char _mark_char( char addr);
extern char _mark_var_str( char* addr);
extern char _mark_const_str( char* addr, int len);
extern char _mark_var_str_arr( char **addr);
extern char _mark_var_int_arr( int **addr );
extern char _mark_const_int_arr( int **addr , int len);
extern char _mark_const_str_arr( char **addr, int len);
