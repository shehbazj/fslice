
extern int  _mark_int( int addr);
extern char _mark_char( char addr);
extern char _mark_var_str( char* addr);
extern char _mark_const_str( char* addr, int len);
extern char _mark_var_str_arr( char **addr);
extern char _mark_var_int_arr( int **addr );
extern char _mark_const_int_arr( int **addr , int len);
extern char _mark_const_str_arr( char **addr, int len);
