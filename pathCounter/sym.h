
enum symType {
	UNDEFINED = 0,
	INT ,
	CONSTANT_STR ,
	VARIABLE_STR ,
	CONSTANT_INT_ARRAY ,
	CONSTANT_STRING_ARRAY ,
	VARIABLE_INT_ARRAY ,
	VARIABLE_STRING_ARRAY ,	
};

extern void _mark( enum symType type, uint64_t addr);
