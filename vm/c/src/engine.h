#ifndef ENGINE__H
#define ENGINE__H

#include "vmtypes.h"

/* Setup the interpreter */
void engine_setup(void);

/* Tear down the interpreter */
void engine_cleanup(void);

/* Add an instruction to the code area of the memory */
void engine_emit(instr_t instr, instr_t** instr_ptr);

void engine_set_Cb(value_t* new_value);

/* Interpret the program in the code area of the memory */
value_t engine_run(void);

#endif // ENGINE__H
