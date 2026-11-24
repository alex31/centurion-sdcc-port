/* GCC-compatible bit operations on CPU6 integer types. */
#ifndef CPU6_BITBUILTINS_H
#define CPU6_BITBUILTINS_H

bool cpu6IsBitBuiltin (const ast *call);
ast *cpu6DecorateBitBuiltin (ast *call);

#endif
