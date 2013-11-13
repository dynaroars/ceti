/*
  Unlike other files using C++, this file contains mostly C code.
  This is because these code will be inserted the input C programs.
*/


#ifndef LIBCREST_CREST_H_
#define LIBCREST_CREST_H_

#ifdef __cplusplus  
#define EXTERN extern "C"
#else
#define EXTERN extern
#endif                                                                  

#define __CREST_ID int
#define __CREST_BRANCH_ID int
#define __CREST_FUNC_ID unsigned int
#define __CREST_VAL long long int
#define __CREST_ADDR unsigned long int
#define __CREST_OP int
#define __CREST_BOOL unsigned char

//corresponding value in kOpTable in .cc
enum {
  /* binary arithmetic */
  __CREST_ADD       =  0,
  __CREST_SUBTRACT  =  1,
  __CREST_MULTIPLY  =  2,
  __CREST_DIVIDE    =  3,
   __CREST_MOD       = 4,
  /* binary bitwise operators */
  __CREST_AND       =  5,
  __CREST_OR        =  6,
  __CREST_XOR       =  7,
  __CREST_SHIFT_L   =  8,
  __CREST_SHIFT_R   =  9,
  /* binary logical operators */
  __CREST_L_AND     = 10,
  __CREST_L_OR      = 11,
  /* binary comparison */
  __CREST_EQ        = 12,
  __CREST_NEQ       = 13,
  __CREST_GT        = 14,
  __CREST_LEQ       = 15,
  __CREST_LT        = 16,
  __CREST_GEQ       = 17,
  /* unhandled binary operators */
  __CREST_CONCRETE  = 18,
  /* unary operators */  
  __CREST_NEGATE    = 19,
  __CREST_NOT       = 20,
  __CREST_L_NOT     = 21,
};

/*
 * Shortcut to indicate that a function should be skipped during instrumentation
 */

#define __SKIP __attribute__((crest_skip))

#define CREST_unsigned_char(x) __CrestUChar(&x)
#define CREST_unsigned_short(x) __CrestUShort(&x)
#define CREST_unsigned_int(x) __CrestUInt(&x)
#define CREST_char(x) __CrestChar(&x)
#define CREST_short(x) __CrestShort(&x)
#define CREST_int(x) __CrestInt(&x)

EXTERN void __CrestInit() __SKIP;
EXTERN void __CrestLoad(__CREST_ID, __CREST_ADDR, __CREST_VAL) __SKIP;
EXTERN void __CrestStore(__CREST_ID, __CREST_ADDR) __SKIP;
EXTERN void __CrestClearStack(__CREST_ID) __SKIP;
EXTERN void __CrestApply1(__CREST_ID, __CREST_OP, __CREST_VAL) __SKIP;
EXTERN void __CrestApply2(__CREST_ID, __CREST_OP, __CREST_VAL) __SKIP;

EXTERN void __CrestHandleReturn(__CREST_ID, __CREST_VAL) __SKIP;
EXTERN void __CrestCall(__CREST_ID, __CREST_FUNC_ID) __SKIP;
EXTERN void __CrestReturn(__CREST_ID) __SKIP;
EXTERN void __CrestBranch(__CREST_ID, __CREST_BRANCH_ID, __CREST_BOOL) __SKIP;

EXTERN void __CrestUChar(unsigned char* x) __SKIP;
EXTERN void __CrestUShort(unsigned short* x) __SKIP;
EXTERN void __CrestUInt(unsigned int* x) __SKIP;
EXTERN void __CrestChar(char* x) __SKIP;
EXTERN void __CrestShort(short* x) __SKIP;
EXTERN void __CrestInt(int * x) __SKIP;

#endif
