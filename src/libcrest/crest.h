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

/*
 * Shortcut to indicate that a function should be skipped during instrumentation
 */

#define __SKIP __attribute__((crest_skip))


#define CREST_int(x) __CrestInt(&x)

EXTERN void __CrestInt(int * x) __SKIP;

#endif
