#include "run_crest/sym_interpreter.h"
#include "libcrest/crest.h"

using namespace crest;

static SymInterpreter* SI;
static int pre_symbolic;

void __CrestInt(int *x){
  pre_symbolic = 0;
  *x = (int)SI->NewInput(c_types::INT, (addr_t)x);
}

