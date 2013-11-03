#include "sym_interpreter.h"

namespace crest{
  SymInterpreter::SymInterpreter()
    :pred_(NULL), ex_(true), fun_ret_val_(false), n_inputs_(0){
    stack_.reserve(16);
  }

  value_t SymInterpreter::NewInput(type_t type, addr_t addr){
    mem_[addr] = new SymExpr(1, n_inputs_);
    ex_.mutable_vars()->insert(std::make_pair(n_inputs_, type));

    value_t ret = 0;
    if (n_inputs_ < ex_.inputs().size()){
      ret = ex_.inputs()[n_inputs_];
    }
    else{
      int max=10000, min = -1000;
      ret = CastTo(min+(rand() %(int)(max-min+1)),type);
      ex_.mutable_inputs()->push_back(ret);
    }
    n_inputs_++;
    return ret;
  }

}
