#ifndef SYM_INTERPRETER_H__
#define SYM_INTERPRETER_H__

#include <map>
#include "basic_types.h"
#include "sym.h"

namespace crest{

  class SymInterpreter{
  public:
    explicit SymInterpreter();
    ~SymInterpreter();
    value_t NewInput(type_t, addr_t);
    
  private:
    struct StackElem{
      SymExpr *expr; //NULL to indicate concrete
      value_t concrete;
    };
    vector<StackElem> stack_;

    std::map<addr_t, SymExpr *> mem_;

    SymPred *pred_;
    SymExec ex_;
    bool fun_ret_val_;
    unsigned int n_inputs_;
  };
}


#endif
