#ifndef SYM_INTERPRETER_H__
#define SYM_INTERPRETER_H__

#include <map>
#include "basic_types.h"
#include "sym.h"

namespace crest{

  class SymInterpreter{
  public:
    SymInterpreter();
    explicit SymInterpreter(const vector<value_t> &);

    void ClearStack(id_t);    
    void Load(id_t, addr_t, value_t);
    void Store(id_t, addr_t);
    
    void ApplyUnaryOp(id_t, unary_op_t, value_t);
    void ApplyBinaryOp(id_t, binary_op_t, value_t);
    void ApplyCompareOp(id_t, compare_op_t, value_t);

    void HandleReturn(id_t, value_t );
    void Call(id_t, func_id_t);
    void Return(id_t);
    void Branch(id_t, branch_id_t, bool);

    value_t NewInput(type_t, addr_t);

    const SymExec &ex() const {return ex_;}
    
  private:
    struct StackElem{
      SymExpr *expr; //nullptr to indicate concrete
      value_t concrete;
    };

    static string StackElem2str(const StackElem &se){
      std::stringstream ss;
      ss << "se: concr " << se.concrete;
      if (se.expr) ss << ", sym " << *se.expr;
      return ss.str();
    }

    vector<StackElem> stack_;

    std::map<addr_t, SymExpr *> mem_;
    SymPred *pred_;
    SymExec ex_;
    bool fun_ret_val_;
    unsigned int n_inputs_;

    //helper
    void PushConcrete(value_t);
    void PushSymbolic(SymExpr *, value_t);
    void ClearPredRegister();

    //debugging
    void DumpMemory();
  };
}


#endif
