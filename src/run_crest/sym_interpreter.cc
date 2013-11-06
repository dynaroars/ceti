#include <utility>
#include "sym_interpreter.h"

namespace crest{
  SymInterpreter::SymInterpreter()
    : pred_(nullptr), ex_(true), fun_ret_val_(false), n_inputs_(0){
    stack_.reserve(16);
  }

  //Vu: diff than orig
  SymInterpreter::SymInterpreter(const vector<value_t> &input)
    : SymInterpreter(){
    ex_.mutable_inputs()->assign(input.begin(), input.end());
  }

  void SymInterpreter::ClearStack(id_t id){
    //tvn unused id
    cout << __func__ << endl;

    for(const auto &s: stack_) delete s.expr;
    stack_.clear();
    ClearPredRegister();
    fun_ret_val_ = false;
  }

  void SymInterpreter::Load(id_t id, addr_t addr, value_t val){
    cout << __func__ 
	 << " id " << id 
	 << ", addr " << addr 
	 << ", val " << val << endl;

    const auto &it = mem_.find(addr);
    if(it == mem_.end()) PushConcrete(val);
    else {
      PushSymbolic(new SymExpr(*it->second), val);
    }

    DumpMemory();
  }

  
  void SymInterpreter::Store(id_t id, addr_t addr){
    cout << __func__ << endl;

    assert(stack_.size()>0);
    
    const auto &se = stack_.back();
    if (se.expr){
      if(se.expr->IsConcrete()){
	mem_.erase(addr);
	delete se.expr;
      }
      else mem_[addr] = se.expr;
    }
    else mem_.erase(addr);

    stack_.pop_back();
    ClearPredRegister();

    DumpMemory();
  }



  void SymInterpreter::ApplyUnaryOp(id_t id , unary_op_t op, value_t val){
    cout << __func__ << endl;

    assert(stack_.size() >= 1);
    auto &a = stack_.back();
    if (a.expr){
      switch (op){

      case c_ops::NEGATE:/*strange,  how do you negate a const or term ?*/
	a.expr->Negate();
	ClearPredRegister();
	break;
      case c_ops::LOGICAL_NOT:
	if(pred_){
	  pred_->Negate();
	  break;
	}
      default:
	//concrete
	delete a.expr;
	a.expr = nullptr;
	ClearPredRegister();
      }
    }

    a.concrete = val;
  }

  void SymInterpreter::ApplyBinaryOp(id_t id , binary_op_t op, value_t val){
    cout << __func__ << endl;

    assert(stack_.size() >= 2);
    auto &a = *(stack_.rbegin()+1);
    auto &b = stack_.back();
    
    cout << "a conc " << a.concrete; 
    if (a.expr) cout << ", xpr " << *a.expr; 
    cout << endl;
    cout << "b conc " << a.concrete; 
    if (b.expr) cout << ", xpr " << *b.expr; 
    cout << endl;


    if (a.expr || b.expr){
      switch(op){
      case c_ops::ADD:
	cout << "ADD" << endl;
	if (a.expr == nullptr){
	  std::swap(a,b);
	  *a.expr += b.concrete;
	}else if (b.expr == nullptr){
	  *a.expr += b.concrete;
	}else {
	  *a.expr += *b.expr;
	  delete b.expr;
	}
	break;
      
      case c_ops::SUBTRACT:  /*tvn check*/
	cout << "SUBTRACT" << endl;
	if(a.expr == nullptr){
	  b.expr->Negate(); /*tvn ???*/
	  std::swap(a,b);
	  *a.expr += b.concrete;
	}else if (b.expr == nullptr){
	  *a.expr -= b.concrete;
	}else {
	  *a.expr -= *b.expr;
	  delete b.expr;
	}
	break;

      case c_ops::MULTIPLY:
	cout << "MULTIPLY" << endl;

	if (a.expr == nullptr){
	  std::swap(a,b);
	  *a.expr *= b.concrete;
	}else if (b.expr == nullptr){
	  *a.expr *= b.concrete;
	}else {
	  std::swap(a,b); /*tvn why*/
	  *a.expr *= b.concrete;
	  delete b.expr;
	}
	cout << "res " << *a.expr  << endl;
	break;

      case c_ops::SHIFT_L: /*tvn why*/
	cout << "SHIFT_L" << endl;

	if(a.expr != nullptr){
	  *a.expr *= (1 << b.concrete);
	}
	delete b.expr;
	break;

      default:
	delete a.expr; //a.expr = nullptr;
	delete b.expr; b.expr = nullptr;
      }
    }

    a.concrete = val;
    DumpMemory();
    stack_.pop_back();
    ClearPredRegister();

    DumpMemory();
  }


  void SymInterpreter::ApplyCompareOp(id_t id , compare_op_t op, value_t val){
    cout << __func__ << endl;

    assert(stack_.size() >= 2);
    auto &a = *(stack_.rbegin()+1);
    auto &b = stack_.back();

    if (a.expr) cout << "a " << *a.expr << endl;
    if (b.expr) cout << "b " << *b.expr << endl; 

    if(a.expr || b.expr){
      //symbolic a -= b, why?  I think so that we have a <= b ==> a-b <= 0
      if(a.expr == nullptr){
	b.expr->Negate();
	std::swap(a,b);
	*a.expr += b.concrete;
      }else if(b.expr == nullptr){
	*a.expr -= b.concrete;
      }else{
	*a.expr -= *b.expr;
	delete b.expr;
      }

      if (!a.expr->IsConcrete()){
	pred_ = new SymPred(op, a.expr);
      }else {
	ClearPredRegister();
	delete a.expr;
      }
      
      a.expr = nullptr;

    }
    
    a.concrete = val;
    stack_.pop_back();

    DumpMemory();
  }


  void SymInterpreter::Call(id_t id, func_id_t fid){
    cout << __func__ << endl;

    //tvn: id, fid unused
    ex_.mutable_path()->Push(kCallId);

    DumpMemory();
  }

  void SymInterpreter::Return(id_t id){
    cout << __func__ << endl;

    //tvn: id unused
    ex_.mutable_path()->Push(kReturnId);
    assert(stack_.size() <= 1);
    fun_ret_val_ = (stack_.size() == 1);
  }

  void SymInterpreter::Branch(id_t id, branch_id_t bid, bool pred_val){
    cout << __func__ << endl;

    assert(stack_.size() == 1);
    stack_.pop_back();
    if(pred_ && !pred_val) pred_->Negate();
    ex_.mutable_path()->Push(bid, pred_);
    pred_ = nullptr;
  }


  value_t SymInterpreter::NewInput(type_t type, addr_t addr){
    cout << __func__ << endl;
    cout << "mem size " << mem_.size() << ", n_inpus " << n_inputs_ << endl;
    mem_[addr] = new SymExpr(1, n_inputs_);
    cout << *mem_[addr] << endl;

    ex_.mutable_vars()->insert(std::make_pair(n_inputs_, type));

    auto ret = 0;
    if (n_inputs_ < ex_.inputs().size()){
      ret = ex_.inputs()[n_inputs_];
    }
    else{
      auto max = 10000, min = -1000;
      ret = CastTo(min+(rand() %(int)(max-min+1)),type);
      ex_.mutable_inputs()->push_back(ret);
    }
    n_inputs_++;
    cout <<"ret " << ret << endl;
    return ret;
  }

  void SymInterpreter::PushConcrete(value_t val){
    cout << __func__ << endl;
    cout << val << endl;
    PushSymbolic(nullptr, val);
  }
  
  void SymInterpreter::PushSymbolic(SymExpr *expr, value_t val){
    cout << __func__ << endl;
    
    stack_.push_back(StackElem());
    auto &se = stack_.back();
    se.expr = expr;
    se.concrete = val;
    if (se.expr) cout << *se.expr << endl;
    cout << se.concrete << endl;
  }

  void SymInterpreter::ClearPredRegister(){
    cout << __func__ << endl;
    delete pred_; 
    pred_=nullptr;
  }

  void SymInterpreter::DumpMemory(){
    cout << __func__ << endl;
    cout << "mem \n" ;
    for(const auto &m: mem_)
      cout << m.first << ": " << *m.second << 
	" [" << *(int *)m.first << "]" << endl;

    cout<< "\nstack \n";
    for (size_t i= 0 ; i < stack_.size(); ++i){
      string s = "";
      if(stack_[i].expr)s = stack_[i].expr->str();
      else if(i == stack_.size() - 1 && pred_)s = pred_->str();

      cout << "s" << i << ": " << stack_[i].concrete << " [" << s << "]";
      if((i == stack_.size() - 1) && fun_ret_val_) cout << "(RET VAL)";
      cout << "\n";
    }
    if(stack_.empty() && fun_ret_val_) cout << "MISSING RET VAL" ;
    
    cout << "\n";

  }

}


