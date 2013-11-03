#ifndef SYM_H__
#define SYM_H__

#include <sstream>
#include <map>
#include <set>
#include "basic_types.h"

namespace crest{

  class SymExpr{
  public:
    explicit SymExpr(value_t);
    explicit SymExpr(value_t, var_t);
    ~SymExpr();
    bool Parse(std::istream &s);

    void AppendVars(std::set<var_t> *vars) const{
      for (const auto &c: coeff_) vars->insert(c.first);
    }

    bool DependsOn(const std::map<var_t, type_t> &vars) const{
      for(const auto &c: coeff_){
	if (vars.find(c.first) != vars.end()){
	  return true;
	}
      }
      return false;
    }

    bool isConcrete() const {return this->coeff_.empty();}

    value_t const_term() const {return this->const_;}
    const std::map<var_t,value_t>& terms() const {return this->coeff_;}

    friend std::ostream& operator<< (std::ostream &os, const SymExpr &e){
      os << e.const_term() << " + " << e.str() ;
      return os;
    }

    const string str() const{
      std::stringstream ss;
      size_t i = 0;
      for (const auto &c: coeff_) {
	ss << c.second << "*" << "x" << c.first;
	if (++i < coeff_.size()) ss << " + ";
      }
      return ss.str();
    }

    bool operator==(const SymExpr &o) const{
      return const_ == o.const_ && coeff_ == o.coeff_;
    }



  private:
    value_t const_;
    std::map<var_t, value_t> coeff_;
  };

  class SymPred{
  public:
    SymPred();
    ~SymPred();
    bool Parse(std::istream &);

    void Negate(){
      op_ = NegateCompareOp(op_);
    }

    void AppendVars(std::set<var_t> *vars) const{
      expr_->AppendVars(vars);
    }

    bool DependsOn(const std::map<var_t, type_t> &vars) const{
      return this->expr_->DependsOn(vars);
    };

    compare_op_t op() const {return this->op_;}
    const SymExpr &expr() const {return *this->expr_;}
    friend std::ostream& operator<< (std::ostream &os, const SymPred &p){

      os << p.expr() << " " << op_str[p.op()] << " 0";
      return os;
    }

    bool operator==(const SymPred &o) const{
      return (op_ == o.op_) && (*expr_ == *o.expr_);
    }


  private:
    compare_op_t op_;
    SymExpr *expr_;
  };

  class SymPath{
  public: 
    SymPath();
    ~SymPath();

    bool Parse(std::istream &s);

    const vector<branch_id_t> &branches() const {return this->branches_;}
    const vector<SymPred *> &constraints() const {return this->constraints_;}
    const vector<size_t> &constraints_idx() const {return this->constraints_idx_;}

    friend std::ostream& operator<< (std::ostream &os, const SymPath &p){
      os << "(path) " << "branches " << container2str(p.branches()) << endl;
      os << "constraints " << endl ;
      os << container2str(p.constraints()) << endl;
      os << "constraints_idx " << container2str(p.constraints_idx());
      return os;
    }
    
    /* For instrumentation */
    explicit SymPath(bool pre_alloc);
  private:
    vector<branch_id_t> branches_;
    vector<SymPred *> constraints_;
    vector<size_t> constraints_idx_;
  };

  class SymExec {
  public:
    SymExec();
    ~SymExec();
    bool Parse(std::istream &s);

    const std::map<var_t, type_t> &vars() const {return this->vars_;}
    const vector<value_t> &inputs() const {return this->inputs_;}
    const SymPath &path() const {return this->path_;} 


    std::map<var_t, type_t> *mutable_vars(){return &this->vars_;}
    vector<value_t> *mutable_inputs(){return &this->inputs_;}
    SymPath *mutable_path(){return &this->path_;} 

    friend std::ostream& operator<< (std::ostream &os, const SymExec &e){
      os << "(exec) "
	 << "vars " << container2str(e.vars()) << ", "
	 << "inputs " << container2str(e.inputs()) << endl;
      os << e.path();
      return os;
    }

    /* For instrumentation */
    explicit SymExec(bool pre_alloc);
  private:
    std::map<var_t, type_t> vars_;
    vector<value_t> inputs_;
    SymPath path_;
  }; 

  //common utils
  void write_file(const string&, const string&);
}


#endif
