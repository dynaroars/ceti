#ifndef SYM_H__
#define SYM_H__

#include <sstream>
#include <map>
#include <set>
#include <algorithm>
#include "basic_types.h"

namespace crest{

  class SymExpr{
  public:
    SymExpr();
    SymExpr(var_t);
    SymExpr(const SymExpr &);
    ~SymExpr();

    void Serialize(std::string *) const;
    bool Parse(std::istream &s);
    void Negate();
    void AppendVars(std::set<var_t> *) const;
    bool DependsOn(const std::map<var_t, type_t> &) const;

    bool IsConcrete() const {return myvars_.empty();}

    const vector<var_t> & myvars() const{return myvars_;}

    friend std::ostream& operator<< (std::ostream &os, const SymExpr &e){
      os << e.expr_str();
      return os;
    }

    const string expr_str() const;
    const string constr_str() const;

    const SymExpr &operator += (const SymExpr &);
    const SymExpr &operator -= (const SymExpr &);
    const SymExpr &operator *= (const SymExpr &);
    const SymExpr &operator /= (const SymExpr &);

    const SymExpr &operator += (const value_t &);
    const SymExpr &operator -= (const value_t &);
    const SymExpr &operator *= (const value_t &);
    const SymExpr &operator /= (const value_t &);
    const SymExpr &operator %= (const value_t &);

    bool operator==(const SymExpr &o) const{
      return myvars_ == o.myvars_ && expr_str_ == expr_str_;
    }

  private:
    vector<var_t>myvars_;
    string expr_str_;
    string constr_str_ ;
    
  };

  class SymPred{
  public:
    SymPred();
    SymPred(compare_op_t, SymExpr *);
    ~SymPred();

    void Serialize(std::string *) const;
    bool Parse(std::istream &);

    void Negate(){op_ = NegateCompareOp(op_);}

    void AppendVars(std::set<var_t> *vars) const{expr_->AppendVars(vars);}

    bool DependsOn(const std::map<var_t, type_t> &vars) const{
      return expr_->DependsOn(vars);
    }
      
    compare_op_t op() const {return op_;}
    const SymExpr &expr() const {return *expr_;}
    friend std::ostream& operator<< (std::ostream &os, const SymPred &p){
      os << p.expr_str();
      return os;
    }

    const string expr_str() const;

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

    void Serialize(std::string *) const;
    bool Parse(std::istream &s);

    void Push(branch_id_t);
    void Push(branch_id_t, SymPred *pred);

    const vector<branch_id_t> &branches() const {return branches_;}
    const vector<SymPred *> &constraints() const {return constraints_;}
    const vector<size_t> &constraints_idx() const {return constraints_idx_;}

    friend std::ostream& operator<< (std::ostream &os, const SymPath &p){
      os << "(path) " << "branches " << container2str(p.branches()) << endl;
      os << "constraints " << container2str(p.constraints()) << endl;
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

    void Serialize(std::string *) const;
    bool Parse(std::istream &s);

    const std::map<var_t, type_t> &vars() const {return vars_;}
    const vector<value_t> &inputs() const {return inputs_;}
    const SymPath &path() const {return path_;} 


    std::map<var_t, type_t> *mutable_vars(){return &vars_;}
    vector<value_t> *mutable_inputs(){return &inputs_;}
    SymPath *mutable_path(){return &path_;} 

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
