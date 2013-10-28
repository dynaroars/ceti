#ifndef SYM_H__
#define SYM_H__

#include "basic_types.h"

namespace crest{

  class SymExpr{
  public:
    SymExpr();
    explicit SymExpr(value_t);
    //SymExpr(value_t c, var_t v);
    ~SymExpr();
    bool operator==(const SymExpr &) const;
    const string str() const;

    bool Parse(std::istream &s);
    void AppendVars(set<var_t> *) const;
    bool DependsOn(const map<var_t, type_t> &) const;

    bool isConcrete() const {return coeff_.empty();}

    value_t const_term() const {return const_;}
    const map<var_t,value_t>& terms() const {return coeff_;}

  private:
    value_t const_;
    map<var_t, value_t> coeff_;
  };

  class SymPred{
  public:
    SymPred();
    //SymPred(compare_op_t op, SymExpr* expr);
    ~SymPred();
    const string str() const;
    bool operator==(const SymPred &) const;
    void Negate();
    bool Parse(std::istream &s);

    void AppendVars(set<var_t> *vars) const{
      expr_->AppendVars(vars);
    }
    bool DependsOn(const map<var_t, type_t> &vars) const{
      return expr_->DependsOn(vars);
    };

    compare_op_t op() const{return op_;}
    const SymExpr &expr() const {return *expr_;}
  private:

    compare_op_t op_;
    SymExpr *expr_;
  };

  class SymPath{
  public: 
    SymPath();
    SymPath(bool pre_allocate);
    ~SymPath();
    const string str() const;

    bool Parse(std::istream &s);

    const vector<branch_id_t> &branches() const {return branches_;}
    const vector<SymPred *> &constraints() const {return constraints_;}
    const vector<size_t> &constraints_idx() const {return constraints_idx_;}

  private:

    vector<branch_id_t> branches_;
    vector<SymPred *> constraints_;
    vector<size_t> constraints_idx_;
  };

  class SymExec {
  public:
    SymExec();
    explicit SymExec(const bool pre_allocate);
    ~SymExec();

    const string str() const;

    bool Parse(std::istream &s);

    //non-mutable
    const map<var_t, type_t> &vars() const {return vars_;}
    const vector<value_t> &inputs() const {return inputs_;}
    const SymPath &path() const {return path_;} 

    //mutable
    map<var_t, type_t> *mutable_vars() {return &vars_;}
    vector<value_t> *mutable_inputs() {return &inputs_;}
    SymPath *mutable_path() {return &path_;}

  private:

    map<var_t, type_t> vars_;
    vector<value_t> inputs_;
    SymPath path_;
  }; 

  //common utils
  void write_file(const string&, const string&);
  string constraints2str(const vector<SymPred *> &);
  string constraints2str(const vector<const SymPred *> &);

}


#endif
