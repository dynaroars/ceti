#include "basic_types.h"

namespace crest{

  class SymExpr{
  public:
    SymExpr();
    explicit SymExpr(value_t c);
    //SymExpr(value_t c, var_t v);
    ~SymExpr();
    const string str() const;
    bool operator==(const SymExpr &) const;

    bool Parse(std::istream &s);
    
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
}
