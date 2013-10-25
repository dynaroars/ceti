#include "sym.h"

namespace crest{
  /*** SymExpr ***/
  SymExpr::SymExpr(): const_(0){}
  SymExpr::SymExpr(value_t c): const_(c){}
  SymExpr::~SymExpr(){}

  bool SymExpr::operator==(const SymExpr &o) const{
    return const_ == o.const_ && coeff_ == o.coeff_;
  }

  const string SymExpr::str() const{
    stringstream ss;
    ss << "(expr) " 
       << "const " << const_
       << ", "
       << "coef " << map2str(coeff_);
    return ss.str();
  }

  bool SymExpr::Parse(std::istream &s){
    size_t len = static_cast<size_t>(s.get());
    s.read((char *)&const_,sizeof(value_t));
    if (s.fail())
      return false;

    coeff_.clear();
    for(size_t i = 0; i < len; ++i){
      var_t v;
      value_t c;
      s.read((char *) &v, sizeof(v));
      s.read((char *) &c, sizeof(c));
      coeff_[v] = c;
    }
    cout << "coeff " << map2str(coeff_) << endl; 
    return !s.fail();
  }

  
  /*** SymPred ***/
  SymPred::SymPred()
    : op_(EQ), expr_(new SymExpr(0)){}

  // SymPred::SymPred(compare_op_t op, SymExpr* expr)
  //   : op_(op), expr_(expr) {}

  SymPred::~SymPred(){delete expr_;}

  const string SymPred::str() const{
    stringstream ss;
    ss << "(pred) " 
       << "op " << op_ 
       << ", "
       << expr_->str();
    return ss.str();
  }
  
  bool SymPred::operator==(const SymPred &o) const{
    return (op_ == o.op_) && (*expr_ == *o.expr_);
  }

  void SymPred::Negate(){
    op_ = NegateCompareOp(op_);
  }

  bool SymPred::Parse(std::istream &s){
    op_ = static_cast<compare_op_t>(s.get());
    return (expr_->Parse(s) && !s.fail());
  }


  /*** SymPath ***/
  SymPath::SymPath(){ }

  SymPath::SymPath(const bool pre_allocate) {
    if (pre_allocate) {

      // To cut down on re-allocation.
      branches_.reserve(4000000);
      constraints_idx_.reserve(50000);
      constraints_.reserve(50000);
    }
  }

  SymPath::~SymPath() {
    for (size_t i = 0; i < constraints_.size(); i++)
      delete constraints_[i];
  }

  const string SymPath::str() const{
    stringstream ss;

    ss << "(path) " << "branches " << vec2str(branches_) << endl;
    ss << "constraints " << endl;
    for(auto cst: constraints_){
      ss << cst->str() << endl;
    }
    ss << "constraints_idx " << vec2str(constraints_idx_);
       
    return ss.str();
  }



  bool SymPath::Parse(std::istream &s){
    vector<SymPred *>::iterator it;
    size_t len;

    //Read the path
    s.read((char*)&len,sizeof(size_t));
    branches_.resize(len);
    s.read((char*)&branches_.front(), len * sizeof(branch_id_t));
    cout << "branches " << vec2str(branches_) << endl;
    if (s.fail())
      return false;

    for (size_t i = 0 ; i < constraints_.size(); ++i)
      delete constraints_[i];

    //read in path constraints
    s.read((char *)&len, sizeof(size_t));
    constraints_idx_.resize(len);
    constraints_.resize(len);
    s.read((char*)&constraints_idx_.front(), len * sizeof(size_t));

    cout << "constraints_idx " << vec2str(constraints_idx_) << endl; 
    //cout << "constraints " << vec2str(constraints_) << endl;

    for(auto it = constraints_.begin(); it != constraints_.end(); ++it){
      *it = new SymPred();
      if(!(*it)->Parse(s))
       	return false;
    }
  
    return !s.fail();
  }

  /*** SymExec ***/
  SymExec::SymExec() { }
  
  SymExec::SymExec(bool pre_allocate)
    : path_(pre_allocate) {std::cout << "SymExec(pre_allocate)\n"; }
  
  SymExec::~SymExec() { }


  const string SymExec::str() const{
    stringstream ss;
    ss << "(exec) "
       << "vars " << map2str(vars()) << ", "
       << "inputs " << vec2str(inputs_) << endl;

    ss << path().str();

    return ss.str();
  }


  bool SymExec::Parse(std::istream &s){
    size_t len;
    s.read((char*) &len, sizeof(len)); //number of input arguments
    printf("len %lu\n",len);
    vars_.clear();

    inputs_.resize(len);
    for (size_t i = 0; i < len; ++i){
      vars_[i] = static_cast<type_t>(s.get());
      s.read((char *)&inputs_[i],sizeof(value_t));
    }
    //cout << "vars " << vec2str(vars_) << endl;
    cout << "inputs " << vec2str(inputs_) << endl;
    cout << "vars "  << map2str(vars_) << endl; 
    
    return (path_.Parse(s) && !s.fail());
  }

  //common utils
  void write_file(const string &file, const string &content){
    std::ofstream out;
    out.open(file);
    if(!out){
      std::cerr << "Failed to open " << file << endl;
      exit(-1);
    }
    out << content;
    out.close();
  }


}
