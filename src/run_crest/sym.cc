#include "sym.h"

namespace crest{
  /*** SymExpr ***/
  SymExpr::SymExpr(value_t c): const_(c){}
  SymExpr::SymExpr(value_t c, var_t v): const_(c){
    coeff_[v] = c;
  }
  SymExpr::~SymExpr(){}

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
    cout << __func__ << endl;
    cout << "const " << const_ << endl;
    cout << "coeff " << container2str(coeff_) << endl; 
    return !s.fail();
  }


  /*** SymPred ***/
  SymPred::SymPred(): op_(c_ops::EQ), expr_(new SymExpr(0)){}
  SymPred::~SymPred(){delete expr_;}

  bool SymPred::Parse(std::istream &s){
    op_ = static_cast<compare_op_t>(s.get());
    cout << __func__ << endl;
    cout << "op " << op_ << endl;
    return (expr_->Parse(s) && !s.fail());
  }


  /*** SymPath ***/
  SymPath::SymPath(){ }
  SymPath::~SymPath() {
    for (size_t i = 0; i < constraints_.size(); i++)
      delete constraints_[i];
  }


  bool SymPath::Parse(std::istream &s){
    size_t len;

    //Read the path
    s.read((char*)&len,sizeof(size_t));
    branches_.resize(len);
    s.read((char*)&branches_.front(), len * sizeof(branch_id_t));
    if (s.fail())
      return false;

    for (size_t i = 0 ; i < constraints_.size(); ++i)
      delete constraints_[i];

    //read in path constraints
    s.read((char *)&len, sizeof(size_t));
    constraints_idx_.resize(len);
    constraints_.resize(len);

    s.read((char*)&constraints_idx_.front(), len * sizeof(size_t));

    cout << __func__ << endl;
    cout << "branches " << container2str(branches_) << endl;
    cout << "constraints_idx " << container2str(constraints_idx_) << endl; 
    cout << "constraints " << constraints_.size() << endl;
    for(auto it = constraints_.begin(); it != constraints_.end(); ++it){
      *it = new SymPred();
      if(!(*it)->Parse(s))
       	return false;
    }
  
    return !s.fail();
  }

  /* For instrumentation */
  SymPath::SymPath(bool pre_alloc){
    if (pre_alloc){
      branches_.reserve(4000000);
      constraints_idx_.reserve(50000);
      constraints_.reserve(50000);
    }
  }
   

  /*** SymExec ***/
  SymExec::SymExec() {}
  SymExec::~SymExec() {}

  bool SymExec::Parse(std::istream &s){
    size_t len;
    s.read((char*) &len, sizeof(len)); //number of input arguments
    vars_.clear();

    inputs_.resize(len);
    for (size_t i = 0; i < len; ++i){
      vars_[i] = static_cast<type_t>(s.get());
      s.read((char *)&inputs_[i],sizeof(value_t));
    }

    cout << __func__ << endl;
    cout << "inputs " << container2str(inputs_) << endl;
    cout << "vars "  << container2str(vars_) << endl; 
    return (path_.Parse(s) && !s.fail());
  }

  /* For instrumentation */
  SymExec::SymExec(bool pre_alloc)
    :path_(pre_alloc){}



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
