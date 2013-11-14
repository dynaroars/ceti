#include "sym.h"

namespace crest{
  /*** SymExpr ***/
  SymExpr::SymExpr(){}
  SymExpr::SymExpr(var_t v){

    if (std::find(myvars().cbegin(), myvars().cend(), v) == myvars().end()){
      myvars_.push_back(v);
    }

    expr_str_ = "x" + std::to_string(v);
    constr_str_ = "";
  }
  
  SymExpr::SymExpr(const SymExpr &e){ 
    myvars_ = e.myvars_;
    expr_str_ = e.expr_str_;
    constr_str_ = e.constr_str_;
  }
  SymExpr::~SymExpr(){}

  void SymExpr::Serialize(string *s) const{
    s->append(expr_str_ + "\n");
    s->append(constr_str_ + "\n");
  }
  
  bool SymExpr::Parse(std::istream &s){
    
    std::getline(s, expr_str_);

    for (size_t i = 0; i < expr_str_.size() && expr_str_[i] != '\0'; i++) {
      if (expr_str_[i] == 'x') {
	int var;
	sscanf(&expr_str_[i+1], "%d", &var);
	if (var >= 0 && var < 128){/* valid variable range */
	  myvars_.push_back(var);
	}
      }
    }

    std::getline(s, constr_str_);
    for (size_t i = 0; i < constr_str_.size() && constr_str_[i] != '\0'; i++) {
      if (constr_str_[i] == 'x') {
	int var;
	sscanf(&constr_str_[i+1], "%d", &var);
	if (var >= 0 && var < 128){/* valid variable range */
	  myvars_.push_back(var);
	}
      }
    }

    cout << __func__  << "\nexpr " << expr_str_ << endl;
    cout << __func__  << "\nconstr " << constr_str_ << endl;
    return !s.fail();
  }

  void SymExpr::Negate(){
      expr_str_ = "(- 0 " + expr_str_ + ")";
    }

  void SymExpr::AppendVars(std::set<var_t> *vars) const{
    for (const auto &v: myvars_) vars->insert(v);
  }
  
  bool SymExpr::DependsOn(const std::map<var_t, type_t> &vars) const{
    for(const auto &v: myvars_){
      if (vars.find(v) != vars.end()){
	return true;
      }
    }
    return false;
  }

  const string SymExpr::expr_str() const{return expr_str_;}
  const string SymExpr::constr_str() const{return constr_str_;}
  
  const SymExpr &SymExpr::operator += (const SymExpr &e){
    expr_str_ = "(+ " + expr_str_ + " " + e.expr_str_ + ")";
    return *this;
  }
  const SymExpr &SymExpr::operator += (const value_t &c){
    expr_str_ = "(+ " + expr_str_ + " " + std::to_string(c) + ")";
    return *this;
  }

  const SymExpr &SymExpr::operator -= (const SymExpr &e){
    expr_str_ = "(- " + expr_str_ + " " + e.expr_str_ + ")";
    return *this;
  }
  const SymExpr &SymExpr::operator -= (const value_t &c){
    expr_str_ = "(- " + expr_str_ + " " + std::to_string(c) + ")";
    return *this;
  }

  const SymExpr &SymExpr::operator *= (const SymExpr &e){
    expr_str_ = "(* " + expr_str_ + " " + e.expr_str_ + ")";
    return *this;
  }
  const SymExpr &SymExpr::operator *= (const value_t &c){
    if (c == 0) {
      myvars_.clear();
      expr_str_ = "";
      constr_str_ = "";
    }
    else{
      expr_str_ = "(* " + expr_str_ + " " + std::to_string(c) + ")";
    }

    return *this;
  }

  const SymExpr &SymExpr::operator /= (const SymExpr &e){
    constr_str_ = "not(= e.expr_str_ 0)";
    expr_str_ = "(div " + expr_str_ + " " + e.expr_str_ + " )";
    return *this;
  }
  const SymExpr &SymExpr::operator /= (const value_t &c){
    assert(c!=0);
    expr_str_ = "(div " + expr_str_ + " " + std::to_string(c) + ")";
    return *this;
  }

  const SymExpr &SymExpr::operator %= (const value_t &c){
    /*The semantic of a%b in C is remainder, not mod, 
    e.g., -7%10 = -7 instead of 3.  
    so after obtaining the result z =x%y,  if z < 0, we add z to y */

    assert(c!=0);
    expr_str_ = "(mod " + expr_str_ + " " + std::to_string(c) + ")";
    return *this;
  }

  
  /*** SymPred ***/
  SymPred::SymPred(compare_op_t op, SymExpr *e): op_(op), expr_(e){}
  SymPred::SymPred():SymPred(c_ops::EQ, new SymExpr()){}
  SymPred::~SymPred(){delete expr_;}

  void SymPred::Serialize(std::string *s) const{
    s->push_back(static_cast<char>(op_));
    expr_->Serialize(s);
  }

  bool SymPred::Parse(std::istream &s){
    op_ = static_cast<compare_op_t>(s.get());
    cout << __func__  << "\nop " << op_ << endl;
    return (expr_->Parse(s) && !s.fail());
  }

  void SymPred::Negate(){op_ = NegateCompareOp(op_);}  

  const string SymPred::expr_str() const{
    if (op_ == c_ops::NEQ)
      return "(not (=  " + expr_->expr_str() + " 0))";
    else 
      return "(" + op_str[op_] + " " + expr_->expr_str() + " 0)";
  }

  /*** SymPath ***/
  SymPath::SymPath(){}
  SymPath::SymPath(bool pre_alloc){
    if (pre_alloc){
      branches_.reserve(4000000);
      constraints_idx_.reserve(50000);
      constraints_.reserve(50000);
    }
  }
  SymPath::~SymPath(){for(const auto &c: constraints_) delete c;}

  void SymPath::Push(branch_id_t bid){branches_.push_back(bid);}
  void SymPath::Push(branch_id_t bid, SymPred *constraint){
    if(constraint){
      constraints_.push_back(constraint);
      constraints_idx_.push_back(branches_.size());
    }
    Push(bid);
  }

  void SymPath::Serialize(std::string *s) const{
    auto len = branches_.size();

    //write the path
    s->append((char *)&len, sizeof(len));
    s->append((char *)&branches_.front(), len * sizeof(branch_id_t));

    //write path constraints
    cout << "writing path constraints " << constraints_.size() << endl;
    cout << container2str(constraints_) << endl;
    //cout << container2str(constraints_idx)) << endl;

    len = constraints_.size();
    s->append((char *)&len, sizeof(len));
    s->append((char *)&constraints_idx_.front(), len * sizeof(size_t));
    for(const auto &c: constraints_) c->Serialize(s);
  }

  bool SymPath::Parse(std::istream &s){
    size_t len;

    //read the path
    s.read((char *)&len,sizeof(size_t));
    branches_.resize(len);
    s.read((char *)&branches_.front(), len * sizeof(branch_id_t));
    if (s.fail()) return false;
      

    //read in path constraints
    for(const auto &c: constraints_) delete c;

    s.read((char *)&len, sizeof(size_t));
    constraints_idx_.resize(len);
    constraints_.resize(len);

    s.read((char *)&constraints_idx_.front(), len * sizeof(size_t));

    cout << __func__ << endl;
    cout << "branches " << container2str(branches_) << endl;
    cout << "constraints_idx " << container2str(constraints_idx_) << endl; 
    cout << "constraints " << constraints_.size() << endl;

    for(auto &c:constraints_){
      c = new SymPred();
      if(!c->Parse(s)) return false;
    }
    return !s.fail();
  }

   
  /*** SymExec ***/
  SymExec::SymExec(){}
  SymExec::SymExec(bool pre_alloc):path_(pre_alloc){}
  SymExec::~SymExec(){}

  void SymExec::Serialize(std::string *s) const{
    auto len = vars_.size();
    s->append((char*) &len, sizeof(len));
    for(const auto &v:vars_){
      s->push_back(static_cast<char>(v.second));
      s->append((char *) &inputs_[v.first], sizeof(value_t));
    }
    path_.Serialize(s);
  }

  bool SymExec::Parse(std::istream &s){
    size_t len;
    s.read((char*) &len, sizeof(len)); //number of input arguments
    vars_.clear();
    inputs_.resize(len);
    for (size_t i = 0; i < len; ++i){
      vars_[i] = static_cast<type_t>(s.get());
      s.read((char *) &inputs_.at(i), sizeof(value_t));
    }

    cout << __func__ << endl;
    cout << "inputs " << container2str(inputs_) << endl;
    cout << "vars "  << container2str(vars_) << endl; 
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
