#include "sym.h"

namespace crest{
  /*** SymExpr ***/
  SymExpr::SymExpr(value_t c){
    const_ = c;
    expr_str_ = std::to_string(c);
  }
  SymExpr::SymExpr(value_t c, var_t v):SymExpr{0}{
    coeff_[v] = c;
  }
  SymExpr::SymExpr(const SymExpr &e){ 
    const_ = e.const_;
    coeff_ = e.coeff_;
    expr_str_ = e.expr_str_;
  }
  SymExpr::~SymExpr(){}

  void SymExpr::Serialize(string *s) const{
    assert(coeff_.size() < 128);
    s->push_back(static_cast<char>(coeff_.size()));
    s->append((char *) &const_, sizeof(value_t));
    for (const auto &c: coeff_){
      s->append((char *)&c.first, sizeof(var_t));
      s->append((char *)&c.second, sizeof(value_t));
    }
  }
  
  bool SymExpr::Parse(std::istream &s){
    auto len = static_cast<size_t>(s.get());
    s.read((char *)&const_, sizeof(value_t));
    if (s.fail())
      return false;

    coeff_.clear();
    for(size_t i = 0; i < len; ++i){
      var_t first;
      value_t second;
      s.read((char *) &first, sizeof(first));
      s.read((char *) &second, sizeof(second));
      coeff_[first] = second;
    }
    cout << __func__ << endl;
    cout << "const " << const_ << endl;
    cout << "coeff " << container2str(coeff_) << endl; 
    return !s.fail();
  }

  void SymExpr::Negate(){
      const_ = -const_;
      for(auto &c: coeff_) c.second = -c.second;

      expr_str_ = "(- 0 " + expr_str_ + " )";
    }

  void SymExpr::AppendVars(std::set<var_t> *vars) const{
    for (const auto &c: coeff_) vars->insert(c.first);
  }
  
  bool SymExpr::DependsOn(const std::map<var_t, type_t> &vars) const{
    for(const auto &c: coeff_){
      if (vars.find(c.first) != vars.end()){
	return true;
      }
    }
    return false;
  }

  const string SymExpr::str() const{
      std::stringstream ss;
      auto i = coeff_.size();
      for (const auto &c: coeff_) {
	if (c.second == 0) continue;
	if (c.second != 1) ss << c.second << "*";
	ss << "x" << c.first ;
	if (--i > 0) ss << " + ";;
      }
      if (const_ != 0){
	if (coeff_.size() > 0) ss << " + ";
	ss << const_;
      }

      return ss.str();
    }

  const SymExpr &SymExpr::operator += (const SymExpr &e){
    const_ += e.const_;

    for(const auto &i: e.coeff_){
      auto j =coeff_.find(i.first);
      if(j == coeff_.end()) 
	coeff_.insert(i);
      else{
	j->second += i.second;
	if (i.second == 0) coeff_.erase(j);
      }
    }
    
    expr_str_ = "(+ " + expr_str_ + " " + e.expr_str_ + " )";
    return *this;
  }

  const SymExpr &SymExpr::operator -= (const SymExpr &e){
    const_ -= e.const_;
    for(const auto &i: e.coeff_){
      auto j =coeff_.find(i.first);
      if(j == coeff_.end()) 
	coeff_[i.first] = -i.second; /*tvn:  ??*/
      else{
	j->second -= i.second;
	if (i.second == 0) coeff_.erase(j);
      }
    }

    expr_str_ = "(- " + expr_str_ + " " + e.expr_str_ + " )";
    return *this;
  }

  const SymExpr &SymExpr::operator *= (const SymExpr &e){
    const_ *= e.const_;

    for(const auto &i: e.coeff_){
      auto j = coeff_.find(i.first);
      if(j == coeff_.end()) 
	coeff_[i.first] = 1;
    }

    expr_str_ = "(* " + expr_str_ + " " + e.expr_str_ + " )";
    return *this;
  }

  const SymExpr &SymExpr::operator /= (const SymExpr &e){
    return *this;
  }

  const SymExpr &SymExpr::operator += (const value_t &c){
    const_ += c; 
    expr_str_ = "(+ " + expr_str_ + " " + std::to_string(c) + " )";
    return *this;
  }

  const SymExpr &SymExpr::operator -= (const value_t &c){
    const_ -= c; 
    expr_str_ = "(- " + expr_str_ + " " + std::to_string(c) + " )";
    return *this;
  }

  const SymExpr &SymExpr::operator *= (const value_t &c){
    if (c == 0){coeff_.clear(); const_=0; expr_str_ = "";}
    else{
      for(auto &co: coeff_) co.second *= c;
      const_ *= c;  //tvn:  z3crest doesn't have this ??
      
      expr_str_ = "(* " + expr_str_ + " " + std::to_string(c) + " )";
    }

    return *this;
  }

  const SymExpr &SymExpr::operator /= (const value_t &c){
    assert(c!=0);
    expr_str_ = "(div " + expr_str_ + " " + std::to_string(c) + " )";
    return *this;
  }

  const SymExpr &SymExpr::operator %= (const value_t &c){
    assert(c!=0);
    expr_str_ = "(mod " + expr_str_ + " " + std::to_string(c) + " )";
    return *this;
  }

  
  /*** SymPred ***/
  SymPred::SymPred(compare_op_t op, SymExpr *e): op_(op), expr_(e){}
  SymPred::SymPred():SymPred(c_ops::EQ, new SymExpr(0)){}
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
