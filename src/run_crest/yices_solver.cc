#include <utility>

#include "yices_solver.h"
#include "yices_c.h"
#include "z3.h"

using std::make_pair;

namespace crest{
  
  bool YicesSolver::
  IncrementalSolve(const vector<value_t> &old_sol,
  		   const map<var_t,type_t> &vars,
  		   const vector<const SymPred *> &constraints,
  		   map<var_t,value_t> *sol){
    
    cout << "** "<< __func__ << " **" << endl;
    cout << "old_sol " << container2str(old_sol) << endl;
    cout << "vars " << container2str(vars) << endl;
    cout << "orig constraints " << endl;
    cout << container2str(constraints) << endl;
    
    //build graph on variables, indicating a dependency when two variables co-occur 
    //in a symbolic predicate
    set<var_t> tmp;
    vector< set<var_t> > depends(vars.size());
    for(auto c: constraints){
      tmp.clear();
      c->AppendVars(&tmp);
      for(auto j:tmp){
       	depends[j].insert(tmp.begin(),tmp.end());
      }
    }
    
    //Initialize set of dependent vars to those in the constraints
    //assumption: last element of constraints is the only new cst
    //aslo init queue for BFS
    cout << "tmp " << container2str(tmp) << endl;
    map<var_t, type_t> dependent_vars;
    queue<var_t> Q;
    tmp.clear();
    constraints.back()->AppendVars(&tmp);
    for (auto j:tmp){
      dependent_vars.insert(*vars.find(j));
      Q.push(j);
    }
    cout << "dependent vars " << container2str(dependent_vars) << endl;
    //cout << container2str(Q) << endl;

    //Run BFS
    while (!Q.empty()){
      var_t i = Q.front();
      cout << "i " << i << endl;
      Q.pop();
      for (auto j:depends[i]){
	if(dependent_vars.find(j) == dependent_vars.end()){
	  Q.push(j);
	  dependent_vars.insert(*vars.find(j));
	}
      }
    }
    cout << "dependent vars after BFS" << container2str(dependent_vars) << endl;
    
    //Generate list of dependent constraints
    vector<const SymPred*> dependent_constraints;
    for (auto c:constraints){
      if (c->DependsOn(dependent_vars)){
	dependent_constraints.push_back(c);
      }
    }

    cout << "dependent constraints" << endl;
    cout << container2str(dependent_constraints) << endl;

    //Run SMT solver
    map<var_t,value_t>solz3 ;

    sol->clear();

    bool resultyices = Solve(dependent_vars, dependent_constraints, sol);

    solz3.clear();    
    bool resultz3 = SolveZ3(dependent_vars, dependent_constraints, &solz3);

    if (resultyices){
      cout << "solved" << endl;
      //merge in constrained vars
      for(auto c: constraints){
	c->AppendVars(&tmp);
      }

      for(auto v: tmp){
	if (sol->find(v) == sol->end()){
	  cout << "gh " << v << endl;
	  sol->insert(make_pair(v, old_sol[v]));
	}
      }

      return true;
    }

    return false;

  }
  

  Z3_ast mk_var(Z3_context ctx, const char * name, Z3_sort ty)
  {   
    Z3_symbol   s  = Z3_mk_string_symbol(ctx, name);
    return Z3_mk_const(ctx, s, ty);
  }

  bool YicesSolver::SolveZ3(const map<var_t, type_t> &vars,
			    const vector<const SymPred *> &constraints,
			    map<var_t,value_t> *sol){
    cout << "** " << __func__ <<" **" << endl;
    cout << "vars " << container2str(vars) << endl;
    cout << "constraints " << container2str(constraints) << endl;

    Z3_config cfg = Z3_mk_config();
    Z3_set_param_value(cfg, "MODEL", "true");
    Z3_context ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    Z3_sort int_ty = Z3_mk_int_sort(ctx);

    // //variables
    // string v_name;
    string v_name;
    map<var_t, Z3_ast> z3_vars;
    for (const auto &v: vars){
      v_name = "x" + std::to_string(v.first);
      Z3_ast v_ = Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, v_name.c_str()), int_ty);
      z3_vars[v.first]= v_ ; 
      cout << "create new var " << v_name << " : " << v_ << endl;
    }

    // for (const auto &e : z3_vars){
    //   cout << "z3_vars[" << e.first << "]=" << *e.second << endl;
    // }
    
    //constraints
    Z3_ast zero = Z3_mk_numeral(ctx, "0", int_ty);
    vector<Z3_ast> terms;
    for (const auto &c: constraints){
      cout << "constraint " << *c << endl;
      terms.clear();
      terms.push_back(Z3_mk_numeral(ctx,std::to_string(c->expr().const_term()).c_str(),int_ty));
      for (auto t: c->expr().terms()){
    	cout << "1st " << t.first << ", 2nd " << t.second << endl;
    	Z3_ast n = Z3_mk_numeral(ctx, std::to_string(t.second).c_str(), int_ty);
    	Z3_ast prod[]  = {z3_vars[t.first], n};
    	terms.push_back(Z3_mk_mul(ctx,2,prod));
      }
      
      Z3_ast su = Z3_mk_add(ctx, terms.size(), &terms.front());
      Z3_ast pred ;

      switch(c->op()){
      case c_ops::EQ : pred = Z3_mk_eq(ctx, su, zero); break;
      case c_ops::NEQ: pred = Z3_mk_not(ctx, Z3_mk_eq(ctx, su, zero)); break;
      case c_ops::GT:  pred = Z3_mk_gt(ctx, su, zero); break;
      case c_ops::LE:  pred = Z3_mk_le(ctx, su, zero); break;
      case c_ops::LT:  pred = Z3_mk_lt(ctx, su, zero); break;
      case c_ops::GE:  pred = Z3_mk_ge(ctx, su, zero); break; 
      default:
    	cout << "unknown comparison op: \n" << c->op() << endl;
    	exit(1);
      }
      
      cout << "pred : " << Z3_ast_to_string(ctx,pred) << endl;
      
    }


    return true;
  }



  bool YicesSolver::Solve(const map<var_t, type_t> &vars,
  			  const vector<const SymPred *> &constraints,
  			  map<var_t,value_t> *sol){

    cout << "** " << __func__ <<" **" << endl;
    cout << "vars " << container2str(vars) << endl;
    cout << "constraints " << container2str(constraints) << endl;

    yices_enable_log_file("yices_log");
    yices_context ctx = yices_mk_context();
    assert(ctx);

    //type limits
    vector<yices_expr> min_expr(c_types::LONG_LONG+1);
    vector<yices_expr> max_expr(c_types::LONG_LONG+1);
    
    for (int i = c_types::U_CHAR; i<=c_types::LONG_LONG; ++i){
      min_expr[i] = yices_mk_num_from_string(ctx, const_cast<char *>(kMinValueStr[i]));
      assert(min_expr[i]);
      max_expr[i] = yices_mk_num_from_string(ctx, const_cast<char *>(kMaxValueStr[i]));
      assert(max_expr[i]);
    }
    
    char int_ty_name[] = "int";
    yices_type int_ty = yices_mk_type(ctx, int_ty_name);
    assert(int_ty);

    //var decl's
    map<var_t, yices_var_decl> x_decl;
    map<var_t, yices_expr> x_expr;
    for (auto v:vars){
      char buff[32];
      const var_t vf = v.first, vs = v.second;
      
      snprintf(buff, sizeof(buff), "x%d", vf);
      cout << "var " << buff << " (vf " << vf << ")" << endl;
      x_decl[vf] = yices_mk_var_decl(ctx,buff,int_ty);  
      x_expr[vf] = yices_mk_var_from_decl(ctx,x_decl[vf]);
      assert(x_decl[vf]);
      assert(x_expr[vf]);

      yices_assert(ctx, yices_mk_ge(ctx,x_expr[vf], min_expr[vs]));
      yices_assert(ctx, yices_mk_le(ctx,x_expr[vf], max_expr[vs]));
    }

    yices_expr zero = yices_mk_num(ctx,0);
    assert(zero);

    //constraints
    vector<yices_expr> terms;
    for(auto i: constraints){
      cout << "constraint " << i << endl;
      const SymExpr &se = i->expr();
      terms.clear();
      terms.push_back(yices_mk_num(ctx, se.const_term()));
      for(auto j: se.terms()){
  	yices_expr prod [2] = {x_expr[j.first], yices_mk_num(ctx, j.second)};
  	terms.push_back(yices_mk_mul(ctx,prod,2));
      }
      yices_expr e = yices_mk_sum(ctx, &terms.front(), terms.size());

      yices_expr pred;
      cout << "op " << i->op() << endl;

      switch(i->op()){
      case c_ops::EQ: pred = yices_mk_eq(ctx, e, zero); break;
      case c_ops::NEQ: pred = yices_mk_diseq(ctx, e, zero); break;
      case c_ops::GT:  pred = yices_mk_gt(ctx, e, zero); break;
      case c_ops::LE:  pred = yices_mk_le(ctx, e, zero); break;
      case c_ops::LT:  pred = yices_mk_lt(ctx, e, zero); break;
      case c_ops::GE:  pred = yices_mk_ge(ctx, e, zero); break; 
      default:
  	cout << "unknown comparison op: \n" << i->op() << endl;
  	exit(1);
      }
      yices_assert(ctx, pred);
    }
    cout << "**** Context ****" << endl;
    yices_dump_context(ctx);
    cout << "*********" << endl;

    bool success = (yices_check(ctx) == l_true);
    if (success){
      cout << "check ok " << endl;
      sol->clear();
      yices_model model = yices_get_model(ctx);
      for(auto i:vars){
  	long val;
  	assert(yices_get_int_value(model, x_decl[i.first], &val));
  	sol->insert(make_pair(i.first, val));
      }
    }
    cout << "sol " << container2str(*sol) << endl;

    yices_del_context(ctx);
    return success;
  }
  
}
