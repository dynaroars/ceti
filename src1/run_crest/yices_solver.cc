#include <utility>

#include "yices_solver.h"
#include "yices_c.h"

using std::make_pair;

namespace crest{
  
  bool YicesSolver::
  IncrementalSolve(const vector<value_t> &old_sol,
  		   const map<var_t,type_t> &vars,
  		   const vector<const SymPred *> &constraints,
  		   map<var_t,value_t> *sol){
    
    cout << "** IncrementalSolve **" << endl;
    cout << "old_sol " << container2str(old_sol) << endl;
    cout << "vars " << map2str(vars) << endl;
    cout << "orig constraints " << endl;
    cout << constraints2str(constraints) << endl;
    


    //build graph on variables, indicating a dependency when two variables co-occur 
    //in a symbolic predicate
    set<var_t> tmp;
    vector< set<var_t> > depends(vars.size());
    for(auto i: constraints){
      tmp.clear();
      i->AppendVars(&tmp);
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
    cout << "dependent vars " << map2str(dependent_vars) << endl;
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
    cout << "dependent vars after BFS" << map2str(dependent_vars) << endl;
    
    //Generate list of dependent constraints
    vector<const SymPred*> dependent_constraints;
    for (auto c:constraints){
      if (c->DependsOn(dependent_vars)){
	dependent_constraints.push_back(c);
      }
    }

    cout << "dependent constraints" << endl;
    cout << constraints2str(dependent_constraints) << endl;

    //Run SMT solver
    sol->clear();
    if (Solve(dependent_vars, dependent_constraints,sol)){
      cout << "solved" << endl;
      return true;
    }

    return false;

  }

  bool YicesSolver::Solve(const map<var_t, type_t> &vars,
			  const vector<const SymPred *> &constraints,
			  map<var_t,value_t> *sol){

    yices_enable_log_file("yices_log");
    yices_context ctx = yices_mk_context();
    assert(ctx);

    //type limits
    vector<yices_expr> min_expr(types::LONG_LONG+1);
    vector<yices_expr> max_expr(types::LONG_LONG+1);
    
    for (int i = types::U_CHAR; i<=types::LONG_LONG; ++i){
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
    for (auto i:vars){
      char buff[32];
      snprintf(buff, sizeof(buff), "x%d", i.first);
      cout << "var " << buff << " (i.first " << i.first << ")" << endl;
      x_decl[i.first] = yices_mk_var_decl(ctx,buff,int_ty);  
      x_expr[i.first] = yices_mk_var_from_decl(ctx,x_decl[i.first]);
      assert(x_decl[i.first]);
      assert(x_expr[i.first]);

      yices_assert(ctx, yices_mk_ge(ctx,x_expr[i.first], min_expr[i.second]));
      yices_assert(ctx, yices_mk_le(ctx,x_expr[i.first], max_expr[i.second]));
    }

    yices_expr zero = yices_mk_num(ctx,0);
    assert(zero);

    //constraints
    vector<yices_expr> terms;
    for(auto i: constraints){
      cout << "constraint " << i->str() << endl;
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
      case ops::EQ: pred = yices_mk_eq(ctx, e, zero); break;
      case ops::NEQ: pred = yices_mk_diseq(ctx, e, zero); break;                                                          
      case ops::GT:  pred = yices_mk_gt(ctx, e, zero); break;                                                             
      case ops::LE:  pred = yices_mk_le(ctx, e, zero); break;                                                             
      case ops::LT:  pred = yices_mk_lt(ctx, e, zero); break;                                                             
      case ops::GE:  pred = yices_mk_ge(ctx, e, zero); break; 
      default:
	cout << "unknown comparison op: \n" << i->op() << endl;
	exit(1);
      }
      yices_assert(ctx, pred);
    }

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
    cout << "sol " << map2str(*sol) << endl;

    yices_del_context(ctx);
    return success;
  }
  
}
