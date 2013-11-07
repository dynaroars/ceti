#include <set>
#include <queue>

#include "smt_solver.h"
#include "z3.h"

using std::make_pair;

namespace crest{
  
  bool SMTSolver::
  IncrementalSolve(const vector<value_t> &old_sol,
  		   const std::map<var_t,type_t> &vars,
  		   const vector<const SymPred *> &constraints,
  		   std::map<var_t,value_t> *sol){
    
    cout << __func__ << endl;
    cout << "old_sol " << container2str(old_sol) << endl;
    cout << "vars " << container2str(vars) << endl;
    cout << "orig constraints " << endl;
    cout << container2str(constraints) << endl;
    
    //build graph on variables, indicating a dependency when two variables co-occur 
    //in a symbolic predicate
    std::set<var_t> tvars;
    vector<std::set<var_t> > depends(vars.size());
    for(const auto &c: constraints){
      tvars.clear();
      c->AppendVars(&tvars);
      for(const auto &j:tvars){
       	depends[j].insert(tvars.begin(),tvars.end());
      }
    }
    for (size_t i = 0 ; i < depends.size(); ++i)
      cout << "depends[" << i << "] = " << container2str(depends.at(i)) << endl;
    
    //Initialize set of dependent vars to those in the constraints
    //assumption: last element of constraints is the only new cst
    //aslo init queue for BFS

    std::map<var_t, type_t> dependent_vars;
    std::queue<var_t> Q;
    tvars.clear();
    constraints.back()->AppendVars(&tvars);
    for(const auto &j:tvars){
      dependent_vars.insert(*vars.find(j));
      Q.push(j);
    }
    cout << "dependent vars " << container2str(dependent_vars) << endl;

    //Run BFS
    while (!Q.empty()){
      auto i = Q.front();
      cout << "i " << i << endl;
      Q.pop();
      for (const auto &j:depends[i]){
	if(dependent_vars.find(j) == dependent_vars.end()){
	  Q.push(j);
	  dependent_vars.insert(*vars.find(j));
	}
      }
    }
    cout << "dependent vars after BFS" << container2str(dependent_vars) << endl;
    
    //Generate list of dependent constraints
    vector<const SymPred*> dependent_constraints;
    for (const auto &c: constraints){
      if (c->DependsOn(dependent_vars)){
	dependent_constraints.push_back(c);
      }
    }

    cout << "dependent constraints" << endl;
    cout << container2str(dependent_constraints) << endl;

    //Run SMT solver

    sol->clear();
    auto result = SolveZ3(dependent_vars, dependent_constraints, sol);

    if (result){
      cout << "solved" << endl;
      //merge in constrained vars
      for(const auto &c: constraints){
	c->AppendVars(&tvars);
      }
      cout << "tvars " << container2str(tvars) << endl;
      for(const auto &v: tvars){
	//if v not found in new sol, use v of old sol
	if (sol->find(v) == sol->end()){
	  sol->insert(make_pair(v, old_sol[v]));
	}
      }
      return true;
    }

    return false;

  }
  

  bool SMTSolver::SolveZ3(const std::map<var_t, type_t> &vars,
			    const vector<const SymPred *> &constraints,
			    std::map<var_t,value_t> *sol){
    cout << __func__ << " Z3 " << z3_version() << endl;
    cout << "vars " << container2str(vars) << endl;
    cout << "constraints " << container2str(constraints) << endl;

    auto cfg = Z3_mk_config();
    Z3_set_param_value(cfg, "MODEL", "true");
    auto ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);
    auto int_ty = Z3_mk_int_sort(ctx);

    //make variables
    string v_name;
    std::map<var_t, Z3_ast> z3_vars;
    for (const auto &v: vars){
      v_name = "x" + std::to_string(v.first) ;
      auto v_ = 
	Z3_mk_const(ctx, Z3_mk_string_symbol(ctx, v_name.c_str()), int_ty);
      z3_vars[v.first]= v_ ; 
    }

    for (const auto &e : z3_vars){
      cout << "z3_vars[" << e.first << "] = " 
	   << Z3_ast_to_string(ctx, e.second) << endl;
    }

    //make constraints
    auto zero = Z3_mk_int(ctx, 0, int_ty);
    vector<Z3_ast> terms;
    for (const auto &c: constraints){
      terms.clear();
      terms.push_back(Z3_mk_int(ctx, c->expr().const_term(), int_ty));
      for (auto t: c->expr().terms()){
    	Z3_ast prod[] {z3_vars[t.first], Z3_mk_int(ctx, t.second, int_ty)};
    	terms.push_back(Z3_mk_mul(ctx, 2, prod));
      }
      auto e = Z3_mk_add(ctx, terms.size(), &terms.front());

      Z3_ast pred ;
      switch(c->op()){
      case c_ops::EQ : pred = Z3_mk_eq(ctx, e, zero); break;
      case c_ops::NEQ: pred = Z3_mk_not(ctx, Z3_mk_eq(ctx, e, zero)); break;
      case c_ops::GT:  pred = Z3_mk_gt(ctx, e, zero); break;
      case c_ops::LE:  pred = Z3_mk_le(ctx, e, zero); break;
      case c_ops::LT:  pred = Z3_mk_lt(ctx, e, zero); break;
      case c_ops::GE:  pred = Z3_mk_ge(ctx, e, zero); break; 
      default:
    	cout << "unknown comparison op: \n" << c->op() << endl;
    	exit(1);
      }

      cout << "constraint " << *c << ", "
	   << Z3_ast_to_string(ctx,pred) << endl;
      Z3_assert_cnstr(ctx, pred);
    }

    Z3_model model = 0;
    auto success = (Z3_check_and_get_model(ctx, &model) == Z3_L_TRUE);
    if (success == Z3_L_TRUE){
      
      cout << "model\n" << Z3_model_to_string(ctx, model) << endl;
      int n_consts = Z3_get_model_num_constants(ctx, model);
      assert(n_consts == (int)vars.size());

      int idx; long val;
      sol->clear();      
      for (int i = 0; i < n_consts; ++i){
	
	auto cnst = Z3_get_model_constant(ctx, model, i);
	auto name = Z3_get_decl_name(ctx, cnst);
	auto a = Z3_mk_app(ctx, cnst, 0, 0);
	auto v = a;
	Z3_eval(ctx, model, a, &v);

	sscanf(Z3_get_symbol_string(ctx, name), "x%d", &idx);
	val = std::strtol(Z3_get_numeral_string(ctx, v), NULL, 0);
	
	sol->insert(make_pair(idx, val));
      }
      cout << "sol " << container2str(*sol) << endl;
    }

    if(model) Z3_del_model(ctx, model);
    Z3_del_context(ctx);

    return success;
  }





  const string SMTSolver::z3_version(){
    std::stringstream ss;
    unsigned major, minor, build, revision;
    Z3_get_version(&major, &minor, &build, &revision);
    ss << major << "." << minor << "." << build << "." << revision;
    return ss.str();
  }
  
}
