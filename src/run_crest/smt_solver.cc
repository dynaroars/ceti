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
    cout << "orig constraints " << container2str(constraints) << endl;
    
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
    vector<string> dependent_constraints;
    for (const auto &c: constraints){
      if (c->DependsOn(dependent_vars)){
	dependent_constraints.push_back(c->expr_str());
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
			  const vector<string> &constraints,
			  std::map<var_t,value_t> *sol){

    cout << __func__ << " Z3 " << z3_version() << endl;
    cout << "vars " << container2str(vars) << endl;
    cout << "constraints " << container2str(constraints) << endl;

    //"(benchmark tst :extrafuns ((x Int) (y Int)) :formula (> x y) :formula (> x 0))"

    //make variables
    string v_decls = ":extrafuns (";
    for (const auto &v: vars){
      string vn = "x" + std::to_string(v.first);
      cout << vn << ", type = " << v.second << endl;
      string vt = "Int";
      v_decls = v_decls + "("+ vn + " " + vt + ") ";
    }
    v_decls = v_decls + ")";
    cout << v_decls << endl;

    //make constraints
    string f_decls = "";
    for (const auto &c: constraints){
      f_decls = f_decls + ":formula " + c + " ";
    }
    cout << f_decls << endl;

    string smtlib_str = "(benchmark tst " + v_decls + f_decls + ")";
    cout << "*** smtlib_str ***: " <<smtlib_str << endl;


    auto cfg = Z3_mk_config();
    //Z3_set_param_value(cfg, "auto_config", "true");
    Z3_set_param_value(cfg, "MODEL", "true");
    auto ctx = Z3_mk_context(cfg);
    Z3_del_config(cfg);

    Z3_parse_smtlib_string(ctx,
			   smtlib_str.c_str(),
			   0,0,0,
			   0,0,0);


    unsigned n_formulas = Z3_get_smtlib_num_formulas(ctx);
    for (unsigned i = 0; i < n_formulas; i++) {
      Z3_ast f = Z3_get_smtlib_formula(ctx, i);
      printf("formula %d: %s\n", i, Z3_ast_to_string(ctx, f));
      Z3_assert_cnstr(ctx, f);
    }

    Z3_model model =0;
    auto success = (Z3_check_and_get_model(ctx, &model) == Z3_L_TRUE);
    if (success == Z3_L_TRUE){
      
      cout << "model\n" << Z3_model_to_string(ctx, model) << endl;
      int n_consts = Z3_get_model_num_constants(ctx, model);
      //assert(n_consts == (int)vars.size());

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
