#ifndef SMT_SOLVER
#define SMT_SOLVER

#include <map>
#include "basic_types.h"
#include "sym.h"

namespace crest{
  class SMTSolver{
  public:
    static bool 
      IncrementalSolve(const vector<value_t> &,
		       const std::map<var_t,type_t> &,
		       const vector<const SymPred *>&,
		       std::map<var_t,value_t> *);

    static bool 
      SolveZ3(const std::map<var_t, type_t> &s,
	      const vector<string> &,
	      std::map<var_t,value_t> *);

    static const string z3_version();
      

  };
}

#endif
