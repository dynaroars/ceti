#ifndef YICES_SOLVER
#define YICES_SOLVER

#include <map>
#include "basic_types.h"
#include "sym.h"

namespace crest{
  class YicesSolver{
  public:
    static bool 
      IncrementalSolve(const vector<value_t> &,
		       const std::map<var_t,type_t> &,
		       const vector<const SymPred *>&,
		       std::map<var_t,value_t> *);

    static bool 
      Solve(const std::map<var_t, type_t> &s,
	    const vector<const SymPred *> &,
	    std::map<var_t,value_t> *);
    
    static bool 
      SolveZ3(const std::map<var_t, type_t> &s,
	      const vector<const SymPred *> &,
	      std::map<var_t,value_t> *);

    static const string z3_version();
      

  };
}

#endif
