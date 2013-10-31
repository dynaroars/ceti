#ifndef YICES_SOLVER
#define YICES_SOLVER

#include "basic_types.h"
#include "sym.h"

namespace crest{
  class YicesSolver{
  public:
    static bool 
      IncrementalSolve(const vector<value_t> &,
		       const map<var_t,type_t> &,
		       const vector<const SymPred *>&,
		       map<var_t,value_t> *);

    static bool 
      Solve(const map<var_t, type_t> &s,
	    const vector<const SymPred *> &,
	    map<var_t,value_t> *);
    
    static bool 
      SolveZ3(const map<var_t, type_t> &s,
	      const vector<const SymPred *> &,
	      map<var_t,value_t> *);
    

  };
}

#endif
