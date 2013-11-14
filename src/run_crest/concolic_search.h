#ifndef CONCOLIC_SEARCH_H__  
#define CONCOLIC_SEARCH_H__  

#include <set>                
#include "sym.h"

namespace crest{
  class Search{
  public:
    explicit Search(const string &, const int &);
    virtual ~Search();
    virtual bool run() = 0;

  protected:

    vector<branch_id_t> branches_;
    vector<branch_id_t> paired_branch_;
    vector<func_id_t> branch_function_;
    vector<unsigned int> branch_count_;

    vector<bool> covered_branches_;
    unsigned int n_covered_branches_;

    vector<bool> reached_functions_; 
    unsigned int n_reachable_functions_;
    unsigned int n_reachable_branches_;

    vector<bool> total_covered_branches_;
    unsigned int total_n_covered_branches_;


    void print_protected_members();
    template<typename T>
    bool SolveAtBranch(const SymExec &, const size_t &, vector<T> *);
    bool CheckPrediction(const SymExec &, const SymExec &, const size_t &);

    template<typename T>
    bool RunProgram(const vector<T> &, SymExec *);

    bool UpdateCoverage(const SymExec &);
    bool UpdateCoverage(const SymExec &, std::set<branch_id_t> *);

  private:
    const string prog_;
    const int max_iters_;
    int num_iters_;
    const string goal = "GOAL";

    void WriteCoverageToFile();
    template<typename T> void WriteInputToFile(const vector<T>&);
      
  };

  class BoundedDepthFirstSearch : public Search{
  public:
    explicit BoundedDepthFirstSearch(const string &, const int &, const int &);
    virtual ~BoundedDepthFirstSearch();
    virtual bool run();

  private:
    int max_depth_;
    bool DFS(const size_t &, int, SymExec &);

  };

}//namespace crest

#endif
