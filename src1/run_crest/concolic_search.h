#ifndef CONCOLIC_SEARCH_H__  
#define CONCOLIC_SEARCH_H__  
                
#include "sym.h"

namespace crest{
  class Search{
  public:
    Search(const string &, const int &);
    virtual ~Search();
    virtual void run() = 0;

  protected:

    branch_id_t max_branch_;
    function_id_t max_function_;

    vector<branch_id_t> branches_;
    vector<branch_id_t> paired_branch_;
    vector<function_id_t> branch_function_;
    vector<unsigned int> branch_count_;

    vector<bool> covered_branches_;
    unsigned int n_covered_branches_;

    vector<bool> reached_functions_; 
    unsigned int n_reachable_functions_;
    unsigned int n_reachable_branches_;

    vector<bool> total_covered_branches_;
    unsigned int total_n_covered_branches_;


    void print_protected_members();
    bool SolveAtBranch(const SymExec &,const size_t &, vector<value_t> *);
		       
    void RunProgram(const vector<value_t> &, SymExec *);
    bool UpdateCoverage(const SymExec &);
    bool UpdateCoverage(const SymExec &, set<branch_id_t> *);

  private:
    const string prog_;
    const int max_iters_;
    int num_iters_;
    

    void WriteCoverageToFile();
    void WriteInputToFile(const vector<value_t>&);

    void LaunchProgram(const vector<value_t> &inputs);

  };

  class BoundedDepthFirstSearch : public Search{

  public:
    explicit BoundedDepthFirstSearch(const string &, const int &, const int &);
    virtual ~BoundedDepthFirstSearch();
    virtual void run();

  private:
    int max_depth_;
    void DFS(const size_t &, const int &, SymExec &);

  };

}//namespace crest

#endif
