#include "run_crest/concolic_search.h"

namespace crest{

  Search::Search(const string &prog, const int &max_iters)
    : prog_(prog), max_iters_(max_iters), num_iters_(0){
    
    /*Read in branches*/
    max_branch_ = 0;
    max_function_ = 0;
    branches_.reserve(100000);
    branch_count_.reserve(100000);
    branch_count_.push_back(0);

    std::ifstream in("branches");
    assert(in);
    function_id_t fid; 
    int nBranches;

    branch_id_t b1,b2;
    while(in >> fid >> nBranches){
      branch_count_.push_back(2*nBranches);
      for (int i = 0; i < nBranches; ++i){
	assert(in >> b1 >> b2);
	branches_.push_back(b1);
	branches_.push_back(b2);
	max_branch_ = std::max(max_branch_, std::max(b1,b2));
      }
    }
    in.close();

    max_branch_++;
    max_function_ = branch_count_.size();

    /*paired_branch[i]=j == paired[j]=i ,  means i paired with j (ignore all 0 since no branch id 0)*/
    paired_branch_.resize(max_branch_);
    for (size_t i = 0 ; i < branches_.size(); i += 2){
      paired_branch_.at(branches_.at(i)) = branches_.at(i+1);
      paired_branch_.at(branches_.at(i+1)) = branches_.at(i);
    }

    /*branch_function[i] == j  means branch j belongs to function i (ignore all j=0)*/
    branch_function_.resize(max_branch_);
    size_t i = 0;
    for (function_id_t j = 0; j < branch_count_.size(); ++j){
      for (size_t k = 0 ; k < branch_count_[j]; k++){
	branch_function_[branches_[i++]] = j;
      }
    }

    //init branches to "uncovered" and functions to unreached
    total_n_covered_branches_ = n_covered_branches_ = 0;
    n_reachable_functions_ = n_reachable_branches_ = 0;

    covered_branches_.resize(max_branch_, false);
    total_covered_branches_.resize(max_branch_, false);

    reached_functions_.resize(max_function_,false);

    /*tvn debug*/
    printf("branches_count %d ", max_function_);
    cout << vec2str(branch_count_) << endl;

    printf("max_branch %d, branches ", max_branch_);
    cout << vec2str(branches_) << endl;

    printf("paired_branch ");
    cout << vec2str(paired_branch_) << endl;

    printf("branch_function ");
    cout << vec2str(branch_function_) << endl;


    /*end tvn debug*/

    printf("Iteration 0: covered %u branches (%u reach funs, %u reach branches)\n",
	   n_covered_branches_, n_reachable_functions_, n_reachable_branches_);
  }
  
  Search::~Search(){}



  void Search::print_protected_members(){
    cout << "** Search::print_protected_members **" << endl;
    cout << "branches " << vec2str(branches_) <<endl;
    
    cout << "n_covered_branches " << n_covered_branches_ << endl;
    cout << "covered_branches" << vec2str(covered_branches_) << endl;
    
    cout << "total_n_covered_branches " << total_n_covered_branches_ << endl;
    cout << "total_covered_branches " 
	 << vec2str(total_covered_branches_) << endl;
    
    cout << "reachable_functions " << n_reachable_functions_ << endl;
    cout << "n_reachable_branches " << n_reachable_branches_ << endl;
    cout << "reached " << vec2str(reached_functions_) << endl;
  }


  
  bool Search::UpdateCoverage(const SymExec &ex){
    return UpdateCoverage(ex, NULL);
  }

  bool Search::UpdateCoverage(const SymExec &ex, set<branch_id_t> *new_branches){
    const unsigned int prev_covered_ = n_covered_branches_;
    const vector<branch_id_t> &ex_branches = ex.path().branches();

    cout << "Search:** UpdateCoverage **" << endl;
    print_protected_members();
    cout << "exec.path().branches() " << vec2str(ex_branches) << endl;

    for (auto i:ex_branches){
      if(i>0 && !covered_branches_[i]){
	covered_branches_[i]=true;
	n_covered_branches_++;
	if(new_branches){
	  new_branches->insert(i);
	}

	if(!reached_functions_[branch_function_[i]]){
	  reached_functions_[branch_function_[i]]=true;
	  n_reachable_functions_++;
	  n_reachable_branches_ += branch_count_[branch_function_[i]];
	}
      }
      if (i > 0 && !total_covered_branches_[i]){
	total_covered_branches_[i]=true;
	total_n_covered_branches_++;
      }
    }
    printf("Iteration %d: covered %u branches "
	   "[%u reach funs, %u reach branches]\n",
	   num_iters_,total_n_covered_branches_,
	   n_reachable_functions_,n_reachable_branches_);

    print_protected_members();

    if (n_covered_branches_ > prev_covered_){
      WriteCoverageToFile();
      return true;
    }
    else{
      return false;
    }

  }

  void Search::WriteCoverageToFile(){
    string file = "coverage";
    stringstream ss;
    for (auto b: branches_){
      if(total_covered_branches_.at(b))
	ss << b << endl;
    }
    write_file(file,ss.str());
  }
  
  void Search::WriteInputToFile(const vector<value_t>&input){
    string file = "input";
    stringstream ss;
    for (auto inp: input)
      ss << inp << endl;
    write_file(file,ss.str());
  }
  
  void Search::LaunchProgram(const vector<value_t> &inputs){
    WriteInputToFile(inputs);
    system(prog_.c_str());
  }

  void Search::RunProgram(const vector<value_t> &inputs, SymExec *ex){
    ++num_iters_;
    printf("num_iters %d, max_iters %d\n",num_iters_,max_iters_);
    if (++num_iters_ > max_iters_){
      exit(0);
    }
    
    if (inputs.size() > 0){
      printf("at iters_: %d, inputs: ", num_iters_);
      for(size_t i = 0; i < inputs.size(); ++i){
	printf("%lld , ", inputs[i]);
      }
      printf("\n");
    }
    LaunchProgram(inputs);
    
    //Read in execution

    std::ifstream in("szd_execution", std::ios::in | std::ios::binary);
    assert (in && ex->Parse(in));
    in.close();
    
  }

  bool Search::
  SolveAtBranch(const SymExec &ex, const size_t &branch_idx, 
		vector<value_t> *input){

    cout << "** SolveAtBranch **" << endl;
    cout << ex.str() << endl;
    cout << "branch_idx " << branch_idx <<endl;
    cout << "input " << vec2str(*input) << endl;

    const vector<SymPred *>& constraints = ex.path().constraints();
    
    //Optimization
    for(int i = static_cast<int>(branch_idx) - 1; i >= 0; --i){
      if (*constraints[branch_idx] == *constraints[i]){
	cout << "optimized, idx " << branch_idx << " = " << i << endl;
	return false;
      }
    }

    vector<const SymPred*> cs(constraints.begin(),
			      constraints.begin()+branch_idx+1);
    map<var_t,value_t>sol;
    cout << "constraint " << constraints[branch_idx]->str() << endl;
    constraints[branch_idx]->Negate();
    cout << "constraint after neg " << constraints[branch_idx]->str() << endl;

    return false;
  }

  /*** BoundedDepthFirstSearch ***/

  BoundedDepthFirstSearch::BoundedDepthFirstSearch
  (const string &prog, const int &max_iters, const int &max_depth)
    : Search(prog, max_iters), max_depth_(max_depth){}

  BoundedDepthFirstSearch::~BoundedDepthFirstSearch(){}

  void BoundedDepthFirstSearch::run(){
    SymExec ex;
    RunProgram(vector<value_t>(), &ex);
    UpdateCoverage(ex);
    DFS(0, max_depth_, ex);
  }

  void BoundedDepthFirstSearch::
  DFS(const size_t &pos, const int &depth, SymExec &prev_ex){
    SymExec cur_ex;
    vector<value_t> input;
    const SymPath& path = prev_ex.path();
    
    for (size_t i = pos; (i < path.constraints().size()) && (depth > 0); ++i){
      if(!SolveAtBranch(prev_ex,i,&input)){
	continue;
      }
    }

  }

}//namespace crest
