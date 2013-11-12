#include <map>
#include <sstream>
#include <algorithm>
#include "concolic_search.h"
#include "smt_solver.h"



namespace crest{

  Search::Search(const string &prog, const int &max_iters)
    : prog_(prog), max_iters_(max_iters), num_iters_(0){
    
    /*Read in branches*/
    branches_.reserve(100000);
    branch_count_.reserve(100000);
    branch_count_.push_back(0);

    std::ifstream in("branches");
    assert(in);

    func_id_t fid; 
    int nBranches;

    branch_id_t b1,b2;
    while(in >> fid >> nBranches){
      branch_count_.push_back(2*nBranches);
      for (auto i = 0; i < nBranches; ++i){
	assert(in >> b1 >> b2);
	branches_.push_back(b1);
	branches_.push_back(b2);
      }
    }
    in.close();
    
    auto max_branch_id = *std::max_element(branches_.begin()+1, branches_.end());
    max_branch_id++;

    /*paired_branch[i]=j, paired_branch[j]=i ,  
      means i paired with j (ignore all 0 since no branch id 0)*/
    paired_branch_.resize(max_branch_id);
    for (size_t i = 0 ; i < branches_.size(); i += 2){
      paired_branch_.at(branches_.at(i)) = branches_.at(i+1);
      paired_branch_.at(branches_.at(i+1)) = branches_.at(i);
    }

    /*branch_function[i] == j  means branch j belongs to function i (ignore all j=0)*/
    branch_function_.resize(max_branch_id);
    size_t i = 0;
    for (func_id_t j = 0; j < branch_count_.size(); ++j){
      for (size_t k = 0 ; k < branch_count_.at(j); k++){
	branch_function_[branches_.at(i++)] = j;
      }
    }

    //init branches to "uncovered" and functions to unreached
    total_n_covered_branches_ = n_covered_branches_ = 0;
    n_reachable_functions_ = n_reachable_branches_ = 0;

    covered_branches_.resize(max_branch_id, false);
    total_covered_branches_.resize(max_branch_id, false);

    reached_functions_.resize(branch_count_.size(),false);

    print_protected_members();

    printf("Iteration 0: covered %u branches (%u reach funs, %u reach branches)\n",
	   n_covered_branches_, n_reachable_functions_, n_reachable_branches_);

  }
  
  Search::~Search(){}



  void Search::print_protected_members(){
    cout << "** Search::print_protected_members **" << endl;
    cout << "branches " << container2str(branches_) <<endl;
    cout << "paired_branch_ " << container2str(paired_branch_) << endl;
    cout << "branch_function_ " << container2str(branch_function_) << endl;
    cout << "branch_count_ " << container2str(branch_count_) << endl;
    
    cout << "n_covered_branches " << n_covered_branches_ << endl;
    cout << "covered_branches" << container2str(covered_branches_) << endl;
    
    cout << "total_n_covered_branches " << total_n_covered_branches_ << endl;
    cout << "total_covered_branches " 
	 << container2str(total_covered_branches_) << endl;
    
    cout << "reachable_functions " << n_reachable_functions_ << endl;
    cout << "n_reachable_branches " << n_reachable_branches_ << endl;
    cout << "reached " << container2str(reached_functions_) << endl;
  }


  
  bool Search::UpdateCoverage(const SymExec &ex){
    return UpdateCoverage(ex, nullptr);
  }

  bool Search::UpdateCoverage(const SymExec &ex, std::set<branch_id_t> *new_branches){
    const auto prev_covered_ = n_covered_branches_;
    const auto &ex_branches = ex.path().branches();

    cout << "Search:** UpdateCoverage **" << endl;
    print_protected_members();
    cout << "exec.path().branches() " << container2str(ex_branches) << endl;

    for (const auto &i: ex_branches){
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
    const auto file = "coverage";
    std::stringstream ss;
    for (const auto &b: branches_){
      if(total_covered_branches_.at(b))
  	ss << b << endl;
    }
    write_file(file,ss.str());
  }
  
  void Search::WriteInputToFile(const vector<value_t>&input){
    const auto file = "input";
    std::stringstream ss;
    for (const auto &inp: input) ss << inp << endl;

    write_file(file,ss.str());
  }
  
  bool Search::RunProgram(const vector<value_t> &inputs, SymExec *ex){
    if (++num_iters_ > max_iters_){
      cout << "max_iters " << max_iters_ << "reached. Exit !" << endl;
      exit(0);
    }
    
    cout << __func__ << " (" << num_iters_ << ", " 
	 << max_iters_ << ")" << endl;
    //printf("** RunProgram ** (%d/%d)\n",num_iters_, max_iters_);
    cout << "input " << container2str(inputs) << endl;;

    WriteInputToFile(inputs);

    auto found_goal = false;
    FILE *fin; char buff[512];
    fin = popen(prog_.c_str(),"r");

    //char *print_exec = "print_execution";
    //system(print_exec);

    while(fgets(buff,sizeof(buff),fin)){
      string res(buff);
      cout << ">> " << res << endl;
      if (res.find(goal) != string::npos){
	found_goal = true;
	cout << "inputs " << container2str(inputs) << endl;
	break;
      }
    }
    pclose(fin);

    if (found_goal) return true;

    //Read in execution
    std::ifstream in("szd_execution", std::ios::in | std::ios::binary);
    assert(in && ex->Parse(in));
    in.close();

    cout << "Parsed info:\n"  << *ex << endl;
    return false;
  }

  bool Search::
  SolveAtBranch(const SymExec &ex, const size_t &branch_idx, 
		vector<value_t> *input){

    cout << __func__ << endl;
    cout << ex << endl;
    cout << "branch_idx " << branch_idx << endl;
    cout << "input " << container2str(*input) << endl;

    const auto &constraints = ex.path().constraints();
    
    //Optimization
    for(auto i = static_cast<int>(branch_idx) - 1; i >= 0; --i){
      if (*constraints.at(branch_idx) == *constraints.at(i)){
	cout << "*********** optimized, idx " << branch_idx << " = " << i << endl;
	return false;
      }
    }

    vector<const SymPred*> 
      cs(constraints.begin(),constraints.begin()+branch_idx+1);
	 
    cout << "constraint " << *constraints[branch_idx];
    cout << ", z3 " << constraints[branch_idx]->expr_str();
    constraints[branch_idx]->Negate();
    cout << ", after neg " << *constraints[branch_idx] ;
    cout << ", z3 " << constraints[branch_idx]->expr_str();
    cout << endl;

    std::map<var_t,value_t>sol;
    auto success = SMTSolver::IncrementalSolve(ex.inputs(), ex.vars(),cs, &sol);
    constraints[branch_idx]->Negate();
    
    if (success){
      cout << "Merge sol with prev input to get neew input" << endl;
      *input = ex.inputs();
      cout << "cur input " << container2str(*input) << endl; 
      cout << "sol " << container2str(sol) << endl;
      for(const auto &i: sol){
	(*input)[i.first] = i.second;
      }
      cout << "new input " << container2str(*input) << endl; 
      return true;
    }

    return false;
  }

  bool Search::
  CheckPrediction(const SymExec &old_exec, const SymExec &new_exec, 
		  const size_t &branch_idx){
    cout << __func__ << endl;
    cout << "branch idx " << branch_idx << endl;;
    cout << "old ex " << old_exec
	 << "\nnew ex " << new_exec << endl;

    if ((old_exec.path().branches().size() <= branch_idx) || 
	(new_exec.path().branches().size() <= branch_idx)){
      return false;
    }

    for (size_t j = 0 ; j < branch_idx; ++j){
      if(new_exec.path().branches().at(j) != old_exec.path().branches().at(j)) {
	return false;
      }
    }

    return (new_exec.path().branches().at(branch_idx) == 
	    paired_branch_.at(old_exec.path().branches().at(branch_idx)));

  }

  /*** BoundedDepthFirstSearch ***/

  BoundedDepthFirstSearch::BoundedDepthFirstSearch
  (const string &prog, const int &max_iters, const int &max_depth)
    : Search(prog, max_iters), max_depth_(max_depth){}

  BoundedDepthFirstSearch::~BoundedDepthFirstSearch(){}

  bool BoundedDepthFirstSearch::run(){
    SymExec ex;

    if(RunProgram(vector<value_t>(), &ex)){
      //UpdateCoverage(ex);
      return true;
    }
    else{
      return DFS(0, max_depth_, ex);
    }
  }

  bool BoundedDepthFirstSearch::
  DFS(const size_t &pos, int depth, SymExec &prev_exec){

    cout << __func__ << 
      " (pos " << pos << ", depth " << depth << ")" << endl;

    SymExec cur_exec;
    vector<value_t> input;
    const auto& path = prev_exec.path();

    for (size_t i = pos; (i < path.constraints().size()) && (depth > 0); ++i){
      cout << "DFS at cst " << i << "/" << path.constraints().size()-1 << endl;

      if(!SolveAtBranch(prev_exec, i, &input)){
	continue;
      }

      if (RunProgram(input, &cur_exec)){
	//UpdateCoverage(cur_exec);
	return true;
      }

      //check for prediction failure
      auto branch_idx = path.constraints_idx()[i];
      if (!CheckPrediction(prev_exec, cur_exec, branch_idx)){
	cout << "Prediction failed" << endl;
	continue;
      }
      
      depth--;
      if (DFS(i+1, depth, cur_exec))
	return true;
      
    }

    return false;
  }

}//namespace crest




int main(int argc, char* argv[]){
  if (argc < 4) {
    printf("Syntax: run_crest <program> "
	   "<number of iterations> "
	   "-<strategy> [strategy options]\n");
    printf("  Strategies include: "
	   "dfs\n");
    return 1;
  }
  
  auto prog = argv[1];
  const auto n_iters = atoi(argv[2]);
  const string search_type = argv[3];
  
  crest::Search *strategy;
  if (search_type == "-dfs"){
    if(argc == 4){
      strategy = new 
	crest::BoundedDepthFirstSearch(prog, n_iters, 1000000);
       
    } else{
      strategy = new 
	crest::BoundedDepthFirstSearch(prog, n_iters, atoi(argv[4]));
    }
  }
  else {
    printf("Err: Unknown search strategy: %s\n", search_type.c_str());
    return 1;
  }
  strategy->run();
  delete strategy;

  return 0;
}
