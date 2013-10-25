#include "run_crest/concolic_search.h"

int main(int argc, char* argv[]){
  if (argc < 4) {
    printf("Syntax: run_crest <program> "
	   "<number of iterations> "
	   "-<strategy> [strategy options]\n");
    printf("  Strategies include: "
	   "dfs\n");
    return 1;
  }
  
  string prog = argv[1];
  int num_iters = atoi(argv[2]);
  string search_type = argv[3];
  
  crest::Search *strategy;
  if (search_type == "-dfs"){
    if(argc == 4){
      strategy = new 
	crest::BoundedDepthFirstSearch(prog, num_iters, 1000000);
       
    } else{
      strategy = new 
	crest::BoundedDepthFirstSearch(prog, num_iters, atoi(argv[4]));
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
