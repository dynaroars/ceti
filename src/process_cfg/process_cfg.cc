// compile with -std=c++11 

#include <cassert>
#include <cstdio>

#include <limits>
#include <iostream>
#include <fstream>
#include <vector>
#include <set>
#include <string>
#include <sstream>
#include <unordered_map>
//#include <ext/hash_map>

using namespace std;

typedef set<int> branch_t;
typedef unordered_map<string,int> hmap_t;
typedef vector< pair<int, size_t> > adj_list_t;
typedef vector<adj_list_t> graph_t;

void readBranches(branch_t &branches){
  ifstream in("branches");
  int fid, numBranches;
  int b1,b2;
  while(in >> fid >> numBranches){
    for (int i = 0; i < numBranches; ++i){
      assert(in >> b1 >> b2);
      branches.insert(b1);
      branches.insert(b2);
    }
  }
  in.close();
}

void readCFG(graph_t &graph){
  hmap_t funcNodeMap;
  ifstream in_cfm("cfg_func_map");
  string func;
  int sid;
  while(in_cfm >> func >> sid){
    funcNodeMap[func]=sid;
  }
  in_cfm.close();

  hmap_t::const_iterator i;
  for(i=funcNodeMap.begin();i != funcNodeMap.end(); ++i){
    printf("%s -> %d, ",i->first.c_str(), i->second);
  }
  printf("\n");

  ifstream in_cfg("cfg");
  string line;
  int src, dst;

  while (getline(in_cfg,line)){
    cout << endl << line << endl;
    istringstream line_in(line);
    line_in >> src;
    line_in.get();

    //adj_list_t nbhrs;
   if (graph.size() <= src)
      graph.resize(src+1);
   adj_list_t &nbhrs = graph.at(src);

    while(line_in){
      if (isdigit(line_in.peek())){
	line_in >> dst;
	nbhrs.push_back(make_pair(dst,0));
      } else {
	line_in >> func;
	cout << func << endl;

	i = funcNodeMap.find(func);
	if (i != funcNodeMap.end())
	  nbhrs.push_back(make_pair(i->second,0));
      }
      line_in.get();
    }
    //graph->push_back(nbhrs);
  }
  in_cfg.close();
}

void disjkstra_bounded_shortest_paths
(const graph_t& graph, const int src, 
 vector<size_t>& dist_map, const size_t max_dist){

  for(int i = 0 ; i < graph.size(); ++i){
    dist_map[i] = numeric_limits<size_t>::max();
  }
  dist_map[src]=0;

  set< pair<size_t, int> >Q;
  Q.insert(make_pair(0,src));
  
  branch_t finished;

  while(!Q.empty()){
    size_t dist = Q.begin()->first;
    int v = Q.begin()->second;
    Q.erase(Q.begin());

    if(dist > max_dist) 
      break;
    
    //process the vertex
    finished.insert(v);
    for(adj_list_t::const_iterator e = graph[v].begin(); e!=graph[v].end(); ++e){
      int u = e->first;
      if (finished.find(u) == finished.end()){
  	size_t d = dist_map[v] + e->second;
  	if ((d < dist_map[u]) && (d <= max_dist)){
  	  Q.erase(make_pair(dist_map[u], u));
  	  Q.insert(make_pair(d, u));
  	  dist_map[u]=d;
  	}
      }
    }
  }
}

int main(){
  // Read in branches
  branch_t branches;
  readBranches(branches);
  printf("Read %d branches.\n",branches.size());
  int ctr = 0;
  for (branch_t::const_iterator it=branches.begin(); it != branches.end(); ++it){
    if (ctr==branches.size()-1){
      printf("%d", *it);
    }
    else{
      printf("%d, ", *it);
    }

    ctr++;
  }
  printf("\n");

  // Read in CFG
  graph_t graph;
  readCFG(graph);
  printf("Read %d nodes.\n",graph.size());

  for (graph_t::iterator i = graph.begin(); i != graph.end(); ++i){
    cout << "nbhrs size " << i->size() << ": ";
    for(adj_list_t::iterator j = i->begin(); j != i->end(); ++j){
      if (branches.find(j->first) != branches.end()){
	j->second = 1;
      }
      else{
	assert(j->second == 0);
      }

      cout << "(" << j->first << "," << j->second << ")" << " , ";
    }
    cout<< endl;
    
  }

  //Write out cfg_branches
  ofstream out ("cfg_branches");
  out << branches.size() << endl;

  vector<size_t>dist(graph.size());
  vector<int> nbhrs;
  int nEdges = 0;
  for (branch_t::const_iterator i = branches.begin(); i != branches.end(); ++i){

    //compute shortest-paths of length 0 and 1 from vertex it
    disjkstra_bounded_shortest_paths(graph, *i, dist, 1);

    nbhrs.clear();
    for (branch_t::const_iterator j = branches.begin(); j != branches.end(); ++j){
      if(dist.at(*j) == 1){
	nbhrs.push_back(*j);
      }
    }

    nEdges += nbhrs.size();

    out << *i << endl;   //me
    out << nbhrs.size() << endl; //of neighbors with dist <= 1
    out << nbhrs.front() << endl; //first neighbr ? 
  }

  out.close();
  printf("Wrote %d branch edges.\n",nEdges);
  
  return 0;
}
