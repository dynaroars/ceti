#include <cstdio>
#include <cstdlib>
#include <cstddef>
#include <iostream>
#include <istream>
#include <fstream>
#include <string>
#include <sstream>
#include <vector>
#include <map>
#include <set>
#include <cassert>


using std::stringstream;
using std::string;
using std::set;
using std::map;
using std::vector;
using std::iostream;

using std::cout;
using std::endl;

namespace crest{
  typedef int branch_id_t;
  typedef long long int value_t;
  typedef unsigned int function_id_t;
  typedef unsigned int var_t;
  typedef long long int value_t;
  typedef unsigned long int address_t;

  enum compare_op_t {EQ = 0, NEQ = 1, GT = 2, LE = 3, LT = 4, GE = 5};
  compare_op_t NegateCompareOp(compare_op_t);

  enum type_t { U_CHAR = 0,       CHAR = 1,
		U_SHORT = 2,      SHORT = 3,
		U_INT = 4,        INT = 5,
		U_LONG = 6,       LONG = 7,
		U_LONG_LONG = 8,  LONG_LONG = 9 };


  template<class T>
    const string vec2str(const vector<T> &vec){
    stringstream ss;
    size_t i = 0;
    ss << vec.size() << " [" ;
    for(auto it: vec){
      ss << it;
      if (++i < vec.size()) ss << ", ";
    }
    ss << "]";
    return ss.str();
  }

  template<class T1, class T2>
    const string map2str(const map<T1,T2> &mmap){
    stringstream ss;
    size_t i = 0;
    
    ss << mmap.size() << " [" ;
    for(auto it: mmap){
      ss <<  "(" << it.first << "," << it.second << ")";
      if (++i < mmap.size()) ss << ", ";
    }
    ss << "]";
    return ss.str();
  }
  
}//namespace crest




//common utils

