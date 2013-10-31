#ifndef BASIC_TYPES_H__
#define BASIC_TYPES_H__

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
#include <queue>
#include <set>
#include <cassert>
#include <type_traits>

using std::string;
using std::set;
using std::map;
using std::queue;
using std::vector;
using std::cout;
using std::endl;

namespace crest{
  typedef int branch_id_t;
  typedef long long int value_t;
  typedef unsigned int function_id_t;
  typedef unsigned int var_t;
  typedef long long int value_t;
  typedef unsigned long int address_t;

  namespace c_ops{
    enum compare_op_t {EQ = 0, NEQ = 1, GT = 2, LE = 3, LT = 4, GE = 5};

  }
  using c_ops::compare_op_t;

  compare_op_t NegateCompareOp(compare_op_t op);

  namespace c_types{
    enum type_t { U_CHAR = 0,       CHAR = 1,
		  U_SHORT = 2,      SHORT = 3,
		  U_INT = 4,        INT = 5,
		  U_LONG = 6,       LONG = 7,
		  U_LONG_LONG = 8,  LONG_LONG = 9 };
  }
  using c_types::type_t;

  value_t CastTo(value_t val, type_t type);

  extern const char* op_str[];
  extern const char* kMinValueStr [];
  extern const char* kMaxValueStr [];

  extern const value_t kMinValue [];
  extern const value_t kMaxValue [];
  extern const size_t kByteSize[];

  template<typename T>
    const string container2str(const T &ms){
    std::stringstream ss;
    size_t i = 0;
    ss << ms.size() << " [" ;
    for(const auto &it: ms){
      ss << it;
      if (++i < ms.size()) ss << ", ";
    }
    ss << "]";
    return ss.str();
  }

  template<typename T>
    const string container2str(const vector<T *> &ms){
    std::stringstream ss;
    size_t i = 0;
    ss << ms.size() << " [" ;
    for(const auto &it: ms){
      ss << *it;
      if (++i < ms.size()) ss << ", ";
    }
    ss << "]";
    return ss.str();
  }


  template<typename T1, typename T2>
    const string container2str(const map<T1,T2> &mmap){
    std::stringstream ss;
    size_t i = 0;
    
    ss << mmap.size() << " [" ;
    for(const auto &it: mmap){
      ss <<  "(" << it.first << "," << it.second << ")";
      if (++i < mmap.size()) ss << ", ";
    }
    ss << "]";
    return ss.str();
  }

}//namespace crest

#endif  // BASE_BASIC_TYPES_H__ 
