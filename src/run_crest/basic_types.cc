#include "basic_types.h"
#include <limits>
using std::numeric_limits;

namespace crest{
  compare_op_t NegateCompareOp(compare_op_t op){
    return static_cast<compare_op_t>(op ^ 1);
  }

  const string op_str[] = {"=", "!=", ">" , "<=", "<", ">="};
  // std::map<const compare_op_t, const string> op_str = 
  //   {{compare_op_t::EQ,  "=="}, 
  //    {compare_op_t::NEQ, "!="},
  //    {compare_op_t::GT,  ">" }, 
  //    {compare_op_t::LE,  "<="}, 
  //    {compare_op_t::LT,  "<" }, 
  //    {compare_op_t::GE,  ">="}};

  // std::map<const compare_op_t, const compare_op_t> op_neg=
  //   {{compare_op_t::EQ,  compare_op_t::NEQ }, 
  //    {compare_op_t::NEQ, compare_op_t::EQ  },
  //    {compare_op_t::GT,  compare_op_t::LE  }, 
  //    {compare_op_t::LE,  compare_op_t::GT  }, 
  //    {compare_op_t::LT,  compare_op_t::GE  }, 
  //    {compare_op_t::GE,  compare_op_t::LT  }};

  // const compare_op_t NegateCompareOp(compare_op_t op){
  //   return op_neg[op];
  // }

  // value_t CastTo(value_t val, type_t type) {
  //   switch (type) {
  //   case c_types::U_CHAR:   return static_cast<unsigned char>(val);
  //   case c_types::CHAR:     return static_cast<char>(val);
  //   case c_types::U_SHORT:  return static_cast<unsigned short>(val);
  //   case c_types::SHORT:    return static_cast<short>(val);
  //   case c_types::U_INT:    return static_cast<unsigned int>(val);
  //   case c_types::INT:      return static_cast<int>(val);
  //   case c_types::U_LONG:   return static_cast<unsigned long>(val);
  //   case c_types::LONG:     return static_cast<long>(val);

  //     // Cast would do nothing in these cases.
  //   case c_types::U_LONG_LONG:
  //   case c_types::LONG_LONG:
  //     return val;
  //   }

  //   // Cannot reach here.                
  //   assert(false);
  //   return 0;
  // }


}//namespace crest
