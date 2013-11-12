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

  // const char* kMinValueStr[] = {
  //   "0",
  //   "-128",
  //   "0",
  //   "-32768",
  //   "0",
  //   "-2147483648",
  //   "0",
  //   "-2147483648",
  //   "0",
  //   "-9223372036854775808",
  // };

  // const char* kMaxValueStr[] = {
  //   "255",
  //   "127",
  //   "65535",
  //   "32767",
  //   "4294967295",
  //   "2147483647",
  //   "4294967295",
  //   "2147483647",
  //   "18446744073709551615",
  //   "9223372036854775807",
  // };


  value_t CastTo(value_t val, type_t type) {
    switch (type) {
    case c_types::U_CHAR:   return static_cast<unsigned char>(val);
    case c_types::CHAR:     return static_cast<char>(val);
    case c_types::U_SHORT:  return static_cast<unsigned short>(val);
    case c_types::SHORT:    return static_cast<short>(val);
    case c_types::U_INT:    return static_cast<unsigned int>(val);
    case c_types::INT:      return static_cast<int>(val);
    case c_types::U_LONG:   return static_cast<unsigned long>(val);
    case c_types::LONG:     return static_cast<long>(val);

    case c_types::FLOAT:     return static_cast<float>(val);
    case c_types::DOUBLE:    return static_cast<double>(val);

      // Cast would do nothing in these cases.
    case c_types::U_LONG_LONG:
    case c_types::LONG_LONG:
      return val;
    }

    // Cannot reach here.                
    assert(false);
    return 0;
  }


  // const value_t kMinValue[] = {
  //   numeric_limits<unsigned char>::min(),   
  //   numeric_limits<char>::min(),            
  //   numeric_limits<unsigned short>::min(),
  //   numeric_limits<short>::min(),
  //   numeric_limits<unsigned int>::min(),
  //   numeric_limits<int>::min(),
  //   numeric_limits<unsigned long>::min(),
  //   numeric_limits<long>::min(),
  //   numeric_limits<unsigned long long>::min(),
  //   numeric_limits<long long>::min(),

  //   numeric_limits<float>::min(),
  //   numeric_limits<double>::min()
  // };

  // const value_t kMaxValue[] = {
  //   numeric_limits<unsigned char>::max(),
  //   numeric_limits<char>::max(),
  //   numeric_limits<unsigned short>::max(),
  //   numeric_limits<short>::max(),
  //   numeric_limits<unsigned int>::max(),
  //   numeric_limits<int>::max(),
  //   numeric_limits<unsigned long>::max(),
  //   numeric_limits<long>::max(),
  //   numeric_limits<unsigned long long>::max(),
  //   numeric_limits<long long>::max(),

  //   numeric_limits<float>::max(),
  //   numeric_limits<double>::max()
  // };

  // const size_t kByteSize[] = {
  //   sizeof(unsigned char),       sizeof(char),
  //   sizeof(unsigned short),      sizeof(short),
  //   sizeof(unsigned int),        sizeof(int),
  //   sizeof(unsigned long),       sizeof(long),
  //   sizeof(unsigned long long),  sizeof(long long),
  //   sizeof(float), sizeof(double)
  // };
  

}//namespace crest
