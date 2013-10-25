#include "basic_types.h"

namespace crest{
  compare_op_t NegateCompareOp(compare_op_t op){
    return static_cast<compare_op_t>(op ^ 1);
  }

}//namespace crest
