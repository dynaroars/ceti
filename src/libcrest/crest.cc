#include "run_crest/sym_interpreter.h"
#include "libcrest/crest.h"
#include "ctime"

using namespace crest;

static SymInterpreter* SI;
static int pre_sym;

static const int kOpTable[]={
  // binary arithmetic
  c_ops::ADD, c_ops::SUBTRACT, c_ops::MULTIPLY, c_ops::DIVIDE, c_ops::CONCRETE,
  // binary bitwise operators
  c_ops::CONCRETE, c_ops::CONCRETE, c_ops::CONCRETE, c_ops::SHIFT_L, c_ops::CONCRETE,
  // binary logical operators
  c_ops::CONCRETE, c_ops::CONCRETE,
  // binary comparison
  c_ops::EQ, c_ops::NEQ, c_ops::GT, c_ops::LE, c_ops::LT, c_ops::GE,
  // unhandled binary operators
  c_ops::CONCRETE,
  // unary operators
  c_ops::NEGATE, c_ops::BITWISE_NOT, c_ops::LOGICAL_NOT
};


void __CrestAtExit(){
  cout << __func__ << endl;

  //write exec out to 'szd_execution'
  const auto &ex = SI->ex();
  cout << ex << endl;

  string buff;
  buff.reserve(1<<26);
  ex.Serialize(&buff);
  std::ofstream out("szd_execution", std::ios::out|std::ios::binary);
  out.write(buff.data(), buff.size());
  assert(!out.fail());
  out.close();
}

void __CrestInit(){
  cout << __func__ << endl;
  srand((unsigned) time(NULL));

  //Read input
  vector<value_t> input; std::ifstream in("input");
  value_t v; while(in >> v) input.push_back(v); in.close();
  
  SI = new SymInterpreter(input);
  pre_sym = 1;
  assert(!atexit(__CrestAtExit));
}


void __CrestCall(__CREST_ID id, __CREST_FUNC_ID fid){
  cout << __func__ << endl;
  SI->Call(id, fid);
}


void __CrestLoad(__CREST_ID id, __CREST_ADDR addr, __CREST_VAL val){
  cout << __func__ << endl;
  if (!pre_sym) SI->Load(id, addr, val);
}

void __CrestStore(__CREST_ID id, __CREST_ADDR addr){
  cout << __func__ << endl;
  if (!pre_sym) SI->Store(id, addr);
}

void __CrestClearStack(__CREST_ID id){
  cout << __func__ << endl;
  if (!pre_sym) SI->ClearStack(id);
}


void __CrestApply1(__CREST_ID id, __CREST_OP op , __CREST_VAL val){
  cout << __func__ << endl;  
  assert((__CREST_NEGATE <= op) && (op <= __CREST_L_NOT));

  if (!pre_sym)
    SI->ApplyUnaryOp(id, static_cast<unary_op_t>(kOpTable[op]), val);
}


void __CrestApply2(__CREST_ID id, __CREST_OP op , __CREST_VAL val){
  cout << __func__ << endl;  

  assert(__CREST_ADD <= op && op <= __CREST_CONCRETE);
  if (pre_sym) return;

  if(__CREST_ADD <= op && op <= __CREST_L_OR)
    SI->ApplyBinaryOp(id, static_cast<binary_op_t>(kOpTable[op]), val);
  else
    SI->ApplyCompareOp(id, static_cast<compare_op_t>(kOpTable[op]), val);
}



void __CrestHandleReturn(__CREST_ID id, __CREST_VAL val){
  cout << __func__ << endl;
  if (!pre_sym) SI->HandleReturn(id, val);
}

void __CrestReturn(__CREST_ID id){
  cout << __func__ << endl;
  SI->Return(id);
}

void __CrestBranch(__CREST_ID id, __CREST_BRANCH_ID bid, __CREST_BOOL b){
  cout << __func__ << endl;  
  if(pre_sym) SI->Load(id,0,b);
  SI->Branch(id, bid, static_cast<bool>(b));
}



void __CrestInt(int *x){
  cout << __func__ << endl;
  pre_sym = 0;
  *x = (int)SI->NewInput(c_types::INT, (addr_t)x);
}


void __CrestUChar(unsigned char* x) {
  cout << __func__ << endl;
  pre_sym = 0;
  *x = (unsigned char)SI->NewInput(c_types::U_CHAR, (addr_t)x);
}

void __CrestUShort(unsigned short* x) {
  cout << __func__ << endl;
  pre_sym = 0;
  *x = (unsigned short)SI->NewInput(c_types::U_SHORT, (addr_t)x);
}

void __CrestUInt(unsigned int* x) {
  cout << __func__ << endl;
  pre_sym = 0;
  *x = (unsigned int)SI->NewInput(c_types::U_INT, (addr_t)x);
}

void __CrestChar(char* x) {
  cout << __func__ << endl;
  pre_sym = 0;
  *x = (char)SI->NewInput(c_types::CHAR, (addr_t)x);
}

void __CrestShort(short* x) {
  cout << __func__ << endl;
  pre_sym = 0;
  *x = (short)SI->NewInput(c_types::SHORT, (addr_t)x);
}
