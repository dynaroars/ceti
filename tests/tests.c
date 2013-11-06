#include <crest.h>
#include <stdio.h>
#include "arrays.h"

//#include"big_prog1.h"

int reference_is_upward_preferred(int inhibit, int up_sep, int down_sep){ 
				  
  int bias;
  if(inhibit)
    bias = up_sep+100;
  else
    bias = up_sep;
  if (bias > down_sep)
    return 1;
  else
    return 0;

}


int buggy_is_upward_preferred(int inhibit, int up_sep, int down_sep, 
			      int fix1, int fix2, int fix3) {

  int bias;
  if(inhibit)
    //bias = down_sep; //fix: bias=up_sep+100
    bias = fix1+fix2*up_sep+fix3;
  else
    bias = up_sep;
  if (bias > down_sep)
    return 1;
  else
    return 0;

}


int buggy_is_upward_preferred2(int inhibit, int up_sep, int down_sep, 
			       int fix1, int fix2, int fix3,
			       int fix1_, int fix2_, int fix3_) {
  //requires 2 fixes
  int bias;
  if(inhibit)
    bias = fix2*up_sep+fix3;
  else
    bias = fix2_*up_sep+fix3_;
  if (bias > down_sep)
    return 1;
  else
    return 0;

}


void test_is_upward_preferred(){
  int fix1,fix2,fix3;
  CREST_int(fix1);
  CREST_int(fix2);
  CREST_int(fix3);

  int max_int = 1000;
  if(-max_int<=fix1&&fix1<=max_int &&
     -max_int<=fix2&&fix2<=max_int &&
     -max_int<=fix3&&fix3<=max_int
     ){
     
    if(buggy_is_upward_preferred(1,0,100 ,fix1,fix2,fix3) == 0 && 
       buggy_is_upward_preferred(1,11,110,fix1,fix2,fix3) == 1 && 
       buggy_is_upward_preferred(0,100,50,fix1,fix2,fix3) == 1 && 
       buggy_is_upward_preferred(1,-20,60,fix1,fix2,fix3) == 1 && 
       buggy_is_upward_preferred(0,0,10  ,fix1,fix2,fix3) == 0){
      printf("GOAL!\n");
      /*fix found*/
    }
  }
}

void test_is_upward_preferred2(){
  int fix1,fix2,fix3,fix1_,fix2_,fix3_;
  CREST_int(fix1);
  CREST_int(fix2);
  CREST_int(fix3);
  CREST_int(fix1_);
  CREST_int(fix2_);
  CREST_int(fix3_);

  int max_int = 1000;
  if(-max_int<=fix1&&fix1<=max_int &&
     -max_int<=fix2&&fix2<=max_int &&
     -max_int<=fix3&&fix3<=max_int &&
     -max_int<=fix1&&fix1_<=max_int &&
     -max_int<=fix2&&fix2_<=max_int &&
     -max_int<=fix3&&fix3_<=max_int
     ){
     
    if(buggy_is_upward_preferred2(1,0,100 ,fix1,fix2,fix3,fix1_,fix2_,fix3_) == 0 && 
       buggy_is_upward_preferred2(1,11,110,fix1,fix2,fix3,fix1_,fix2_,fix3_) == 1 && 
       buggy_is_upward_preferred2(0,100,50,fix1,fix2,fix3,fix1_,fix2_,fix3_) == 1 && 
       buggy_is_upward_preferred2(1,-20,60,fix1,fix2,fix3,fix1_,fix2_,fix3_) == 1 && 
       buggy_is_upward_preferred2(0,0,10  ,fix1,fix2,fix3,fix1_,fix2_,fix3_) == 0){
      printf("GOAL!\n");
      /*fix found*/
    }
  }
}



int buggy_calc(int op, int a, int b, 
	       int fix1, int fix2, int fix3){
  int r = a + b;
  if (op != 0){
    //r = b - a; fix: r= a - b ;
    r = fix1*a + fix2*b + fix3;
  }
  return r;
}

void test_calc(){
  /*Repair with On-The-Fly Program Analysis ?*/
  int fix1,fix2,fix3;
  CREST_int(fix1);
  CREST_int(fix2);
  CREST_int(fix3);

  int max_int = 1000;
  if(-max_int<=fix1&&fix1<=max_int &&
     -max_int<=fix2&&fix2<=max_int &&
     -max_int<=fix3&&fix3<=max_int){
     
    if(buggy_calc(0,3,5, fix1,fix2,fix3) == 8 && 
       buggy_calc(1,5,3, fix1,fix2,fix3) == 2 && 
       buggy_calc(1,6,1, fix1,fix2,fix3) == 5){
      printf("^^^ FIXED ^^^\n");
      /*fix found*/
    }
  }

}




int main(){

  /* test_is_upward_preferred2(); */
  /* test_calc(); */
  /* test_gcd(); */
  /* test_arr_init(); */
  test_arr_max();
  //test_arr_copy();
  //test_arr_2c_p1();
  return 0;
}
