#include <crest.h>
#include <stdio.h>
#include <assert.h>

void tvn_foo(int a, int b){
  if (3*b < 100){ 
    fprintf(stdout, "3b - 100 < 0\n");
    if (a*4 >=0){
      fprintf(stdout, "4a >= 0\n");
	if (2*b + a*3 == 19) {
	  fprintf(stdout, "2b+3a - 19 == 0\n");
	  fprintf(stdout, "\nGOAL!\n");
	}else{
	  fprintf(stdout, "2b+3a - 19 != 0\n");
	}
    }else{
      fprintf(stdout, "4a < 0\n");
    }
  }else{
    fprintf(stdout, "3b - 100 >= 0\n");
  }
  
}

int main(){
  int a, b;
  CREST_int(a);
  CREST_int(b);
  tvn_foo(a,b);
  return 0;
}
