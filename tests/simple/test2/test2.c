#include <crest.h>
#include <stdio.h>

void tvn_foo(int a, int b, int c, int d){
  int a1 = a+1;
  if (a1 == 5) {  //3  ,  13  
    int b1 = b + 2;  
    if (b1 == 19) {  //5, 12
      int c1 = c + 3 ;
      if (c1 == 7) {  //7, 11
	int d1 = d + 15;
        if (d1 == 4) { //9, 10
          fprintf(stdout, "GOAL!\n");
        }
      }
    }
  }

}

int main(){
  int a, b, c, d;
  CREST_int(a);
  CREST_int(b);
  CREST_int(c);
  CREST_int(d);
  tvn_foo(a,b,c,d);
  return 0;
}
