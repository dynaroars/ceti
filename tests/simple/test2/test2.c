#include <crest.h>
#include <stdio.h>

void tvn_foo(int a, int b, int c, int d){
  if (a == 5) {
    if (b == 19) {
      if (c == 7) {
        if (d == 4) {
          fprintf(stderr, "GOAL!\n");
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
