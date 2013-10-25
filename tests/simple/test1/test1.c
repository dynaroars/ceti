#include <crest.h>
#include <stdio.h>

void tvn_foo(int a){
  if (a == 5) {
    fprintf(stderr, "GOAL!\n");
  }

}

int main(){
  int a;
  CREST_int(a);
  tvn_foo(a);
  return 0;
}
