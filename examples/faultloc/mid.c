/*
  From original Tuarantula paper, compute the middle number from 3 inputs
  Empirical Evaluation of the Tarantula Automatic Fault-Localization Technique
  
 */

#include <stdio.h>
#include <stdlib.h>
//#include <assert.h>

int main(int argc,char **argv){
  //0
  //config vars
  //9
  int x = atoi(argv[1]); 
  //10
  int y = atoi(argv[2]);
  //11
  int z = atoi(argv[3]);

  //12
  int m = z;

  //13
  if (y < z){
    //4
    if (x<y){
      //1
      m = y;
    }
    else 
      //3
      if (x<z){
	//2
	m = x;
    }
  }
  else{
    //8
    if(x>y){
      //5
      m=y;
    }
    else 
      //7
      if (x>z){
      //6
      m =x;
    }
  }

  printf("Middle number is: %d\n",m);
  //14
  return 0;
  
}
