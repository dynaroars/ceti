#include <stdio.h>
#include <assert.h>
#include <crest.h>
#include "common.h"

int arr_equiv(int a1[], int a2[], int siz){

  int i = 0;
  for(;i<siz;++i){
    if (a1[i]!=a2[i]){
      return 0;
    }
  }
  return 1;
}
void print_arr(int a[], int siz){
  int i = 0;
  printf("[");
  for(; i < siz;++i){
    printf("%d",a[i]);
    if (i < siz-1) printf(", ");
  }
  printf("]\n");
}

/*Array Init*/

void buggy_arr_init(int arr[],
		    int fa1, int fa2, int fa3){
  int i = 0;
  for (i;i<sizeof(arr);++i){
    arr[i]=fa1*i+fa3; //fix: arr[i] = i
  }
}


void test_arr_init(){
  int fa1,fa2,fa3;
  CREST_int(fa1);
  CREST_int(fa2);
  CREST_int(fa3);
  int max_int = 1000;

  int siz=10;
  int arr[10]={0,1,2,3,4,5,6,7,8,9};
  buggy_arr_init(arr,fa1,fa2,fa3);

  int arr_ref[10]={0,1,2,3,4,5,6,7,8,9};

  if (arr_equiv(arr,arr_ref,siz)){
    printf("^^^ GOAL ^^^\n");
    /*fix found*/
  }

}


int ref_arr_2c_p1(int arr[], int c){
  return arr[2*c];
}

int buggy_arr_2c_p1(int arr[], int c,
			int af1, int af2, int af3){
  return arr[af1*c];
}


void test_arr_2c_p1(){
  int fa1, fa2, fa3;
  CREST_int(fa1);
  CREST_int(fa2);
  CREST_int(fa3);

  int arr1[10]={0,7,28,15,-2,8,14,44,9,-1};
  int arr2[10]={10,-7,8,-15,88,15,-4,-4,-9,-1};
  int arr3[10]={100,-70,80,-150,880,150,-40,-40,-90,-10};

  int rb1 = buggy_arr_2c_p1(arr1,0,fa1,fa2,fa3);
  int rr1 = ref_arr_2c_p1(arr1,0);
  int rb2 = buggy_arr_2c_p1(arr1,3,fa1,fa2,fa3);
  int rr2 = ref_arr_2c_p1(arr1,3);
  int rb3 = buggy_arr_2c_p1(arr1,4,fa1,fa2,fa3) ;
  int rr3 = ref_arr_2c_p1(arr1,4);
  if( rb1 == rr1 &&
      rb2 == rr2 &&
      rb3 == rr3){
    printf("^^^ GOAL ^^^\n");
  }

}

/*Discovering Properties about Arrays in Simple Programs*/

/*Array Max*/
int buggy_arr_max0(int arr[], int siz,
		  int fa1, int fa2, int fa3){

  int max = arr[0];
  int i=fa1;
  for (; i < siz; ++i){
    if (max < arr[i]){
      max = arr[i];
    }
  }
  return max;
}

int buggy_arr_max1(int arr[], int siz,
		  int fa1, int fa2, int fa3){

  /*
    for i = fix3 ... OK
    max = arr[?]  ... NOT OK
    max = arr[i]+?? ... OK
   */
  int max = arr[0];
  int i;
  for (i = 1; i < siz; ++i){
    if (max < arr[i]){
      max = fa1*arr[i]+fa2*i+fa3;
    }
  }
  return max;
}

int buggy_arr_max2(int arr[], int siz,
		   int fa1, int fa2, int fa3,
		   int fb1, int fb2, int fb3){

  int max = arr[0];
  int i;
  for (i = 1; i < siz; ++i){
    if (max > arr[i])
      max = fa1*arr[i]+fa2*i+fa3;
    else
      max = fb1*arr[i]+fb2*i+fb3;
      
  }
  return max;
}


void test_arr_max(){
  int fa1,fa2,fa3,
    fb1,fb2,fb3;
  CREST_int(fa1);
  CREST_int(fa2);
  CREST_int(fa3);
  CREST_int(fb1);
  CREST_int(fb2);
  CREST_int(fb3);
  int max_int = 10;


  int arr1[10]={0,1,2,3,4,5,6,7,8,9};
  int arr2[7]={7,4,10,6,7,8,9};
  int arr3[3]={10,20,99};
  int arr4[3]={10,99,20};
  if(in_range(fa1,max_int) && in_range(fa2,max_int) && in_range(fa3,max_int)&&
     in_range(fa1,max_int) && in_range(fa2,max_int) && in_range(fa3,max_int)){
    if (buggy_arr_max2(arr1,10,fa1,fa2,fa3,fb1,fb2,fb3)==9,
	buggy_arr_max2(arr2,7,fa1,fa2,fa3,fb1,fb2,fb3)==10,
	buggy_arr_max2(arr3,3,fa1,fa2,fa3,fb1,fb2,fb3)==99,
	buggy_arr_max2(arr4,3,fa1,fa2,fa3,fb1,fb2,fb3)==99){
      printf("^^^ GOAL ^^^\n");
    }
  }

}


/* Array Copy */
void ref_arr_copy(int src[], int dst[], int siz){
  int i=0;
  for (; i< siz; ++i)
    dst[i]=src[i];

  assert(arr_equiv(src,dst,siz));
  
}



void test_arr_copy(){
  int arr1[10]={0,1,2,3,4,5,6,7,8,9};
  int arr2[7]={7,4,10,6,7,8,9};
  int arr3[3]={10,20,99};
  int arr4[3]={10,99,20};
  
  int arrb1[10]={-1,-1,-1,-1,-1,-1,-1,-1,-1,-1};
  ref_arr_copy(arr1,arrb1,10);

  if(1){
    print_arr(arrb1,10);
  }
  
}
