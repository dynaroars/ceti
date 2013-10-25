#include <stdio.h>
#include <crest.h>

int arr_equiv(int a1[], int a2[]){
  if (sizeof(a1) != sizeof(a2)){
    return 0;
  }

  int i = 0;
  for(;i<sizeof(a1);++i){
    if (a1[i]!=a2[i]){
      return 0;
    }
  }
  return 1;
}
void print_arr(int a[]){
  int i = 0;
  for(;i<sizeof(a);++i){
    printf("%d, ",a[i]);
  }
  printf("\n");
}

/*Array Init*/

void buggy_arr_init(int arr[],
		    int fix1, int fix2, int fix3){
  int i = 0;
  for (i;i<sizeof(arr);++i){
    arr[i]=fix1*i+fix3; //fix: arr[i] = i
  }
}


void test_arr_init(){
  int fix1,fix2,fix3;
  CREST_int(fix1);
  CREST_int(fix2);
  CREST_int(fix3);
  int max_int = 1000;

  int siz=10;
  int arr[10]={0,1,2,3,4,5,6,7,8,9};
  buggy_arr_init(arr,fix1,fix2,fix3);

  int arr_ref[10]={0,1,2,3,4,5,6,7,8,9};

if (arr_equiv(arr,arr_ref)){
    printf("^^^ FIXED ^^^\n");
    /*fix found*/
  }

}

/*Discovering Properties about Arrays in Simple Programs*/
/*Array Max*/
int buggy_arr_max(int arr[], int siz,
		  int fix1, int fix2, int fix3){

  /*
    for i = fix3 ... OK
    max = arr[?]  ... NOT OK
    max = arr[i]+?? ... OK
   */
  int max = arr[0];
  int i;
  for (i = 1; i < siz; ++i){
    if (max < arr[i]){
      max = fix1*arr[i]+fix2;
    }
  }
  return max;
}


void test_arr_max(){
  int fix1,fix2,fix3;
  CREST_int(fix1);
  CREST_int(fix2);
  CREST_int(fix3);
  int max_int = 1000;


  int arr1[10]={0,1,2,3,4,5,6,7,8,9};
  int arr2[7]={7,4,10,6,7,8,9};
  int arr3[3]={10,20,99};
  int arr4[3]={10,99,20};

  if(-max_int<=fix1&&fix1<=max_int &&
     -max_int<=fix2&&fix2<=max_int &&
     -max_int<=fix3&&fix3<=max_int){

    if (buggy_arr_max(arr1,10,fix1,fix2,fix3)==9,
	buggy_arr_max(arr2,7,fix1,fix2,fix3)==10,
	buggy_arr_max(arr3,3,fix1,fix2,fix3)==99,
	buggy_arr_max(arr4,3,fix1,fix2,fix3)==99){
      printf("^^^ FIXED ^^^\n");
    }
  }

}
