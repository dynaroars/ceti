int buggyQ(int x, int y, int z){
  int t1 =  2 + (x || y || z) ; //bug  x && y
  int t2 = t1 - 2;
  return t2;
}
int mainQ(int x, int y, int z){
  return buggyQ(x, y, z);
}

void main(int argc, char* argv[]){
  printf("%d\n",mainQ(atoi(argv[1]), atoi(argv[2]),atoi(argv[3])));
}
