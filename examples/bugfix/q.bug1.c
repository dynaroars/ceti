int buggyQ(int x, int y, int z){
  int t0 = 0;
  int t1 = 1;
  int t2 = 2;
  int dc = (t0 && t1 <= 600) || t2 > 600;
  return (x && y && z);
}
int mainQ(int x, int y, int z){
  return buggyQ(x, y, z);
}


void main(int argc, char* argv[]){
  printf("%d\n",mainQ(atoi(argv[1]), atoi(argv[2]),atoi(argv[3])));
}
