int buggyQ(int x, int y){
  return x + y == 110; //bug
}
int mainQ(int x, int y){
  return buggyQ(x, y);
}


void main(int argc, char* argv[]){
  printf("%d\n",mainQ(atoi(argv[1]), atoi(argv[2])));
}
