//cannot fix this because of mix type && and <
int buggyQ(int x, int y, int z){
  return (x && y < z);
}
int mainQ(int x, int y, int z){
  return buggyQ(x, y, z);
}


void main(int argc, char* argv[]){
  printf("%d\n",mainQ(atoi(argv[1]), atoi(argv[2]),atoi(argv[3])));
}
