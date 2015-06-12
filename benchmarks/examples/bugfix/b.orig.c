int buggyQ(float x, float y){
  return x + y == 100.3; 
}
int mainQ(float x, float y){
  return buggyQ(x, y);
}


void main(int argc, char* argv[]){
  printf("%d\n",mainQ(atof(argv[1]), atof(argv[2])));
}
