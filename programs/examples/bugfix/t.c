float mainQ(float x, float y){
  int a=3;
  int b=4;
  float c = a*x + b*y;
  return c;
}


void main(int argc, char* argv[]){
  printf("%g\n",mainQ(atof(argv[1]), atof(argv[2])));
}
