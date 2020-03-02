int main() {
  int c = 1;
  switch(c){
    int x = 1;
    {
    case 0:
      return 1;
    }
    if (x) {
    case 1:
    case 8:
      return 2;
    } else {
    case 2:
    case 5:
      x = 2;
      x++;
      return 3;
    }
  case 4:
    x = 3;
    return 4;
  default:
    return 5;
  }
}
