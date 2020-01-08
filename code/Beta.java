class Beta {
  public Beta b;
  public void test(int x) {
    // int b = 1; // OK
    // Beta x = null; // BAD
    // int Beta = 1; // OK
    // Beta b = b; // BAD
    // Beta b = this.b; // OK
  }
}
