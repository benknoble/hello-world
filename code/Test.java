public class Test {
  // enum S { A, b }
  public static void main(String[] args) {
    System.out.println(null instanceof Test);
    System.out.println("Hello World!");
    int a = (new Test()).s;
    System.out.println(a);
    // System.out.println(S.A.toString().toLowerCase());
    // System.out.println(S.b.toString().toUpperCase());
  }

  public Test() { }
  public int test = 5 ;
  public static int s = 4;
}
