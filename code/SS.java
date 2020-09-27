import java.util.*;

class R {
  final int a, b, c;
  R(int a, int b, int c) {
    this.a = a;
    this.b = b;
    this.c = c;
  }

  @Override
  public boolean equals(Object o) {
    if (!(o instanceof R)) return false;
    R r = (R)o;
    return a == r.a && b == r.b && c == r.c;
  }

  @Override
  public int hashCode() {
    return Objects.hash(a, b, c);
  }

  @Override
  public String toString() {
    return String.format("R[%d, %d, %d]", a, b, c);
  }
}

class SS {
  static R R(int a, int b, int c) { return new R(a, b, c); }

  final static Set<R> s =
    Set.of(
        R(1,2,3),
        R(3,4,5));

  public static void main(String[] args) {
    System.out.println(s);
    System.out.println(s.contains(R(1,2,3)));
    System.out.println(s.contains(R(2,2,3)));
  }
}
