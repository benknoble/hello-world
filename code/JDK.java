public class JDK {
  // record Point(int x, int y) {}
  public static void main(String[] args) {
    var x = 1; //requires Java SE 10/JDK 10+
    var y = switch (x) { //requires JDK 13+, --enable-preview --source 13
                         // in JDK 14, becomes standard
      case 1 -> 2; // syntax highlighting broken (vim)
      default -> {
        yield 0;
      }
    };
    System.out.println(x);
    System.out.println(y);
    // JDK 14+
    // var p = new Point(1,2);
    // System.out.println(p);
    // System.out.println(p.x());
    // System.out.println(p.y());
  }
}
