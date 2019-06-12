public class Stack {
  public static void main(String[] args) {
    // Stack s = new Stack();
    // System.out.println(s.p);
    // System.out.println(s.p());
    java.util.Stack<String> stack = new java.util.Stack<String>();
    stack.push("a");
    stack.push("b");
    stack.push("c");
    stack.push("d");
    System.out.println(stack.size()); //=> 4
    // bottom of stack at 0
    // top of stack at length-1
    System.out.println(stack.get(1)); //=> "b"
  }

  // int p = 4;
  // int p() { return 5; }

}
