interface I1 {double x = 1;}
class T1 implements I1 {double x = 2;}
class T2 extends T1 {private double x = 3;}
class T3 extends T1 {
    double x = 4;
    void show() {
        System.out.println( I1.x );
    }
}

public class Main {
    public static void main(String[] args) {
        new T3().show();
    }
}
