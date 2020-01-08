interface I1 {double x = 1;}
class T1 implements I1 {double x = 2;}
class T2 extends T1 {private double x = 3;}
class T3 extends T1 {
    double x = 4;
    void show() {
        double top = I1.x;
        top = ((T1)(this)).x;
        // top = ((T2)(this)).x; //BAD
        top = this.x;
        System.out.println(top);
    }
}

public class Main {
    public static void main(String[] args) {
        new T3().show();
    }
}
