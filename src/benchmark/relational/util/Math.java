package benchmark.relational.util;

public class Math {
	public static int pow(int a, int b) {
	    if (b == 0)        return 1;
	    if (b == 1)        return a;
	    if (b % 2 == 0)    return     pow ( a * a, b/2); //even a=(a^2)^b/2
	    else               return a * pow ( a * a, b/2); //odd  a=a*(a^2)^b/2
	}
}
