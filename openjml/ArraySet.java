public class ArraySet {
    public static int MAX_SIZE = 2000000000;

    //@ ensures \result <==> (\exists int i; 0 <= i && i < a.length && a[i] == v);
    //@ ensures (!\result) ==> (\forall int i; 0 <= i && i < a.length ==> a[i] != v);
    //@ pure
    static public boolean contains(int[] a, int v) {
	int i = 0;
	//@ maintaining 0 <= i && i <= a.length;
	//@ maintaining (\forall int j; 0 <= j && j < i ==> a[j] != v);
	while (i < a.length) {
	    if (a[i] == v) return true;
	    i++;
	}
	return false;
    }

    //@ ensures (\forall int v; ! contains(\result, v));
    static public int[] empty_set() {
	return new int[0];
    }

    //@ ensures contains(\result, v);
    static public int[] singleton_set(int v) {
	int[] res = new int[1];
	res[0] = v;
	return res;
    }

    //@ requires a.length < MAX_SIZE / 2;
    //@ requires b.length < MAX_SIZE / 2;
    //@ ensures (\forall int v; contains(\result, v) <==> (contains(a, v) || contains(b, v)));
    static public int[] union(int[] a, int[] b) {
	int[] res = new int[a.length + b.length];
	//@ maintaining 0 <= i && i <= a.length;
	//@ maintaining (\forall int j; 0 <= j && j < i ==> contains(res, a[j]));
	for (int i = 0; i < a.length; i++) {
	    res[i] = a[i];
	}
	//@ maintaining 0 <= i && i <= b.length;
	//@ maintaining (\forall int j; 0 <= j && j < a.length ==> contains(res, a[j]));
	//@ maintaining (\forall int j; 0 <= j && j < i ==> contains(res, b[j]));
	for (int i = 0; i < b.length; i++) {
	    res[a.length+i] = b[i];
	}
	return res;
    }

}
