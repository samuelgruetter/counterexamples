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

    // correct @ ensures (a <= b && \result == b || a >= b && \result == a);
    //@ ensures (a <= b && \result == b || a >= b && \result == b);
    //@ pure
    static public int max(int a, int b) {
	//@ show a;
	//@ show b;
	if (a < b) return b;
	return a;
    }
    /*
ArraySet.max Method assertions are INVALID
ArraySet.java:22: warning: Show statement expression a has value 0
	//@ show a;
		 ^
ArraySet.java:23: warning: Show statement expression b has value ( - 1 )
	//@ show b;
		 ^
ArraySet.java:25: warning: The prover cannot establish an assertion (Postcondition: ArraySet.java:19: ) in method max
	return a;
	^
ArraySet.java:19: warning: Associated declaration: ArraySet.java:25:
    //@ ensures (a <= b && \result == b || a >= b && \result == b);
	^

COUNTEREXAMPLE
b_0_0___10 = 0
a_704_704___13 = 0
objectTimesFinalized_11042_0___5 = ( _ as-array k!1 )
_JML___exception_696_696___11 = NULL
a_0_0___9 = 0
_JML___termination_696_696___12 = 0
_JML___result_696_696___15 = 0
THIS = THIS
Pre_3_0_601___17 = true
ASSERT_115_696 = true
MAX_SIZE_46_0___3 = 0
theString_8541_0___4 = ( _ as-array k!2 )
theHashCode_1958_0___6 = ( _ as-array k!4 )
owner_1510_0___7 = ( _ as-array k!5 )
PRE_a_704 = 0
_JML__tmp52 = true
PRE_b_711 = ( - 1 )
_alloc___7_0___8 = ( _ as-array k!3 )
__JML_AssumeCheck_ = 0
b_711_711___14 = ( - 1 )
    */

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
	//@ show a;
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
