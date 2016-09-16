/*@
	requires \valid(t+(0..n-1));
	requires \valid(v+(0..n-1));
	requires n > 0;
	assigns \nothing;
	ensures \result <==> \forall integer i ; 0 <= i <n ==> t[i] == v[i];	
*/

int compare(int t[], int v[], int n){
	/*@
		loop invariant 0 <= i <= n;
		loop invariant \forall integer j; 0 <= j < i ==> t[j] == v[j];
		loop variant n - i;
	*/
	for(int i = 0; i < n; i++) {
		if(t[i] != v[i]) {
			return 0;
		}
	}
	return 1;
}
