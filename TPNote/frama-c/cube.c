/*@
  requires \valid(t+(0..n-1));
  requires n > 0;
  requires n < 300;
  assigns t[0..n-1];
  ensures \forall integer i ; 0 <= i < n ==> t[i] == i*i*i;
*/

int cube(int t[], int n) {
  /*@
    loop invariant 0 <= i <= n;
    loop invariant \forall integer j ; 0 <= j < i ==> t[j] == j*j*j;
    loop variant n-i;
  */
  for(int i = 0; i < n; i++) {
    t[i] = i*i*i;
  }
}
