// Split -> Split -> CVC4 -> Auto level 1
/*@ predicate BeginLower(int* arr, integer n, integer slice) =
  @   \forall integer i, j; 0 <= i <= slice && i <= j <= n - 1 ==> arr[i] <= arr[j];
  @
  @ predicate EndGreater(int* arr, integer n, integer slice) =
  @   \forall integer i, j; 0 <= i <= j && slice <= j <= n - 1 ==> arr[i] <= arr[j];
  @
  @ predicate SubseqSorted(int* arr, integer start, integer end) =
  @   \forall integer i, j; start <= i <= j <= end ==> arr[i] <= arr[j];
  @
  @ predicate Sorted(int* arr, integer n) =
  @   SubseqSorted(arr, 0, n-1);
  @
  @ predicate Swap{L1, L2}(int* arr, integer n, integer i, integer j) =
  @   0 <= i < n && 0 <= j < n &&
  @   \at(arr[i], L1) == \at(arr[j], L2) &&
  @   \at(arr[j], L1) == \at(arr[i], L2) &&
  @   \forall integer k; 0 <= k < n && k != j && k != i ==>
  @     \at(arr[k], L1) == \at(arr[k], L2);
  @
  @ inductive Permut{L1, L2}(int* arr, integer n){
  @   case PermutRefl{L1}:
  @     \forall int* arr, integer n; 
  @       Permut{L1, L1}(arr, n);
  @   case PermutSym{L1, L2}:
  @     \forall int* arr, integer n, i, j;
  @       Permut{L1, L2}(arr, n) ==> Permut{L2, L1}(arr, n);
  @   case PermutSwap{L1, L2}:
  @     \forall int* arr, integer n, i, j; 
  @       Swap{L1, L2}(arr, n, i, j) ==> Permut{L1, L2}(arr, n);
  @   case PermutTrans{L1, L2, L3}:
  @     \forall int* arr, integer n;
  @       Permut{L1, L2}(arr, n) && Permut{L2, L3}(arr, n) ==> Permut{L1, L3}(arr, n);
  @ }
  @*/

/*@ requires \valid(arr + (0..n));
  @ requires n > 0;
  @
  @ ensures Sorted(arr, n);
  @ ensures Permut{Pre, Post}(arr, n);
  @*/
void cocktail_back(int *arr, int n) {
    int swapped = 1;
    int start = 0;
    int end = n - 1;

    /*@ loop invariant 0 <= start <= end + 1 <= n;
      @
      @ loop invariant swapped >= 0;
      @ loop invariant start > end ==> swapped == 0;
      @ loop invariant swapped == 0 ==> Sorted(arr, n);
      @
      @ loop invariant BeginLower(arr, n, start - 1);
      @ loop invariant EndGreater(arr, n, end + 1);
      @
      @ loop invariant Permut{Pre, Here}(arr, n);
      @
      @ loop variant end - start;
      @*/
    while (swapped > 0) {
        int i, tmp;

        //@ assert Permut{Pre, Here}(arr, n);

        swapped = 0;
        /*@ loop invariant start - 1 <= i <= end - 1;
          @
          @ loop invariant 0 <= swapped <= end - i - 1;
          @ loop invariant swapped == 0 ==> SubseqSorted(arr, i + 1, n - 1);
          @
          @ loop invariant BeginLower(arr, n, start - 1);
          @ loop invariant EndGreater(arr, n, end + 1);
          @ loop invariant \forall integer j; 
          @   start - 1 <= i < j <= n - 1 ==> arr[i + 1] <= arr[j];
          @
          @ loop invariant Permut{Pre, Here}(arr, n);
          @
          @ loop variant i;
          @*/
        for (i = end - 1; i >= start; --i) {
            //@ ghost first: ;
            if (arr[i] > arr[i + 1]) {
                tmp = arr[i];
                arr[i] = arr[i + 1];
                arr[i + 1] = tmp;
                ++swapped;
                //@ assert Swap{first, Here}(arr, n, i, i+1);
            }
        }

        //@ assert BeginLower(arr, n, start);
        //@ assert swapped == 0 ==> Sorted(arr, n);

        if (!swapped)
            break;
        ++start;

        //@ assert SubseqSorted(arr, 0, start) && Permut{Pre, Here}(arr, n);

        swapped = 0;
        /*@ loop invariant start <= i <= end;
          @
          @ loop invariant 0 <= swapped <= i - start;
          @ loop invariant swapped == 0 ==> SubseqSorted(arr, 0, i);
          @
          @ loop invariant BeginLower(arr, n, start - 1);
          @ loop invariant EndGreater(arr, n, end + 1);
          @ loop invariant \forall integer j; 
          @   0 <= j <= i <= end ==> arr[j] <= arr[i];
          @
          @ loop invariant Permut{Pre, Here}(arr, n);
          @
          @ loop variant end - i;
          @*/
        for (i = start; i < end; ++i) {
            //@ ghost second: ;
            if (arr[i] > arr[i + 1]) {
                tmp = arr[i];
                arr[i] = arr[i + 1];
                arr[i + 1] = tmp;
                ++swapped;
                //@ assert Swap{second, Here}(arr, n, i, i+1);
            }
            //@ assert \forall integer j; start - 1 <= j <= n - 1 ==> arr[start - 1] <= arr[j];
        }
        --end;
        //@ assert swapped == 0 ==> Sorted(arr, n);
    }
}
