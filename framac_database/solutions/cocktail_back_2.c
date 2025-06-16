/*@ predicate swap_in_array{L1,L2}(int* a, integer b, integer e, integer i, integer j) =
        b <= i < e && b <= j < e &&
        \at(a[i], L1) == \at(a[j], L2) &&
        \at(a[j], L1) == \at(a[i], L2) &&
        \forall integer k; b <= k < e && k != j && k != i ==>
            \at(a[k], L1) == \at(a[k], L2);

    inductive permutation{L1,L2}(int* a, integer b, integer e){
    case reflexive{L1}:
        \forall int* a, integer b,e ; permutation{L1,L1}(a, b, e);
    case swap{L1,L2}:
        \forall int* a, integer b,e,i,j ;
            swap_in_array{L1,L2}(a,b,e,i,j) ==> permutation{L1,L2}(a, b, e);
    case transitive{L1,L2,L3}:
        \forall int* a, integer b,e ;
            permutation{L1,L2}(a, b, e) && permutation{L2,L3}(a, b, e) ==>
                permutation{L1,L3}(a, b, e);
    }
*/

/*@ predicate sorted(int *t, integer a, integer b) =
        \forall integer i, j; a <= i <= j <= b ==> t[i] <= t[j];
*/

/*@ requires \valid(arr + (0 .. n));
    requires n > 0;
    assigns arr[0 .. n];
    ensures sorted(arr, 0, n-1);
    ensures permutation{Pre, Post}(arr,0,n);
*/
void cocktail_back(int *arr, int n) {
    int swapped = 1;
    int start = 0;
    int end = n - 1;

    /*@ loop invariant 0 <= start <= end+1;
        loop invariant start-1 <= end <= n-1;
        loop invariant start > end ==> swapped == 0;
        loop invariant swapped == 0 ==> sorted(arr, 0, n-1);
        loop invariant \forall integer i, j;
            0 <= i <= start-1 && i <= j <= n-1 ==> arr[i] <= arr[j];
        loop invariant \forall integer i, j;
            end+1 <= i <= n-1 && 0 <= j <= i ==> arr[j] <= arr[i];
        loop invariant swapped >= 0;
        loop invariant permutation{Pre, Here}(arr,0,n);
        loop variant end - start + 1;
    */
    while (swapped > 0) {
        int i, tmp;

        //@ assert permutation{Pre, Here}(arr,0,n);

        swapped = 0;
        /*@ loop invariant start-1 <= i <= end-1;
            loop invariant 0 <= swapped <= end - i - 1;
            loop invariant \forall integer j; 
                i < j <= n-1 ==> arr[i + 1] <= arr[j];
            loop invariant \forall integer i, j;
                0 <= i <= start-1 && i <= j <= n-1 ==> arr[i] <= arr[j];
            loop invariant \forall integer i, j;
                end+1 <= i <= n-1 && 0 <= j <= i ==> arr[j] <= arr[i];
            loop invariant swapped == 0 ==> sorted(arr, i+1,n-1);
            loop invariant permutation{Pre, Here}(arr,0,n);
            loop variant i+1;
        */
        for (i = end - 1; i >= start; --i) {
            //@ ghost begin1: ;
            if (arr[i] > arr[i + 1]) {
                tmp = arr[i];
                arr[i] = arr[i + 1];
                arr[i + 1] = tmp;
                ++swapped;
                //@ assert swap_in_array{begin1,Here}(arr,0,n,i,i+1);
            }
        }

        /*@ assert \forall integer i, j; 
            0 <= i <= start && i <= j <= n-1 ==> arr[i] <= arr[j];
        */

        //@ assert swapped == 0 ==> sorted(arr, 0, n-1);

        if (!swapped)
            break;
        ++start;

        //@ assert sorted(arr, 0, start) && permutation{Pre, Here}(arr,0,n);

        swapped = 0;
        /*@ loop invariant start <= i <= end;
            loop invariant 0 <= swapped <= i - start;
            loop invariant \forall integer j; 
                0 <= j <= i ==> arr[j] <= arr[i];
            loop invariant \forall integer i, j;
                0 <= i <= start-1 && i <= j <= n-1 ==> arr[i] <= arr[j];
            loop invariant \forall integer i, j;
                end+1 <= i <= n-1 && 0 <= j <= i ==> arr[j] <= arr[i];
            loop invariant swapped == 0 ==> sorted(arr, 0, i);
            loop invariant permutation{Pre, Here}(arr,0,n);
            loop variant (end - i);
        */
        for (i = start; i < end; ++i) {
            //@ ghost begin2: ;
            if (arr[i] > arr[i + 1]) {
                tmp = arr[i];
                arr[i] = arr[i + 1];
                arr[i + 1] = tmp;
                ++swapped;
                //@ assert swap_in_array{begin2,Here}(arr,0,n,i,i+1);
            }
        /*@ assert \forall integer j; 
                start-1 <= j <= n-1 ==> arr[start-1] <= arr[j];
        */
        }
        --end;
        //@ assert swapped == 0 ==> sorted(arr, 0, n-1);
    }
}
