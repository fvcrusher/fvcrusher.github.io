// 1
/*@
    predicate SortedPart{L}(int *a, integer m, integer n) =
        \forall integer i; m <= i < n ==> a[i] <= a[i + 1];

    predicate Sorted{L}(int *a, integer n) =
        SortedPart{L}(a, 0, n - 1);

    predicate Unchanged{K,L}(int* a, integer m, integer n) =
        \forall integer i; m <= i < n ==> \at(a[i],K) == \at(a[i],L);

    predicate Swap{L1, L2}(int *a, integer n, integer i, integer j) =
        0 <= i < n && 0 <= j < n &&
        \at(a[i], L1) == \at(a[j], L2) &&
        \at(a[j], L1) == \at(a[i], L2) &&
        \forall integer k; 0 <= k < n && k != i && k != j ==> \at(a[k], L1) == \at(a[k], L2);

    inductive Permutation{L1, L2}(int *a, integer n) {
        case reflexive{L1}:
            \forall int *a, integer n; Permutation{L1, L1}(a, n);

        case transitive{L1, L2, L3}:
            \forall int *a, integer n; Permutation{L1, L2}(a, n) && Permutation{L2, L3}(a, n) ==>
                Permutation{L1, L3}(a, n);

        case swapStep{L1, L2}:
            \forall int *a, integer n, i, j; Swap{L1, L2}(a, n, i, j) ==> Permutation{L1, L2}(a, n);
    }
*/
/*@
    requires n > 0;
    requires \valid(arr + (0..n - 1));

    assigns arr[0..n-1];

    ensures \valid(arr + (0..n - 1));
    ensures Permutation{Pre, Post}(arr, n);
    ensures Sorted{Post}(arr, n);
*/
void cocktail_fwd(int *arr, int n) {
    int swapped = 1;
    int start = 0;
    int end = n - 1;

    /*@
        loop invariant 0 <= start;
        loop invariant end < n;

        loop invariant start > end ==> swapped == 0;

        loop invariant 0 <= swapped;

        loop invariant Permutation{Pre,Here}(arr, n);

        loop invariant swapped == 0 ==> SortedPart{Here}(arr, start, end);

        loop invariant SortedPart{Here}(arr, end, n - 1);
        loop invariant end < n - 1 ==> \forall integer k; start <= k <= end ==> arr[end + 1] >= arr[k];

        loop invariant SortedPart{Here}(arr, 0, start);
        loop invariant start > 0 ==> \forall integer k; start <= k <= end ==> arr[start - 1] <= arr[k];

        loop variant end - start + 1;
    */
    while (swapped > 0) {
        int i, tmp;

        Loop_1_Entry:
        ;
        swapped = 0;
        /*@
            loop invariant start <= i <= end;

            loop invariant start == end ==> swapped == 0;
            loop invariant 0 <= swapped <= i - start;

            loop invariant Permutation{Pre,Here}(arr, n);

            loop invariant swapped == 0 ==> SortedPart{Here}(arr, start, i);

            loop invariant SortedPart{Here}(arr, end + 1, n - 1);
            loop invariant end < n - 1 ==> \forall integer k; start <= k <= end ==> arr[end + 1] >= arr[k];

            loop invariant \forall integer k; start <= k <= i ==> arr[i] >= arr[k];

            loop invariant SortedPart{Here}(arr, 0, start);
            loop invariant start > 0 ==> \forall integer k; start <= k <= end ==> arr[start - 1] <= arr[k];

            loop invariant \forall integer k; i + 1 <= k < end ==> \at(arr[k], Loop_1_Entry) == arr[k];

            loop variant end - i;
        */
        for (i = start; i < end; ++i) {
            if (arr[i] > arr[i + 1]) {
                tmp = arr[i];
                arr[i] = arr[i + 1];
                arr[i + 1] = tmp;
                /*@
                    assert Swap{LoopCurrent,Here}(arr, n, i, i + 1);
                */
                /*@
                    assert Permutation{LoopCurrent,Here}(arr, n);
                */
                ++swapped;
            }
        }

        if (!swapped)
            break;

        --end;

        Loop_2_Entry:
        ;

        swapped = 0;
        /*@
            loop invariant start - 1 <= i <= end - 1;

            loop invariant start >= end ==> swapped == 0;
            loop invariant 0 <= swapped <= end - 1 - i;

            loop invariant Permutation{Pre,Here}(arr, n);

            loop invariant swapped == 0 ==> SortedPart{Here}(arr, i + 1, end);

            loop invariant SortedPart{Here}(arr, end + 1, n - 1);
            loop invariant end < n - 1 ==> \forall integer k; start <= k <= end ==> arr[end + 1] >= arr[k];

            loop invariant SortedPart{Here}(arr, 0, start);
            loop invariant start > 0 ==> \forall integer k; start <= k <= end ==> arr[start - 1] <= arr[k];

            loop invariant \forall integer k; i + 1 <= k <= end ==> arr[i + 1] <= arr[k];

            loop invariant \forall integer k; start <= k <= i ==> \at(arr[k], Loop_2_Entry) == arr[k];

            loop variant i - start + 1;
        */
        for (i = end - 1; i >= start; --i) {
            if (arr[i] > arr[i + 1]) {
                tmp = arr[i];
                arr[i] = arr[i + 1];
                arr[i + 1] = tmp;
                /*@
                    assert Swap{LoopCurrent,Here}(arr, n, i, i + 1);
                */
                /*@
                    assert Permutation{LoopCurrent,Here}(arr, n);
                */
                ++swapped;
            }

            /*@
                assert \forall integer k; i <= k <= end ==> arr[i] <= arr[k];
            */
        }

        ++start;
    }
}
