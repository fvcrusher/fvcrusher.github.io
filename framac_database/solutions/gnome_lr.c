/*@ predicate Sorted{L}(int *arr, integer begin, integer end) =
    \forall integer i;
	begin <= i < end - 1 ==> arr[i] <= arr[i + 1];
*/

/*@ predicate Swap{L1, L2}(int *arr, integer n, integer i, integer j) =
  	0 <= i < n && 0 <= j < n &&
	\at(arr[i], L1) == \at(arr[j], L2) &&
	\at(arr[j], L1) == \at(arr[i], L2) &&
	\forall integer k; (0 <= k < n && k != i && k != j) ==> \at(arr[k], L1) == \at(arr[k], L2);
*/

/*@ inductive Permuted{L1,L2}(int *arr, integer l, integer r) {
    case Permuted_refl{L}:
        \forall int *arr, integer l, r;
            Permuted{L,L}(arr, l, r);

    case Permuted_sym{L1,L2}:
        \forall int *arr, integer l, r;
            Permuted{L1,L2}(arr, l, r)
                ==> Permuted{L2,L1}(arr, l, r);

    case Permuted_trans{L1,L2,L3}:
        \forall int *arr, integer l, r;
            Permuted{L1,L2}(arr, l, r) && Permuted{L2,L3}(arr, l, r)
                ==> Permuted{L1,L3}(arr, l, r);

    case Permuted_swap{L1,L2}:
        \forall int *arr, integer n, l, r, i, j;
            l <= i <= r &&
            l <= j <= r &&
            Swap{L1,L2}(arr, n, i, j)
                ==> Permuted{L1,L2}(arr, l, r);
    }
*/

/*@
logic integer inversions_for_one_elem{L}(int* arr, integer n, integer i, integer j) =
	(n < 2 || i < 0 || i > n - 1 || i > j || j > n - 1) ? 0
	    : (\at(arr[i], L) > \at(arr[j], L) ? 1 : 0) + inversions_for_one_elem{L}(arr, n, i, j + 1);
*/

/*@ ghost
/@ lemma
 requires \valid(arr+(0..(n-1)));
 requires n >= 2;
 requires 0 <= i <= j <= n;
 decreases n - j;

 ensures inversions_for_one_elem(arr, n, i, j) >= 0; @/

void inversions_for_one_elem_nonneg(int *arr, int n, int i, int j) {
    if (j <= n - 1) {
    	inversions_for_one_elem_nonneg(arr, n, i, j + 1);
    }
}
*/

/*@
axiomatic Inversions{
logic integer inversions{L}(int* arr, integer n, integer i) =
	(n < 2 || i < 0 || i > n - 1) ? 0
		: inversions_for_one_elem{L}(arr, n, i, i + 1) + inversions{L}(arr, n, i + 1);

axiom inversions_axiom{L1, L2}:
    \forall int *a, integer n, k;
        (\valid{L1}(a + (0..(n - 1))) &&
        \valid{L2}(a + (0..(n - 1))) && 
        0 <= k < n - 1 && 
        \at(a[k], L1) > \at(a[k + 1], L1) &&
        \at(a[k], L2) <= \at(a[k + 1], L2) &&
        Swap{L1, L2}(a, n, k, k + 1))
            ==> inversions{L1}(a, n, 0) > inversions{L2}(a, n, 0);
}
*/

/*@ ghost
/@ lemma
 requires \valid(arr+(0..(n-1)));
 requires n >= 2;
 requires 0 <= i <= n;
 decreases n - i;

 ensures inversions(arr, n, i) >= 0; @/

void inversions_nonneg(int *arr, int n, int i) {
    if (i <= n - 1) {
    	inversions_nonneg(arr, n, i + 1);
    }
}
*/

/*@ requires n >= 2;
    requires \valid(arr + (0..n-1));

    ensures Permuted{Pre, Post}(arr, 0, n - 1);
    ensures Sorted{Post}(arr, 0, n);
*/

void gnome_lr(int *arr, int n) {
    int tmp, idx = 0;
    //@ ghost start : ;

/*@ 
    loop invariant 0 <= idx <= n;
    loop invariant Permuted{Pre, Here}(arr, 0, n - 1);
    loop invariant Sorted(arr, 0, idx);
    loop invariant inversions(arr, n, 0) >= 0;
    loop invariant \valid(arr+(0..n-1));
    //loop invariant n == \at(n, start);

    loop variant 2 * inversions(arr, n, 0) + n - idx;
*/
    while (idx < n) {
        //@ ghost int elems_swapped = 0;
        if (idx == 0) {
            idx++;
            //@ assert \at(idx, LoopCurrent) < idx;
            //@ assert inversions{LoopCurrent}(arr, n, 0) == inversions(arr, n, 0);
            //@ assert inversions{LoopCurrent}(arr, n, 0) + n - \at(idx, LoopCurrent) > inversions(arr, n, 0) + n - idx;
            //@ assert Permuted{Pre, Here}(arr, 0, n - 1);
        }
        if (arr[idx] >= arr[idx - 1]) {
            idx++;
            //@ assert \at(idx, LoopCurrent) < idx;
            //@ assert inversions{LoopCurrent}(arr, n, 0) == inversions(arr, n, 0);
            //@ assert 2 * inversions{LoopCurrent}(arr, n, 0) + n - \at(idx, LoopCurrent) > 2 * inversions(arr, n, 0) + n - idx;
            //@ assert Permuted{Pre, Here}(arr, 0, n - 1);
        } else {
            //@ ghost int q = idx - 1;
            //@ ghost label: ;
            tmp = arr[idx];
            arr[idx] = arr[idx - 1];
            arr[idx - 1] = tmp;
            //@ ghost elems_swapped = 1;

            //@ assert Swap{LoopCurrent, Here}(arr, n, idx - 1, idx);
            //@ assert Permuted{Pre, Here}(arr, 0, n - 1);
            //@ assert \valid(arr+(0..(n-1)));
            
            //@ assert \at(arr[idx], label) < \at(arr[idx - 1], label) && arr[idx] >= arr[idx - 1] && Swap{label, Here}(arr, n, idx - 1, idx);
            //@ ghost q = idx - 1;
            //@ assert \at(arr[q + 1], label) < \at(arr[q], label) && arr[q + 1] >= arr[q] && Swap{label, Here}(arr, n, q, q + 1);
            
            // assert \exists integer k; (k == idx - 1 && \at(arr[k + 1], label) < \at(arr[k], label) && arr[k + 1] >= arr[k] && Swap{label, Here}(arr, n, k, idx));
            // assert inversions{label}(arr, idx - 1, 0) > inversions(arr, idx - 1, 0);
            //@ assert inversions{label}(arr, n, 0) > inversions(arr, n, 0);

            //@ assert 2 * inversions{LoopCurrent}(arr, n, 0) + n - \at(idx, LoopCurrent) > 2 * inversions(arr, n, 0) + n - idx;

            //@ assert Swap{LoopCurrent, Here}(arr, n, idx - 1, idx);
            //@ assert Permuted{Pre, Here}(arr, 0, n - 1);

            idx--;
            //@ assert 2 * inversions{LoopCurrent}(arr, n, 0) + n - \at(idx, LoopCurrent) > 2 * inversions(arr, n, 0) + n - idx;
            //@ assert Swap{LoopCurrent, Here}(arr, n, idx, idx + 1);
            //@ assert Permuted{Pre, Here}(arr, 0, n - 1);
        }

    //@ assert 2 * inversions{LoopCurrent}(arr, n, 0) + n - \at(idx, LoopCurrent) > 2 * inversions(arr, n, 0) + n - idx;
    //@ assert elems_swapped == 1 ==> Swap{LoopCurrent, Here}(arr, n, idx, idx + 1);
    //@ assert Permuted{Pre, Here}(arr, 0, n - 1);
    }
    return;
}

