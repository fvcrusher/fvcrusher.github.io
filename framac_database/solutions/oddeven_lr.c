// 13 
// #include <limits.h>

/*@
predicate sorted{L}(int* arr, integer start, integer end) = 
	\forall integer i; start <= i < end ==> \at(arr[i], L) <= \at(arr[i + 1], L);
*/

/*@
predicate sorted_loop{L}(int* arr, integer start, integer end) = 
  \forall integer i; (start <= i < end ==> \forall integer j; i < j < end ==> \at(arr[i], L) <= \at(arr[j], L));
*/

/*@
lemma sorted_equiv{L}:
  \forall int* arr, integer start, integer end;
    sorted(arr, start, end - 1) ==> sorted_loop(arr, start, end);
*/

/*@
predicate odd_sorted(int* arr, integer n) = 
	\forall integer i; (0 <= i < n - 1 && i%2 == 1) ==> arr[i] <= arr[i + 1]; */

/*@
predicate even_sorted(int* arr, integer n) = 
	\forall integer i; (0 <= i < n - 1 && i%2 == 0) ==> arr[i] <= arr[i + 1]; */
// */

/*@
predicate swapped{L1, L2}(int *arr, integer n, integer i, integer j) =
	0 <= i < n && 0 <= j < n &&
	\at(arr[i], L1) == \at(arr[j], L2) &&
	\at(arr[j], L1) == \at(arr[i], L2) &&
	(\forall integer k; (0 <= k < n && k != i && k != j)
		==> \at(arr[k], L1) == \at(arr[k], L2));*/
// */

/*@
axiomatic Permutations_Count {
	logic integer permutations_count{L}(int *a, integer n);

	// If array is sorted, then there is no i : a[i] > a[i + 1], then permutations_count = 0
	axiom permutations_count_sorted{L}:
		\forall int *a, integer n; sorted(a, 0, n - 1) ==> permutations_count{L}(a, n) == 0;
		
	// If array is not sorted, then there is at least one i : a[i] > a[i + 1], then permutations_count >= 1;
	axiom permutations_count_not_sorted{L}:
		\forall int *a, integer n; !sorted(a, 0, n - 1) ==> permutations_count{L}(a, n) > 0;
		
	// If we swapped two sequential members of array correctly, there are less i: a[i] > a[i + 1], so permutations count decreases.
	axiom permutations_count_right_swap{L1,L2}:
		\forall int *a, integer i, n;
		swapped{L1, L2}(a, n, i, i + 1) &&
		\at(a[i], L1) > \at(a[i + 1], L1) &&
		\at(a[i], L2) <= \at(a[i + 1], L2)
		 ==> permutations_count{L1}(a, n) > permutations_count{L2}(a, n);
}*/
// */

/*@ 
inductive Permuted{L1,L2}(int *arr, integer l, integer r) {
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
            swapped{L1,L2}(arr, n, i, j)
                ==> Permuted{L1,L2}(arr, l, r);
}*/
// */

/*
inductive swapp{L}(int* arr, integer start, end) 
*/


/*@
predicate swapped_2(int* arr1, int* arr2, integer n, integer i, integer j) = 
	0 <= i < n && 0 <= j < n &&
	arr1[i] == arr2[j] &&
	arr1[j] == arr2[i] &&
	(\forall integer k; (0 <= k < n && k != i && k != j) 
		==> arr1[k] == arr2[k]);*/
// */

// ---------------------------------------------------------------------------- //

/*@ axiomatic count_one_cmp_axiomatic {


logic integer count_one{L}(int* arr, integer n, integer i, integer i_0, integer j, integer j_0) =
	(2 > n || 0 > i || i > n - 1 || i > j || ((0 > i_0 || i_0 > n - 1 || j_0 != i_0 + 1) && i_0 != -1 && j_0 != -1) || j > n - 1) ? 0
	    : (\at(arr[i], L) > \at(arr[j], L) ? 1 : 0) + count_one{L}(arr, n, i, i_0, j + 1, j_0);


axiom count_one_cmp_axiom{L}:
    \forall int *a1, int *a2, integer n, i, i_0, j, j_0;
       (\valid(a1+(0..(n-1))) &&
        \valid(a2+(0..(n-1))) &&
        a1[i_0] > a1[j_0] && a2[i_0] <= a2[j_0] && swapped_2(a1, a2, n, i_0, j_0) &&
        0 <= i_0 && 0 <= j_0 &&
        0 <= i <= j <= n &&
        i == i_0 &&
        j_0 == i_0 + 1 <= n - 1
            ==> (j <= j_0 ==> count_one{L}(a1, n, i, i_0, j, j_0) > count_one{L}(a2, n, i, i_0, j, j_0))
             && (j > j_0 ==> count_one{L}(a1, n, i, i_0, j, j_0) == count_one{L}(a2, n, i, i_0, j, j_0)));

axiom count_one_not_cmp_axiom{L}:
    \forall int *a1, int *a2, integer n, i, i_0, j, j_0;
       (\valid(a1+(0..(n-1))) &&
        \valid(a2+(0..(n-1))) &&
        a1[i_0] > a1[j_0] && a2[i_0] <= a2[j_0] && swapped_2(a1, a2, n, i_0, j_0) &&
        0 <= i_0 && 0 <= j_0 &&
        0 <= i <= j <= n &&
        i != i_0 &&
        j_0 == i_0 + 1 <= n - 1
            ==> ((j != j_0 ==> count_one(a1, n, i, i_0, j, j_0) == count_one(a2, n, i, i_0, j, j_0))
             &&  (j == j_0 ==> count_one(a1, n, i, i_0, j, j_0) != count_one(a2, n, i, i_0, j, j_0) || count_one(a1, n, i, i_0, j, j_0) == count_one(a2, n, i, i_0, j, j_0))));

}
*/


/*@ ghost
/@ lemma
 requires \valid(arr+(0..(n-1)));
 requires n >= 2;
 decreases n - j;

 ensures count_one(arr, n, i, -1, j, -1) >= 0; @/

void count_one_nonneg(int *arr, int n, int i, int j) {
    if (j <= n - 1) {
    	count_one_nonneg(arr, n, i, j + 1);
    }
}*/

/*@ ghost
/@ lemma
 requires \valid(arr+(0..(n-1)));
 requires (j_0 == i_0 + 1 && 0 <= i_0 <= n - 1) || (j_0 == -1 && i_0 == - 1);
 requires n >= 2;
 decreases n - j;

 ensures count_one(arr, n, i, i_0, j, j_0) == count_one(arr, n, i, -1, j, -1); @/

void count_one_minus_one(int *arr, int n, int i, int i_0, int j, int j_0) {
    if (j <= n - 1) {
    	count_one_minus_one(arr, n, i, i_0, j + 1, j_0);
    }
}
*/


/*@ ghost
/@ lemma
 requires \valid(a1+(0..(n-1)));
 requires \valid(a2+(0..(n-1)));
 requires a1[i_0] > a1[j_0] && a2[i_0] <= a2[j_0] && swapped_2(a1, a2, n, i_0, j_0);
 requires 0 <= i_0 && 0 <= j_0;
 requires 0 <= i <= j <= n;
 requires i == i_0;
 requires j_0 == i_0 + 1 <= n - 1;
 decreases n - j;
 
 ensures j <= j_0 ==> count_one(a1, n, i, i_0, j, j_0) > count_one(a2, n, i, i_0, j, j_0);
 ensures j > j_0 ==> count_one(a1, n, i, i_0, j, j_0) == count_one(a2, n, i, i_0, j, j_0);
@/

void count_one_cmp(int *a1, int *a2, int n, int i, int i_0,  int j, int j_0) {
    if (2 <= n && 0 <= i && i <= n - 1 && i <= j && ((0 <= i_0 && i_0 <= n - 1 && j_0 == i_0 + 1) || i_0 == -1 || j_0 == -1) && j <= n - 1) {
    	count_one_cmp(a1, a2, n, i, i_0, j + 1, j_0);
    }
}*/
// */

/*@ ghost
/@ lemma
 requires \valid(a1+(0..(n-1)));
 requires \valid(a2+(0..(n-1)));
 requires a1[i_0] > a1[j_0] && a2[i_0] <= a2[j_0] && swapped_2(a1, a2, n, i_0, j_0);
 requires 0 <= i_0 && 0 <= j_0;
 requires 0 <= i <= j <= n;
 requires i <= n - 1;
 requires j_0 == i_0 + 1 <= n - 1;
 requires i != i_0;
 decreases n - j;
 
 ensures j != j_0 ==> count_one(a1, n, i, i_0, j, j_0) == count_one(a2, n, i, i_0, j, j_0);
 ensures j == j_0 ==> (count_one(a1, n, i, i_0, j, j_0) != count_one(a2, n, i, i_0, j, j_0) || count_one(a1, n, i, i_0, j, j_0) == count_one(a2, n, i, i_0, j, j_0));
@/

void count_one_cmp_not(int *a1, int *a2, int n, int i, int i_0,  int j, int j_0) {
    if (2 <= n && 0 <= i && i <= n - 1 && i <= j && ((0 <= i_0 && i_0 <= n - 1 && j_0 == i_0 + 1) || i_0 == -1 || j_0 == -1) && j <= n - 1) {
    	count_one_cmp_not(a1, a2, n, i, i_0, j + 1, j_0);
    }
}*/
// */

/*@ ghost
/@ lemma
 requires \valid(a1+(0..(n-1)));
 requires \valid(a2+(0..(n-1)));
 
 requires \forall integer k; 0 <= k <= n - 1 ==> a1[k] == a2[k];
 requires n >= 2;
 decreases n - j;
 
 ensures count_one(a1, n, i, -1, j, -1) == count_one(a2, n, i, -1, j, -1); @/

void count_one_same(int *a1, int *a2, int n, int i, int j) {
    if (j <= n - 1) {
    	count_one_same(a1, a2, n, i, j + 1);
    }
}*/
// */


/* ghost
/@ lemma
 requires \valid(arr+(0..(n-1)));
 requires n >= 2;
 requires 0 <= i <= n - 1;
 requires i <= j <= n;
 requires \forall integer k; (j <= k <= n - 1 ==> arr[i] <= arr[k]);
 requires sorted(arr, n, i);
 requires i_0 == -1 && j_0 == -1;
 decreases n - j;

 ensures count_one(arr, n, i, i_0, j, j_0) == 0; @/

void sorted_count_one_minus(int *arr, int n, int i, int i_0, int j, int j_0) {
    if (2 <= n && 0 <= i && i <= n - 1 && i <= j && ((0 <= i_0 && i_0 <= n - 1 && j_0 == i_0 + 1) || i_0 == -1 || j_0 == -1) && j <= n - 1) {
      sorted_count_one_minus(arr, n, i, i_0, j + 1, j_0);
    }
}
*/


/*@ ghost
/@ lemma
 requires \valid(arr+(0..(n-1)));
 requires n >= 2;
 requires 0 <= i <= n - 1;
 requires i <= j <= n;
 requires \forall integer k; j <= k <= n - 1 ==> arr[i] <= arr[k];
 decreases n - j;

 ensures count_one(arr, n, i, -1, j, -1) == 0; @/

void sorted_count_one_minus(int *arr, int n, int i, int j) {
    if (j <= n - 1) {
      sorted_count_one_minus(arr, n, i, j + 1);
    }
}
*/


// ======================================================================= //

/*@
logic integer count{L}(int* arr, integer n, integer i, integer i_0, integer j_0) =
	(n < 2 || 0 > i || ((0 > i_0 || i_0 > n - 1 || j_0 != i_0 + 1) && i_0 != -1 && j_0 != -1) || i > n - 1) ? 0
		: count_one{L}(arr, n, i, i_0, i + 1, j_0) + count{L}(arr, n, i + 1, i_0, j_0);*/
// */

/*@ ghost
/@ lemma
 requires \valid(arr+(0..(n-1)));
 requires n >= 2;
 decreases n - i;

 ensures count(arr, n, i, -1, -1) >= 0; @/

void count_nonneg(int *arr, int n, int i) {
    if (i <= n - 1) {
    	count_nonneg(arr, n, i + 1);
    }
}*/
// */

/*@ ghost
/@ lemma
 requires \valid(arr+(0..(n-1)));
 requires (j_0 == i_0 + 1 && 0 <= i_0 <= n - 1) || (j_0 == -1 && i_0 == - 1);
 requires n >= 2;
 decreases n - i;

 ensures count(arr, n, i, i_0, j_0) == count(arr, n, i, -1, -1); @/

void count_minus_one(int *arr, int n, int i, int i_0, int j_0) {
    if (i <= n - 1) {
    	count_minus_one(arr, n, i + 1, i_0, j_0);
    }
}
*/



/*@ ghost
/@ lemma
 requires \valid(a1+(0..(n-1)));
 requires \valid(a2+(0..(n-1)));
 //requires 0 <= i <= i_0 < j_0 <= n - 1;
 requires a1[i_0] > a1[j_0] && a2[i_0] <= a2[j_0] && swapped_2(a1, a2, n, i_0, j_0);
 requires 0 <= i_0 && 0 <= j_0;
 requires 0 <= i <= n;
 requires 0 <= i_0 <= n - 1;
 requires j_0 == i_0 + 1 <= n - 1;
 decreases n - i;
 
 ensures i <= i_0 ==> count(a1, n, i, i_0, j_0) > count(a2, n, i, i_0, j_0);
 ensures i > i_0 ==> count(a1, n, i, i_0, j_0) == count(a2, n, i, i_0, j_0);

@/

void count_cmp(int *a1, int *a2, int n, int i, int i_0, int j_0) {
    if (2 <= n && 0 <= i && ((0 <= i_0 && i_0 <= n - 1 && j_0 == i_0 + 1) || i_0 == -1 || j_0 == -1) && i <= n - 1) {
    	count_cmp(a1, a2, n, i + 1, i_0, j_0);
    }
}*/
// */


/*@ ghost
/@ lemma
 requires \valid(a1+(0..(n-1)));
 requires \valid(a2+(0..(n-1)));
 requires \forall integer k; 0 <= k <= n - 1 ==> a1[k] == a2[k];
 requires n >= 2;
 decreases n - i;
 
 ensures count(a1, n, i, -1, -1) == count(a2, n, i, -1, -1); @/

void count_same(int *a1, int *a2, int n, int i) {
    if (i <= n - 1) {
    	count_same(a1, a2, n, i + 1);
    }
}*/
// */

/*@ ghost
/@ lemma
 requires \valid(arr+(0..(n-1)));
 requires n >= 2;
 requires j_0 == -1 || 0 <= j_0 <= n - 1;
 requires i_0 == -1 || 0 <= i_0 < i_0 + 1 <= n - 1;
 requires count(arr, n, 0, i_0, j_0) == 0;
 decreases n - i;
 
 ensures sorted(arr, n, 0); @/

void count_sorted(int *arr, int n, int i, int i_0, int j_0) {
    if (2 <= n && 0 <= i && ((0 <= i_0 && i_0 <= n - 1 && j_0 == i_0 + 1) || i_0 == -1 || j_0 == -1) && i <= n - 1) {
    	count_sorted(arr, n, i + 1, i_0, j_0);
    }
}*/
// */


/*@ ghost
/@ lemma
 requires \valid(arr+(0..(n-1)));
 requires n >= 2;

 //requires \forall integer k; (0 <= k < n ==> \forall integer l; k < l < n ==> arr[k] <= arr[l]);
 requires sorted_loop(arr, 0, n);
 requires 0 <= i <= n;
 requires n >= 2;
 decreases n - i;

 ensures count(arr, n, i, -1, -1) == 0; @/

void sorted_count_minus(int *arr, int n, int i) {
    if (i <= n - 1) {
      sorted_count_minus(arr, n, i + 1);
    }
}*/

/*@ ghost
/@ lemma
 requires \valid(arr+(0..(n-1)));
 requires n >= 2;

 //requires \forall integer k; (0 <= k < n ==> \forall integer l; k < l < n ==> arr[k] <= arr[l]);
 requires sorted(arr, 0, n - 1);
 requires 0 <= i <= n;
 requires n >= 2;
 decreases n - i;

 ensures count(arr, n, i, -1, -1) == 0; @/

void sorted_count(int *arr, int n, int i) {
    if (i <= n - 1) {
      sorted_count(arr, n, i + 1);
    }
}*/



/*@
predicate same_array{L1, L2}(int* arr, integer start, integer end) = \forall integer k; start <= k <= end - 1 ==> \at(arr[k], L1) == \at(arr[k], L2);*/
// */

/*@
predicate same_arrays(int* arr1, int* arr2, integer start, integer end) = \forall integer k; start <= k <= end - 1 ==> arr1[k] == arr2[k];*/
// */

/*@
	requires n >= 2;
	requires \valid(arr + (0..n-1));
	requires \forall integer i; 0 <= i <= n ==> (-0x7fffffff - 1) <= arr[i] <= 0x7fffffff;
	
	ensures n == \old(n);
	ensures Permuted{Pre, Post}(arr, 0, n - 1);
	ensures sorted(arr, 0, n - 1);	*/
// */
void oddeven_lr(int *arr, int n) {
    int i, tmp, cnt = 1;
    
    /*@
    	loop invariant Permuted{LoopEntry, Here}(arr, 0, n - 1);
    	loop invariant cnt == 0 ==> sorted(arr, 0, n - 1);
    	loop invariant 0 <= cnt;
    	loop invariant n == \at(n, LoopEntry);
    	loop invariant count(arr, n, 0, -1, -1) + (cnt > 0 ? 1 : 0) >= 0;
    	
    	loop variant count(arr, n, 0, -1, -1) + (cnt > 0 ? 1 : 0);
    */
    while (cnt > 0) {
        cnt = 0;
        //@ ghost int cnt_1 = 0;
        //@ ghost int cnt_2 = 0;
        
        //@ assert cnt == cnt_1 + cnt_2;
        //@ assert cnt == cnt_1;
	/*@
		loop invariant n == 0 ? i == 1 : 1 <= i <= n;
		loop invariant i%2 == 1;
		loop invariant n == 0 ? cnt == 0 : 0 <= cnt <= (i + 1) / 2;
	   	
		loop invariant Permuted{LoopEntry, Here}(arr, 0, n - 1);
		loop invariant odd_sorted(arr, i);
		
		loop invariant cnt_1 == 0 ==> same_array{Here, LoopEntry}(arr, 0, n);
		//loop invariant cnt > 0 ==> count(arr, n, 0, -1, -1) < count{LoopEntry}(arr, n, 0, -1, -1);
		loop invariant cnt == cnt_1 + cnt_2;
		loop invariant cnt_2 == 0;
		
		loop invariant cnt_1 > 0 ==> count(arr, n, 0, -1, -1) < count{LoopEntry}(arr, n, 0, -1, -1);
    loop invariant count{LoopCurrent}(arr, n, 0, -1, -1) <= count{LoopEntry}(arr, n, 0, -1, -1);
		
		loop variant n - i;	
	*/
        for (i = 1; i <= n - 2; i = i + 2) {

            if (arr[i] > arr[i + 1]) {
//             
            	/*@ ghost before_swap1: ;*/
            	tmp = arr[i];
                arr[i] = arr[i + 1];
                arr[i + 1] = tmp;
                
                /*@ assert swapped{before_swap1, Here}(arr, n, i, i + 1);*/
                /*@ assert \at(arr[i], LoopCurrent) > \at(arr[i + 1], LoopCurrent);*/
                /*@ assert arr[i] <= arr[i + 1];*/
                /*@ assert count{Here}(arr, n, 0, i, i + 1) < count{LoopCurrent}(arr, n, 0, i, i + 1);*/
                //@ assert count{LoopCurrent}(arr, n, 0, -1, -1) <= count{LoopEntry}(arr, n, 0, -1, -1);
                /*@ assert count{Here}(arr, n, 0, i, i + 1) < count{LoopEntry}(arr, n, 0, i, i + 1);*/

                ++cnt;
                //@ ghost cnt_1++;
                //@ assert cnt_2 == 0;
                //@ assert cnt == cnt_1 + cnt_2;
                //@ assert cnt == cnt_1;
//                 
                /* assert swapped{before_swap1, Here}(arr, n, i, i + 1);*/
                /* assert \at(arr[i], LoopCurrent) > \at(arr[i + 1], LoopCurrent);*/
                /* assert arr[i] <= arr[i + 1];*/
                /* assert count{Here}(arr, n, 0, i, i + 1) < count{LoopCurrent}(arr, n, 0, i, i + 1);*/
                /* assert count{Here}(arr, n, 0, i, i + 1) < count{LoopEntry}(arr, n, 0, i, i + 1);*/
                // assert cnt > 0 ==> count(arr, n, 0, -1, -1) < count{LoopEntry}(arr, n, 0, -1, -1);
                //@ assert cnt_1 > 0 ==> count(arr, n, 0, -1, -1) < count{LoopEntry}(arr, n, 0, -1, -1);
                /*@ assert Permuted{LoopCurrent, Here}(arr, 0, n - 1);*/

				        /*@ assert odd_sorted(arr, i);*/
                /*@ assert sorted(arr, i, i + 1);*/

                /*@ assert 0 <= cnt <= (i + 1) / 2 + 1;*/
                /*@ assert cnt > 0;*/

            }
            
            //@ assert cnt == cnt_1 + cnt_2;
            //@ assert cnt_2 == 0;
            //@ assert cnt == cnt_1;
            /*@ assert Permuted{LoopCurrent, Here}(arr, 0, n - 1);*/
            /*@ assert odd_sorted(arr, i);*/
            /*@ assert sorted(arr, i, i + 1);*/
            // assert cnt > 0 ==> count(arr, n, 0, -1, -1) < count{LoopEntry}(arr, n, 0, -1, -1);
            //@ assert cnt_1 > 0 ==> count(arr, n, 0, -1, -1) < count{LoopEntry}(arr, n, 0, -1, -1);
        }  
        //@ assert cnt == cnt_1;
        /*@ assert 0 <= cnt <= (n + 1) / 2;*/
        /*@ assert Permuted{LoopCurrent, Here}(arr, 0, n - 1);*/
        /*@ assert odd_sorted(arr, n);*/
//         
        /*@ assert cnt_1 == 0 ==> same_array{Here, LoopCurrent}(arr, 0, n);*/
        //@ assert cnt > 0 ==> count(arr, n, 0, -1, -1) < count{LoopCurrent}(arr, n, 0, -1, -1);
        //@ assert cnt_1 > 0 ==> count(arr, n, 0, -1, -1) < count{LoopCurrent}(arr, n, 0, -1, -1);
        //@ assert cnt_2 == 0;
        // assert count{Here}(arr, n, 0, -1, -1) == count{Here}(arr, n, 0, -1, -1);
        //i = 0;
        //@ ghost between: ;
        /*@		
		    loop invariant 0 <= i <= n;
		    loop invariant i % 2 == 0;
		    loop invariant 0 <= cnt <= (n + 1) / 2 + (i + 1) / 2;

	       	
		    loop invariant Permuted{LoopEntry, Here}(arr, 0, n - 1);
		    loop invariant cnt == 0 ==> odd_sorted(arr, n);
		    loop invariant even_sorted(arr, i);
		    
		    loop invariant cnt_2 >= 0;
		    loop invariant cnt_2 == 0 ==> same_array{Here, LoopEntry}(arr, 0, n);
		    loop invariant cnt == cnt_1 + cnt_2;
		    loop invariant cnt_2 > 0 ==> count(arr, n, 0, -1, -1) < count{LoopEntry}(arr, n, 0, -1, -1);
		    loop invariant i == \at(i, LoopEntry) ==> \forall integer k; 0 <= k < n ==> \at(arr[k], Here) == \at(arr[k], LoopEntry);
		    loop invariant i == 0 ==> count{LoopEntry}(arr, n, 0, -1, -1) == count{Here}(arr, n, 0, -1, -1);
		    loop invariant count{Here}(arr, n, 0, -1, -1) <= count{LoopEntry}(arr, n, 0, -1, -1);
		    
		    loop variant n - i;
        */
//         
        for (i = 0; i <= n - 2; i = i + 2) {
            //@ assert i == 0 ==> \forall integer k; 0 <= k < n ==> \at(arr[k], Here) == \at(arr[k], LoopCurrent);
            //@ assert cnt_2 == 0 ==> same_array{Here, LoopEntry}(arr, 0, n);
            if (arr[i] > arr[i + 1]) {
            	/*@ ghost before_swap2: ;*/
                tmp = arr[i];
                arr[i] = arr[i + 1];
                arr[i + 1] = tmp;

                /*@ assert swapped{before_swap2, Here}(arr, n, i, i + 1);*/
                /*@ assert \at(arr[i], LoopCurrent) > \at(arr[i + 1], LoopCurrent);*/
                /*@ assert arr[i] <= arr[i + 1];*/
                /*@ assert count{Here}(arr, n, 0, i, i + 1) < count{LoopCurrent}(arr, n, 0, i, i + 1);*/
                //@ assert count{LoopCurrent}(arr, n, 0, -1, -1) <= count{LoopEntry}(arr, n, 0, -1, -1);
                /*@ assert count{Here}(arr, n, 0, i, i + 1) < count{LoopEntry}(arr, n, 0, i, i + 1);*/
                
                ++cnt;
                //@ ghost cnt_2++;
                //@ assert cnt_2 != 0;
                //@ assert cnt == cnt_1 + cnt_2;
                /*@ assert 0 < cnt <= n;*/
                
                /* assert swapped{before_swap2, Here}(arr, n, i, i + 1);*/
                /* assert \at(arr[i], LoopCurrent) > \at(arr[i + 1], LoopCurrent);*/
                /* assert arr[i] <= arr[i + 1];*/
                /* assert count{Here}(arr, n, 0, i, i + 1) < count{LoopCurrent}(arr, n, 0, i, i + 1);*/
                /* assert count{Here}(arr, n, 0, i, i + 1) < count{LoopEntry}(arr, n, 0, i, i + 1);*/
                //@ assert cnt_2 > 0 ==> count(arr, n, 0, -1, -1) < count{LoopEntry}(arr, n, 0, -1, -1);
                
                //@ assert arr[i] <= arr[i + 1];
                /*@ assert \at(arr[i], before_swap2) > \at(arr[i + 1], before_swap2);*/
                /*@ assert count{Here}(arr, n, 0, i, i + 1) < count{LoopCurrent}(arr, n, 0, i, i + 1);*/
                
                /*@ assert swapped{before_swap2, Here}(arr, n, i, i + 1);*/
                /*@ assert Permuted{LoopCurrent, Here}(arr, 0, n - 1);*/
                /*@ assert even_sorted(arr, i);*/
                /*@ assert sorted(arr, i, i + 1);*/
                //@ assert cnt_2 != 0;

            }
            //@ assert cnt_2 == 0 ==> same_array{Here, LoopEntry}(arr, 0, n);
            /*@ assert Permuted{LoopCurrent, Here}(arr, 0, n - 1);*/
            /*@ assert even_sorted(arr, i);*/
            /*@ assert sorted(arr, i, i + 1);*/
            /*@ assert cnt == 0 ==> odd_sorted(arr, n);*/
            //@ assert cnt == cnt_1 + cnt_2;
            //@ assert cnt_2 > 0 ==> count(arr, n, 0, -1, -1) < count{LoopEntry}(arr, n, 0, -1, -1);
            
            //@ assert cnt_2 == 0 ==> count{LoopCurrent}(arr, n, 0, -1, -1) == count{LoopEntry}(arr, n, 0, -1, -1);
            
        }
//      
        //@ assert cnt == cnt_1 + cnt_2;
        /*@ assert 0 <= cnt <= n;*/
// 		
        /*@ assert Permuted{LoopCurrent, Here}(arr, 0, n - 1);*/
        /*@ assert even_sorted(arr, n);*/
        /*@ assert cnt == 0 ==> (odd_sorted(arr, n) && even_sorted(arr, n));*/
        /*@ assert cnt == 0 ==> sorted(arr, 0, n - 1);*/
        
        // assert cnt == 0 ==> sorted_loop(arr, 0, n - 1);
        // assert sorted_loop(arr, 0, n - 1) ==> count(arr, n, 0, -1, -1) == 0;
        /* assert (cnt_1 == 0 && cnt_2 == 0 && sorted_loop(arr, 0, n - 1))==> count(arr, n, 0, -1, -1) == 0;*/
        //@ assert sorted(arr, 0, n - 1) ==> count(arr, n, 0, -1, -1) == 0;
        /*@ assert cnt == 0 ==> count(arr, n, 0, -1, -1) == 0;*/
        
        /*@ assert cnt_1 == 0 && cnt_2 == 0 ==> same_array{Here, LoopCurrent}(arr, 0, n);*/
        
        /*@ assert cnt == 0 ==> same_array{Here, LoopCurrent}(arr, 0, n);*/
        /*@ assert cnt == 0 ==> count(arr, n, 0, -1, -1) == count{LoopCurrent}(arr, n, 0, -1, -1);*/

        /*@ assert cnt == 0 ==> (cnt > 0 ? 1 : 0) < (\at(cnt, LoopCurrent) > 0 ? 1 : 0);*/
        /*@ assert cnt > 0 ==> (cnt > 0 ? 1 : 0) == (\at(cnt, LoopCurrent) > 0 ? 1 : 0);*/

        /*@ assert cnt > 0 ==> count(arr, n, 0, -1, -1) < count{LoopCurrent}(arr, n, 0, -1, -1);*/

        /*@ assert count(arr, n, 0, -1, -1) + (cnt > 0 ? 1 : 0) < count{LoopCurrent}(arr, n, 0, -1, -1) + (\at(cnt, LoopCurrent) > 0 ? 1 : 0);*/
    }
//     
    /*@ assert cnt == 0;*/

    // assert sorted(arr, 0, n - 1);
    // assert sorted(arr, 0, n - 1) ==> sorted_loop(arr, 0, n - 1);

    /*@ assert Permuted{Pre, Here}(arr, 0, n - 1);*/
    /*@ assert sorted(arr, 0, n - 1);*/
}
// 


