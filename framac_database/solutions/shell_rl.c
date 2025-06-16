#include <limits.h>

// 10
// Shell sort algorithm

/*@ axiomatic Permut {
  @ 
  @ predicate permut{L1, L2}(int *t1, int *t2, integer n);
  @
  @ axiom permut_refl{L}:
  @     \forall int *t, integer n; permut{L, L}(t, t, n);
  @ 
  @ axiom permut_sym{L1, L2} :
  @     \forall int *t1, *t2, integer n; permut{L1, L2}(t1, t2, n) ==> permut{L2, L1}(t2, t1, n);
  @ 
  @ axiom permut_trans{L1, L2, L3} :
  @     \forall int *t1, *t2, *t3, integer n; 
  @         permut{L1, L2}(t1, t2, n) && permut{L2, L3}(t2, t3, n) ==> permut{L1, L3}(t1, t3, n);
  @
  @ axiom permut_exchange{L1, L2, L3} :
  @     \forall int *t1, *t2, *t3, integer i, j, n, gap;
  @         0 <= i <= j < n && t1 == t2 && t2 == t3 &&
  @         k_shift{L1, L2}(t1, n, i, j, gap) &&
  @         \at(t1[j], L3) == \at(t1[i], L1) ==> permut{L1, L3}(t1, t2, n);
  @ }
  @*/
  
/*@ axiomatic K_shift {
  @ 
  @ predicate k_shift{L1, L2}(int *a, integer n, integer begin, integer end, integer gap);
  @
  @ axiom k_shift_base{L1}:
  @     \forall int *t1, integer i, n, gap;
  @         0 <= i < n && 0 <= gap < n && n > 0 ==> k_shift{L1, L1}(t1, n, i, i, gap);
  @
  @ axiom k_shift_recursive{L1, L2, L3}:
  @     \forall int *t1, integer i, j, n, gap;
  @         0 <= i < j + gap < n && 0 <= gap < n && n > 0 &&
  @         (\forall integer k; 0 <= k < n && k != j ==> \at(t1[k], L2) == \at(t1[k], L3)) &&
  @         \at(t1[j + gap], L2) == \at(t1[j], L3) && 
  @         k_shift{L1, L2}(t1, n, i, j, gap) 
  @             ==> k_shift{L1, L3}(t1, n, i, j + gap, gap);
  @ }
  @*/ 
  
/*@ logic integer get_max_index(integer begin, integer end, integer gap) = 
  @     begin % gap == end % gap ? end : get_max_index(begin, end - 1, gap);
  @*/
  
/*@ predicate sorted(int* arr, integer l, integer r) =
  @     \forall integer i; l <= i <= r - 1 ==> arr[i] <= arr[i + 1];
  @*/
  
/*@ predicate k_sorted(int* arr, integer l, integer r, integer k) =
  @     \forall integer i, j; l <= i < j <= r && i % l == j % l ==> arr[i] <= arr[j];
  @*/    

/*@ requires \valid(arr + (0..n-1));
  @ requires n > 0;
  @
  @ assigns arr[0..n-1];
  @
  @ ensures sorted(arr, 0, n - 1);
  @ ensures permut{Pre, Post}(arr, arr, n);
  @ ensures \valid(arr + (0..n-1));
  @*/
  void shell_rl(int *arr, int n) {
    int i, j, tmp, gap;      
    /*@ loop invariant 0 <= gap <= n / 2;
      @ loop invariant permut{Pre, Here}(arr, arr, n);
      @ loop invariant gap == 0 ==> sorted(arr, 0, n - 1);
      @ loop variant gap;
      @*/
    for (gap = n / 2; gap > 0; gap /= 2) {   
        /*@ loop invariant -1 <= i <= n - gap; 
          @ loop invariant permut{Pre, Here}(arr, arr, n);
          @ loop invariant gap == 1 ==> sorted(arr, i + 1, n - 1);
          @ loop variant i;
          @*/
        for (i = n - gap; i >= 0; --i) {
            tmp = arr[i];
            /*@
              @ loop invariant 0 <= j < n && i <= j;
              @ loop invariant k_shift{LoopEntry, Here}(arr, n, i, j, gap);
              @ loop invariant gap == 1 && j == i ==> sorted(arr, i + 1, n - 1);
              @ loop invariant gap == 1 && j > i ==> sorted(arr, i, n - 1);
              @ loop invariant gap == 1 ==> \forall integer k; i <= k < j ==> arr[k] < tmp;
              @ loop variant n - gap - j;
              @*/
            for (j = i; j < n - gap && arr[j + gap] < tmp; j += gap) {
                arr[j] = arr[j + gap];
            }
            
            arr[j] = tmp;

        }

        //@ assert gap <= 1 ==> sorted(arr, 0, n - 1);
    }
}
