#include <limits.h>

/*@
  @ predicate valid_mtx(int ** mat, int n, int m) =
  @     \forall int i;
  @         (0 <= i < n) ==> \valid_read(mat[i] + (0..m-1));
  @
  @ predicate tmp_value_exists(int** mtx, integer n, integer m, int tmp) =
  @    \exists integer j, i; 0 <= j < n && 0 <= i < m && mtx[j][i] == tmp;
  @
  @ predicate tmp_is_min{L}(int** mtx, integer left_r, integer right_r, integer left_c, integer right_c, int tmp) =
  @     \forall integer j, i; left_r <= j < right_r && left_c <= i < right_c ==> mtx[j][i] >= tmp;
  @
  @ predicate tmp_is_max{L}(int** mtx, integer left_r, integer right_r, integer left_c, integer right_c, int tmp) =
  @     \forall integer j, i; left_r <= j < right_r && left_c <= i < right_c ==> mtx[j][i] <= tmp;
  @  
  @ lemma minimum_for_quadrant_of_mtx{L}:
  @   \forall int** mtx, integer n, i, j, mmin;
  @    j < n && 
  @    (\forall integer k; 0 <= k < j && k % 2 == 0 ==> mmin <= mtx[k][i]) && 
  @    (\forall integer k; 0 <= k < n && k % 2 == 1 ==> mmin <= mtx[k][i]) ==>
  @      (\forall integer k; 0 <= k < j ==> mmin <= mtx[k][i]);
  @
  @ lemma maximum_for_quadrant_of_mtx{L}:
  @   \forall int** mtx, integer n, i, j, mmax;
  @    j < n && 
  @    (\forall integer k; 0 <= k < j && k % 2 == 0 ==> mmax >= mtx[k][i]) && 
  @    (\forall integer k; 0 <= k < n && k % 2 == 1 ==> mmax >= mtx[k][i]) ==>
  @      (\forall integer k; 0 <= k < j ==> mmax >= mtx[k][i]);
  @
  @ lemma transitivity_of_minimum{L}:
  @  \forall int** mtx, int tmp, mmin, integer n, i;
  @    (tmp_is_min(mtx, 0, n, 0, i, mmin) && tmp < mmin) ==>
  @      tmp_is_min(mtx, 0, n, 0, i, tmp);
  @
  @ lemma transitivity_of_maximum{L}:
  @  \forall int** mtx, int tmp, mmax, integer n, i;
  @    (tmp_is_max(mtx, 0, n, 0, i, mmax) && tmp > mmax) ==>
  @      tmp_is_max(mtx, 0, n, 0, i, tmp);
  @*/


/*@
  @ requires 0 < n < INT_MAX && 0 < m < INT_MAX;
  @ requires \valid(min);
  @ requires \valid(max);
  @ requires \valid_read(mat + (0..n-1));
  @ requires valid_mtx(mat, n, m);
  @
  @ assigns *min, *max;
  @
  @ ensures \forall integer i, j; 0 <= i < n && 0 <= j < m ==> mat[i][j] == \old(mat[i][j]);
  @
  @ ensures tmp_value_exists(mat, n, m, *min);
  @ ensures tmp_value_exists(mat, n, m, *max);
  @
  @ ensures tmp_is_min(mat, 0, n, 0, m, *min);
  @ ensures tmp_is_max(mat, 0, n, 0, m, *max);
  @*/
void mat_minmax_11(int **mat, int n, int m, int *min, int *max) {
  int mmin = mat[0][0];
  int mmax = mat[0][0];
  //@assert mmin == mat[0][0];
  //@assert mmax == mat[0][0];

  /*@
    @ loop invariant 0 <= i <= m;
    @ loop invariant mmax >= mmin;
    @
    @ loop invariant tmp_value_exists(mat, n, m, mmin);
    @ loop invariant tmp_value_exists(mat, n, m, mmax);
    @
    @ loop invariant tmp_is_min(mat, 0, n, 0, i, mmin);
    @ loop invariant tmp_is_max(mat, 0, n, 0, i, mmax);
    @
    @ loop assigns mmin, mmax, i;
    @ loop variant m - i;
    @*/
  for (int i = 0; i < m; ++i) {   
    //@ assert tmp_is_min(mat, 0, n, 0, i, mmin);
    //@ assert tmp_is_max(mat, 0, n, 0, i, mmax);
    
    /*@
      @ loop invariant 1 <= j <= n + 1;
      @ loop invariant mmax >= mmin;
      @
      @ loop invariant j % 2 == 1;
      @
      @ loop invariant tmp_value_exists(mat, n, m, mmin);
      @ loop invariant tmp_value_exists(mat, n, m, mmax);
      @
      @ loop invariant tmp_is_min(mat, 0, n, 0, i, mmin);
      @ loop invariant tmp_is_max(mat, 0, n, 0, i, mmax);
      @
      @ loop invariant \forall integer k; 1 <= k < j && k % 2 == 1 ==> mmin <= mat[k][i];
      @ loop invariant \forall integer k; 1 <= k < j && k % 2 == 1 ==> mmax >= mat[k][i];
      @
      @ loop assigns mmin, mmax, j;
      @ loop variant n - j + 1;
      @*/
    for (int j = 1; j < n; j += 2) {
      int v = mat[j][i];
      //@ assert tmp_value_exists(mat, n, m, v);
      //@ assert tmp_is_min(mat, 0, n, 0, i, mmin);
      //@ assert tmp_is_max(mat, 0, n, 0, i, mmax);
      //@ assert mmax >= mmin;

      if (v < mmin) {
        //@ assert tmp_is_min(mat, 0, n, 0, i, mmin) && v < mmin;
        //@ assert tmp_is_min(mat, 0, n, 0, i, mmin) && v < mmin ==> tmp_is_min(mat, 0, n, 0, i, v);
        mmin = v;
        //@ assert \forall integer k; 1 <= k <= j && k % 2 == 1 ==> mmin <= mat[k][i];
        //@ assert tmp_is_min(mat, 0, n, 0, i, mmin);
      } else if (v > mmax) {
        //@ assert tmp_is_max(mat, 0, n, 0, i, mmax) && v > mmax;
        //@ assert tmp_is_max(mat, 0, n, 0, i, mmax) && v > mmax ==> tmp_is_max(mat, 0, n, 0, i, v);
        mmax = v;
        //@ assert \forall integer k; 1 <= k <= j && k % 2 == 1 ==> mmax >= mat[k][i];
        //@ assert tmp_is_max(mat, 0, n, 0, i, mmax);
      }
      //@ assert tmp_is_min(mat, 0, n, 0, i, mmin);
      //@ assert tmp_is_max(mat, 0, n, 0, i, mmax);
    }

    //@ assert \forall integer k; 0 <= k < n && k % 2 == 1 ==> mmin <= mat[k][i];
    //@ assert \forall integer k; 0 <= k < n && k % 2 == 1 ==> mmax >= mat[k][i];
    //@ assert tmp_is_min(mat, 0, n, 0, i, mmin);
    //@ assert tmp_is_max(mat, 0, n, 0, i, mmax);
    //@ assert mmax >= mmin;
    //@ assert \forall integer k, l; 0 <= k < n && 0 <= l < m ==> mat[k][l] == \at(mat[k][l], Pre);

    /*@ 
      @ loop invariant 0 <= j <= n + 1;
      @ loop invariant mmax >= mmin;
      @ loop invariant j % 2 == 0;
      @ loop invariant tmp_value_exists(mat, n, m, mmin);
      @ loop invariant tmp_value_exists(mat, n, m, mmax);
      @
      @ loop invariant tmp_is_min(mat, 0, n, 0, i, mmin);
      @ loop invariant tmp_is_max(mat, 0, n, 0, i, mmax);
      @
      @ loop invariant \forall integer k; 0 <= k < j && k % 2 == 0 ==> mmin <= mat[k][i];
      @ loop invariant \forall integer k; 0 <= k < n && k % 2 == 1 ==> mmin <= mat[k][i];
      @ loop invariant \forall integer k; 0 <= k < j < n ==> mmin <= mat[k][i];
      @
      @ loop invariant \forall integer k; 0 <= k < j && k % 2 == 0 ==> mmax >= mat[k][i];
      @ loop invariant \forall integer k; 0 <= k < n && k % 2 == 1 ==> mmax >= mat[k][i];
      @ loop invariant \forall integer k; 0 <= k < j < n ==> mmax >= mat[k][i];
      @
      @ loop assigns mmin, mmax, j;
      @ loop variant n - j + 1;
      @*/
      for (int j = 0; j < n; j += 2) {
        int v = mat[j][i];
        //@ assert tmp_value_exists(mat, n, m, v);
        //@ assert tmp_is_min(mat, 0, n, 0, i, mmin);
        //@ assert tmp_is_max(mat, 0, n, 0, i, mmax);
        //@ assert mmax >= mmin;

        if (v < mmin) {
          //@ assert tmp_is_min(mat, 0, n, 0, i, mmin) && v < mmin ==> tmp_is_min(mat, 0, n, 0, i, v);
          mmin = v;
          //@ assert \forall integer k; 0 <= k <= j && k % 2 == 0 ==> mmin <= mat[k][i];
          //@ assert \forall integer k; 0 <= k < n && k % 2 == 1 ==> mmin <= mat[k][i];
          //@ assert \forall integer k; 0 <= k <= j ==> mmin <= mat[k][i];
          //@ assert tmp_is_min(mat, 0, n, 0, i, mmin);
        } else if (v > mmax) {
          //@ assert tmp_is_max(mat, 0, n, 0, i, mmax) && v > mmax ==> tmp_is_max(mat, 0, n, 0, i, v);
          mmax = v;
          //@ assert \forall integer k; 0 <= k <= j && k % 2 == 0 ==> mmax >= mat[k][i];
          //@ assert \forall integer k; 0 <= k < n && k % 2 == 1 ==> mmax >= mat[k][i];
          //@ assert \forall integer k; 0 <= k <= j ==> mmax >= mat[k][i];
          //@ assert tmp_is_max(mat, 0, n, 0, i, mmax);
        }
        //@ assert tmp_is_min(mat, 0, n, 0, i, mmin);
        //@ assert tmp_is_max(mat, 0, n, 0, i, mmax);
      }
      
    //@ assert \forall integer k; 0 <= k < n ==> mmin <= mat[k][i];
    //@ assert \forall integer k; 0 <= k < n ==> mmax >= mat[k][i];

    //@ assert tmp_is_min(mat, 0, n, 0, i + 1, mmin);
    //@ assert tmp_is_max(mat, 0, n, 0, i + 1, mmax);
  }

  //@ assert tmp_value_exists(mat, n, m, mmin);
  //@ assert tmp_value_exists(mat, n, m, mmax);
  *min = mmin;
  *max = mmax;
}
