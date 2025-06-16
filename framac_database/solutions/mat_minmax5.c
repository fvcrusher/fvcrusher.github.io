/*@ 
    axiomatic Extrema
    {
        predicate
        MaxElement{L}(int **a, integer n, integer m, int max) = 
            \forall integer i, j; 0 <= i < m && 0 <= j < n ==> max >= a[j][i];
        
        predicate
        MinElement{L}(int **a, integer n, integer m, int min) = 
            \forall integer i, j; 0 <= i < m && 0 <= j < n ==> min <= a[j][i];
    }
*/


/*@
    axiomatic ExtremaExist
    {
        predicate
        Exist{L}(int **a, integer n, integer m, int elem) = 
            \exists integer i, j; 0 <= i < m && 0 <= j < n && elem == a[j][i];
    }
*/


/*@ 
    axiomatic ExtremaRow
    {
        predicate
        MaxElementRow{L}(int **a, integer n, integer m, int max) = 
            \forall integer j; 0 <= j < n ==> max >= a[j][m];
        
        predicate
        MinElementRow{L}(int **a, integer n, integer m, int min) = 
            \forall integer j; 0 <= j < n ==> min <= a[j][m];
    }
*/


/*@
    requires 0 < n;
    requires 0 < m;
    requires \valid(mat + (0 .. n - 1));
    requires \forall integer i; 0 <= i < n ==> \valid(mat[i] + (0 .. m - 1));
    requires \valid(max);
    requires \valid(min);

    assigns *min, *max;

    ensures MaxElement(mat, n, m, *max);
    ensures MinElement(mat, n, m, *min);
    ensures Exist(mat, n, m, *max);
    ensures Exist(mat, n, m, *min);
*/


void mat_minmax_5(int **mat, int n, int m, int *min, int *max) {
    int mmin = mat[0][0];
    int mmax = mat[0][0];

    /*@
        loop invariant MaxElement(mat, n, i, mmax);
        loop invariant MinElement(mat, n, i, mmin);
        loop invariant Exist(mat, n, m, mmax);
        loop invariant Exist(mat, n, m, mmin);
        loop invariant 0 <= i <= m;
        loop variant m - i;
    */
    for (int i = 0; i < m; ++i) {
        int imin = mat[0][i];
        int imax = mat[0][i];

        /*@
            loop invariant MinElementRow(mat, j, i, imin);
            loop invariant Exist(mat, n, m, imin);
            loop invariant 0 <= j <= n;
            loop variant n - j;
        */
        for (int j = 1; j < n; ++j) {
            if (mat[j][i] < imin) {
                imin = mat[j][i];
            }
        }

        /*@
            loop invariant MaxElementRow(mat, j, i, imax);
            loop invariant Exist(mat, n, m, imax);
            loop invariant 0 <= j <= n;
            loop variant n - j;
        */
        for (int j = 1; j < n; ++j) {
            if (mat[j][i] > imax) {
                imax = mat[j][i];
            }
        }

        if (imin < mmin) {
            mmin = imin;
        }
        if (imax > mmax) {
            mmax = imax;
        }
    }
    *min = mmin;
    *max = mmax;
}
