/*@
    predicate CurrentColMin(int** arr, integer n, integer col_ind, int elem) = 
        \forall integer k; (0 <= k < n) ==> (arr[k][col_ind] >= elem);
    predicate CurrentColMax(int** arr, integer n, integer col_ind, int elem) = 
        \forall integer k; (0 <= k < n) ==> (arr[k][col_ind] <= elem);

    predicate MaxElem(int** arr, integer n, integer m, int elem) = 
        \forall integer k, l; ((0 <= k < n) && (0 <= l < m)) ==> (elem >= arr[k][l]);
    predicate MinElem(int** arr, integer n, integer m, int elem) = 
        \forall integer k, l; ((0 <= k < n) && (0 <= l < m)) ==> (elem <= arr[k][l]);
@*/



/*@
    predicate CheckNestedArrValid(int **a, int n, int m) = \forall integer i; (0 <= i < n) ==> \valid(a[i] + (0 .. m-1));
@*/

/*
Нужно, чтобы 
0. Размеры массива валидны
1. Выделенная память валидна
2. Массив не изменился
3. Числа мин и макс входят в массив
4. Число мин меньше либо равно всем элементам массива
5. Число макс больше либо равно всем элементам массива
*/

/*@
    requires n > 0;
    requires m > 0;
    requires \valid(min);
    requires \valid(max);
    requires \valid(mat + (0 .. n-1));
    requires CheckNestedArrValid(mat, n, m);
    assigns *min, *max;
    ensures \forall integer i, j; ((0 <= i < n) && (0 <= j < m)) ==> \old(mat[i][j]) == mat[i][j];
    ensures \exists integer i, j; (0 <= i < n) && (0 <= j < m) && (*min == mat[i][j]);
    ensures \exists integer i, j; (0 <= i < n) && (0 <= j < m) && (*max == mat[i][j]);
    ensures MaxElem(mat, n, m, *max);
    ensures MinElem(mat, n, m, *min);
@*/
void mat_minmax_7(int **mat, int n, int m, int *min, int *max) {
    int mmin = mat[0][0];
    //@ assert mmin == mat[0][0];
    int mmax = mat[0][0];
    //@ assert mmax == mat[0][0];


    /*@
        loop invariant 0 <= i <= m;
        loop invariant \forall integer i, j; 
        ((0 <= i < n) && (0 <= j < m)) ==> (mat[i][j] == \at(mat[i][j], LoopEntry));
        loop invariant (i > 0) ==> CurrentColMax(mat, n, i - 1, mmax);
        loop invariant (i > 0) ==> CurrentColMin(mat, n, i - 1, mmin);
        loop invariant (i > 0) ==> mmax >= mat[n-1][i-1];
        loop invariant (i == 0) ==> mmax == mat[0][0];
        loop invariant (i > 0) ==> mmin <= mat[n-1][i-1];
        loop invariant (i == 0) ==> mmin == mat[0][0]; 
        loop invariant MaxElem(mat, n, i, mmax);
        loop invariant MinElem(mat, n, i, mmin);
        loop invariant \exists integer k,l; ((0 <= k < n) && (0 <= l < m)) && (mat[k][l] == mmax);
        loop invariant \exists integer k,l; ((0 <= k < n) && (0 <= l < m)) && (mat[k][l] == mmin);
        loop assigns mmin, mmax, i;
        loop variant m - i;
    @*/
    for (int i = 0; i < m; ++i) {
        
        
        /*@
            loop invariant 0 <= j <= n;
            loop invariant \forall integer i, j; 
            ((0 <= i < n) && (0 <= j < m)) ==> (mat[i][j] == \at(mat[i][j], LoopEntry));
            loop invariant (i > 0) ==> (mmin <= mat[n-1][i - 1]);
            loop invariant CurrentColMin(mat, j, i, mmin);
            loop invariant MinElem(mat, n, i, mmin);
            loop invariant \exists integer k,l; ((0 <= k < n) && (0 <= l < m)) && (mmin == mat[k][l]);
            loop assigns mmin, j;
            loop variant n - j;
        @*/
        for (int j = 0; j < n; ++j) {
            if (mat[j][i] < mmin) {
                mmin = mat[j][i];
            }
        }
        
        /*@
            loop invariant 0 <= j <= n;
            loop invariant \forall integer i, j; 
            ((0 <= i < n) && (0 <= j < m)) ==> (mat[i][j] == \at(mat[i][j], LoopEntry));
            loop invariant (i > 0) ==> (mmax >= mat[n-1][i - 1]);
            loop invariant CurrentColMax(mat, j, i, mmax);
            loop invariant MaxElem(mat, n, i, mmax);
            loop invariant \exists integer k,l; ((0 <= k < n) && (0 <= l < m)) && (mmax == mat[k][l]);
            loop assigns mmax, j;
            loop variant n - j;
        @*/
        for (int j = 0; j < n; ++j) {
            if (mat[j][i] > mmax) {
                mmax = mat[j][i];
            }
        }
    }
    *min = mmin;
    //@ assert *min == mmin;
    *max = mmax;
    //@ assert *max == mmax;
}
