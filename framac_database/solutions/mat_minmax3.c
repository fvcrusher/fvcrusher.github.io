/***** Контракт *****

requires
- Выделена память под min и max;
- Размеры матрицы неотрицательные и ненулевые;
- Выделена память под матрицу.
Последнее означает, что (валидны начальные элементы каждой строки матрицы) И (валидна каждая такая строка).

assigns
- Изменяемые области памяти - только *min и *max.

ensures
- Память матрицы не должна быть изменена в новом состоянии по сравнению со старым;
- min и max должны быть элементами из матрицы;
- min и max должны быть действительно минимальным и максимальным элементами.
Последнее означает, что любой элемент из матрицы должен не превосходить max и быть не меньше, чем min.

loops
- Завершаемость: с каждым шагом мы приближаемся к концу расчета <==> луповые варианты (n - i), (m - j) -> 0;
- Эншуры: на каждом шаге...
  + элементы массива остаются неизменны (к концу шага);
  + mmin и mmax изменяемы;
  + mmin и mmax принадлежат массиву;
  + mmin и mmax ограничивают снизу и сверху, соответственно, множество всех рассмотренных на данном шаге элементов матрицы.

predicates
Пояснение к предикатам проверки локальных экстремумов. Так как поиск минимума и максимума построчный, то проверка mmin и mmax на очередном шаге осуществляется так: подадим на вход номера текущей строки и элемента в ней, считая, что элемент уже проверен. Для всех строк, предшествующих текущей, проверим все элементы строки. Для текущей строки проверим все элементы до текущего включительно. Соединим обе проверки конъюнкцией.

*/

/*************************************************************/

/*@
    predicate RowsAreValid(int **matrix, int n, int m) = \forall integer i; (0 <= i < n) ==> \valid(matrix[i] + (0 .. m-1));
    
    predicate IsCurrentMin(int **matrix, int current_row, int current_col, int m, int current_min) = (\forall int row, col; (0 <= row < current_row) && (0 <= col < m) ==> (matrix[row][col] >= current_min)) && (\forall int col; (0 <= col <= current_col) ==> (matrix[current_row][col] >= current_min));
    
    predicate IsCurrentMax(int **matrix, int current_row, int current_col, int m, int current_max) = (\forall int row, col; (0 <= row < current_row) && (0 <= col < m) ==> (matrix[row][col] <= current_max)) && (\forall int col; (0 <= col <= current_col) ==> (matrix[current_row][col] <= current_max));

    predicate IsGloblMin(int** matrix, int n, int m, int globl_min) = \forall int k, l; ((0 <= k < n) && (0 <= l < m)) ==> (globl_min <= matrix[k][l]);
    
    predicate IsGloblMax(int** matrix, int n, int m, int globl_max) = \forall int k, l; ((0 <= k < n) && (0 <= l < m)) ==> (globl_max >= matrix[k][l]);
    
@*/

/*************************************************************/

/*@
    requires \valid(min) && \valid(max);    
    requires (n>0) && (m>0);
    
    requires \valid(mat + (0..n-1));
    requires RowsAreValid(mat, n, m);
   
    assigns *min, *max;
  
    ensures \forall int i, j; ((0 <= i < n) && (0 <= j < m)) ==> \old(mat[i][j]) == mat[i][j];
    
    ensures \exists int i, j; (0 <= i < n) && (0 <= j < m) && (*min == mat[i][j]);
    ensures \exists int i, j; (0 <= i < n) && (0 <= j < m) && (*max == mat[i][j]);
    
    ensures IsGloblMin(mat, n, m, *min);
    ensures IsGloblMax(mat, n, m, *max);
    
@*/

void mat_minmax_3(int **mat, int n, int m, int *min, int *max)
{
    int mmin = mat[0][0];
    //@ assert mmin == mat[0][0];
    int mmax = mat[0][0];
    //@ assert mmax == mat[0][0];
    
    /*@
       loop assigns mmin, mmax, i;
       loop invariant 0 <= i < n;

       loop invariant \forall int i, j; ((0 <= i < n) && (0 <= j < m)) ==> (mat[i][j] == \at(mat[i][j], LoopEntry));
       
       loop invariant \exists int k,l; ((0 <= k < n) && (0 <= l < m)) && (mat[k][l] == mmax);
       loop invariant \exists int k,l; ((0 <= k < n) && (0 <= l < m)) && (mat[k][l] == mmin);
       
       loop invariant IsCurrentMin(mat, i, m, m, mmin);
       loop invariant IsCurrentMax(mat, i, m, m, mmax);
       
       loop variant n - i;
    @*/
    for (int i = 0; i < n; ++i) {
    
        /*@
            loop assigns mmin, j;
            loop invariant 0 <= j < m;
            
            loop invariant \forall int j; ((0 <= j < m)) ==> (mat[i][j] == \at(mat[i][j], LoopEntry));
          
            loop invariant \exists int k; (0 <= k <= j) && (mat[i][k] == mmin);
            loop invariant IsCurrentMin(mat, i, j, m, mmin);
            
            loop variant m - j;
        @*/
        for (int j = 0; j < m; ++j) {
            if (mat[i][j] < mmin) {
                mmin = mat[i][j];
            }
            //@ assert mmin <= mat[i][j];
        }
        //@ assert IsCurrentMin(mat, i, m, m, mmin);
        
        /*@
            loop assigns mmax, j;
            loop invariant 0 <= j < m;
          
            loop invariant \forall int j; ((0 <= j < m)) ==> (mat[i][j] == \at(mat[i][j], LoopEntry));
          
            loop invariant \exists int p; (0 <= p < j) && (mat[i][p] == mmax);
            loop invariant IsCurrentMax(mat, i, j, m, mmax);
          
            loop variant m - j;
        @*/
        for (int j = 0; j < m; ++j) {
            if (mat[i][j] > mmax) {
                mmax = mat[i][j];
            }
            //@ assert mmax >= mat[i][j];
        }
        //@ assert IsCurrentMax(mat, i, m, m, mmax);
    }
    *min = mmin;
    //@ assert *min == mmin;
    *max = mmax;
    //@ assert *max == mmax;
}
