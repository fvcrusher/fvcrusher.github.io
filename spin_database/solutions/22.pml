#define N 3

// 22. Решите с помощью SPIN следующую головоломку («Магический квадрат»). Расположите в
// квадрате 3 x 3 (в общем случая, N x N) 9 (N 2) последовательных натуральных чисел так, чтобы
// сумма чисел в каждой строке, каждом столбце и на обеих диагоналях была одинакова.


// Пример решения
// 2 7 6
// 9 5 1
// 4 3 8

inline print_square() {
    byte i, j;
    for (i : 0..(N-1)) {
        for (j : 0..(N-1)) {
            printf("%d", square[i * N + j]);
        }
        printf("\n");
    }
    printf("\n");
}

inline sums() {
    int temp_row_sum, temp_line_sum;
    int diag1_sum, diag2_sum;
    int i, j;
    
    row_sum = 0;
    diag_sum = 0;
    line_sum = 0;
    
    for (i : 0..(N-1)) {
        temp_line_sum = 0;
        temp_row_sum = 0;
        for (j : 0..(N-1)) {
            temp_row_sum = temp_row_sum + square[i * N + j];
            temp_line_sum = temp_line_sum + square[i + j * N];
            diag1_sum = diag1_sum + ((i == j) -> square[i * N + j] : 0);
            diag2_sum = diag2_sum + ((i == N - 1 - j) -> square[i * N + j] : 0);
        }
        
        row_sum = ((row_sum == 0 && temp_row_sum != 0) -> temp_row_sum : ((row_sum == temp_row_sum && temp_row_sum != 0) -> row_sum : -1));
        line_sum = ((line_sum == 0 && temp_line_sum != 0) -> temp_line_sum : ((line_sum == temp_line_sum && temp_line_sum != 0) -> line_sum : -1));
    }

    diag_sum = ((diag1_sum == diag2_sum) -> diag1_sum : -1);
}

byte square[N * N];
int counter = 1;

int row_sum = 0;
int line_sum = 0;
int diag_sum = 0;

#define GOAL ((counter == N*N + 1) && (row_sum > 0) && (line_sum > 0) && (diag_sum > 0) && (row_sum == diag_sum) && (row_sum == line_sum) && (line_sum == diag_sum))

proctype main() {
    int index;

    do
    :: (index >= 0 && index < N * N - 1) -> index++;
    :: (index > 0 && index < N * N) -> index--;
    :: (square[index] == 0) -> atomic { square[index] = counter; counter++; print_square(); sums(); index = 0; }
    :: (counter > N * N) -> break;
    od
    
}

init {
    run main();
}

ltl { !(<>GOAL) }
