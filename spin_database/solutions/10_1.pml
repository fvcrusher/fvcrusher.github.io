#define N 8

byte figures[2*N];

byte n;

byte i, j;

byte x, y;

bool valid;

inline print_state(){
    int k = 0;
    printf("n=%d\n", n);
    do
    ::(k != n) -> printf("(x=%d, y=%d)\n", figures[k], figures[k+1]); k = k + 2;
    ::(k == n) -> break;
    od
}

inline setRandom(){
    select(x: 1 .. N);
    select(y: 1 .. N);
}

proctype P(){
    do
    /* Если клетка-кандидат не совпадает с последней занятой ферзём клеткой и 
       не находится на её горизонтали или вертикали */
    ::((figures[(n - 1) - 1] != x) && (figures[(n - 1)] != y)) ->
        i = 0;
        valid = 1;
        do
        :: ((i == n)) -> break;
        /* Клетка совпадает с уже занятой */
        :: ((figures[i] == x) && (figures[i + 1] == y)) ->
            atomic{
                valid = 0;
                printf("Failed candidate is (%d, %d), queen is (%d, %d)\n", x, y, figures[i], figures[i+1]);
                break;
            }
            
        /* Проверка поражения клетки ферзём по диагонали */
        :: (((figures[i] - x)*(figures[i] - x) == (figures[i+1] - y) * (figures[i+1] - y))) ->
            atomic{
                valid = 0;
                printf("Failed candidate is (%d, %d), queen is (%d, %d)\n", x, y, figures[i], figures[i+1]);
                break;
            }
        /* Проверка поражения клетки по горизонтали */
        :: (figures[i] == x) ->
            atomic{
                valid = 0;
                printf("Failed candidate is (%d, %d), queen is (%d, %d)\n", x, y, figures[i], figures[i+1]);
                break;
            }
        /* Проверка поражения клетки по вертикали */
        :: (figures[i + 1] == y) ->
            atomic{
                valid = 0;
                printf("Failed candidate is (%d, %d), queen is (%d, %d)\n", x, y, figures[i], figures[i+1]);
                break;
            }
        /* Если условия выше не выполнились, передвинемся на след. ферзя */
        :: (((figures[i] != x) && (figures[i + 1] != y)) && (i != n) && ((figures[i] - x)*(figures[i] - x) != (figures[i+1] - y) * (figures[i+1] - y)))
            -> i = i + 2; 
        :: printf("Who r you!? (%d, %d)\n", x, y);
        od
        if
        /* Если по выходе из цикла клетка не опознана как невалидная */
        :: (valid)->
            /* Установить в клетку ферзя */
            atomic {
                n = n + 2;
                figures[n - 2] = x;
                figures[n - 1] = y;
                printf("The queen settled on (%d, %d)\n", x, y);
                print_state();
            }
        /* Иначе выйдем из условного оператора */
        :: (!valid) ->
            printf("The cell (%d, %d) can't be occupated\n", x, y);
        fi
    ::setRandom();
    od
}

init {
    for (i: 0..(2*N-1)){
        figures[i] = 0;
    }
    setRandom();
    figures[0] = x;
    figures[1] = y;
    printf("The queen settled on (%d, %d)\n", x, y);
    n = 2;
    print_state();
    valid = 1;
    run P();
}

ltl NeverGonnaGiveYouUp {
    !<>(n == 2 * N)
}