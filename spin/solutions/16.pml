#define WHITE 0
#define BLACK 1

#define EMPTY 0
#define FILLED 1

// Линия шашек будет представлена парами битов - первый бит указывает, занята ли
// ячейка, вторая ячейка указывает на цвет шашки в ячейке, если ячейка занята.
// Очевидно, ячеек всего 10 (6 шашек + 4 пустых места слева).
bit field[20] = { 
    EMPTY, 0, // ╮
    EMPTY, 0, // ├─ Пустые ячейки (цвет обнуляем, нам он не важен с EMPTY ячейками).
    EMPTY, 0, // │
    EMPTY, 0, // ╯
    FILLED, BLACK, // ╮
    FILLED, WHITE, // │
    FILLED, BLACK, // ├─ Разложенные шашки (черная, белая, черная, белая, черная, белая).
    FILLED, WHITE, // │
    FILLED, BLACK, // │
    FILLED, WHITE  // ╯
};


// Проще всего будет понять, что все белые слева, а все черные - справа по 
// индексу последней белой и индексу первой черной шашки.
// Если `last_white < first_black` - значит мы добились того, чего хотели
int last_white = 9;
int first_black = 4;


// Счетчик шагов решения
byte steps = 0;

#define SAFE steps < 3
#define GOAL (last_white < first_black && steps == 3)


// Для удобства чтения полученного решения загадки
inline printState() {
    printf("      ╭──────┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─╮\n")
    printf("╭─────┤Индекс│0│1│2│3│4│5│6│7│8│9│  ' ' - Пустое место\n");
    printf("│ШАГ %d├──────┼─┼─┼─┼─┼─┼─┼─┼─┼─┼─┤  'B' - Черная шашка\n", steps);
    printf("╰─────┤Шашка │%c│%c│%c│%c│%c│%c│%c│%c│%c│%c│  'W' - Белая шашка\n", 
        (!field[0] -> ' ' : (field[1] -> 'B' : 'W')),
        (!field[2] -> ' ' : (field[3] -> 'B' : 'W')),
        (!field[4] -> ' ' : (field[5] -> 'B' : 'W')),
        (!field[6] -> ' ' : (field[7] -> 'B' : 'W')),
        (!field[8] -> ' ' : (field[9] -> 'B' : 'W')),
        (!field[10] -> ' ' : (field[11] -> 'B' : 'W')),
        (!field[12] -> ' ' : (field[13] -> 'B' : 'W')),
        (!field[14] -> ' ' : (field[15] -> 'B' : 'W')),
        (!field[16] -> ' ' : (field[17] -> 'B' : 'W')),
        (!field[18] -> ' ' : (field[19] -> 'B' : 'W'))
    );
    printf("      ├──────┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┤\n");
    printf("      │ Последняя белая: %d       │\n", last_white);
    printf("      │ Первая черная: %d         │\n", first_black);
    printf("      ╰──────────────────────────╯\n\n");
}


// Перемещаем две шашки начиная с индекса i (i и i+1 шашки) на два пустых места
// начиная с j (j и j+1 места)
// Попутно увеличиваем кол-во шагов
inline move(i, j) {
    atomic {
        steps++;

        field[2 * j] = field[2 * i];
        field[2 * j + 1] = field[2 * i + 1];
        field[2 * (j + 1)] = field[2 * (i + 1)];
        field[2 * (j + 1) + 1] = field[2 * (i + 1) + 1];

        field[2 * i] = 0;
        field[2 * i + 1] = 0;
        field[2 * (i + 1)] = 0;
        field[2 * (i + 1) + 1] = 0;

        byte k;
        for (k : 0..9) {
            last_white = ((field[k * 2] && field[k * 2 + 1] == WHITE) -> k : last_white);
            first_black = ((field[(9 - k) * 2] && field[(9 - k) * 2 + 1] == BLACK) -> (9 - k) : first_black);
        }
    }
}


// Проверка можем ли передвинуть шашки начиная с индекса i (i и i+1 шашки) на
// два пустых места начиная с j (j и j+1 места)
#define canMove(i, j) \
    field[2 * i] && field[2 * (i + 1)] && \
    !field[2 * j] && !field[2 * (j + 1)]


// Веток много - сделаем дефайн для простоты
#define branch(i, j) (canMove(i, j)) -> atomic { \
    printf( \
        "ШАГ %d: Двигаем шашки с мест %d и %d на места %d и %d\n", \
        steps+1, i, i+1, j, j+1 \
    ); move(i, j); printState(); }


proctype Checkers() {
    do
    :: branch(0, 2)
    :: branch(0, 3)
    :: branch(0, 4)
    :: branch(0, 5)
    :: branch(0, 6)
    :: branch(0, 7)
    :: branch(0, 8)
    :: branch(1, 3)
    :: branch(1, 4)
    :: branch(1, 5)
    :: branch(1, 6)
    :: branch(1, 7)
    :: branch(1, 8)
    :: branch(2, 0)
    :: branch(2, 4)
    :: branch(2, 5)
    :: branch(2, 6)
    :: branch(2, 7)
    :: branch(2, 8)
    :: branch(3, 0)
    :: branch(3, 1)
    :: branch(3, 5)
    :: branch(3, 6)
    :: branch(3, 7)
    :: branch(3, 8)
    :: branch(4, 0)
    :: branch(4, 1)
    :: branch(4, 2)
    :: branch(4, 6)
    :: branch(4, 7)
    :: branch(4, 8)
    :: branch(5, 0)
    :: branch(5, 1)
    :: branch(5, 2)
    :: branch(5, 3)
    :: branch(5, 7)
    :: branch(5, 8)
    :: branch(6, 0)
    :: branch(6, 1)
    :: branch(6, 2)
    :: branch(6, 3)
    :: branch(6, 4)
    :: branch(6, 8)
    :: branch(7, 0)
    :: branch(7, 1)
    :: branch(7, 2)
    :: branch(7, 3)
    :: branch(7, 4)
    :: branch(7, 5)
    :: branch(8, 0)
    :: branch(8, 1)
    :: branch(8, 2)
    :: branch(8, 3)
    :: branch(8, 4)
    :: branch(8, 5)
    :: branch(8, 6)
    od
}

init {
    printf("ИЗНАЧАЛЬНОЕ СОСТОЯНИЕ\n")
    printState();
    run Checkers();
}

ltl { !(SAFE U GOAL); }
