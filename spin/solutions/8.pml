// Works for every N!

/* Всего 9 возможных действий:
 *   1) Обмен между 1 и 2 (обе непустые)
 *   2) Обмен между 2 и 3 (обе непустые)
 *   3) Обмен между 1 и 3 (обе непустые)
 *   4) С непустой 1 на пустую 2
 *   5) С непустой 2 на пустую 1
 *   6) С непустой 2 на пустую 3
 *   7) С непустой 3 на пустую 2
 *   8) С непустой 1 на пустую 3
 *   9) С непустой 3 на пустую 1
 */

// time spin -run -i 8.pml --> 68.8 sec

#define N 8

byte rod1[N], rod2[N], rod3[N] = 0;
byte rod1_idx, rod2_idx, rod3_idx = 0;

#define MOVE(from, to) \
    rod##to[rod##to##_idx] = rod##from[rod##from##_idx - 1]; \
    rod##from[rod##from##_idx - 1] = 0; \
    rod##from##_idx--; \
    rod##to##_idx++;

#define HEAD(where) rod##where[rod##where##_idx - 1]

#define PRINT_STATE //printf("rod1: %d %d %d %d %d %d %d %d\n\trod2: %d %d %d %d %d %d %d %d\n\trod3: %d %d %d %d %d %d %d %d\n", rod1[0], rod1[1], rod1[2], rod1[3], rod1[4], rod1[5], rod1[6], rod1[7], rod2[0], rod2[1], rod2[2], rod2[3], rod2[4], rod2[5], rod2[6], rod2[7], rod3[0], rod3[1], rod3[2], rod3[3], rod3[4], rod3[5], rod3[6], rod3[7])
#define PRINT_ACTION(from, to) printf("Перекладываю кольцо размера %d со стержня %d на стержень %d\n", rod##from[rod##from##_idx - 1], from, to);

// Если на интересующем нас стержне лежат все кольца, а на других - ни одного,
// то задача решена, так как перекладывать можем только меньшее на большее по 
// proctype.
#define ROD_FILLED(target_rod) (rod##target_rod##_idx == N)

#define GOAL (ROD_FILLED(2) || ROD_FILLED(3)) 

active proctype Hanoi() {
    byte idx;
    for (idx : 0 .. N - 1) {
        rod1[idx] = N - idx;
    }
    rod1_idx = N;

    do
    :: (rod1_idx > 0 && rod2_idx > 0) -> atomic {
        if
        :: (HEAD(1) < HEAD(2)) -> atomic { PRINT_ACTION(1, 2); MOVE(1, 2); PRINT_STATE; }
        :: (HEAD(1) > HEAD(2)) -> atomic { PRINT_ACTION(2, 1); MOVE(2, 1); PRINT_STATE; }
        fi
    }

    :: (rod2_idx > 0 && rod3_idx > 0) -> atomic {
        if
        :: (HEAD(2) < HEAD(3)) -> atomic { PRINT_ACTION(2, 3); MOVE(2, 3); PRINT_STATE; }
        :: (HEAD(2) > HEAD(3)) -> atomic { PRINT_ACTION(3, 2); MOVE(3, 2); PRINT_STATE; }
        fi
    }

    :: (rod1_idx > 0 && rod3_idx > 0) -> atomic {
        if
        :: (HEAD(1) < HEAD(3)) -> atomic { PRINT_ACTION(1, 3); MOVE(1, 3); PRINT_STATE; }
        :: (HEAD(1) > HEAD(3)) -> atomic { PRINT_ACTION(3, 1); MOVE(3, 1); PRINT_STATE; }
        fi
    }

    :: (rod1_idx > 0 && rod2_idx == 0) -> atomic { PRINT_ACTION(1, 2); MOVE(1, 2); PRINT_STATE; }
    :: (rod1_idx == 0 && rod2_idx > 0) -> atomic { PRINT_ACTION(2, 1); MOVE(2, 1); PRINT_STATE; }

    :: (rod2_idx > 0 && rod3_idx == 0) -> atomic { PRINT_ACTION(2, 3); MOVE(2, 3); PRINT_STATE; }
    :: (rod2_idx == 0 && rod3_idx > 0) -> atomic { PRINT_ACTION(3, 2); MOVE(3, 2); PRINT_STATE; }

    :: (rod1_idx > 0 && rod3_idx == 0) -> atomic { PRINT_ACTION(1, 3); MOVE(1, 3); PRINT_STATE; }
    :: (rod1_idx == 0 && rod3_idx > 0) -> atomic { PRINT_ACTION(3, 1); MOVE(3, 1); PRINT_STATE; }
    od
}

ltl { !(<>GOAL); }
