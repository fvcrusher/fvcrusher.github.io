byte first_jug = 0;
byte second_jug = 0;
#define FIRST_ROOM 5
#define SECOND_ROOM 8

#define GOAL (first_jug == 2)
// In case if it is acceptable to measure 2 gallons in 8-galon jar
// #define GOAL (first_jug == 2 || second_jug == 2)

active proctype transfusion() {
    do
    :: (first_jug < FIRST_ROOM) -> atomic { 
        printf("Наливаем первый кувшин (%d галлонов)\n", FIRST_ROOM); 
        first_jug = FIRST_ROOM; 
        printf("Текущее состояние: первый: %d/%d, второй: %d/%d\n", first_jug, FIRST_ROOM, second_jug, SECOND_ROOM);
    }
    :: (second_jug < SECOND_ROOM) -> atomic { 
        printf("Наливаем второй кувшин (%d галлонов)\n", SECOND_ROOM); 
        second_jug = SECOND_ROOM; 
        printf("Текущее состояние: первый: %d/%d, второй: %d/%d\n", first_jug, FIRST_ROOM, second_jug, SECOND_ROOM);
    }
    :: (first_jug > 0) -> atomic { 
        printf("Выливаем первый кувшин (%d галлонов)\n", FIRST_ROOM); 
        first_jug = 0; 
        printf("Текущее состояние: первый: %d/%d, второй: %d/%d\n", first_jug, FIRST_ROOM, second_jug, SECOND_ROOM);
    }
    :: (second_jug > 0) -> atomic { 
        printf("Выливаем первый кувшин (%d галлонов)\n", SECOND_ROOM); 
        second_jug = 0; 
        printf("Текущее состояние: первый: %d/%d, второй: %d/%d\n", first_jug, FIRST_ROOM, second_jug, SECOND_ROOM);
    }
    :: (first_jug > 0) -> atomic { 
        byte capacity = SECOND_ROOM - second_jug; 
        if 
        :: (capacity >= first_jug) -> atomic {
            printf("Переливаем %d галлонов из первого кувшина (%d галлонов) во второй (%d галлонов)\n", first_jug, FIRST_ROOM, SECOND_ROOM); 
            second_jug = second_jug + first_jug; 
            first_jug = 0;
        }
        :: (capacity < first_jug) -> atomic {
            printf("Переливаем %d галлонов из первого кувшина (%d галлонов) во второй (%d галлонов)\n", capacity, FIRST_ROOM, SECOND_ROOM); 
            second_jug = SECOND_ROOM; 
            first_jug = first_jug - capacity;
        }
        fi;
        printf("Текущее состояние: первый: %d/%d, второй: %d/%d\n", first_jug, FIRST_ROOM, second_jug, SECOND_ROOM);
    }
    :: (second_jug > 0) -> atomic { 
        printf("Fusing from second_jug to first_jug\n"); 
        byte capacity = FIRST_ROOM - first_jug;
        if
        :: (second_jug > capacity) -> atomic {
            printf("Переливаем %d галлонов из второго кувшина (%d галлонов) в первый (%d галлонов)\n", capacity, SECOND_ROOM, FIRST_ROOM); 
            first_jug = FIRST_ROOM; 
            second_jug = second_jug - capacity;
        }
        :: (second_jug <= capacity) -> atomic {
            printf("Переливаем %d галлонов из второго кувшина (%d галлонов) в первый (%d галлонов)\n", second_jug, SECOND_ROOM, FIRST_ROOM); 
            first_jug = first_jug + second_jug; 
            second_jug = 0;
        }
        fi;
        printf("Текущее состояние: первый: %d/%d, второй: %d/%d\n", first_jug, FIRST_ROOM, second_jug, SECOND_ROOM);
    }
    od
}

ltl { !(<>GOAL) }
