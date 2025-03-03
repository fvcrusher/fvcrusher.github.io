#define N 8

int visited_count = 0;
int i_current, j_current = 0;
typedef line {
    bit content[N] = 0
};
line field[N];

#define visited(i, j) (field[i].content[j] == 1)

inline move(i, j) {
    if
    :: (!visited(i, j)) -> atomic {
        i_current = i;
        j_current = j;
        field[i].content[j] = 1;
        visited_count++
    }
    fi;
}

#define GOAL (visited_count == N * N) 

proctype HobbieHorsing(int i, j) {
    move(i, j);

    do
    :: (i >= 2 && j >= 1) -> atomic {
        printf("Moving to (%d, %d)\n", i - 2, j - 1);
    }
    :: (i >= 2 && j < N - 1) -> atomic {
        printf("Moving to (%d, %d)\n", i - 2, j + 1);
    }

    :: (i >= 1 && j >= 2) -> atomic {
        printf("Moving to (%d, %d)\n", i - 1, j - 2);
    }
    :: (i >= 1 && j < N - 2) -> atomic {
        printf("Moving to (%d, %d)\n", i - 1, j + 2);
    }

    :: (i < N - 2 && j >= 1) -> atomic {
        printf("Moving to (%d, %d)\n", i + 2, j - 1);
    }
    :: (i < N - 2 && j < N - 1) -> atomic {
        printf("Moving to (%d, %d)\n", i + 2, j + 1);
    }

    :: (i < N - 1 && j >= 2) -> atomic {
        printf("Moving to (%d, %d)\n", i + 1, j - 2);
    }
    :: (i < N - 1 && j < N - 2) -> atomic {
        printf("Moving to (%d, %d)\n", i + 1, j + 2);
    }
    od
}

init {
    run HobbieHorsing(3, 3);
}

ltl { !(<>GOAL); }
