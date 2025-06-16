#define UPPER_LIMIT 255

void count_pos(int *arr, int n) {
    int count[UPPER_LIMIT + 1];
    int i, j;

    for (i = 0; i <= UPPER_LIMIT; ++i) {
        count[i] = 0;
    }

    for (i = 0; i < n; ++i) {
        ++count[arr[i]];
    }

    for (i = 1; i <= UPPER_LIMIT; ++i) {
        count[i] += count[i - 1];
    }
    
    for (i = 0; i < UPPER_LIMIT; ++i) {
        for (j = count[i]; j < count[i + 1]; ++j) {
            arr[j] = i;
        }
    }
    for (j = count[UPPER_LIMIT]; j < n; ++j) {
        arr[j] = UPPER_LIMIT;
    }
}
