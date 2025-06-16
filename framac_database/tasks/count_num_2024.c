#define UPPER_LIMIT 255

void count_num(int *arr, int n) {
    int count[UPPER_LIMIT + 1];
    int i, j, pos;

    for (i = 0; i <= UPPER_LIMIT; ++i) {
        count[i] = 0;
    }

    for (i = 0; i < n; ++i) {
        ++count[arr[i]];
    }

    pos = 0;
    for (i = 0; i <= UPPER_LIMIT; ++i) {
        for (j = 0; j < count[i]; ++j) {
            arr[j] = i;
        }
        pos += count[i];
    }
}
