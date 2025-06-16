void bubble_rl(int *arr, int n) {
    int i, j, tmp;
    for (i = 0; i < n - 1; ++i) {
        for (j = n - 1; j > i; --j) {
            if (arr[j] < arr[j - 1]) {
                tmp = arr[j];
                arr[j] = arr[j - 1];
                arr[j - 1] = tmp;
            }
        }
    }
}
