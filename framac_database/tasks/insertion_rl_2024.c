void insertion_rl(int *arr, int n) {
    int i, key, j;
    for (i = n - 2; i >= 0; --i) {
        key = arr[i];
        for (j = i + 1; j < n && arr[j] < key; ++j) {
            arr[j - 1] = arr[j];
        }
        arr[j - 1] = key;
    }
}
