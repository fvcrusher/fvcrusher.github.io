void shell_lr(int *arr, int n) {
    int i, j, tmp, gap;
    for (gap = n / 2; gap > 0; gap /= 2) {
        for (i = gap; i < n; ++i) {
            tmp = arr[i];
            for (j = i; j >= gap && arr[j - gap] > tmp; j -= gap) {
                arr[j] = arr[j - gap];
            }
            arr[j] = tmp;
        }
    }
}
