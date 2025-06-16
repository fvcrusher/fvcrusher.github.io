void shell_rl(int *arr, int n) {
    int i, j, tmp, gap;
    for (gap = n / 2; gap > 0; gap /= 2) {
        for (i = n - gap; i >= 0; --i) {
            tmp = arr[i];
            for (j = i; j < n - gap && arr[j + gap] < tmp; j += gap) {
                arr[j] = arr[j + gap];
            }
            arr[j] = tmp;
        }
    }
}
