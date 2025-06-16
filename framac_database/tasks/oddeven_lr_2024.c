void oddeven_lr(int *arr, int n) {
    int i, tmp, cnt = 1;
    while (cnt > 0) {
        cnt = 0;
        for (i = 1; i <= n - 2; i = i + 2) {
            if (arr[i] > arr[i + 1]) {
                tmp = arr[i];
                arr[i] = arr[i + 1];
                arr[i + 1] = tmp;
                ++cnt;
            }
        }
        for (i = 0; i <= n - 2; i = i + 2) {
            if (arr[i] > arr[i + 1]) {
                tmp = arr[i];
                arr[i] = arr[i + 1];
                arr[i + 1] = tmp;
                ++cnt;
            }
        }
    }
}
