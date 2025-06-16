void oddeven_rl(int *arr, int n) {
    int i, tmp, cnt = 1;
    while (cnt > 0) {
        cnt = 0;
        for (i = n - 1; i > 0; i -= 2) {
            if (arr[i] < arr[i - 1]) {
                tmp = arr[i];
                arr[i] = arr[i - 1];
                arr[i - 1] = tmp;
                ++cnt;
            }
        }
        for (i = n - 2; i > 0; i -= 2) {
            if (arr[i] < arr[i - 1]) {
                tmp = arr[i];
                arr[i] = arr[i - 1];
                arr[i - 1] = tmp;
                ++cnt;
            }
        }
    }
}
