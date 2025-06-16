void gnome_rl(int *arr, int n) {
    int tmp, idx = n - 1;

    while (idx >= 0) {
        if (idx == n - 1) {
            idx--;
        }
        if (arr[idx] <= arr[idx + 1]) {
            idx--;
        } else {
            tmp = arr[idx];
            arr[idx] = arr[idx + 1];
            arr[idx + 1] = tmp;
            idx++;
        }
    }
}
