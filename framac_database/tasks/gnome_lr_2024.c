void gnome_lr(int *arr, int n) {
    int tmp, idx = 0;

    while (idx < n) {
        if (idx == 0) {
            idx++;
        }
        if (arr[idx] >= arr[idx - 1]) {
            idx++;
        } else {
            tmp = arr[idx];
            arr[idx] = arr[idx - 1];
            arr[idx - 1] = tmp;
            idx--;
        }
    }
    return;
}
