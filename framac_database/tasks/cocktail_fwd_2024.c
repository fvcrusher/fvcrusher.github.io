void cocktail_fwd(int *arr, int n) {
    int swapped = 1;
    int start = 0;
    int end = n - 1;

    while (swapped > 0) {
        int i, tmp;

        swapped = 0;
        for (i = start; i < end; ++i) {
            if (arr[i] > arr[i + 1]) {
                tmp = arr[i];
                arr[i] = arr[i + 1];
                arr[i + 1] = tmp;
                ++swapped;
            }
        }

        if (!swapped)
            break;
        --end;

        swapped = 0;
        for (i = end - 1; i >= start; --i) {
            if (arr[i] > arr[i + 1]) {
                tmp = arr[i];
                arr[i] = arr[i + 1];
                arr[i + 1] = tmp;
                ++swapped;
            }
        }
        ++start;
    }
}
