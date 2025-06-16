void cycle_rl(int *arr, int n) {
    int lo, idx, x, i, tmp;
    for (lo = n - 1; lo > 0; --lo) {
        x = arr[lo];
        idx = lo;

        for (i = lo - 1; i >= 0; --i) {
            if (arr[i] > x) {
                --idx;
            }
        }

        if (idx == lo) {
            continue;
        }

        while (x == arr[idx]) {
            --idx;
        }

        if (idx != lo) {
            tmp = arr[idx];
            arr[idx] = x;
            x = tmp;
        }

        while (idx != lo) {
            idx = lo;

            for (i = lo - 1; i >= 0; --i) {
                if (arr[i] > x) {
                    --idx;
                }
            }

            while (x == arr[idx]) {
                --idx;
            }

            if (x != arr[idx]) {
                tmp = arr[idx];
                arr[idx] = x;
                x = tmp;
            }
        }
    }
}
