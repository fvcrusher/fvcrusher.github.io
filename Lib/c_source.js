export class CSource
{
    #source_code = null;
    #clear_source_code = null;
    #function_name = null;

    static #remove_comments(source_code)
    {
        let resulting_code = "";
        for (let idx = 0; idx < source_code.length; idx++)
        {
            if (source_code.slice(idx).startsWith("//"))
            {
                while (idx < source_code.length && !(source_code[idx] == "\n"))
                    idx++;
            }

            else if (source_code.slice(idx).startsWith("/*"))
            {
                while (idx < source_code.length && !(source_code.slice(idx).startsWith("*/")))
                    idx++;
                idx += 2;
            }

            resulting_code += source_code[idx];
        }

        return resulting_code;
    }

    static #remove_voids(source_code)
    {
        let no_empty_lines = source_code.replace(/\n[\s]*\n/g, "\n").trim();
        return no_empty_lines;
    }

    static #remove_preproc_directives(source_code)
    {
        let no_preproc_directives = source_code.replace(/#[^\n]+?\n/g, "");
        return no_preproc_directives;
    }

    static #format_source(source_code)
    {
        let without_comments = CSource.#remove_comments(source_code);
        let without_preproc_directives = CSource.#remove_preproc_directives(without_comments);
        let clear = CSource.#remove_voids(without_preproc_directives);
        return clear.trim();
    }

    static #get_function_name(source_code)
    {
        let result = /(?:void|int|float|char|bool|signed|unsigned|short|long|double)(?: (?:void|int|float|char|bool|signed|unsigned|short|long|double))* (?<function_name>\w+?)\(/g.exec(source_code);
        if (result == null)
            return "";
        return result[1];
    }

    constructor(source_code)
    {
        this.#source_code = source_code;
        this.#clear_source_code = CSource.#format_source(source_code);
        this.#function_name = CSource.#get_function_name(this.clear_source_unformatted);
    }

    get source()
    {
        return this.#source_code;
    }

    get clear_source()
    {
        return this.#clear_source_code;
    }

    static #unformat_source(source)
    {
        return source.replace(/\s+/g, " ").replace(/ ?([;,=+\-\{\}\[\]\(\)<>|&*!]) ?/g, "$1").trim();
    }

    get clear_source_unformatted()
    {
        return CSource.#unformat_source(this.#clear_source_code);
    }

    get function_name()
    {
        return this.#function_name;
    }

    get hash()
    {
        let p = 31;
        let m = 1e9 + 9;
        let p_pow = 1;

        let hash = 0;

        let str_value = this.clear_source_unformatted

        for (let idx = 0; idx < str_value.length; idx++)
        {
            hash = (hash + str_value.charCodeAt(idx) * p_pow) % m;
            p_pow = (p_pow * p) % m;
        }

        return hash.toString();
    }

    get source_id()
    {
        return this.#function_name + this.hash;
    }
}


// let s1 = new CSource("// Split -> Split -> CVC4 -> Auto level 1\n/*@ predicate BeginLower(int* arr, integer n, integer slice) =\n  @   \\forall integer i, j; 0 <= i <= slice && i <= j <= n - 1 ==> arr[i] <= arr[j];\n  @\n  @ predicate EndGreater(int* arr, integer n, integer slice) =\n  @   \\forall integer i, j; 0 <= i <= j && slice <= j <= n - 1 ==> arr[i] <= arr[j];\n  @\n  @ predicate SubseqSorted(int* arr, integer start, integer end) =\n  @   \\forall integer i, j; start <= i <= j <= end ==> arr[i] <= arr[j];\n  @\n  @ predicate Sorted(int* arr, integer n) =\n  @   SubseqSorted(arr, 0, n-1);\n  @\n  @ predicate Swap{L1, L2}(int* arr, integer n, integer i, integer j) =\n  @   0 <= i < n && 0 <= j < n &&\n  @   \\at(arr[i], L1) == \\at(arr[j], L2) &&\n  @   \\at(arr[j], L1) == \\at(arr[i], L2) &&\n  @   \\forall integer k; 0 <= k < n && k != j && k != i ==>\n  @     \\at(arr[k], L1) == \\at(arr[k], L2);\n  @\n  @ inductive Permut{L1, L2}(int* arr, integer n){\n  @   case PermutRefl{L1}:\n  @     \\forall int* arr, integer n; \n  @       Permut{L1, L1}(arr, n);\n  @   case PermutSym{L1, L2}:\n  @     \\forall int* arr, integer n, i, j;\n  @       Permut{L1, L2}(arr, n) ==> Permut{L2, L1}(arr, n);\n  @   case PermutSwap{L1, L2}:\n  @     \\forall int* arr, integer n, i, j; \n  @       Swap{L1, L2}(arr, n, i, j) ==> Permut{L1, L2}(arr, n);\n  @   case PermutTrans{L1, L2, L3}:\n  @     \\forall int* arr, integer n;\n  @       Permut{L1, L2}(arr, n) && Permut{L2, L3}(arr, n) ==> Permut{L1, L3}(arr, n);\n  @ }\n  @*/\n\n/*@ requires \\valid(arr + (0..n));\n  @ requires n > 0;\n  @\n  @ ensures Sorted(arr, n);\n  @ ensures Permut{Pre, Post}(arr, n);\n  @*/\nvoid cocktail_back(int *arr, int n) {\n    int swapped = 1;\n    int start = 0;\n    int end = n - 1;\n\n    /*@ loop invariant 0 <= start <= end + 1 <= n;\n      @\n      @ loop invariant swapped >= 0;\n      @ loop invariant start > end ==> swapped == 0;\n      @ loop invariant swapped == 0 ==> Sorted(arr, n);\n      @\n      @ loop invariant BeginLower(arr, n, start - 1);\n      @ loop invariant EndGreater(arr, n, end + 1);\n      @\n      @ loop invariant Permut{Pre, Here}(arr, n);\n      @\n      @ loop variant end - start;\n      @*/\n    while (swapped > 0) {\n        int i, tmp;\n\n        //@ assert Permut{Pre, Here}(arr, n);\n\n        swapped = 0;\n        /*@ loop invariant start - 1 <= i <= end - 1;\n          @\n          @ loop invariant 0 <= swapped <= end - i - 1;\n          @ loop invariant swapped == 0 ==> SubseqSorted(arr, i + 1, n - 1);\n          @\n          @ loop invariant BeginLower(arr, n, start - 1);\n          @ loop invariant EndGreater(arr, n, end + 1);\n          @ loop invariant \\forall integer j; \n          @   start - 1 <= i < j <= n - 1 ==> arr[i + 1] <= arr[j];\n          @\n          @ loop invariant Permut{Pre, Here}(arr, n);\n          @\n          @ loop variant i;\n          @*/\n        for (i = end - 1; i >= start; --i) {\n            //@ ghost first: ;\n            if (arr[i] > arr[i + 1]) {\n                tmp = arr[i];\n                arr[i] = arr[i + 1];\n                arr[i + 1] = tmp;\n                ++swapped;\n                //@ assert Swap{first, Here}(arr, n, i, i+1);\n            }\n        }\n\n        //@ assert BeginLower(arr, n, start);\n        //@ assert swapped == 0 ==> Sorted(arr, n);\n\n        if (!swapped)\n            break;\n        ++start;\n\n        //@ assert SubseqSorted(arr, 0, start) && Permut{Pre, Here}(arr, n);\n\n        swapped = 0;\n        /*@ loop invariant start <= i <= end;\n          @\n          @ loop invariant 0 <= swapped <= i - start;\n          @ loop invariant swapped == 0 ==> SubseqSorted(arr, 0, i);\n          @\n          @ loop invariant BeginLower(arr, n, start - 1);\n          @ loop invariant EndGreater(arr, n, end + 1);\n          @ loop invariant \\forall integer j; \n          @   0 <= j <= i <= end ==> arr[j] <= arr[i];\n          @\n          @ loop invariant Permut{Pre, Here}(arr, n);\n          @\n          @ loop variant end - i;\n          @*/\n        for (i = start; i < end; ++i) {\n            //@ ghost second: ;\n            if (arr[i] > arr[i + 1]) {\n                tmp = arr[i];\n                arr[i] = arr[i + 1];\n                arr[i + 1] = tmp;\n                ++swapped;\n                //@ assert Swap{second, Here}(arr, n, i, i+1);\n            }\n            //@ assert \\forall integer j; start - 1 <= j <= n - 1 ==> arr[start - 1] <= arr[j];\n        }\n        --end;\n        //@ assert swapped == 0 ==> Sorted(arr, n);\n    }\n}")
// let s2 = new CSource("/*@ predicate swap_in_array{L1,L2}(int* a, integer b, integer e, integer i, integer j) =\n        b <= i < e && b <= j < e &&\n        \\at(a[i], L1) == \\at(a[j], L2) &&\n        \\at(a[j], L1) == \\at(a[i], L2) &&\n        \\forall integer k; b <= k < e && k != j && k != i ==>\n            \\at(a[k], L1) == \\at(a[k], L2);\n\n    inductive permutation{L1,L2}(int* a, integer b, integer e){\n    case reflexive{L1}:\n        \\forall int* a, integer b,e ; permutation{L1,L1}(a, b, e);\n    case swap{L1,L2}:\n        \\forall int* a, integer b,e,i,j ;\n            swap_in_array{L1,L2}(a,b,e,i,j) ==> permutation{L1,L2}(a, b, e);\n    case transitive{L1,L2,L3}:\n        \\forall int* a, integer b,e ;\n            permutation{L1,L2}(a, b, e) && permutation{L2,L3}(a, b, e) ==>\n                permutation{L1,L3}(a, b, e);\n    }\n*/\n\n/*@ predicate sorted(int *t, integer a, integer b) =\n        \\forall integer i, j; a <= i <= j <= b ==> t[i] <= t[j];\n*/\n\n/*@ requires \\valid(arr + (0 .. n));\n    requires n > 0;\n    assigns arr[0 .. n];\n    ensures sorted(arr, 0, n-1);\n    ensures permutation{Pre, Post}(arr,0,n);\n*/\nvoid cocktail_back(int *arr, int n) {\n    int swapped = 1;\n    int start = 0;\n    int end = n - 1;\n\n    /*@ loop invariant 0 <= start <= end+1;\n        loop invariant start-1 <= end <= n-1;\n        loop invariant start > end ==> swapped == 0;\n        loop invariant swapped == 0 ==> sorted(arr, 0, n-1);\n        loop invariant \\forall integer i, j;\n            0 <= i <= start-1 && i <= j <= n-1 ==> arr[i] <= arr[j];\n        loop invariant \\forall integer i, j;\n            end+1 <= i <= n-1 && 0 <= j <= i ==> arr[j] <= arr[i];\n        loop invariant swapped >= 0;\n        loop invariant permutation{Pre, Here}(arr,0,n);\n        loop variant end - start + 1;\n    */\n    while (swapped > 0) {\n        int i, tmp;\n\n        //@ assert permutation{Pre, Here}(arr,0,n);\n\n        swapped = 0;\n        /*@ loop invariant start-1 <= i <= end-1;\n            loop invariant 0 <= swapped <= end - i - 1;\n            loop invariant \\forall integer j; \n                i < j <= n-1 ==> arr[i + 1] <= arr[j];\n            loop invariant \\forall integer i, j;\n                0 <= i <= start-1 && i <= j <= n-1 ==> arr[i] <= arr[j];\n            loop invariant \\forall integer i, j;\n                end+1 <= i <= n-1 && 0 <= j <= i ==> arr[j] <= arr[i];\n            loop invariant swapped == 0 ==> sorted(arr, i+1,n-1);\n            loop invariant permutation{Pre, Here}(arr,0,n);\n            loop variant i+1;\n        */\n        for (i = end - 1; i >= start; --i) {\n            //@ ghost begin1: ;\n            if (arr[i] > arr[i + 1]) {\n                tmp = arr[i];\n                arr[i] = arr[i + 1];\n                arr[i + 1] = tmp;\n                ++swapped;\n                //@ assert swap_in_array{begin1,Here}(arr,0,n,i,i+1);\n            }\n        }\n\n        /*@ assert \\forall integer i, j; \n            0 <= i <= start && i <= j <= n-1 ==> arr[i] <= arr[j];\n        */\n\n        //@ assert swapped == 0 ==> sorted(arr, 0, n-1);\n\n        if (!swapped)\n            break;\n        ++start;\n\n        //@ assert sorted(arr, 0, start) && permutation{Pre, Here}(arr,0,n);\n\n        swapped = 0;\n        /*@ loop invariant start <= i <= end;\n            loop invariant 0 <= swapped <= i - start;\n            loop invariant \\forall integer j; \n                0 <= j <= i ==> arr[j] <= arr[i];\n            loop invariant \\forall integer i, j;\n                0 <= i <= start-1 && i <= j <= n-1 ==> arr[i] <= arr[j];\n            loop invariant \\forall integer i, j;\n                end+1 <= i <= n-1 && 0 <= j <= i ==> arr[j] <= arr[i];\n            loop invariant swapped == 0 ==> sorted(arr, 0, i);\n            loop invariant permutation{Pre, Here}(arr,0,n);\n            loop variant (end - i);\n        */\n        for (i = start; i < end; ++i) {\n            //@ ghost begin2: ;\n            if (arr[i] > arr[i + 1]) {\n                tmp = arr[i];\n                arr[i] = arr[i + 1];\n                arr[i + 1] = tmp;\n                ++swapped;\n                //@ assert swap_in_array{begin2,Here}(arr,0,n,i,i+1);\n            }\n        /*@ assert \\forall integer j; \n                start-1 <= j <= n-1 ==> arr[start-1] <= arr[j];\n        */\n        }\n        --end;\n        //@ assert swapped == 0 ==> sorted(arr, 0, n-1);\n    }\n}\n")

// console.log(s1.hash == s2.hash)
// console.log(s2.hash)

// let s = new CSource("#include <limits.h>\n\n/*@\n  @ predicate valid_mtx(int ** mat, int n, int m) =\n  @     \\forall int i;\n  @         (0 <= i < n) ==> \\valid_read(mat[i] + (0..m-1));\n  @\n  @ predicate tmp_value_exists(int** mtx, integer n, integer m, int tmp) =\n  @    \\exists integer j, i; 0 <= j < n && 0 <= i < m && mtx[j][i] == tmp;\n  @\n  @ predicate tmp_is_min{L}(int** mtx, integer left_r, integer right_r, integer left_c, integer right_c, int tmp) =\n  @     \\forall integer j, i; left_r <= j < right_r && left_c <= i < right_c ==> mtx[j][i] >= tmp;\n  @\n  @ predicate tmp_is_max{L}(int** mtx, integer left_r, integer right_r, integer left_c, integer right_c, int tmp) =\n  @     \\forall integer j, i; left_r <= j < right_r && left_c <= i < right_c ==> mtx[j][i] <= tmp;\n  @  \n  @ lemma minimum_for_quadrant_of_mtx{L}:\n  @   \\forall int** mtx, integer n, i, j, mmin;\n  @    j < n && \n  @    (\\forall integer k; 0 <= k < j && k % 2 == 0 ==> mmin <= mtx[k][i]) && \n  @    (\\forall integer k; 0 <= k < n && k % 2 == 1 ==> mmin <= mtx[k][i]) ==>\n  @      (\\forall integer k; 0 <= k < j ==> mmin <= mtx[k][i]);\n  @\n  @ lemma maximum_for_quadrant_of_mtx{L}:\n  @   \\forall int** mtx, integer n, i, j, mmax;\n  @    j < n && \n  @    (\\forall integer k; 0 <= k < j && k % 2 == 0 ==> mmax >= mtx[k][i]) && \n  @    (\\forall integer k; 0 <= k < n && k % 2 == 1 ==> mmax >= mtx[k][i]) ==>\n  @      (\\forall integer k; 0 <= k < j ==> mmax >= mtx[k][i]);\n  @\n  @ lemma transitivity_of_minimum{L}:\n  @  \\forall int** mtx, int tmp, mmin, integer n, i;\n  @    (tmp_is_min(mtx, 0, n, 0, i, mmin) && tmp < mmin) ==>\n  @      tmp_is_min(mtx, 0, n, 0, i, tmp);\n  @\n  @ lemma transitivity_of_maximum{L}:\n  @  \\forall int** mtx, int tmp, mmax, integer n, i;\n  @    (tmp_is_max(mtx, 0, n, 0, i, mmax) && tmp > mmax) ==>\n  @      tmp_is_max(mtx, 0, n, 0, i, tmp);\n  @*/\n\n\n/*@\n  @ requires 0 < n < INT_MAX && 0 < m < INT_MAX;\n  @ requires \\valid(min);\n  @ requires \\valid(max);\n  @ requires \\valid_read(mat + (0..n-1));\n  @ requires valid_mtx(mat, n, m);\n  @\n  @ assigns *min, *max;\n  @\n  @ ensures \\forall integer i, j; 0 <= i < n && 0 <= j < m ==> mat[i][j] == \\old(mat[i][j]);\n  @\n  @ ensures tmp_value_exists(mat, n, m, *min);\n  @ ensures tmp_value_exists(mat, n, m, *max);\n  @\n  @ ensures tmp_is_min(mat, 0, n, 0, m, *min);\n  @ ensures tmp_is_max(mat, 0, n, 0, m, *max);\n  @*/\nvoid mat_minmax_11(int **mat, int n, int m, int *min, int *max) {\n  int mmin = mat[0][0];\n  int mmax = mat[0][0];\n  //@assert mmin == mat[0][0];\n  //@assert mmax == mat[0][0];\n\n  /*@\n    @ loop invariant 0 <= i <= m;\n    @ loop invariant mmax >= mmin;\n    @\n    @ loop invariant tmp_value_exists(mat, n, m, mmin);\n    @ loop invariant tmp_value_exists(mat, n, m, mmax);\n    @\n    @ loop invariant tmp_is_min(mat, 0, n, 0, i, mmin);\n    @ loop invariant tmp_is_max(mat, 0, n, 0, i, mmax);\n    @\n    @ loop assigns mmin, mmax, i;\n    @ loop variant m - i;\n    @*/\n  for (int i = 0; i < m; ++i) {   \n    //@ assert tmp_is_min(mat, 0, n, 0, i, mmin);\n    //@ assert tmp_is_max(mat, 0, n, 0, i, mmax);\n    \n    /*@\n      @ loop invariant 1 <= j <= n + 1;\n      @ loop invariant mmax >= mmin;\n      @\n      @ loop invariant j % 2 == 1;\n      @\n      @ loop invariant tmp_value_exists(mat, n, m, mmin);\n      @ loop invariant tmp_value_exists(mat, n, m, mmax);\n      @\n      @ loop invariant tmp_is_min(mat, 0, n, 0, i, mmin);\n      @ loop invariant tmp_is_max(mat, 0, n, 0, i, mmax);\n      @\n      @ loop invariant \\forall integer k; 1 <= k < j && k % 2 == 1 ==> mmin <= mat[k][i];\n      @ loop invariant \\forall integer k; 1 <= k < j && k % 2 == 1 ==> mmax >= mat[k][i];\n      @\n      @ loop assigns mmin, mmax, j;\n      @ loop variant n - j + 1;\n      @*/\n    for (int j = 1; j < n; j += 2) {\n      int v = mat[j][i];\n      //@ assert tmp_value_exists(mat, n, m, v);\n      //@ assert tmp_is_min(mat, 0, n, 0, i, mmin);\n      //@ assert tmp_is_max(mat, 0, n, 0, i, mmax);\n      //@ assert mmax >= mmin;\n\n      if (v < mmin) {\n        //@ assert tmp_is_min(mat, 0, n, 0, i, mmin) && v < mmin;\n        //@ assert tmp_is_min(mat, 0, n, 0, i, mmin) && v < mmin ==> tmp_is_min(mat, 0, n, 0, i, v);\n        mmin = v;\n        //@ assert \\forall integer k; 1 <= k <= j && k % 2 == 1 ==> mmin <= mat[k][i];\n        //@ assert tmp_is_min(mat, 0, n, 0, i, mmin);\n      } else if (v > mmax) {\n        //@ assert tmp_is_max(mat, 0, n, 0, i, mmax) && v > mmax;\n        //@ assert tmp_is_max(mat, 0, n, 0, i, mmax) && v > mmax ==> tmp_is_max(mat, 0, n, 0, i, v);\n        mmax = v;\n        //@ assert \\forall integer k; 1 <= k <= j && k % 2 == 1 ==> mmax >= mat[k][i];\n        //@ assert tmp_is_max(mat, 0, n, 0, i, mmax);\n      }\n      //@ assert tmp_is_min(mat, 0, n, 0, i, mmin);\n      //@ assert tmp_is_max(mat, 0, n, 0, i, mmax);\n    }\n\n    //@ assert \\forall integer k; 0 <= k < n && k % 2 == 1 ==> mmin <= mat[k][i];\n    //@ assert \\forall integer k; 0 <= k < n && k % 2 == 1 ==> mmax >= mat[k][i];\n    //@ assert tmp_is_min(mat, 0, n, 0, i, mmin);\n    //@ assert tmp_is_max(mat, 0, n, 0, i, mmax);\n    //@ assert mmax >= mmin;\n    //@ assert \\forall integer k, l; 0 <= k < n && 0 <= l < m ==> mat[k][l] == \\at(mat[k][l], Pre);\n\n    /*@ \n      @ loop invariant 0 <= j <= n + 1;\n      @ loop invariant mmax >= mmin;\n      @ loop invariant j % 2 == 0;\n      @ loop invariant tmp_value_exists(mat, n, m, mmin);\n      @ loop invariant tmp_value_exists(mat, n, m, mmax);\n      @\n      @ loop invariant tmp_is_min(mat, 0, n, 0, i, mmin);\n      @ loop invariant tmp_is_max(mat, 0, n, 0, i, mmax);\n      @\n      @ loop invariant \\forall integer k; 0 <= k < j && k % 2 == 0 ==> mmin <= mat[k][i];\n      @ loop invariant \\forall integer k; 0 <= k < n && k % 2 == 1 ==> mmin <= mat[k][i];\n      @ loop invariant \\forall integer k; 0 <= k < j < n ==> mmin <= mat[k][i];\n      @\n      @ loop invariant \\forall integer k; 0 <= k < j && k % 2 == 0 ==> mmax >= mat[k][i];\n      @ loop invariant \\forall integer k; 0 <= k < n && k % 2 == 1 ==> mmax >= mat[k][i];\n      @ loop invariant \\forall integer k; 0 <= k < j < n ==> mmax >= mat[k][i];\n      @\n      @ loop assigns mmin, mmax, j;\n      @ loop variant n - j + 1;\n      @*/\n      for (int j = 0; j < n; j += 2) {\n        int v = mat[j][i];\n        //@ assert tmp_value_exists(mat, n, m, v);\n        //@ assert tmp_is_min(mat, 0, n, 0, i, mmin);\n        //@ assert tmp_is_max(mat, 0, n, 0, i, mmax);\n        //@ assert mmax >= mmin;\n\n        if (v < mmin) {\n          //@ assert tmp_is_min(mat, 0, n, 0, i, mmin) && v < mmin ==> tmp_is_min(mat, 0, n, 0, i, v);\n          mmin = v;\n          //@ assert \\forall integer k; 0 <= k <= j && k % 2 == 0 ==> mmin <= mat[k][i];\n          //@ assert \\forall integer k; 0 <= k < n && k % 2 == 1 ==> mmin <= mat[k][i];\n          //@ assert \\forall integer k; 0 <= k <= j ==> mmin <= mat[k][i];\n          //@ assert tmp_is_min(mat, 0, n, 0, i, mmin);\n        } else if (v > mmax) {\n          //@ assert tmp_is_max(mat, 0, n, 0, i, mmax) && v > mmax ==> tmp_is_max(mat, 0, n, 0, i, v);\n          mmax = v;\n          //@ assert \\forall integer k; 0 <= k <= j && k % 2 == 0 ==> mmax >= mat[k][i];\n          //@ assert \\forall integer k; 0 <= k < n && k % 2 == 1 ==> mmax >= mat[k][i];\n          //@ assert \\forall integer k; 0 <= k <= j ==> mmax >= mat[k][i];\n          //@ assert tmp_is_max(mat, 0, n, 0, i, mmax);\n        }\n        //@ assert tmp_is_min(mat, 0, n, 0, i, mmin);\n        //@ assert tmp_is_max(mat, 0, n, 0, i, mmax);\n      }\n      \n    //@ assert \\forall integer k; 0 <= k < n ==> mmin <= mat[k][i];\n    //@ assert \\forall integer k; 0 <= k < n ==> mmax >= mat[k][i];\n\n    //@ assert tmp_is_min(mat, 0, n, 0, i + 1, mmin);\n    //@ assert tmp_is_max(mat, 0, n, 0, i + 1, mmax);\n  }\n\n  //@ assert tmp_value_exists(mat, n, m, mmin);\n  //@ assert tmp_value_exists(mat, n, m, mmax);\n  *min = mmin;\n  *max = mmax;\n}")
// console.log(s.clear_source)
