extern void bubble_sort(int *a, int sz);
extern int rv_mult_int__int_(int, int);
int a[25];

void f_rec(int *a, int n, int *rvp_i) {
    if (!(*rvp_i <= n))
        return;

    bubble_sort(a, 5);
    (*rvp_i)++;

    f_rec(a, n, rvp_i);
}

int f(int *a, int n) {
    int i = 0;
    int j = 0;
    f_rec(a, n, &i);
    return j;
}
