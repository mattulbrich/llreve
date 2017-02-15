extern void bubble_sort(int *a, int sz);
extern int rv_mult_int__int_(int, int);
int a[25];

void f_rec(int *a, int *rvp_i) {
    if (!(*rvp_i >= 0))
        return;

    bubble_sort(a, 5);
    *rvp_i = *rvp_i - 1;

    f_rec(a, rvp_i);
}

int f(int *a, int n) {
    int i = n;
    int j = 0;
    f_rec(a, &i);
    return j;
}
