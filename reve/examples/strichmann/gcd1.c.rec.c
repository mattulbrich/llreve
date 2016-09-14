void swap(short *a, short *b) {
    short tmp = *a;
    *a = *b;
    *b = tmp;
}

unsigned char gcdRec(short *rvp_a, short *rvp_b) {
    if (!(*rvp_a != 0)) {
        return 0;
    }
    *rvp_b = *rvp_b % *rvp_a;
    swap(&*rvp_a, &*rvp_b);
    *rvp_a = *rvp_a;
    return gcdRec(rvp_a, rvp_b);
}

short gcd(short *a, short *b) {
    short rvretval = 0;
    gcdRec(a, b);
    // a = 5;
    return *b;
}
