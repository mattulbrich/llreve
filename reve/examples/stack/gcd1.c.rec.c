void swap(short *a, short *b) {
    short tmp = *a;
    *a = *b;
    *b = tmp;
}


unsigned char Loop_gcd_while1(short *rvp_a, short *rvp_b, short *rvp_rvretval) {
    if (!(*rvp_a != 0))
        return 0;
    *rvp_b = *rvp_b % *rvp_a;
    swap(&*rvp_a, &*rvp_b);
    *rvp_a = *rvp_a;
    return Loop_gcd_while1(rvp_a, rvp_b, rvp_rvretval);
}

short gcd(short a, short b) {
    short rvretval = 0;
    Loop_gcd_while1(&a, &b, &rvretval);
    a = 5;
    return b;
}
