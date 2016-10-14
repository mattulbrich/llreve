/*@ opt -disable-auto-coupling @*/
/*@ opt -disable-auto-abstraction @*/
/*@ opt -couple-functions=g,a @*/
/*@ opt -couple-functions=h,b @*/
/*@ opt -couple-functions=f,f @*/
/*@ opt -fun f @*/
/*@ opt -assume-equivalent=h,b @*/
/*@ opt -assume-equivalent=g,a @*/

// g and a are _not_ equivalent so this tests if we are correctly ignoring the source code if --assume-equivalent=g,a is passed
int a(int x) {
    return x+1;
}
// extern int a(int x);
extern int b(int x);
int f(int x) {
    x = a(x);
    x = b(x);
    return x;
}
