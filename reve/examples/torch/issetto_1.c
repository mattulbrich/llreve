extern int __mark(int);
// we don’t support floating points so use an int here
#define real int
#define TH_CONCAT_4_EXPAND(x,y,z,w) x ## y ## z ## w
#define TH_CONCAT_4(x,y,z,w) TH_CONCAT_4_EXPAND(x,y,z,w)
#define THTensor_(NAME)   TH_CONCAT_4(TH,Real,Tensor_,NAME)

typedef struct THAllocator {
  void* (*malloc)(void*, long);
  void* (*realloc)(void*, void*, long);
  void (*free)(void*, void*);
} THAllocator;

typedef struct THStorage
{
    real *data;
    long size;
    int refcount;
    char flag;
    THAllocator *allocator;
    void *allocatorContext;
    struct THStorage *view;
} THStorage;

typedef struct THTensor
{
    long *size;
    long *stride;
    int nDimension;

    THStorage *storage;
    long storageOffset;
    int refcount;

    char flag;

} THTensor;

int THTensor_(isSetTo)(const THTensor *self, const THTensor* src)
{
  if (self->storage == src->storage &&
      self->storageOffset == src->storageOffset &&
      self->nDimension == src->nDimension)
  {
    int d;
    for (d = 0; __mark(42) & (d < self->nDimension); ++d)
    {
      if (self->size[d] != src->size[d] || self->stride[d] != src->stride[d])
        return 0;
    }
    return 1;
  }
  return 0;
}
