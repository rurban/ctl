#include <assert.h>
#include <ctl/bvector.h>
int main(void) { bvec v = bvec_init(); for (size_t i = 0; i < 130; i++) bvec_push_back(&v, i % 3 == 0); assert(v.size == 130); assert(v.capacity == 256); for (size_t i = 0; i < 130; i++) assert(bvec_at(&v, i) == (i % 3 == 0)); bvec_set(&v, 64, true); assert(bvec_at(&v, 64)); bvec_pop_back(&v); assert(v.size == 129); bvec_free(&v); }