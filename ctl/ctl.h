#ifndef __CTL_H__
#define __CTL_H__

#include <stdlib.h>
#include <stdint.h>

#define CAT(a, b) a##b

#define PASTE(a, b) CAT(a, b)

#define JOIN(prefix, name) PASTE(prefix, PASTE(_, name))

/* iterator with extra B nodes */
#define CTL_COMMONFIELDS_ITER \
    B* next;                  \
    T* ref;                   \
    void (*step)(struct I*);  \
    B* end;                   \
    int done;                 \
    B* node

/* iterator with simple arrays of T, no intermediate nodes of B */
#define CTL_VECTORFIELDS_ITER \
    T* next;                  \
    T* ref;                   \
    void (*step)(struct I*);  \
    T* end;                   \
    int done

#define SWAP(TYPE, a, b) { TYPE temp = *(a); *(a) = *(b); *(b) = temp; }

#define foreach(a, b, c) for(JOIN(a, it) c = JOIN(JOIN(a, it), each) (b); !c.done; c.step(&c))

#define len(a) (sizeof(a) / sizeof(*(a)))

#define LOG(...) fprintf(stderr, __VA_ARGS__)

#endif
