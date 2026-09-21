/* span: a non-owning view over a contiguous run of T.
   SPDX-License-Identifier: MIT */

#ifndef T
#error "Template type T undefined for <ctl/span.h>"
#endif

#include <ctl/ctl.h>
#include <assert.h>

#define CTL_SPAN
#define A JOIN(span, T)

typedef struct A
{
    T *data;
    size_t size;
} A;

static inline A JOIN(A, init)(T *data, size_t size)
{
    A self;
    self.data = data;
    self.size = size;
    return self;
}

static inline int JOIN(A, empty)(A *self)
{
    return self->size == 0;
}

static inline T *JOIN(A, data)(A *self)
{
    return self->data;
}

static inline T *JOIN(A, at)(A *self, size_t index)
{
    assert(index < self->size);
    return index < self->size ? &self->data[index] : NULL;
}

static inline T *JOIN(A, front)(A *self)
{
    return JOIN(A, at)(self, 0);
}

static inline T *JOIN(A, back)(A *self)
{
    return self->size ? &self->data[self->size - 1] : NULL;
}

static inline T *JOIN(A, begin)(A *self)
{
    return self->data;
}

static inline T *JOIN(A, end)(A *self)
{
    return self->data + self->size;
}

// A view over [offset, offset + count). count == SIZE_MAX means "to the end".
static inline A JOIN(A, subspan)(A *self, size_t offset, size_t count)
{
    assert(offset <= self->size);
    size_t remaining = self->size - offset;
    if (count > remaining)
        count = remaining;
    return JOIN(A, init)(self->data + offset, count);
}

static inline A JOIN(A, first)(A *self, size_t count)
{
    return JOIN(A, subspan)(self, 0, count);
}

static inline A JOIN(A, last)(A *self, size_t count)
{
    assert(count <= self->size);
    return JOIN(A, subspan)(self, self->size - count, count);
}

#undef A
#undef T
#undef CTL_SPAN
