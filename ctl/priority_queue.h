/* Its first element is always the greatest of the elements it contains, according to
   some strict weak ordering criterion. deriving from vector.
   SPDX-License-Identifier: MIT */

#ifndef T
#error "Template type T undefined for <ctl/priority_queue.h>"
#endif

#define front top
#define at __AT
#define back __BACK
#define begin __BEGIN
#define end __END
#define set __SET
#define pop_back __POP_BACK
#define wipe __WIPE
#define clear __CLEAR
#define fit __FIT
#define reserve __RESERVE
#define push_back __PUSH_BACK
#define resize __RESIZE
#define assign __ASSIGN
#define shrink_to_fit __SHRINK_TO_FIT
#define data __DATA
#define emplace __EMPLACE
#define insert __INSERT
#define erase __ERASE
#define sort __SORT
#define step __STEP
#define range __RANGE
#define each __EACH
#define remove_if __REMOVE_IF

#define CTL_PQU
#define vec pqu
#define HOLD
#define init __INIT
#include <ctl/vector.h>
#undef init
#undef vec
#undef emplace

#define A JOIN(pqu, T)

static inline A JOIN(A, init)(int _compare(T *, T *))
{
    A self = JOIN(A, __INIT)();
    if (_compare)
        self.compare = _compare;
    else
        _JOIN(A, _set_default_methods)(&self);
    return self;
}

static inline void JOIN(A, up)(A *self, size_t n)
{
    ASSERT(self->compare || !"compare undefined");
    if (n > 0)
    {
        size_t p = (n - 1) / 2;
        T *x = &self->vector[n];
        T *y = &self->vector[p];
        if (self->compare(y, x))
        {
            SWAP(T, x, y);
            JOIN(A, up)(self, p);
        }
    }
}

static inline void JOIN(A, down)(A *self, size_t n)
{
    ASSERT(self->compare || !"compare undefined");
    size_t min = 2;
    if (self->size < min)
        return;
    else if (self->size == min)
    {
        T *a = &self->vector[0];
        T *b = &self->vector[1];
        if (self->compare(a, b))
            SWAP(T, a, b);
    }
    else
    {
        size_t l = 2 * n + 1;
        size_t r = 2 * n + 2;
        if (r < self->size)
        {
            size_t index = self->compare(&self->vector[r], &self->vector[l]) ? l : r;
            T *x = &self->vector[index];
            T *y = &self->vector[n];
            if (self->compare(y, x))
            {
                SWAP(T, x, y);
                JOIN(A, down)(self, index);
            }
        }
    }
}

static inline void JOIN(A, push)(A *self, T value)
{
    JOIN(A, push_back)(self, value);
    JOIN(A, up)(self, self->size - 1);
}

static inline void JOIN(A, pop)(A *self)
{
    SWAP(T, JOIN(A, front)(self), JOIN(A, back)(self));
    JOIN(A, pop_back)(self);
    JOIN(A, down)(self, 0);
}

static inline void JOIN(A, emplace)(A *self, T *value)
{
    JOIN(A, push_back)(self, *value);
    JOIN(A, up)(self, self->size - 1);
    // JOIN(A, it) pos = JOIN(A, begin)(self);
    // JOIN(A, __EMPLACE)(&pos, value);
    // JOIN(A, up)(self, self->size - 1);
}

#undef front
#undef at
#undef back
#undef begin
#undef end
#undef set
#undef pop_back
#undef wipe
#undef clear
#undef fit
#undef reserve
#undef push_back
#undef resize
#undef assign
#undef shrink_to_fit
#undef data
#undef insert
#undef erase
#undef sort
#undef step
#undef range
#undef each
#undef remove_if

#undef T // See HOLD.
#undef POD
#undef NOT_INTEGRAL
#undef A
#define CTL_PQU
