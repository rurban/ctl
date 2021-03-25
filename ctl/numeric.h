// Optional numeric algorithms
// requested via INCLUDE_NUMERIC
// SPDX-License-Identifier: MIT

// For non-POD T types need a T_inc method.

#undef CTL_NUMERIC
#define CTL_NUMERIC

#if !defined(CTL_USET) && !defined(CTL_SET) && !defined(CTL_PQU)

static inline void JOIN(A, iota)(A *self, T value)
{
    foreach(A, self, i)
    {
#ifdef POD
        *i.ref = value;
        value += 1;
#else
        if (self->free)
            self->free(i.ref);
        // inc already copies the value
        *i.ref = JOIN(T, inc)(&value);
        //value = self->copy(&value);
#endif
    }
}

static inline void JOIN(A, iota_range)(I *range, T value)
{
#ifndef POD
    A* self = range->container;
#endif
    foreach_range_(A, i, range)
    {
#ifdef POD
        *i.ref = value;
        value += 1;
#else
        if (self->free)
            self->free(i.ref);
        *i.ref = JOIN(T, inc)(&value);
#endif
    }
}

#endif // PQU,USET,SET
