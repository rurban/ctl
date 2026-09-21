/* flat_map (C++23): sorted contiguous associative container of unique
   key/value pairs.  Like map.h derives from set.h, this derives from
   flat_set.h (remapping the `fset` prefix to `fmap`) and adds the
   key/value-specific insert_or_assign methods.  `T` must be a struct whose
   `compare`/`equal` order by the key only, e.g. the strint pair.
   SPDX-License-Identifier: MIT */

#ifndef T
#error "Template struct type T undefined for <ctl/flat_map.h>"
#endif

#include <ctl/ctl.h>

#define CTL_FLAT_MAP
#define HOLD
#define fset fmap
#include <ctl/flat_set.h>

/* inserts pair, or overwrites the mapped value of an existing equal key */
static inline I JOIN(A, insert_or_assign)(A *self, T pair)
{
    CTL_ASSERT_COMPARE
    size_t i = JOIN(A, _lower_bound_i)(self, &pair);
    if (i < self->size && !self->compare(&pair, &self->vector[i]))
    {
        if (self->free)
            self->free(&self->vector[i]);
        self->vector[i] = pair;
        return JOIN(I, iter)(self, i);
    }
    JOIN(A, insert_index)(self, i, pair);
    return JOIN(I, iter)(self, i);
}

static inline I JOIN(A, insert_or_assign_found)(A *self, T pair, int *foundp)
{
    CTL_ASSERT_COMPARE
    size_t i = JOIN(A, _lower_bound_i)(self, &pair);
    int found = i < self->size && !self->compare(&pair, &self->vector[i]);
    *foundp = found;
    if (found)
    {
        if (self->free)
            self->free(&self->vector[i]);
        self->vector[i] = pair;
        return JOIN(I, iter)(self, i);
    }
    JOIN(A, insert_index)(self, i, pair);
    return JOIN(I, iter)(self, i);
}

#undef fset
#undef A
#undef I
#undef GI
#undef T
#undef POD
#undef NOT_INTEGRAL
#undef CTL_FLAT_MAP
#undef CTL_FLAT_SET
