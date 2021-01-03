# set_T_free (set_T* self) - CTL - C Container Template library

Defined in header [**<ctl/set.h>**](../set.md)

# SYNOPSIS

    static inline int
    int_cmp(int a, int b) {
      return a < b;
    }

    #undef POD
    #define T int
    #include <ctl/set.h>

    set_int a = set_int_init (int_cmp);

# DESCRIPTION

Constructs a new set container from a user supplied comparison function object T_cmp.
# SEEALSO

[map_T_free](../map/free.md) `(map_T* self)`
