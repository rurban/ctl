# set_T_init (int T_compare(T*, T*)) - CTL - C Container Template library

Defined in header [**<ctl/set.h>**](../set.md)

# SYNOPSIS

    static inline int
    int_cmp(int *a, int *b) {
      return *a < *b;
    }

    #undef POD
    #define T int
    #include <ctl/set.h>

    set_int a = set_int_init (int_cmp);

# DESCRIPTION

Constructs a new set container from a user supplied comparison function object
`int T_cmp (T* a, T* b)`.

# SEEALSO

[map_T_init](../map/init.md) (int T_compare(T*, T*))
