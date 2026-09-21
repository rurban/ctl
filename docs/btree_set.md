# btree_set - CTL C Container Template library

Defined in header **<ctl/btree_set.h>**, CTL prefix **btset**.

## SYNOPSIS

    #define POD
    #define T int
    #include <ctl/btree_set.h>

    static int int_compare(int *left, int *right) {
      return (*left > *right) - (*left < *right);
    }

    btset_int values = btset_int_init(int_compare);
    btset_int_insert(&values, 42);
    btset_int_erase(&values, 42);
    btset_int_free(&values);

## DESCRIPTION

`btree_set` is an ordered, unique-value container implemented as a B-tree.
Lookup and insertion descend only one tree path. Insertion and erasure can move
stored values, so references and iterators are invalidated by either operation.

`BTSET_MAX_KEYS` controls the maximum number of keys in a node. It must be an
odd value of at least 3 and defaults to 7. Define it before including the
header to tune node size for a workload. The header undefines the macro after
instantiation.

The compare callback may use either a two-way less-than result or a three-way
negative/zero/positive result. `equal`, when set, determines equivalence;
otherwise two values are equivalent when neither compares less than the other.

## MEMBER FUNCTIONS

    A init(int compare(T*, T*))
    A init_from(A* source)
    void free(A* self)
    void clear(A* self)
    A copy(A* self)
    void swap(A* left, A* right)

`init` constructs an empty B-tree. `init_from` copies callback configuration
only. `copy` duplicates values through `T_copy` for non-POD types.

## LOOKUP

    T* find_value(A* self, T key)
    int contains(A* self, T key)
    size_t count(A* self, T key)
    T* at(A* self, size_t index)
    T* front(A* self)
    T* back(A* self)

`at` exposes sorted positional access. It returns `NULL` for an invalid index.

## MODIFIERS

    T* insert(A* self, T key)
    bool erase(A* self, T key)

`insert` returns the stored value, including an existing equivalent value.
`erase` returns whether it removed a value. Its key is borrowed, not freed.

## ITERATORS

    I begin(A* self)
    I end(A* self)
    void I_next(I* iter)
    int I_done(I* iter)

Iteration is in ascending key order.
