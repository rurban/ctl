# ctl - C Container Template library

Overview manual page for the C Container Template Library.

## SYNOPSIS

    #include <stdio.h>

    #define POD
    #define T int
    #include <ctl/vector.h>

    int compare(int* a, int* b) { return *b < *a; }

    int main(void)
    {
        vec_int a = vec_int_init();
        vec_int_push_back(&a, 9);
        vec_int_push_back(&a, 1);
        vec_int_push_back(&a, 8);
        vec_int_sort(&a, compare);
        foreach(vec_int, &a, it)
            printf("%d\n", *it.ref);
        vec_int_free(&a);
    }

## DESCRIPTION

CTL configures a family of type-safe, header-only containers from a single
template mechanism: `#define T <type>` selects the element type, then
including a container header (`ctl/vector.h`, `ctl/set.h`, ...) instantiates
every method for that type, named with the container's prefix, e.g.
`vec_int_push_back`.

`POD` states that `T` is Plain Old Data (no owned resources). Without `POD`,
`T` must have memory ownership: declare `void T_free(T*)` and
`T T_copy(T*)` before including the container header.

    typedef struct { ... } type;
    void type_free(type*);
    type type_copy(type*);
    #define T type
    #include <ctl/vector.h>

A missing declaration fails to compile with a human-readable error naming the
missing function, e.g. `error: 'type_free' undeclared`.

## CONTAINERS

Each container has its own manual page. Prefix is the identifier used for
every generated function and type name, e.g. `vec_int_size`.

  * vector(3), prefix `vec`: dynamic array, like std::vector.
  * bvector(3), prefix `bvec`: packed boolean vector, one bit per element.
  * array(3), prefix `arrN`: fixed-size array, like std::array.
  * string(3), prefix `str`: byte string, like std::string.
  * deque(3), prefix `deq`: double-ended queue, paged storage.
  * list(3), prefix `list`: doubly-linked list.
  * forward_list(3), prefix `slist`: singly-linked list.
  * priority_queue(3), prefix `pqu`: heap-backed priority queue.
  * queue(3), prefix `queue`: FIFO adapter over deque.
  * stack(3), prefix `stack`: LIFO adapter over deque.
  * set(3), prefix `set`: sorted unique keys, red-black tree.
  * btree_set(3), prefix `btset`: sorted unique keys, B-tree.
  * map(3), prefix `map`: sorted key/value pairs.
  * unordered_set(3), prefix `uset`: hashed unique keys, chained buckets.
  * unordered_map(3), prefix `umap`: hashed key/value pairs.
  * swisstable(3), prefix `swiss_TK_T`: open-addressing hashmap, separate
    key and value types.
  * flat_set(3), prefix `fset`: sorted unique keys in one contiguous vector.
  * flat_multiset(3), prefix `fmset`: like flat_set, duplicates kept.
  * flat_map(3), prefix `fmap`: sorted key/value pairs in one vector.
  * flat_multimap(3), prefix `fmmap`: like flat_map, duplicates kept.
  * inplace_vector(3), prefix `inplace_vecN`: fixed-capacity, inline storage.
  * hive(3), prefix `hive`: stable-reference bucket container.
  * span(3), prefix `span`: non-owning view over a run of `T`.
  * strv(3): non-owning view over `char`, like std::string_view.
  * algorithm(3): generic `<algorithm>`-style free functions.
  * numeric(3): generic `<numeric>`-style free functions.

## SEE ALSO

The full manual, container by container, with complexity guarantees and
performance comparisons against the C++ STL:
https://rurban.github.io/ctl/

Header reference and source: https://github.com/rurban/ctl

## BUGS

Report at https://github.com/rurban/ctl/issues

## AUTHOR

Reini Urban, based on the original glouw/ctl by Gustav Louw.
