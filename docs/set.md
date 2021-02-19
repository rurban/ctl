# set - CTL - C Container Template library

Defined in header **<ctl/set.h>**, CTL prefix **set**,
parent for [map](map.md).

## SYNOPSIS

    static inline int
    int_cmp(int *a, int *b) {
      return *a < *b;
    }

    #define POD
    #define T int
    #include <ctl/set.h>

    int i = 0;
    set_int a = set_int_init (int_cmp);

    for (i=0; i<1000; i++) {
      set_int_insert (&a, i);
    }

    foreach(set_int, &a, it) { i = it.ref->key); }
    printf("last key %d, ", i);

    printf("min {\"%s\", %d} ", set_int_min (a));
    printf("max {\"%s\", %d}\n", set_int_max (a));
    set_int_free(&a);

## DESCRIPTION

**set** is a sorted associative container that contains unique values.
Values are sorted by using the custom comparison function `compare`. Search, removal,
and insertion operations have logarithmic complexity. set is implemented as **red-black tree**.

The function names are composed of the prefix **set_**, the user-defined type
**T** and the method name. E.g `set_int` with `#define T int`.

Everywhere the CTL uses the Compare requirements, uniqueness is
determined by using the equivalence relation. In imprecise terms, two objects
`a` and `b` are considered equivalent (not unique) if neither compares less than the
other: `!compare(a, b) && !compare(b, a)`. _(Which obviously fails with double nan)_

Note that **find** does not use this double comparison, rather a single compare
or optional equal call. For simple integral types this always works, as the
default equal method is always set, but for non-POD types with the default 2-way
compare method (`*a < *b`) you may want to set a proper equal method by yourself.

**Three-way comparison** (`<=>`, i.e. `*a < *b ? -1 : *a == *b ? 0 : 1`) is
permitted only with pure set functions (find, erase), but not with any generic
algorithm methods. Supporting three-way comparison bedises the default two-way
`operator<` comparison is too costly there.

## Member types

`T`                     value type

`A` being `set_T`       container type

`B` being `set_T_node`  node type

`I` being `set_T_it`    iterator type

## Member functions

    A init (int compare(T*, T*))

constructs the set.

    free (A* self)

destructs the set.

    assign (A* self, A* other)

replaces the contents of the container.

    A copy (A* self)

returns a copy of the container.

## Element access

    T* at (A* self, size_t index)

access specified element with bounds checking

## Iterators

    I begin (A* self)

constructs an iterator to the beginning

    I end (A* self)

constructs an iterator to the end.

    I* next (I* iter)

Advances the iterator by 1 forwards. There's no prev yet.

    I* advance (I* iter, long i)

All our variants accepts negative `i` to move back. The return value may be ignored.


See [iterators](iterators.md) for more.

## Capacity

    int empty (A* self)

checks whether the container is empty

    size_t size (A* self)

returns the number of elements

    size_t max_size ()

returns the maximum possible number of elements, hard-coded to 2GB (32bit).

## Modifiers

    clear (A* self)

clears the contents

    B* insert (A* self, T value)
    B* insert_found (A* self, T value, int *foundp)
    insert_range (A* self, I* range)

inserts the element(s). (C++17)

    insert_generic (A* self, GI* range2)

inserts copies of values from generic range2. _(NYI)_

    emplace (A* self, T* value)

constructs elements in-place. _(NYI)_

    emplace_hint (A* self, B* pos, T* value)

constructs elements in-place at position. _(NYI)_

    erase (A* self, T value)

erases the element by value.

    erase_it (I* pos)

erases the element at pos.

    I* erase_range (I* range)

erases elements.

    erase_generic (A* self, GI* range)

erases elements by value from another container.

    swap (A* self, A* other)

swaps the contents

    extract (A* self, T key)

extracts a node from the container. _(NYI)_

    extract_it (I* pos)

extracts nodes from the container. _(NYI)_

    merge (A* self)

splices nodes from another container _(NYI)_

## Lookup

    size_t count (A* self)

returns the number of elements matching specific key.

    I find (A* self, T key)
    B* find_node (A* self, T key)

finds element with specific key. does not consume/delete the key.
see above the problem with a simple 2-way compare method.

    bool find_range (I* range, T key)

finds element in range, and sets range to the found element or the end.
it does not iterate over the range, but checks if the found element is within
the range.

    bool contains (A* self, T key)

checks if the container contains an element with specific key. (C++20)

    equal_range (A* self, T key, I* lower_bound, I* upper_bound)

returns `lower_bound` and `upper_bound` ranges for the key. Different to the
[algorithm](algorithm.md) `equal_range` function.

    I lower_bound (A* self, T key)

returns an iterator to the first element not less than the given key.

    I upper_bound (A* self, T key)

returns an iterator to the first element greater than the given key.

## Observers

    FN value_comp (A* self)

Returns the function that compares keys in objects of type value_type T. _(NYI)_

## Non-member functions

    swap (A* self)

specializes the swap algorithm

    size_t remove_if (A* self, int match(T*))

Removes all elements satisfying specific criteria.

    size_t erase_if (A* self, int match(T*))

erases all elements satisfying specific criteria. (C++20) _(NYI)_

    A intersection (A* self, A* other)
    A union (A* self, A* other)
    A difference (A* self, A* other)
    A symmetric_difference (A* self, A* other)

    bool all_of (A* self, int _match(T*)) (C++11)
    bool any_of `(A* self, int _match(T*)) (C++11)
    bool none_of (A* self, int _match(T*)) (C++11)
    bool all_of_range (I* range, int _match(T*))
    bool any_of_range (I* range, int _match(T*))
    bool none_of_range (I* range, int _match(T*))

    foreach (A, self, iter) {...}
    foreach_range (A, iter, first, last) {...}
    foreach_range_ (A, iter, range) {...}

    size_t count (A* self, T value)
    size_t count_if (A* self, int _match(T*))
    size_t count_range (I* range, T value) (C++20)
    size_t count_if_range (I* range, int _match(T*)) (C++20)

    find (A* self, T key)
    find_if (A* self, int _match(T*))
    find_if_not (A* self, int _match(T*)) (C++11)
    find_range (I* range, T key) (C++20)
    find_if_range (I* range, int _match(T*)) (C++20)
    find_if_not_range (I* range, int _match(T*)) (C++20)
    bool find_first_of_range (I* range1, GI* range2)

    remove (A* self, T key)                        _(NYI)_
    size_t remove_if (A* self, int match(T*))
    merge  (A* self, A* other)                     _(NYI)_
    int equal (A* self, A* other)

    A transform (A* self, T unop(T*))
    A transform_it (A* self, I* pos, T _binop(T*, T*))
    I transform_range (I* range1, I dest, T _unop(T*))
    I transform_it_range (I* range1, I* pos, I dest, T _binop(T*, T*))

applies a function to a range of elements. Returning results in a copy, or for
the range variants in an output iterator `dest`.  unop takes the iterator
element, binop takes as 2nd argument the 2nd iterator `pos`.

    generate (A* self, T _gen(void))
    generate_range (I* range, T _gen(void)) (C++20) (NY)

assigns the results of successive function calls to every element in a
range.

    generate_n (A* self, size_t count, T _gen(void))
    generate_n_range (I* first, size_t n, T _gen(void))

assigns the results of successive function calls to N elements in a range.
Unlike with the STL, `generate_n` shrinks to n elements.

See [algorithm](algorithm.md) for more.
