# hive - CTL - C Container Template library

Defined in header **<ctl/hive.h>**, CTL prefix **hive**.

## SYNOPSIS

    #define POD
    #define T int
    #include <ctl/hive.h>

    hive_int a = hive_int_init();
    hive_int_it it = hive_int_insert(&a, 42);
    int *stable = it.ref;              // address stays valid for its lifetime
    hive_int_insert(&a, 7);
    hive_int_erase_it(&it);            // frees the slot for reuse
    foreach(hive_int, &a, i) printf("%d ", *i.ref);
    hive_int_free(&a);

## DESCRIPTION

**hive** (C++26, formerly `plf::colony`) is an unordered container that gives
every element a **stable address** for its whole lifetime and **reuses the
memory of erased elements** for later insertions.

Storage is a linked list of fixed-capacity blocks with a per-container free-list
of erased slots. Erased slots are skipped during iteration and refilled on the
next insert (most-recently-erased first). Because elements never move,
pointers and iterators to *live* elements remain valid across insert/erase of
*other* elements. Iteration order is unspecified.

The block capacity defaults to `CTL_HIVE_BLOCK` (32); `#define` it before the
include to change it.

The function names are composed of the prefix **hive_**, the user-defined type
**T** and the method name.

## Member types

`T`                       value type

`A` being `hive_T`        container type

`B` being `hive_T_block`  block (bucket) type

`I` being `hive_T_it`     iterator type

## Member functions

    A init (void)
    free (A* self)
    A copy (A* self)

For non-POD `T` set `self.equal` (or `self.compare`) if you use `find`,
`contains` or `count`.

## Iterators

    I begin (A* self)
    I end (A* self)
    I* ref / next / done         // via foreach

`it.ref` is the stable element address; it stays valid until that element is
erased. See [iterators](iterators.md).

## Capacity

    int empty (A* self)
    size_t size (A* self)
    size_t capacity (A* self)    // sum of block capacities
    size_t max_size (void)
    reserve (A* self, size_t n)  // pre-allocate blocks

## Modifiers

    I insert (A* self, T value)

inserts value, reusing an erased slot if one exists, and returns an iterator to
it (whose `.ref` is stable).

    I emplace (A* self, T* value)

    I erase_it (I* pos)

erases the element at pos, frees its slot for reuse, and returns an iterator to
the next live element.

    size_t remove_if (A* self, int match(T*))
    size_t erase_if  (A* self, int match(T*))

    clear (A* self)
    swap (A* self, A* other)

## Lookup

    I find (A* self, T key)          // linear scan (hive is unordered)
    int contains (A* self, T key)
    size_t count (A* self, T key)
