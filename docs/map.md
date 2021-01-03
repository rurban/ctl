# map - CTL - C Container Template library

Defined in header **<ctl/map.h>**, CTL prefix **map**,
deriving from [set](set.md).

# SYNOPSIS

    typedef struct {
      char *key;
      int value;
    } charint;

    static inline int
    charint_cmp(charint *a, charint *b) {
      return strcmp(a->key, b->key);
    }
    static inline void
    charint_free(charint *a) {
      free(a->key);
    }
    static inline charint
    charint_copy(charint *self) {
      char *copy_key = (char*) malloc(strlen(self->key) + 1);
      strcpy (copy_key, self->key);
      charint copy = {
        copy_key,
        self->value,
      };
      return copy;
    }

    #undef POD
    #define T charint
    #include <ctl/map.h>

    map_charint a = map_charint_init(charint_compare);

    char c_char[36];
    for (int i=0; i<1000; i++) {
      snprintf(c_char, 36, "%c%d", 48 + (rand() % 74), rand());
      map_charint_insert(&a, charint_copy(&(charint){ c_char, i }));
    }

    foreach(map_charint, &a, it) { strcpy (c_char, it.ref->key); }
    printf("last key \"%s\", ", c_char);

    map_charint_node *b = map_charint_begin(&a);
    printf("min {\"%s\", %d} ", b->key.key, b->key.value);
    b = map_charint_node_max(b);
    printf("max {\"%s\", %d}\n", b->key.key, b->key.value);

    map_charint_free(&a);

# DESCRIPTION

map is a sorted associative container that contains key-value pairs with unique
keys. Keys are sorted by using the comparison function Compare. Search, removal,
and insertion operations have logarithmic complexity. map is an extended set
with a struct as value, and implemented as red-black trees.

The function names are composed of the prefix **map_**, the user-defined type
**T** and the method name. E.g `map_charint` with `#define T charint`.

Everywhere the CTL uses the Compare requirements, uniqueness is
determined by using the equivalence relation. In imprecise terms, two objects a
and b are considered equivalent (not unique) if neither compares less than the
other: !comp(a, b) && !comp(b, a).

# Member types

`T`                     value type

`A` being `map_T`       container type

`B` being `map_T_node`  node type

`I` being `map_T_it`    iterator type

## Member functions

[init](map/init.md) `(int T_compare(T*, T*))`

constructs the map

[free](map/free.md) `(A* self)`

destructs the map

[assign](map/assign.md) `(A* self, A* other)`

replaces the contents of the container

[get_allocator](map/get_allocator.md) `(A* self)`

returns the associated allocator

## Element access

[at](map/at.md) `(A* self, size_t index)`

access specified element with bounds checking

## Iterators

[begin](map/begin.md) `(A* self)`

returns an iterator to the beginning

[end](map/end.md) `(A* self)`

returns an iterator to the end

## Capacity

[empty](map/empty.md) `(A* self)`

checks whether the container is empty

[size](map/size.md) `(A* self)`

returns the number of elements

[max_size](map/max_size.md)   ()

returns the maximum possible number of elements

## Modifiers

[clear](map/clear.md) `(A* self)`

clears the contents

[insert](map/insert.md) `(A* self)`

inserts elements or nodes `(since C++17)`

[insert_or_assign](map/insert_or_assign.md) `(A* self)`

inserts an element or assigns to the current element if the key already exists

[emplace](map/emplace.md) `(A* self, ...)`

constructs element in-place

[emplace_hint](map/emplace_hint.md) `(A* self, it *position, ...)`

constructs elements in-place at position

[try_emplace](map/try_emplace.md) `(A* self)`

inserts in-place if the key does not exist, does nothing if the key exists

[erase](set/erase.md) `(A* self, T key)`

erases the element by value

[erase_it](set/erase.md) `(A* self, I* position)`

erases the element at position

[erase_range](set/erase.md) `(A* self, I* first, I* last)`

erases elements

[swap](map/swap.md) `(A* self, A* other)`

swaps the contents

[extract](set/extract.md) `(A* self, T key)`

extracts a node from the container. NYI

[extract_it](set/extract.md) `(A* self, I* position)`

extracts nodes from the container. NYI

[merge](map/merge.md) `(A* self, A* other)`

merges two containers

## Lookup

[count](map/count.md) `(A* self, T key)`

returns the number of elements matching specific key

[find](map/find.md) `(A* self, T key)`

finds element with specific key

[contains](map/contains.md) `(A* self, T key)`

checks if the container contains element with specific key. `(C++20)`

[equal_range](map/equal_range.md) `(A* self)`

returns range of elements matching a specific key. `(NYI)`

[lower_bound](map/lower_bound.md) `(A* self)`

returns an iterator to the first element not less than the given key. `(NYI)`

[upper_bound](map/upper_bound.md) `(A* self)`

returns an iterator to the first element greater than the given key. `(NYI)`

## Observers

[value_comp](map/value_comp.md) `(A* self)`

Returns the function that compares keys in objects of type value_type T. `(NYI)`

## Non-member functions

[swap](map/swap.md) `(A* self)`

specializes the swap algorithm

[remove_if](map/remove_if.md) `(A* self, int T_match(T*))`

Removes all elements satisfying specific criteria.

[erase_if](map/erase_if.md) `(A* self)`

erases all elements satisfying specific criteria `(C++20)`

[intersection](set/intersection.md) `(A* self, A* other)`

[union](set/union.md) `(A* self, A* other)`

[difference](set/difference.md) `(A* self, A* other)`

[symmetric_difference](set/symmetric_difference.md) `(A* self, A* other)`

