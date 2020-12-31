# C TEMPLATE LIBRARY (CTL)

CTL is a fast compiling, type safe, header only, template-like library for ISO C99/C11.

## Motivation

CTL aims to improve ISO C99/C11 developer productivity by implementing the following
STL containers in ISO C99/C11:

```
ctl/deque.h          = std::deque           prefix: deq
ctl/list.h           = std::list            prefix: list
ctl/priority_queue.h = std::priority_queue  prefix: pqu
ctl/queue.h          = std::queue           prefix: queue
ctl/set.h            = std::set             prefix: set
ctl/stack.h          = std::stack           prefix: stack
ctl/string.h         = std::string          prefix: str
ctl/vector.h         = std::vector          prefix: vec
```
hashmap's are in work still.

It is based on glouw's ctl, but with proper names, and using the incpath `ctl/` prefix.

## Use

Configure a CTL container with a built-in or typedef type `T`.

```C
#include <stdio.h>

#define P
#define T int
#include <ctl/vector.h>

int compare(int* a, int* b) { return *b < *a; }

int main(void)
{
    vec_int a = vec_int_init();
    vec_int_push_back(&a, 9);
    vec_int_push_back(&a, 1);
    vec_int_push_back(&a, 8);
    vec_int_push_back(&a, 3);
    vec_int_push_back(&a, 4);
    vec_int_sort(&a, compare);
    foreach(vec_int, &a, it)
        printf("%d\n", *it.ref);
    vec_int_free(&a);
}
```

Definition `P` states type `T` is Plain Old Data (POD).

For a much more thorough getting started guide,
see the wiki: https://github.com/rurban/ctl/wiki and
https://github.com/glouw/ctl/wiki for the original sample with three-letter names.

## Memory Ownership

Types with memory ownership require definition `P` be omitted, and require
function declarations for the C++ equivalent of the destructor and copy constructor,
prior to the inclusion of the container:

```C
typedef struct { ... } type;
void type_free(type*);
type type_copy(type*);
#define T type
#include <ctl/vector.h>
```

Forgetting a declaration will print a human-readable error message:

```shell
tests/test_c11.c:11:11: error: ‘type_free’ undeclared (first use in this function)
   11 | #define T type
```

## Performance

CTL performance is presented in solid colors, and STL in dotted colors,
for template type `T` as type `int` for all measurements.

![](images/vec.log.png)
![](images/lst.log.png)
![](images/deq.log.png)
![](images/set.log.png)
![](images/pqu.log.png)
![](images/compile.log.png)

Omitted from these performance measurements are `queue.h`, `stack.h`, and `string.h`,
as their performance characteristics can be inferred from `deque.h`, and `vector.h`,
respectively.

Note, CTL strings do not support short strings yet.

## Running Tests

To run all functional tests, run:

```shell
make
```

To compile examples, run:

```shell
make examples
```

To generate performance graphs, run:

```shell
sh gen_images.sh
# Graphing requires python3 and the Plotly family of libraries via pip3.
```

To do all of the above in one step, run:

```shell
./all.sh
```

For maintaining CTL, a container templated to type `int` can be
outputted to `stdout` by running make on the container name, eg:

```shell
make deque
make list
make priority_queue
make queue
make set
make stack
make string
make vector
```

## Other

STL `std::map` will not be implemented in CTL because maps only provide slight
syntactic improvements over sets.

STL `std::unordered_map` and `std::unordered_set` will not be implemented in CTL
because ordered containers are preferred, even at the cost of performance.

STL variants of multi-sets and multi-maps will not be implemented because
similar behaviour can be implemented as an amalgamation of a `set` and `lst`.

## Base Implementation Details

    vector.h: See `realloc`.
    deque.h: Paged `realloc`.
    list.h: Doubly linked list.
    set.h: Red black tree.

## Acknowledgements

Tahnks you `glouw` for three-letter variant https://github.com/glouw/ctl.
Thank you `kully` for the Plotly code, and thank you for the general review.
Thank you `smlckz` for the `foreach` cleanup.
