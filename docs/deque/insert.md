# deq_T_insert - CTL - C Container Template library

Defined in header [**<ctl/deque.h>**](../deque.md)

# SYNOPSIS

    #define T int
    #include <ctl/deque.h>

    deq_int a = deq_int_init ();

    deq_int_insert (&a, 1, rand());

    deq_int_it it = deq_int_it_each(&a);
    deq_int_it_advance(&it, 1);
    deq_int_it *pos = deq_int_insert_it(&a, &it, 1);

    deq_int_insert_count (&a, 100, 0);

    deq_int b = deq_int_init ();
    deq_int_insert_count (&b, 10, -1);
    deq_int_it from = deq_int_it_each(&b);
    deq_int_it end = deq_int_it_each(&b);
    deq_int_it_advance(&from, 5);
    end.index = b.size;
    end.done = 1;
    deq_int_insert_range (&a, pos, &from, &end);

# DESCRIPTION

`it insert (A* self, size_t index, T value)`
inserts value before index. Returns void.

`it insert_it (A* self, T* pos, T value)`
inserts value before pos. Returns pos, which points now to the element inserted.

`it insert_count (A* self, T* pos, size_t count, T value)`
Inserts count values before pos.  Returns pos, which points now to the first element inserted.
The first value is inserted asis, the others as copy.

`it insert_range (A* self, T* pos, T* first, T* last)`
Inserts values from range `[first, last)` before pos. Returns pos, which points
now to the first element inserted.

first and last may not be iterators into self. They must be from a deque of the
same type. The STL deque allows overlaps in some cases, but not in all, so we disallow it
at all.

pos may be the end iterator.

# SEEALSO

* [deq_T_emplace](emplace.md)
* [deq_T_push_front](push_front.md)
* [deq_T_push_back](push_back.md)
