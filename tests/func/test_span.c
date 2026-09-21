#include <assert.h>
#include <stddef.h>
#define T int
#include <ctl/span.h>
int main(void)
{
    int values[] = {1, 2, 3, 4, 5};
    span_int view = span_int_init(values, 5);
    assert(!span_int_empty(&view));
    assert(*span_int_front(&view) == 1);
    assert(*span_int_back(&view) == 5);
    assert(*span_int_at(&view, 2) == 3);
    assert(span_int_data(&view) == values);

    int sum = 0;
    for (int *it = span_int_begin(&view); it != span_int_end(&view); it++)
        sum += *it;
    assert(sum == 15);

    span_int mid = span_int_subspan(&view, 1, 3);
    assert(mid.size == 3);
    assert(*span_int_front(&mid) == 2);
    assert(*span_int_back(&mid) == 4);

    span_int head = span_int_first(&view, 2);
    assert(head.size == 2 && head.data == values);

    span_int tail = span_int_last(&view, 2);
    assert(tail.size == 2 && *span_int_front(&tail) == 4);

    span_int clipped = span_int_subspan(&view, 3, 100);
    assert(clipped.size == 2);
    return 0;
}
