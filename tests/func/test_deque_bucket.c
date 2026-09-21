#include <assert.h>
#include <stddef.h>

#define POD
#define DEQ_BUCKET_SIZE 4
#define T int
#include <ctl/deque.h>

int main(void)
{
    deq_int values = deq_int_init();

    deq_int_push_back(&values, 1);
    assert(values.size == 1);
    assert(values.pages[values.mark_a]->a == 0);
    assert(values.pages[values.mark_a]->b == 1);
    assert(sizeof(*values.pages[values.mark_a]) < 8 * sizeof(int));

    for (int i = 2; i <= 5; i++)
        deq_int_push_back(&values, i);

    assert(values.size == 5);
    assert(values.mark_b - values.mark_a == 2);
    for (size_t i = 0; i < values.size; i++)
        assert(*deq_int_at(&values, i) == (int)i + 1);

    deq_int_free(&values);
    return 0;
}
