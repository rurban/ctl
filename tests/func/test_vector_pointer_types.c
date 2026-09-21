#include <assert.h>
#include <string.h>

typedef struct SweepEvent {
    int id;
} SweepEvent;
typedef SweepEvent *SweepEventPtr;

#define POD
#define NOT_INTEGRAL
#define T SweepEvent
#include <ctl/vector.h>

#define POD
#define NOT_INTEGRAL
#define T SweepEventPtr
#include <ctl/vector.h>

int main(void)
{
    SweepEvent first = {.id = 1};
    SweepEvent second = {.id = 2};
    vec_SweepEvent values = vec_SweepEvent_init();
    vec_SweepEventPtr pointers = vec_SweepEventPtr_init();

    vec_SweepEvent_push_back(&values, first);
    vec_SweepEvent_push_back(&values, second);
    vec_SweepEventPtr_push_back(&pointers, &first);
    vec_SweepEventPtr_push_back(&pointers, &second);

    assert(values.size == 2);
    assert(values.vector[0].id == 1);
    assert(values.vector[1].id == 2);
    assert(pointers.size == 2);
    assert(pointers.vector[0] == &first);
    assert(pointers.vector[1] == &second);

    vec_SweepEvent_free(&values);
    vec_SweepEventPtr_free(&pointers);
    assert(first.id == 1);
    assert(second.id == 2);
    return 0;
}
