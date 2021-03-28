#define GENERATE_ENUM(x) TEST_##x,
#define GENERATE_NAME(x) #x,

// clang-format off
enum
{
    FOREACH_METH(GENERATE_ENUM)
#ifdef DEBUG
    FOREACH_DEBUG(GENERATE_ENUM)
#endif
    TEST_TOTAL
};
static const char *test_ok_names[] = { FOREACH_METH(GENERATE_NAME) };
static const int number_ok = sizeof(test_ok_names)/sizeof(char*);
#ifdef DEBUG
static const char *test_names[] = { FOREACH_METH(GENERATE_NAME) FOREACH_DEBUG(GENERATE_NAME) ""};
#endif
// clang-format on

typedef enum types_t
{
    CTL_VECTOR,
    CTL_ARRAY,
    CTL_DEQUE,
    CTL_LIST,
    CTL_SLIST,
    CTL_SET,
    CTL_USET /* 6. max 8 (4 bits) */
} types_t;
static const types_t types[] = {CTL_VECTOR, CTL_ARRAY, CTL_DEQUE, CTL_LIST, CTL_SLIST, CTL_SET, CTL_USET};
static const int num_types = sizeof(types)/sizeof(types[0]);

#include <vector>
#include <array>
#include <deque>
#include <list>
#include <forward_list>
#include <set>
#include <unordered_set>
#include <algorithm>

template <size_t N> using arrint = std::array<int, N>;

template <typename T> size_t size(const std::forward_list<T> &list)
{
    size_t i = 0;
    for (const auto &x : list)
    {
        (void)x;
        i++;
    }
    return i;
}

types_t pick_type(void) {
    const int LEN = len(types);
    return types[TEST_RAND(LEN)];
}

void print_vec(vec_int *a)
{
    printf("%-15s: ", "vec");
    foreach (vec_int, a, it) printf("%d, ", *it.ref);
    printf("\n");
}
void print_arr25(arr25_int *a)
{
    printf("%-15s: ", "arr25");
    foreach (arr25_int, a, it) printf("%d, ", it.ref ? *it.ref : -1);
    printf("\n");
}
void print_deq(deq_int *a)
{
    printf("%-15s: ", "deq");
    foreach (deq_int, a, it) printf("%d, ", *it.ref);
    printf("\n");
}
void print_list(list_int *a)
{
    printf("%-15s: ", "list");
    list_foreach_ref(list_int, a, it) printf("%d, ", *it.ref);
    printf("\n");
}
void print_slist(slist_int *a)
{
    printf("%-15s: ", "slist");
    foreach (slist_int, a, it) printf("%d, ", *it.ref);
    printf("\n");
}
void print_set(set_int *a)
{
    printf("%-15s: ", "set");
    if (a->size)
        foreach (set_int, a, it) printf("%d, ", *it.ref);
    printf("\n");
}
void print_uset(uset_int *a)
{
    printf("%-15s: ", "uset");
    if (a->size)
        foreach (uset_int, a, it) printf("%d, ", *it.ref);
    printf("\n");
}

#define print_stl(b, cppty)                                                                                            \
    LOG("=> %-15s: ", #cppty);                                                                                         \
    for (auto &_d : b)                                                                                                 \
    {                                                                                                                  \
        LOG("%d, ", _d);                                                                                               \
    }                                                                                                                  \
    LOG("\n")

#undef TEST_MAX_SIZE
#define TEST_MAX_SIZE 25
#ifdef DEBUG
#define TEST_MAX_VALUE 15
#else
#define print_vec(x)
#define print_arr25(x)
#define print_deq(x)
#define print_list(x)
#define print_slist(x)
#define print_set(x)
#define print_uset(x)
#undef print_stl
#define print_stl(x, y)
#define TEST_MAX_VALUE 25
#endif

#define CHECK(ty1, ty2, cppty, _x, _y)                                                                                 \
    {                                                                                                                  \
        print_stl(_y, cppty);                                                                                          \
        if (ty1##_int_size(&_x) != _y.size())                                                                          \
        {                                                                                                              \
            LOG("CTL size %zu != STL %zu\n", ty1##_int_size(&_x), _y.size());                                          \
        }                                                                                                              \
        if (strcmp(#ty1, "uset") && strcmp(#ty2, "uset"))                                                              \
        {                                                                                                              \
            assert(_x.size == _y.size());                                                                              \
        }                                                                                                              \
        CHECK_COMMON(ty1, ty2, cppty, _x, _y);                                                                         \
    }
// forward_list has no size(), not even length()
#define CHECK_SLIST(ty1, ty2, cppty, _x, _y)                                                                           \
    {                                                                                                                  \
        print_stl(_y, cppty);                                                                                          \
        if (ty1##_int_size(&_x) != size(_y))                                                                           \
        {                                                                                                              \
            LOG("CTL size %zu != STL %zu\n", ty1##_int_size(&_x), size(_y));                                           \
        }                                                                                                              \
        if (strcmp(#ty2, "uset"))                                                                                      \
        {                                                                                                              \
            assert(ty1##_int_size(&_x) == size(_y));                                                                   \
        }                                                                                                              \
        CHECK_COMMON(ty1, ty2, cppty, _x, _y);                                                                         \
    }
// from or to uset is unordered, all C++ set algorithms on uset are considered
// broken. we'd really need to sort every uset iterator if used genericly
#define CHECK_COMMON(ty1, ty2, cppty, _x, _y)                                                                          \
    {                                                                                                                  \
        if (strcmp(#ty1, "uset") && strcmp(#ty2, "uset"))                                                              \
        {                                                                                                              \
            ty1##_int_it _it1 = ty1##_int_begin(&_x);                                                                  \
            assert(ty1##_int_empty(&_x) == _y.empty());                                                                \
            LOG("\n");                                                                                                 \
            int i = 0;                                                                                                 \
            for (auto &_d : _y)                                                                                        \
            {                                                                                                          \
                i++;                                                                                                   \
                if (*_it1.ref != _d)                                                                                   \
                {                                                                                                      \
                    LOG("[%d]: CTL %d != STL %d\n", i, *_it1.ref, _d);                                                 \
                }                                                                                                      \
                /*assert(*_it1.ref == _d);*/                                                                           \
                ty1##_int_it_next(&_it1);                                                                              \
            }                                                                                                          \
            std::cppty::iterator _iter = _y.begin();                                                                   \
            foreach (ty1##_int, &_x, _it2)                                                                             \
            {                                                                                                          \
                /*assert(*_it2.ref == *_iter);*/                                                                       \
                _iter++;                                                                                               \
            }                                                                                                          \
        }                                                                                                              \
    }

#define SETUP_LIST1                                                                                                    \
    list_int a = list_int_init();                                                                                      \
    std::list<int> b;                                                                                                  \
    for (int i = 0; i < TEST_RAND(TEST_MAX_SIZE); i++)                                                                 \
    {                                                                                                                  \
        vb = 1 + TEST_RAND(TEST_MAX_VALUE - 1);                                                                        \
        list_int_push_back(&a, vb);                                                                                    \
        b.push_back(vb);                                                                                               \
    }                                                                                                                  \
    list_int_sort(&a);                                                                                                 \
    b.sort();                                                                                                          \
    print_list(&a)

#define SETUP_LIST2                                                                                                    \
    list_int aa = list_int_init();                                                                                     \
    std::list<int> bb;                                                                                                 \
    for (int i = 0; i < TEST_RAND(25); i++)                                                                            \
    {                                                                                                                  \
        vb = 1 + TEST_RAND(TEST_MAX_VALUE - 1);                                                                        \
        list_int_push_back(&aa, vb);                                                                                   \
        bb.push_back(vb);                                                                                              \
    }                                                                                                                  \
    list_int_sort(&aa);                                                                                                \
    bb.sort();                                                                                                         \
    list_int_it range2 = list_int_begin(&aa);                                                                          \
    print_list(&aa)

#define SETUP_SLIST1                                                                                                   \
    slist_int a = slist_int_init();                                                                                    \
    std::forward_list<int> b;                                                                                          \
    for (int i = 0; i < TEST_RAND(TEST_MAX_SIZE); i++)                                                                 \
    {                                                                                                                  \
        vb = 1 + TEST_RAND(TEST_MAX_VALUE - 1);                                                                        \
        slist_int_push_front(&a, vb);                                                                                  \
        b.push_front(vb);                                                                                              \
    }                                                                                                                  \
    slist_int_sort(&a);                                                                                                \
    b.sort();                                                                                                          \
    print_slist(&a)

#define SETUP_SLIST2                                                                                                   \
    slist_int aa = slist_int_init();                                                                                   \
    std::forward_list<int> bb;                                                                                         \
    for (int i = 0; i < TEST_RAND(25); i++)                                                                            \
    {                                                                                                                  \
        vb = 1 + TEST_RAND(TEST_MAX_VALUE - 1);                                                                        \
        slist_int_push_front(&aa, vb);                                                                                 \
        bb.push_front(vb);                                                                                             \
    }                                                                                                                  \
    slist_int_sort(&aa);                                                                                               \
    bb.sort();                                                                                                         \
    slist_int_it range2 = slist_int_begin(&aa);                                                                        \
    print_slist(&aa)

#define SETUP_VEC1                                                                                                     \
    vec_int a = vec_int_init();                                                                                        \
    std::vector<int> b;                                                                                                \
    for (int i = 0; i < TEST_RAND(TEST_MAX_SIZE); i++)                                                                 \
    {                                                                                                                  \
        vb = 1 + TEST_RAND(TEST_MAX_VALUE - 1);                                                                        \
        vec_int_push_back(&a, vb);                                                                                     \
        b.push_back(vb);                                                                                               \
    }                                                                                                                  \
    vec_int_sort(&a);                                                                                                  \
    std::sort(b.begin(), b.end());                                                                                     \
    print_vec(&a)
#define SETUP_VEC2                                                                                                     \
    vec_int aa = vec_int_init();                                                                                       \
    std::vector<int> bb;                                                                                               \
    for (int i = 0; i < TEST_RAND(25); i++)                                                                            \
    {                                                                                                                  \
        vb = 1 + TEST_RAND(TEST_MAX_VALUE - 1);                                                                        \
        vec_int_push_back(&aa, vb);                                                                                    \
        bb.push_back(vb);                                                                                              \
    }                                                                                                                  \
    vec_int_sort(&aa);                                                                                                 \
    std::sort(bb.begin(), bb.end());                                                                                   \
    vec_int_it range2 = vec_int_begin(&aa);                                                                            \
    print_vec(&aa)

#define SETUP_ARR1                                                                                                     \
    arr25_int a = arr25_int_init();                                                                                    \
    if (a.equal != _arr25_int__default_integral_equal)                                                                 \
        break;                                                                                                         \
    std::array<int, 25> b;                                                                                             \
    for (int i = 0; i < 25; i++)                                                                                       \
    {                                                                                                                  \
        vb = 1 + TEST_RAND(TEST_MAX_VALUE - 1);                                                                        \
        a.vector[i] = vb;                                                                                              \
        b[i] = vb;                                                                                                     \
    }                                                                                                                  \
    print_arr25(&a)
#define SETUP_ARR2                                                                                                     \
    arr25_int aa = arr25_int_init();                                                                                   \
    std::array<int, 25> bb;                                                                                            \
    for (int i = 0; i < 25; i++)                                                                                       \
    {                                                                                                                  \
        vb = 1 + TEST_RAND(TEST_MAX_VALUE - 1);                                                                        \
        aa.vector[i] = vb;                                                                                             \
        bb[i] = vb;                                                                                                    \
    }                                                                                                                  \
    arr25_int_sort(&aa);                                                                                               \
    std::sort(bb.begin(), bb.end());                                                                                   \
    arr25_int_it range2 = arr25_int_begin(&aa);                                                                        \
    print_arr25(&aa)

#define SETUP_DEQ1                                                                                                     \
    deq_int a = deq_int_init();                                                                                        \
    std::deque<int> b;                                                                                                 \
    for (int i = 0; i < TEST_RAND(TEST_MAX_SIZE); i++)                                                                 \
    {                                                                                                                  \
        vb = 1 + TEST_RAND(TEST_MAX_VALUE - 1);                                                                        \
        deq_int_push_back(&a, vb);                                                                                     \
        b.push_back(vb);                                                                                               \
    }                                                                                                                  \
    deq_int_sort(&a);                                                                                                  \
    std::sort(b.begin(), b.end());                                                                                     \
    print_deq(&a)
#define SETUP_DEQ2                                                                                                     \
    deq_int aa = deq_int_init();                                                                                       \
    std::deque<int> bb;                                                                                                \
    for (int i = 0; i < TEST_RAND(25); i++)                                                                            \
    {                                                                                                                  \
        vb = 1 + TEST_RAND(TEST_MAX_VALUE - 1);                                                                        \
        deq_int_push_back(&aa, vb);                                                                                    \
        bb.push_back(vb);                                                                                              \
    }                                                                                                                  \
    deq_int_sort(&aa);                                                                                                 \
    std::sort(bb.begin(), bb.end());                                                                                   \
    deq_int_it range2 = deq_int_begin(&aa);                                                                            \
    print_deq(&aa)

#define SETUP_SET1                                                                                                     \
    set_int a = set_int_init(NULL);                                                                                    \
    std::set<int> b;                                                                                                   \
    for (int i = 0; i < 1 + TEST_RAND(TEST_MAX_SIZE - 1); i++)                                                         \
    {                                                                                                                  \
        vb = 1 + TEST_RAND(TEST_MAX_VALUE - 1);                                                                        \
        set_int_insert(&a, vb);                                                                                        \
        b.insert(vb);                                                                                                  \
    }                                                                                                                  \
    print_set(&a)
#define SETUP_SET2                                                                                                     \
    set_int aa = set_int_init(NULL);                                                                                   \
    std::set<int> bb;                                                                                                  \
    for (int i = 0; i < TEST_RAND(25); i++)                                                                            \
    {                                                                                                                  \
        vb = 1 + TEST_RAND(TEST_MAX_VALUE - 1);                                                                        \
        set_int_insert(&aa, vb);                                                                                       \
        bb.insert(vb);                                                                                                 \
    }                                                                                                                  \
    set_int_it range2 = set_int_begin(&aa);                                                                            \
    print_set(&aa)

#define SETUP_USET1                                                                                                    \
    uset_int a = uset_int_init();                                                                            \
    std::unordered_set<int> b;                                                                                         \
    for (int i = 0; i < 1 + TEST_RAND(TEST_MAX_SIZE - 1); i++)                                                         \
    {                                                                                                                  \
        vb = 1 + TEST_RAND(TEST_MAX_VALUE - 1);                                                                        \
        uset_int_insert(&a, vb);                                                                                       \
        b.insert(vb);                                                                                                  \
    }                                                                                                                  \
    print_uset(&a)
#define SETUP_USET2                                                                                                    \
    uset_int aa = uset_int_init();                                                                           \
    std::unordered_set<int> bb;                                                                                        \
    for (int i = 0; i < TEST_RAND(25); i++)                                                                            \
    {                                                                                                                  \
        vb = 1 + TEST_RAND(TEST_MAX_VALUE - 1);                                                                        \
        uset_int_insert(&aa, vb);                                                                                      \
        bb.insert(vb);                                                                                                 \
    }                                                                                                                  \
    uset_int_it range2 = uset_int_begin(&aa);                                                                          \
    print_uset(&aa)
