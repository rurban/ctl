#!/bin/bash
CC="gcc -std=c11"
CXX="g++ -std=c++17"
CFLAGS="-O3 -march=native"
VERSION=$($CXX --version | head -1)

function perf_graph
{
    LOG=$1
    TITLE=$2
    LIST=$3
    OUT=bin
    echo "$LOG"
    for TEST in ${LIST[*]}
    do
        if [[ $TEST == *.c ]]
        then
            $CC -o "$OUT" $CFLAGS $TEST -I.
        else
            $CXX -o "$OUT" $CFLAGS $TEST
        fi
        ./$OUT >> "$LOG"
    done
    python3 tests/perf/perf_plot.py "$LOG" "$TITLE" &&
      (mv "$LOG.png" docs/images/; rm -- "./$LOG" "./$OUT")
}

function perf_compile_two_bar
{
    KEY='stamp'
    TIMEFORMAT="$KEY %R"
    LOG=$1
    TITLE=$2
    A=$3
    B=$4
    AA=bina
    BB=binb
    echo "$LOG"
    X=$( (time $CC  -o $AA $CFLAGS $A -I.) 2>&1 | grep $KEY | cut -d ' ' -f 2)
    Y=$( (time $CXX -o $BB $CFLAGS $B)     2>&1 | grep $KEY | cut -d ' ' -f 2)
    I=$(stat --printf="%s" $AA)
    J=$(stat --printf="%s" $BB)
    python3 tests/perf/perf_plot_bar.py "$LOG" "$TITLE" $X $Y $I $J $A $B &&
      (mv "$LOG.png" docs/images/; rm -- "./$AA" "./$BB")
}

perf_graph \
    'set.log' \
    "std::set<int> (dotted) vs. CTL set_int (solid) ($CFLAGS) ($VERSION)" \
    "tests/perf/set/perf_set_insert.cc \
     tests/perf/set/perf_set_insert.c \
     tests/perf/set/perf_set_erase.cc \
     tests/perf/set/perf_set_erase.c
     tests/perf/set/perf_set_iterate.cc \
     tests/perf/set/perf_set_iterate.c"

perf_graph \
    'uset.log' \
    "std::unordered_set<int> (dotted) vs. CTL uset_int (solid) ($CFLAGS) ($VERSION)" \
    "tests/perf/uset/perf_uset_insert.cc \
     tests/perf/uset/perf_uset_insert.c \
     tests/perf/uset/perf_uset_erase.cc \
     tests/perf/uset/perf_uset_erase.c
     tests/perf/uset/perf_uset_iterate.cc \
     tests/perf/uset/perf_uset_iterate.c"

perf_graph \
    'pqu.log' \
    "std::priority_queue<int> (dotted) vs. CTL pqu_int (solid) ($CFLAGS) ($VERSION)" \
    "tests/perf/pqu/perf_priority_queue_push.cc \
     tests/perf/pqu/perf_pqu_push.c \
     tests/perf/pqu/perf_priority_queue_pop.cc \
     tests/perf/pqu/perf_pqu_pop.c"

perf_graph \
    'vec.log' \
    "std::vector<int> (dotted) vs. CTL vec_int (solid) ($CFLAGS) ($VERSION)" \
    "tests/perf/vec/perf_vector_push_back.cc \
     tests/perf/vec/perf_vec_push_back.c \
     tests/perf/vec/perf_vector_pop_back.cc \
     tests/perf/vec/perf_vec_pop_back.c \
     tests/perf/vec/perf_vector_sort.cc \
     tests/perf/vec/perf_vec_sort.c \
     tests/perf/vec/perf_vector_iterate.cc \
     tests/perf/vec/perf_vec_iterate.c"

perf_graph \
    'list.log' \
    "std::list<int> (dotted) vs. CTL list_int (solid) ($CFLAGS) ($VERSION)" \
    "tests/perf/lst/perf_list_push_back.cc
     tests/perf/lst/perf_lst_push_back.c \
     tests/perf/lst/perf_list_pop_back.cc \
     tests/perf/lst/perf_lst_pop_back.c \
     tests/perf/lst/perf_list_pop_front.cc \
     tests/perf/lst/perf_lst_pop_front.c \
     tests/perf/lst/perf_list_push_front.cc \
     tests/perf/lst/perf_lst_push_front.c \
     tests/perf/lst/perf_list_sort.cc \
     tests/perf/lst/perf_lst_sort.c \
     tests/perf/lst/perf_list_iterate.cc \
     tests/perf/lst/perf_lst_iterate.c"

perf_graph \
    'deq.log' \
    "std::deque<int> (dotted) vs. CTL deq_int (solid) ($CFLAGS) ($VERSION)" \
    "tests/perf/deq/perf_deque_push_back.cc
     tests/perf/deq/perf_deq_push_back.c \
     tests/perf/deq/perf_deque_pop_back.cc \
     tests/perf/deq/perf_deq_pop_back.c \
     tests/perf/deq/perf_deque_pop_front.cc \
     tests/perf/deq/perf_deq_pop_front.c \
     tests/perf/deq/perf_deque_push_front.cc \
     tests/perf/deq/perf_deq_push_front.c \
     tests/perf/deq/perf_deque_sort.cc \
     tests/perf/deq/perf_deq_sort.c \
     tests/perf/deq/perf_deque_iterate.cc \
     tests/perf/deq/perf_deq_iterate.c"

perf_compile_two_bar \
    'compile.log' \
    "CTL vs STL Compilation ($CFLAGS) ($VERSION)" \
    'tests/perf/perf_compile_c11.c' \
    'tests/perf/perf_compile_cc.cc'
