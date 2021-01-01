#!/bin/sh
CC="gcc -std=c11"
CXX="g++ -std=c++17"
CFLAGS="-O3 -march=native"
VERSION=$($CXX --version | head -1)
if test -z "$PNG"; then
  PNG="uset uset_pow2 uset_cached _set pqu vec slist list deq arr compile"
fi

perf_graph()
{
    LOG=$1
    TITLE=$2
    LIST=$3
    OUT=bin
    echo "$LOG"
    for TEST in $LIST
    do
        # allow glob expansion of CFLAGS and TEST lists
        # shellcheck disable=SC2086
        case $TEST in
        *.c)   $CC -o "$OUT" $CFLAGS $TEST -I.
               ;;
        *.cc)  $CXX -o "$OUT" $CFLAGS $TEST
               ;;
        esac
        ./$OUT >> "$LOG"
    done
    python3 tests/perf/perf_plot.py "$LOG" "$TITLE" &&
      (mv "./$LOG.png" docs/images/; mv "./$LOG" tests/perf/; rm -- "./$OUT")
}

perf_compile_two_bar()
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
    # allow glob expansion of CFLAGS
    # shellcheck disable=SC2086
    X=$( (time $CC  -o $AA $CFLAGS "$A" -I.) 2>&1 | grep $KEY | cut -d ' ' -f 2)
    # shellcheck disable=SC2086
    Y=$( (time $CXX -o $BB $CFLAGS "$B")     2>&1 | grep $KEY | cut -d ' ' -f 2)
    I=$(stat --printf="%s" $AA)
    J=$(stat --printf="%s" $BB)
    python3 tests/perf/perf_plot_bar.py "$LOG" "$TITLE" "$X" "$Y" "$I" "$J" "$A" "$B" &&
      (mv "$LOG.png" docs/images/; rm -- "./$AA" "./$BB")
}

uset() {
  perf_graph \
    'uset.log' \
    "std::unordered_set<int> (dotted) vs. CTL uset_int (solid) ($CFLAGS) ($VERSION)" \
    "tests/perf/uset/perf_uset_insert.cc \
     tests/perf/uset/perf_uset_insert.c \
     tests/perf/uset/perf_uset_erase.cc \
     tests/perf/uset/perf_uset_erase.c
     tests/perf/uset/perf_uset_iterate.cc \
     tests/perf/uset/perf_uset_iterate.c"
}

uset_pow2() {
  ORIG_CFLAGS="$CFLAGS"
  CFLAGS="$CFLAGS -DCTL_USET_GROWTH_POWER2"
  perf_graph \
    'uset_pow2.log' \
    "std::unordered_set<int> (dotted) vs. CTL uset_int POWER2 (solid) ($CFLAGS) ($VERSION)" \
    "tests/perf/uset/perf_uset_insert.cc \
     tests/perf/uset/perf_uset_insert.c \
     tests/perf/uset/perf_uset_erase.cc \
     tests/perf/uset/perf_uset_erase.c
     tests/perf/uset/perf_uset_iterate.cc \
     tests/perf/uset/perf_uset_iterate.c"
  CFLAGS="$ORIG_CFLAGS"
}

uset_cached() {
  ORIG_CFLAGS="$CFLAGS"
  CFLAGS="$CFLAGS -DCTL_USET_CACHED_HASH"
  perf_graph \
    'uset_cached.log' \
    "std::unordered_set<int> (dotted) vs. CTL uset_int CACHED_HASH (solid) ($CFLAGS) ($VERSION)" \
    "tests/perf/uset/perf_uset_insert.cc \
     tests/perf/uset/perf_uset_insert.c \
     tests/perf/uset/perf_uset_erase.cc \
     tests/perf/uset/perf_uset_erase.c
     tests/perf/uset/perf_uset_iterate.cc \
     tests/perf/uset/perf_uset_iterate.c"
  CFLAGS="$ORIG_CFLAGS"
}

_set() {
  perf_graph \
    'set.log' \
    "std::set<int> (dotted) vs. CTL set_int (solid) ($CFLAGS) ($VERSION)" \
    "tests/perf/set/perf_set_insert.cc \
     tests/perf/set/perf_set_insert.c \
     tests/perf/set/perf_set_erase.cc \
     tests/perf/set/perf_set_erase.c \
     tests/perf/set/perf_set_clear.cc \
     tests/perf/set/perf_set_clear.c \
     tests/perf/set/perf_set_iterate.cc \
     tests/perf/set/perf_set_iterate.c"
}

pqu() {
  perf_graph \
    'pqu.log' \
    "std::priority_queue<int> (dotted) vs. CTL pqu_int (solid) ($CFLAGS) ($VERSION)" \
    "tests/perf/pqu/perf_priority_queue_push.cc \
     tests/perf/pqu/perf_pqu_push.c \
     tests/perf/pqu/perf_priority_queue_pop.cc \
     tests/perf/pqu/perf_pqu_pop.c \
     tests/perf/pqu/perf_priority_queue_top.cc \
     tests/perf/pqu/perf_pqu_top.c"
}

vec() {
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
}

str() {
  perf_graph \
    'str.log' \
    "std::string (dotted) vs. CTL str (solid) ($CFLAGS) ($VERSION)" \
    "tests/perf/str/perf_string_push_back.cc \
     tests/perf/str/perf_str_push_back.c \
     tests/perf/str/perf_string_erase.cc \
     tests/perf/str/perf_str_erase.c \
     tests/perf/str/perf_string_sort.cc \
     tests/perf/str/perf_str_sort.c \
     tests/perf/str/perf_string_iterate.cc \
     tests/perf/str/perf_str_iterate.c"
}

slist() {
  perf_graph \
    'slist.log' \
    "std::forward_list<int> (dotted) vs. CTL slist_int (solid) ($CFLAGS) ($VERSION)" \
    "tests/perf/slist/perf_fwlist_pop_front.cc \
     tests/perf/slist/perf_slist_pop_front.c \
     tests/perf/slist/perf_fwlist_push_front.cc \
     tests/perf/slist/perf_slist_push_front.c \
     tests/perf/slist/perf_fwlist_sort.cc \
     tests/perf/slist/perf_slist_sort.c \
     tests/perf/slist/perf_fwlist_iterate.cc \
     tests/perf/slist/perf_slist_iterate.c"
}

list() {
  perf_graph \
    'list.log' \
    "std::list<int> (dotted) vs. CTL list_int (solid) ($CFLAGS) ($VERSION)" \
    "tests/perf/lst/perf_list_push_back.cc
     tests/perf/lst/perf_lst_push_back.c \
     tests/perf/lst/perf_list_pop_back.cc \
     tests/perf/lst/perf_lst_pop_back.c \
     tests/perf/lst/perf_list_push_front.cc \
     tests/perf/lst/perf_lst_push_front.c \
     tests/perf/lst/perf_list_sort.cc \
     tests/perf/lst/perf_lst_sort.c \
     tests/perf/lst/perf_list_iterate.cc \
     tests/perf/lst/perf_lst_iterate.c"
  # removed the one most boring:
  #   tests/perf/lst/perf_list_pop_front.cc
  #   tests/perf/lst/perf_lst_pop_front.c
}

deq() {
  perf_graph \
    'deq.log' \
    "std::deque<int> (dotted) vs. CTL deq_int (solid) ($CFLAGS) ($VERSION)" \
    "tests/perf/deq/perf_deque_push_back.cc
     tests/perf/deq/perf_deq_push_back.c \
     tests/perf/deq/perf_deque_pop_back.cc \
     tests/perf/deq/perf_deq_pop_back.c \
     tests/perf/deq/perf_deque_pop_front.cc \
     tests/perf/deq/perf_deq_pop_front.c \
     tests/perf/deq/perf_deque_sort.cc \
     tests/perf/deq/perf_deq_sort.c \
     tests/perf/deq/perf_deque_iterate.cc \
     tests/perf/deq/perf_deq_iterate.c"
# removed the one most boring:
#    tests/perf/deq/perf_deque_push_front.cc
#    tests/perf/deq/perf_deq_push_front.c
}

arr() {
  rm tests/perf/arr/gen_arr*
  make tests/perf/arr/perf_arr_generate && tests/perf/arr/perf_arr_generate
  for TEST in tests/perf/arr/gen_array*.cc; do
      $CXX -o "${TEST//.cc/}" $CFLAGS $TEST -I.
  done
  for TEST in tests/perf/arr/gen_arr*.c; do
      $CC -o "${TEST//.c/}" $CFLAGS $TEST -I.
  done
  LOG=arr.log
  TITLE="std::array<double,NNN> (dotted) vs. CTL arrNNN_double (solid) ($CFLAGS) ($VERSION)"
  echo "$LOG"
  rm -- "./$LOG"
  for m in find fill_n sort iterate
  do
      echo "tests/perf/arr/gen_array_$m.cc" >> "$LOG"
      for OUT in tests/perf/arr/gen_array*_$m; do
          $OUT >> "$LOG"
      done
      echo "tests/perf/arr/gen_arr_$m.c" >> "$LOG"
      for OUT in tests/perf/arr/gen_arr0*_$m; do
          $OUT >> "$LOG"
      done
  done
  python3 tests/perf/perf_plot.py "$LOG" "$TITLE" &&
      (mv "$LOG.png" docs/images/; mv $LOG tests/perf/; rm tests/perf/arr/gen_arr* )
}

compile() {
  perf_compile_two_bar \
    'compile.log' \
    "CTL vs STL Compilation ($CFLAGS) ($VERSION)" \
    'tests/perf/perf_compile_c11.c' \
    'tests/perf/perf_compile_cc.cc'
}

for png in $PNG; do
    $png
done
