PREFIX ?= /usr/local
CC ?= gcc
CXX ?= g++

# TODO probe for -std=c++20
CXX += -std=c++17
CC  += -std=c11

.SUFFIXES: .o .i .3 .cc .c .md
.PHONY: all man install clean doc images perf examples ALWAYS

#LONG ?= 0
#SANITIZE ?= 0
SRAND ?= 1

CFLAGS  = -I.
CFLAGS += -Wall -Wextra -Wpedantic -Wfatal-errors -Wshadow
CFLAGS += -march=native
CFLAGS += -g

.ifdef LONG
CFLAGS += -Werror
CFLAGS += -DLONG
.endif

.ifdef DEBUG
O0 = 1
CFLAGS += -DDEBUG
.endif

.ifdef SANITIZE
CFLAGS += -fsanitize=address,undefined -fno-omit-frame-pointer
.endif

.ifdef Og
CFLAGS += -Og
.elifdef O0
CFLAGS += -O0
.elifdef O1
CFLAGS += -O1
.elifdef O2
CFLAGS += -O2
.elifdef O3
CFLAGS += -O3
.elifdef Ofast
CFLAGS += -Ofast
.elifdef Os
CFLAGS += -Os
.else
CFLAGS += -O3
.endif

.if ${SRAND} > 0
CFLAGS += -DSRAND
. ifdef SEED
CFLAGS += -DSEED=${SEED}
. endif
.else
. if defined(SEED) && ${SEED} != ""
CFLAGS += -DSRAND -DSEED=${SEED}
. endif
.endif

CXXFLAGS=${CFLAGS}

H        = ${wildcard ctl/*.h} ctl/bits/*.h
COMMON_H = ctl/ctl.h ctl/bits/container.h ctl/algorithm.h
TESTS = \
	tests/func/test_c11 \
	tests/func/test_container_composing \
	tests/func/test_integral \
	tests/func/test_integral_c11 \
	tests/func/test_deque \
	tests/func/test_list \
	tests/func/test_string \
	tests/func/test_priority_queue \
	tests/func/test_queue \
	tests/func/test_set \
	tests/func/test_unordered_set \
	tests/func/test_unordered_set_power2 \
	tests/func/test_unordered_set_cached \
	tests/func/test_stack \
	tests/func/test_vector \
	tests/func/test_vec_capacity \
	tests/func/test_str_capacity
.ifdef DEBUG
TESTS += \
	tests/func/test_map     \
	tests/func/test_unordered_map
.endif

EXAMPLES = \
	examples/astar \
	examples/postfix \
	examples/json \
	examples/snow \
	examples/6502

# was GNU ${foreach bin,${TESTS},./${bin} &&}
all: ${TESTS} docs/index.md
.for t in ${TESTS}
	./${t}
.endfor
	@${CC} --version | head -n2
	@echo ${CC} ${CFLAGS}
	@${CXX} --version | head -n2
	@echo ${CXX} ${CXXFLAGS}

check: all
.cflags: ALWAYS
	@echo "${CFLAGS}" >$@.tmp; cmp $@.tmp $@ || mv $@.tmp $@
images:
	./gen_images.sh

PERFS_C  = ${patsubst %.c,%, ${wildcard tests/perf/*/perf*.c} tests/perf/perf_compile_c11.c}
PERFS_CC = ${patsubst %.cc,%, ${wildcard tests/perf/*/perf*.cc} tests/perf/perf_compile_cc.cc}

perf: ${PERFS_C} ${PERFS_CC}

${wildcard tests/perf/lst/perf*.c} : ${COMMON_H} ctl/list.h
${wildcard tests/perf/set/perf*.c} : ${COMMON_H} ctl/set.h
${wildcard tests/perf/deq/perf*.c} : ${COMMON_H} ctl/deque.h
${wildcard tests/perf/pqu/perf*.c} : ${COMMON_H} ctl/priority_queue.h
${wildcard tests/perf/vec/perf*.c} : ${COMMON_H} ctl/vector.h
${wildcard tests/perf/uset/perf*.c}: ${COMMON_H} ctl/unordered_set.h

examples: ${EXAMPLES}

MANPAGES = ${patsubst docs/%.md,docs/man/%.h.3, ${wildcard docs/*.md}}

man: docs/man/ctl.h.3 ${MANPAGES}

docs/index.md : README.md
	./update-index.pl

docs/man/ctl.h.3: docs/index.md
	@mkdir -p docs/man
	ronn < $< > $@
docs/man/%.h.3 : docs/%.md
	ronn < $< > $@

install: man
	-rm docs/man/index.h.3
	mkdir -p ${DESTDIR)${PREFIX)/include/ctl
	cp ctl/*.h ${DESTDIR)${PREFIX)/include/ctl/
	mkdir -p ${DESTDIR)${PREFIX)/share/man/man3
	cp docs/man/* ${DESTDIR)${PREFIX)/share/man/man3/
	mkdir -p ${DESTDIR)${PREFIX)/share/doc/ctl/images
	cp docs/*.md ${DESTDIR)${PREFIX)/share/doc/ctl/
	cp -r docs/*/*.md ${DESTDIR)${PREFIX)/share/doc/ctl/
	cp docs/images/*.log.png ${DESTDIR)${PREFIX)/share/doc/ctl/images/

clean:
	@rm -f .cflags .cflags.tmp
	@rm -f ${TESTS}
	@rm -f ${EXAMPLES}
	@rm -f ${PERFS_C} ${PERFS_CC}
	@rm -f docs/man/ctl.h.3 ${MANPAGES}
	@if test -d docs/man; then rmdir docs/man; fi

help:
	@echo " make targets for the ctl, a header-only library for C"
	@echo " "
	@echo " all, check: run all tests"
	@echo " images:     generate the performance graphs"
	@echo " perf:       compile the performance binaries seperately"
	@echo " examples:   compile the examples"
	@echo " man:        create the manpages in docs/man"
	@echo " install:    copy to ${DESTDIR)${PREFIX)/include/ctl"
	@echo "                     ${DESTDIR)${PREFIX)/share/man/man3"
	@echo "                     ${DESTDIR)${PREFIX)/share/doc/ctl"
	@echo " clean:      the tests, perf, examples and manpages"
	@echo " <file>.i:   expand the file with -DT=int for debugging"

.h.i:
	@${CC} ${CFLAGS} -DT=int $< -E | clang-format -style=webkit
.c.i:
	@${CC} ${CFLAGS} -DT=int $< -E | clang-format -style=webkit
.cc.i:
	@${CXX} ${CFLAGS} -DT=int $< -P -E | clang-format -style=webkit
ctl/unordered_map.i ctl/map.i:
	@${CXX} ${CFLAGS} $< -DT=strint -P -E | clang-format -style=webkit

.for srcc in ${subst .c,, ${wildcard examples/*.c tests/func/*.c}}
${srcc} : ${srcc}.c .cflags ${H}
	${CC} ${CFLAGS} -o $@ $@.c
.endfor
.for srccc in ${subst .c,, ${wildcard examples/*.cc tests/func/*.cc}}
${srccc} : ${srccc}.cc .cflags ${H}
	${CXX} ${CFLAGS} -o $@ $@.cc
.endfor

#tests/func/%: tests/func/%.cc .cflags ${H}
#	${CXX} ${CFLAGS} -o $@ $@.cc
#tests/func/test_integral_c11: .cflags ${H} tests/func/test_integral_c11.c
#	${CC} ${CFLAGS} -o $@ $@.c
#tests/func/test_integral: .cflags ${H} tests/func/test_integral.cc
#	${CXX} ${CFLAGS} -o $@ $@.cc
#tests/func/test_container_composing: .cflags ${H} \
#                          tests/func/test_container_composing.cc
#	${CXX} ${CFLAGS} -o $@ $@.cc
tests/func/test_deque:    .cflags ${COMMON_H} ctl/deque.h \
                          tests/func/test_deque.cc
	${CXX} ${CFLAGS} -o $@ $@.cc
tests/func/test_list:     .cflags ${COMMON_H} ctl/list.h \
                          tests/func/test_list.cc
	${CXX} ${CFLAGS} -o $@ $@.cc
tests/func/test_priority_queue: .cflags ${COMMON_H} ctl/priority_queue.h ctl/vector.h \
                          tests/func/test_priority_queue.cc
	${CXX} ${CFLAGS} -o $@ $@.cc
tests/func/test_queue:    .cflags ${COMMON_H} ctl/queue.h ctl/deque.h \
                          tests/func/test_queue.cc
	${CXX} ${CFLAGS} -o $@ $@.cc
tests/func/test_set:      .cflags ${COMMON_H} ctl/set.h \
                          tests/func/test_set.cc
	${CXX} ${CFLAGS} -o $@ $@.cc
tests/func/test_map:      .cflags ${COMMON_H} ctl/map.h ctl/set.h \
                          tests/func/test_map.cc
	${CXX} ${CFLAGS} -o $@ $@.cc
tests/func/test_unordered_set: .cflags ${COMMON_H} ctl/unordered_set.h \
                          tests/func/test_unordered_set.cc
	${CXX} ${CFLAGS} -o $@ $@.cc
tests/func/test_unordered_set_power2: .cflags ${COMMON_H} ctl/unordered_set.h \
                          tests/func/test_unordered_set.cc
	${CXX} ${CFLAGS} -DCTL_USET_GROWTH_POWER2 tests/func/test_unordered_set.cc -o $@
tests/func/test_unordered_set_cached: .cflags ${COMMON_H} ctl/unordered_set.h \
                          tests/func/test_unordered_set.cc
	${CXX} ${CFLAGS} -DCTL_USET_CACHED_HASH tests/func/test_unordered_set.cc -o $@
tests/func/test_unordered_map: .cflags ${COMMON_H} ctl/unordered_map.h ctl/unordered_set.h \
                          tests/func/test_unordered_map.cc
	${CXX} ${CFLAGS} -o $@ $@.cc
tests/func/test_stack:    .cflags ${COMMON_H} ctl/stack.h ctl/deque.h \
                          tests/func/test_stack.cc
	${CXX} ${CFLAGS} -o $@ $@.cc
tests/func/test_string:   .cflags ${COMMON_H} ctl/string.h ctl/vector.h \
                          tests/func/test_string.cc
	${CXX} ${CFLAGS} -o $@ $@.cc
tests/func/test_str_capacity: .cflags ${COMMON_H} ctl/string.h ctl/vector.h \
                          tests/func/test_str_capacity.cc
	${CXX} ${CFLAGS} -o $@ $@.cc
tests/func/test_vec_capacity: .cflags ${COMMON_H} ctl/vector.h \
                          tests/func/test_vec_capacity.cc
	${CXX} ${CFLAGS} -o $@ $@.cc
tests/func/test_vector:   .cflags ${COMMON_H} ctl/vector.h \
                          tests/func/test_vector.cc
	${CXX} ${CFLAGS} -o $@ $@.cc

ALWAYS:
