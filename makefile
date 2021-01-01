# nmake guard: \
# https://stackoverflow.com/questions/8270391/use-the-same-makefile-for-make-linux-and-nmake-windows \
.ifndef 0 # \
.else
# bmake starts here
PREFIX ?= /usr/local
CC ?= gcc
CXX ?= g++
VERSION!=(grep 'define CTL_VERSION' ctl/ctl.h | cut -f3 -d' ')
VERSION ?= 202102

# probe for -std=c++20, 17 or 11
TRY_CXX20!=(${CXX} -std=c++20 -I. tests/func/test_deque.cc -o /dev/null && echo -std=c++20) || true
.if ${TRY_CXX20} != ""
CXX += -std=c++20
.else
TRY_CXX17!=(${CXX} -std=c++17 -I. tests/func/test_deque.cc -o /dev/null && echo -std=c++17) || true
. if ${TRY_CXX17} != ""
CXX += -std=c++17
. else
TRY_CXX11!=(${CXX} -std=c++11 -I. tests/func/test_deque.cc -o /dev/null && echo -std=c++11) || true
.  if ${TRY_CXX11} != ""
CXX += -std=c++11
.  endif
. endif
.endif
CC  += -std=c11

.SUFFIXES: .o .i .3 .cc .c .md
.PHONY: all man install clean doc images perf examples verify cppcheck asan \
        debug stress stress-long ALWAYS

#LONG ?= 0
#SANITIZE ?= 0
SRAND ?= 1

CFLAGS  = -I.
CFLAGS += -Wall -Wextra -Wpedantic -Wfatal-errors -Wshadow
CFLAGS += -g
# only targetting intel
CAN_MARCH_NATIVE!=(${CC} ${CFLAGS} -march=native tests/func/test_c11.c) || true
.if ${CAN_MARCH_NATIVE} != ""
CFLAGS += -march=native
.endif

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

.ifdef GCOV
Og = 1
CFLAGS += -fprofile-arcs -ftest-coverage -lgcov
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

CXXFLAGS += ${CFLAGS}

H        = ${wildcard ctl/*.h} 
COMMON_H = ctl/ctl.h ctl/algorithm.h ${wildcard ctl/bits/*.h}
TESTS = \
	tests/func/test_vector \
	tests/func/test_string \
	tests/func/test_array \
	tests/func/test_deque \
	tests/func/test_list \
	tests/func/test_set \
	tests/func/test_unordered_set \
	tests/func/test_priority_queue \
	tests/func/test_queue \
	tests/func/test_stack \
	tests/func/test_unordered_set_power2 \
	tests/func/test_unordered_set_cached \
	tests/func/test_unordered_set_sleep \
	tests/func/test_double_array \
	tests/func/test_int_vector \
	tests/func/test_vec_capacity \
	tests/func/test_str_capacity \
	tests/func/test_integral \
	tests/func/test_integral_c11 \
	tests/func/test_c11 \
	tests/func/test_container_composing \
	tests/func/test_generic_iter \
	tests/func/test_generic_iter2

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
check: ${TESTS} docs/index.md
.for t in ${TESTS}
	./${t}
.endfor
	@${CC} --version | head -n2
	@echo ${CC} ${CFLAGS}
	@${CXX} --version | head -n2
	@echo ${CXX} ${CXXFLAGS}

all: check perf examples api.lst #verify

api.lst: $(H)
	grep '^JOIN(A, ' ctl/*.h | perl -pe 's/JOIN\(A, (\w+?)\)/ $1/' >$@
.cflags: ALWAYS
	@echo "$(CC);$(CXX) $(CFLAGS)" >$@.tmp; cmp $@.tmp $@ || mv $@.tmp $@
images:
	./gen_images.sh

PERFS_C  = ${patsubst %.c,%, ${wildcard tests/perf/*/perf*.c} \
	     $(wildcard tests/perf/arr/gen_*.c)tests/perf/perf_compile_c11.c}
PERFS_CC = ${patsubst %.cc,%, ${wildcard tests/perf/*/perf*.cc} \
	     $(wildcard tests/perf/arr/gen_*.cc) tests/perf/perf_compile_cc.cc}

perf: ${PERFS_C} ${PERFS_CC} tests/perf/arr/perf_arr_generate

tests/perf/arr/perf_arr_generate: tests/perf/arr/perf_arr_generate.c
	$(CC) $(CFLAGS) -o $@ $@.c
	tests/perf/arr/perf_arr_generate

${wildcard tests/perf/lst/perf*.cc?} : ${COMMON_H} ctl/list.h
${wildcard tests/perf/set/perf*.cc?} : ${COMMON_H} ctl/set.h
${wildcard tests/perf/deq/perf*.cc?} : ${COMMON_H} ctl/deque.h
${wildcard tests/perf/pqu/perf*.cc?} : ${COMMON_H} ctl/priority_queue.h
${wildcard tests/perf/vec/perf*.cc?} : ${COMMON_H} ctl/vector.h
${wildcard tests/perf/uset/perf*.cc?}: ${COMMON_H} ctl/unordered_set.h
${wildcard tests/perf/arr/gen*.cc?}: ${COMMON_H} ctl/array.h
${wildcard tests/perf/str/perf*.cc?} : ${COMMON_H} ctl/vector.h ctl/string.h

examples: ${EXAMPLES}

MANPAGES = ${patsubst docs/%.md,docs/man/%.h.3, ${wildcard docs/*.md}}

man: docs/man/ctl.h.3 ${MANPAGES}

README.md: ${wildcard tests/func/test_*.cc}
	./update-grid.pl

docs/index.md : README.md
	./update-index.pl

RONN_ARGS=--manual "CTL Manual $(VERSION)" --organization=rurban/ctl
# FIXME
docs/man/ctl.h.3: docs/index.md
	@mkdir -p docs/man
	ronn ${RONN_ARGS} < $< > $@

docs/man/%.h.3 : docs/%.md
	@mkdir -p docs/man
	ronn ${RONN_ARGS} < $< > $@

clean:
	@rm -f .cflags .cflags.tmp
	@rm -f ${TESTS}
	@rm -f ${EXAMPLES}
	@rm -f ${PERFS_C} ${PERFS_CC} ${VERIFIY}
	@rm -f tests/perf/arr/perf_arr_generate
	@rm -f tests/perf/*.log
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

VERIFY = ${subst .c,, ${wildcard tests/verify/*.c}}

tests/verify/set-erase tests/verify/set-find : tests/verify/set-erase.c \
	                                       tests/verify/set-find.c .cflags ${H}
	${CC} ${CFLAGS} -o $@ $@.c && ./$@
	-cbmc --unwind 6 -I. $@.c

.for srcc1 in ${subst .c,, ${wildcard tests/verify/*-1.c}}
${srcc1} : ${srcc1}.c .cflags ${H}
	${CC} ${CFLAGS} -o $@ $@.c && ./$@
	-cbmc --unwind 4 -I. $@.c
.endfor
.for srcc2 in ${subst .c,, ${wildcard tests/verify/*-2.c}}
${srcc2} : ${srcc2}.c .cflags ${H}
	${CC} ${CFLAGS} -o $@ $@.c && ./$@
	-cbmc --unwind 6 -I. $@.c
	-for c in `satabs --show-claims -I. $@.c | \
                   perl -lne'/Claim (main.\d+):/ && print $$1'`; do \
             timeout 5m satabs --concurrency --max-threads 4 --iterations 24 --claim $$c -I. $@.c; \
         done
.endfor

verify: ${VERIFY}

cppcheck:
	cppcheck -j4 -I. tests/func/

#tests/func/%: tests/func/%.cc .cflags ${H}
#	${CXX} ${CXXFLAGS} -o $@ $@.cc
#tests/func/test_integral_c11: .cflags ${H} tests/func/test_integral_c11.c
#	${CC} ${CFLAGS} -o $@ $@.c
#tests/func/test_integral: .cflags ${H} tests/func/test_integral.cc
#	${CXX} ${CXXFLAGS} -o $@ $@.cc
#tests/func/test_container_composing: .cflags ${H} \
#                          tests/func/test_container_composing.cc
#	${CXX} ${CXXFLAGS} -o $@ $@.cc
#tests/func/test_generic_iter: .cflags ${H} \
#                          tests/func/test_generic_iter.cc
#	${CXX} ${CXXFLAGS} -o $@ $@.cc
tests/func/test_deque:    .cflags ${COMMON_H} tests/test.h tests/func/digi.hh ctl/deque.h \
                          tests/func/test_deque.cc
	${CXX} ${CXXFLAGS} -o $@ $@.cc
tests/func/test_list:     .cflags ${COMMON_H} tests/test.h tests/func/digi.hh ctl/list.h \
                          tests/func/test_list.cc
	${CXX} ${CXXFLAGS} -o $@ $@.cc
tests/func/test_forward_list: .cflags ${COMMON_H} tests/test.h tests/func/digi.hh ctl/forward_list.h \
                          tests/func/test_forward_list.cc
	${CXX} ${CXXFLAGS} -o $@ $@.cc
tests/func/test_priority_queue: .cflags ${COMMON_H} tests/test.h tests/func/digi.hh ctl/priority_queue.h ctl/vector.h \
                          tests/func/test_priority_queue.cc
	${CXX} ${CXXFLAGS} -o $@ $@.cc
tests/func/test_queue:    .cflags ${COMMON_H} tests/test.h tests/func/digi.hh ctl/queue.h ctl/deque.h \
                          tests/func/test_queue.cc
	${CXX} ${CXXFLAGS} -o $@ $@.cc
tests/func/test_set:      .cflags ${COMMON_H} tests/test.h tests/func/digi.hh ctl/set.h \
                          tests/func/test_set.cc
	${CXX} ${CXXFLAGS} -o $@ $@.cc
tests/func/test_map:      .cflags ${COMMON_H} tests/test.h tests/func/strint.hh ctl/map.h ctl/set.h \
                          tests/func/test_map.cc
	${CXX} ${CXXFLAGS} -o $@ $@.cc
tests/func/test_unordered_set: .cflags ${COMMON_H} tests/test.h tests/func/digi.hh ctl/unordered_set.h \
                          tests/func/test_unordered_set.cc
	${CXX} ${CXXFLAGS} -o $@ $@.cc
tests/func/test_unordered_set_power2: .cflags ${COMMON_H} tests/test.h tests/func/digi.hh ctl/unordered_set.h \
                          tests/func/test_unordered_set.cc
	${CXX} ${CXXFLAGS} -DCTL_USET_GROWTH_POWER2 tests/func/test_unordered_set.cc -o $@
tests/func/test_unordered_set_cached: .cflags ${COMMON_H} tests/test.h tests/func/digi.hh ctl/unordered_set.h \
                          tests/func/test_unordered_set.cc
	${CXX} ${CXXFLAGS} -DCTL_USET_CACHED_HASH tests/func/test_unordered_set.cc -o $@
tests/func/test_unordered_set_sleep: .cflags ${COMMON_H} tests/test.h ctl/unordered_set.h \
                          tests/func/test_unordered_set_sleep.c
	${CC} ${CFLAGS} -O3 -finline tests/func/test_unordered_set_sleep.c -o $@
tests/func/test_unordered_map: .cflags ${COMMON_H} tests/test.h tests/func/strint.hh ctl/unordered_map.h ctl/unordered_set.h \
                          tests/func/test_unordered_map.cc
	${CXX} ${CXXFLAGS} -o $@ $@.cc
tests/func/test_stack:    .cflags ${COMMON_H} tests/test.h tests/func/digi.hh ctl/stack.h ctl/deque.h \
                          tests/func/test_stack.cc
	${CXX} ${CXXFLAGS} -o $@ $@.cc
tests/func/test_string:   .cflags ${COMMON_H} tests/test.h ctl/string.h ctl/vector.h \
                          tests/func/test_string.cc
	${CXX} ${CXXFLAGS} -o $@ $@.cc
tests/func/test_str_capacity: .cflags ${COMMON_H} tests/test.h ctl/string.h ctl/vector.h \
                          tests/func/test_str_capacity.cc
	${CXX} ${CXXFLAGS} -o $@ $@.cc
tests/func/test_vec_capacity: .cflags ${COMMON_H} tests/test.h ctl/vector.h \
                          tests/func/test_vec_capacity.cc
	${CXX} ${CXXFLAGS} -o $@ $@.cc
tests/func/test_vector:   .cflags ${COMMON_H} tests/test.h tests/func/digi.hh ctl/vector.h \
                          tests/func/test_vector.cc
	${CXX} ${CXXFLAGS} -o $@ $@.cc
tests/func/test_array:   .cflags ${COMMON_H} tests/test.h tests/func/digi.hh ctl/array.h \
                          tests/func/test_array.cc
	${CXX} ${CXXFLAGS} -o $@ $@.cc
tests/func/test_double_array:   .cflags ${COMMON_H} tests/test.h ctl/array.h \
                          tests/func/test_double_array.cc
	${CXX} ${CXXFLAGS} -o $@ $@.cc
tests/func/test_int_vector: .cflags ${COMMON_H} tests/test.h ctl/vector.h \
                          tests/func/test_int_vector.cc
	${CXX} ${CXXFLAGS} -o $@ $@.cc

compile_commands.json : $(H) makefile
	make clean; bear make

asan:
	$(MAKE) SANITIZE=1
debug:
	$(MAKE) DEBUG=1
stress:
	if test -n "$(CTL)"; then timeout 10m sh -c "while $(MAKE) -s SANITIZE=1 \
	        tests/func/test_$(CTL) && tests/func/test_$(CTL); do true; done"; \
	else timeout 20m sh -c "while $(MAKE) -s SANITIZE=1; do true; done"; fi

stress-long:
	if test -n "$(CTL)"; then timeout 20m sh -c "while $(MAKE) -s SANITIZE=1 LONG=1 \
                tests/func/test_$(CTL) && tests/func/test_$(CTL); do true; done"; \
	else timeout 30m sh -c "while $(MAKE) -s SANITIZE=1 LONG=1; do true; done"; fi

.PHONY: test-c++ test-g++ test-clang++ test-icc test-pgc++
test-c++:
	for std in 20 2a 17 14 11 03 98; do $(MAKE) CXX="c++ -std=c++$$std"; done
test-g++:
	for std in 20 2a 17 14 11 03 98; do $(MAKE) CXX="g++ -std=c++$$std"; done
test-clang++:
	for std in 20 2a 17 14 11 03 98; do $(MAKE) CXX="clang++ -std=c++$$std"; done
test-icc:
	for std in 17 14 11 0x; do $(MAKE) CXX="icc -static-intel -std=c++$$std"; done
test-pgc++:
	for std in 20 2a 17 14 11 03 98; do $(MAKE) CXX="pgc++ -std=c++$$std"; done

# we skip some git files per default: .github/ docs/subdirs
dist: man
	-rm docs/man/index.h.3
	-rm docs/man/memory.h.3
	-rm docs/man/numeric.h.3
	rm -rf ctl-${VERSION}
	mkdir ctl-${VERSION}
	mkdir -p ctl-${VERSION}/ctl/bits
	mkdir -p ctl-${VERSION}/docs/images
	mkdir -p ctl-${VERSION}/docs/man
	cp docs/man/*.3 ctl-${VERSION}/docs/man/
	mkdir -p ctl-${VERSION}/examples
	mkdir -p ctl-${VERSION}/tests/{func,perf,verify}
	mkdir -p ctl-${VERSION}/tests/perf/{arr,deq,lst,pqu,set,str,uset,vec}
	for f in `git ls-tree -r --full-tree master|cut -c54-`; do \
          cp -p "$$f" "ctl-${VERSION}/$$f"; done
	-rm ctl-${VERSION}/.git*
	-rm ctl-${VERSION}/.cirrus.yml
	tar cfz ctl-${VERSION}.tar.gz ctl-${VERSION}
	tar cfJ ctl-${VERSION}.tar.xz ctl-${VERSION}
	rm -rf ctl-${VERSION}

install: man
	-rm docs/man/index.h.3
	-rm docs/man/memory.h.3
	-rm docs/man/numeric.h.3
	mkdir -p $(DESTDIR)$(PREFIX)/include/ctl/bits
	cp ctl/*.h $(DESTDIR)$(PREFIX)/include/ctl/
	cp ctl/bits/*.h $(DESTDIR)$(PREFIX)/include/ctl/bits/
	mkdir -p ${DESTDIR)${PREFIX)/share/man/man3
	cp docs/man/* ${DESTDIR)${PREFIX)/share/man/man3/
	mkdir -p ${DESTDIR)${PREFIX)/share/doc/ctl/images
	cp docs/*.md ${DESTDIR)${PREFIX)/share/doc/ctl/
	cp docs/images/*.log.png ${DESTDIR)${PREFIX)/share/doc/ctl/images/

ALWAYS:

# \
.endif
