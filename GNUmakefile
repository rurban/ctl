PREFIX = /usr/local
CC ?= gcc
CXX ?= g++
VERSION := $(shell grep 'define CTL_VERSION' ctl/ctl.h | cut -f3 -d' ')
VERSION ?= 202103

.SUFFIXES: .cc .c .i .ii .o .md .3
.PHONY: all check man install clean doc images perf examples verify cppcheck asan \
        debug stress stress-long ALWAYS

TRY_CXX20 := $(shell $(CXX) -std=c++20 -I. tests/perf/lst/perf_list_push_back.cc -o /dev/null)
ifeq ($(.SHELLSTATUS),0)
CXX += -std=c++20
else
TRY_CXX2a := $(shell $(CXX) -std=c++2a -I. tests/perf/lst/perf_list_push_back.cc -o /dev/null)
ifeq ($(.SHELLSTATUS),0)
CXX += -std=c++2a
else
TRY_CXX17 := $(shell $(CXX) -std=c++17 -I. tests/perf/lst/perf_list_push_back.cc -o /dev/null)
ifeq ($(.SHELLSTATUS),0)
CXX += -std=c++17
else
TRY_CXX11 := $(shell $(CXX) -std=c++11 -I. tests/perf/lst/perf_list_push_back.cc -o /dev/null)
ifeq ($(.SHELLSTATUS),0)
CXX += -std=c++11
endif
endif
endif
endif
CC += -std=c11

LONG = 0
SANITIZE = 0
SRAND = 1
GCOV = 0

O0 = 0
O1 = 0
O2 = 0
O3 = 0
Og = 0
Ofast = 0
Os = 0

CFLAGS  = -I.
CFLAGS += -Wall -Wextra -Wpedantic -Wfatal-errors -Wshadow
CFLAGS += -g
# only targetting intel
TRY_MARCH_NATIVE := $(shell $(CC) $(CFLAGS) -march=native -mtune=native tests/verify/vector-1.c -o /dev/null)
ifeq ($(.SHELLSTATUS),0)
CFLAGS += -march=native -mtune=native
endif

ifeq (1, $(LONG))
CFLAGS += -Werror
CFLAGS += -DLONG
endif

ifeq (1, $(DEBUG))
O0 = 1
CFLAGS += -DDEBUG
endif

ifeq (1, $(SANITIZE))
CFLAGS += -fsanitize=address,undefined -fno-omit-frame-pointer -DHAVE_ASAN
endif

ifeq (1, $(GCOV))
Og = 1
CFLAGS += -fprofile-arcs -ftest-coverage -lgcov
endif

ifeq (1, $(Og))
CFLAGS += -Og
else
ifeq (1, $(O0))
CFLAGS += -O0
else
ifeq (1, $(O1))
CFLAGS += -O1
else
ifeq (1, $(O2))
CFLAGS += -O2
else
ifeq (1, $(O3))
CFLAGS += -O3
else
ifeq (1, $(Ofast))
CFLAGS += -Ofast
else
ifeq (1, $(Os))
CFLAGS += -Os
else
CFLAGS += -O3
endif
endif
endif
endif
endif
endif
endif

ifeq (1, $(SRAND))
CFLAGS += -DSRAND
ifneq ($(SEED),)
CFLAGS += -DSEED=$(SEED)
endif
else
ifneq ($(SEED),)
CFLAGS += -DSRAND -DSEED=$(SEED)
endif
endif

CXXFLAGS += $(CFLAGS)

H        = $(wildcard ctl/*.h) $(wildcard ctl/bits/*.h)
COMMON_H = ctl/ctl.h ctl/algorithm.h ctl/bits/container.h \
           ctl/bits/integral.h ctl/bits/iterators.h ctl/bits/iterator_vtable.h
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
	tests/func/test_forward_list \
	tests/func/test_unordered_set_power2 \
	tests/func/test_unordered_set_cached \
	tests/func/test_unordered_set_sleep \
	tests/func/test_swisstable \
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

ifneq ($(DEBUG),)
TESTS += \
	tests/func/test_map     \
	tests/func/test_unordered_map
endif

EXAMPLES = \
	examples/astar \
	examples/postfix \
	examples/json \
	examples/snow \
	examples/6502

check: $(TESTS) docs/index.md
	$(foreach bin,$(TESTS),./$(bin) &&) exit 0
	@$(CC) --version | head -n2
	@echo $(CC) $(CFLAGS)
	@$(CXX) --version | head -n2
	@echo $(CXX) $(CXXFLAGS)

all: check perf examples api.lst compile_commands.json verify

api.lst: $(H) GNUmakefile
	perl -lne'/^static.*JOIN\(A, (\w+)\)(.+\))$$/ && print "$$ARGV: $$1 $$2"' ctl/*.h > $@

.cflags: ALWAYS
	@echo "$(CC);$(CXX) $(CFLAGS)" >$@.tmp; cmp $@.tmp $@ >/dev/null || mv $@.tmp $@
images:
	./gen_images.sh

PERFS_C  = $(patsubst %.c,%, $(wildcard tests/perf/*/perf_*.c) \
           $(wildcard tests/perf/arr/gen_*.c) tests/perf/perf_compile_c11.c) \
           tests/perf/perf_compile_c11_algorithm
PERFS_CC = $(patsubst %.cc,%, $(wildcard tests/perf/*/perf_*.cc) \
	   $(wildcard tests/perf/arr/gen_*.cc) tests/perf/perf_compile_cc.cc) \
           tests/perf/perf_compile_cc_algorithm

tests/perf/arr/perf_arr_generate: tests/perf/arr/perf_arr_generate.c
	$(CC) $(CFLAGS) -o $@ $@.c
	tests/perf/arr/perf_arr_generate
perf: $(PERFS_C) $(PERFS_CC) tests/perf/arr/perf_arr_generate

$(wildcard tests/perf/lst/perf*.cc?) : $(COMMON_H) ctl/list.h
$(wildcard tests/perf/set/perf*.cc?) : $(COMMON_H) ctl/set.h
$(wildcard tests/perf/deq/perf*.cc?) : $(COMMON_H) ctl/deque.h
$(wildcard tests/perf/pqu/perf*.cc?) : $(COMMON_H) ctl/priority_queue.h
$(wildcard tests/perf/vec/perf*.cc?) : $(COMMON_H) ctl/vector.h
$(wildcard tests/perf/uset/perf*.cc?): $(COMMON_H) ctl/unordered_set.h
$(wildcard tests/perf/str/perf*.cc?): $(COMMON_H) ctl/string.h ctl/vector.h
$(wildcard tests/perf/arr/gen*.cc?): $(COMMON_H) ctl/array.h

tests/perf/arr/gen_array0% : tests/perf/arr/gen_array0%.cc \
  tests/perf/arr/perf_arr_generate .cflags $(COMMON_H) ctl/array.h
	@$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/perf/arr/gen_arr0% : tests/perf/arr/gen_arr0%.c \
  tests/perf/arr/perf_arr_generate .cflags $(COMMON_H) ctl/array.h
	@$(CC) $(CFLAGS) -o $@ $@.c
tests/perf/perf_compile_c11_algorithm: $(H) tests/perf/perf_compile_c11.c
	$(CC) $(CFLAGS) -DALGORITHM -o $@ tests/perf/perf_compile_c11.c
tests/perf/perf_compile_cc_algorithm: tests/perf/perf_compile_cc.cc
	$(CXX) $(CXXFLAGS) -DALGORITHM -o $@ tests/perf/perf_compile_cc.cc

compile_commands.json : $(H) GNUmakefile
	-make clean
	bear -- make

examples: $(EXAMPLES)

VERIFY = $(patsubst %.c,%, $(wildcard tests/verify/*.c))
CBMC_CHECKS=--bounds-check --pointer-check --memory-leak-check            \
  --div-by-zero-check --signed-overflow-check --unsigned-overflow-check   \
  --pointer-overflow-check --conversion-check --undefined-shift-check     \
  --float-overflow-check --nan-check --enum-range-check
  # cbmc 5.12.1: --pointer-primitive-check

tests/verify/% : tests/verify/%.c $(H)
	$(CC) $(CFLAGS) $@.c -o $@ && ./$@
	if which cbmc; then \
          cbmc $(CBMC_CHECKS) --compact-trace --depth 6  --unwind 6 -I. $@.c; \
        else true; fi
tests/verify/%-2 : tests/verify/%-2.c $(H)
	$(CC) $(CFLAGS) $@.c -o $@ && ./$@
	if which cbmc; then \
          cbmc $(CBMC_CHECKS) --compact-trace --depth 6 --unwind 6 -I. $@.c; \
        else true; fi
	#if which satabs; then for c in `tests/verify/all_claims.sh $@.c`; do \
        #    echo satabs --claim "$$c" -I. $@.c; \
        #    timeout 5m satabs --concurrency --max-threads 4 --iterations 24 --claim "$$c" -I. $@.c; \
        #  done; else true; fi

verify: $(VERIFY)

cppcheck:
	cppcheck -j4 -I. --check-level=exhaustive tests/func/

MANPAGES = $(patsubst docs/%.md,docs/man/%.h.3, $(wildcard docs/*.md))

README.md: ./update-grid.pl tests/func/test_vector tests/func/test_string \
  tests/func/test_array tests/func/test_deque tests/func/test_list tests/func/test_set \
  tests/func/test_unordered_set	tests/func/test_priority_queue tests/func/test_queue \
  tests/func/test_stack
	./update-grid.pl

docs/index.md : README.md ./update-index.pl
	./update-index.pl

man: docs/man/ctl.h.3 $(MANPAGES)
	-rm docs/man/index.h.3
	-rm docs/man/memory.h.3
	-rm docs/man/numeric.h.3

RONN_ARGS=--manual "CTL Manual $(VERSION)" --organization=rurban/ctl
# FIXME
docs/man/ctl.h.3: docs/index.md
	@mkdir -p docs/man
	ronn $(RONN_ARGS) < $< > $@

docs/man/%.h.3 : docs/%.md
	@mkdir -p docs/man
	ronn $(RONN_ARGS) < $< > $@

clean:
	@rm -f .cflags .cflags.tmp
	@rm -f $(TESTS)
	@rm -f $(EXAMPLES)
	@rm -f $(PERFS_C) $(PERFS_CC) $(VERIFY)
	@rm -f *.gcov *.gcda *.gcno
	@rm -f tests/perf/arr/perf_arr_generate tests/perf/arr/gen_arr*
	@rm -f tests/perf/*.log
	@rm -f docs/man/ctl.h.3 $(MANPAGES)
	@if test -d docs/man; then rmdir docs/man; fi

help:
	@echo " make targets for the ctl, a header-only library for C"
	@echo " "
	@echo " all, check: run all tests"
	@echo " images:     generate the performance graphs"
	@echo " perf:       compile the performance binaries seperately"
	@echo " examples:   compile the examples"
	@echo " man:        create the manpages in docs/man"
	@echo " install:    copy to $(DESTDIR)$(PREFIX)/include/ctl"
	@echo "                     $(DESTDIR)$(PREFIX)/share/man/man3"
	@echo "                     $(DESTDIR)$(PREFIX)/share/doc/ctl"
	@echo " clean:      the tests, perf, examples and manpages"
	@echo " <file>.i:   expand the file with -DT=int for debugging"

ctl/string.i:
	$(call expand,$(subst .i,,$@))
ctl/map.i:
	$(call expand,$(subst .i,,$@),-DTK=charp -DT=int -DPOD)
ctl/array.i:
	$(call expand,$(subst .i,,$@),-DT=int -DN=128 -DPOD)
ctl/unordered_map.i:
	$(call expand,$(subst .i,,$@),-DTK=charp -DT=int -DPOD)
ctl/swisstable.i:
	$(call expand,$(subst .i,,$@),-DTK=charp -DT=int -DPOD)

%.i : %.h
	@$(CC) $(CFLAGS) -DT=int -DPOD $< -E | clang-format -style=webkit
%.i : %.c
	@$(CC) $(CFLAGS) $< -E | clang-format -style=webkit
%.i : %.cc
	@$(CXX) $(CFLAGS) $< -E | clang-format -style=webkit
%.ii : %.cc
	@$(CXX) $(CFLAGS) $< -E -P | clang-format -style=webkit

examples/% : examples/%.c .cflags $(H)
	$(CC) $(CFLAGS) -o $@ $@.c

tests/func/test_deque:    .cflags $(COMMON_H) tests/test.h tests/func/digi.hh ctl/deque.h \
                          tests/func/test_deque.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_list:     .cflags $(COMMON_H) tests/test.h tests/func/digi.hh ctl/list.h \
                          tests/func/test_list.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_forward_list: .cflags $(COMMON_H) tests/test.h tests/func/digi.hh ctl/forward_list.h \
                          tests/func/test_forward_list.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_priority_queue: .cflags $(COMMON_H) tests/test.h \
                          tests/func/digi.hh ctl/priority_queue.h ctl/vector.h \
                          tests/func/test_priority_queue.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_queue:    .cflags $(COMMON_H) tests/test.h tests/func/digi.hh ctl/queue.h ctl/deque.h \
                          tests/func/test_queue.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_set:      .cflags $(COMMON_H) tests/test.h tests/func/digi.hh ctl/set.h \
                          tests/func/test_set.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_map:      .cflags $(H) tests/test.h tests/func/strint.hh ctl/set.h ctl/map.h tests/func/test_map.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_unordered_set: .cflags $(COMMON_H) ctl/unordered_set.h \
                          tests/func/test_unordered_set.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_unordered_set_power2: .cflags $(COMMON_H) tests/test.h tests/func/digi.hh ctl/unordered_set.h \
                          tests/func/test_unordered_set.cc
	$(CXX) $(CXXFLAGS) -DCTL_USET_GROWTH_POWER2 tests/func/test_unordered_set.cc -o $@
tests/func/test_unordered_set_cached: .cflags $(COMMON_H) tests/test.h tests/func/digi.hh ctl/unordered_set.h \
                          tests/func/test_unordered_set.cc
	$(CXX) $(CXXFLAGS) -DCTL_USET_CACHED_HASH tests/func/test_unordered_set.cc -o $@
tests/func/test_unordered_set_sleep: .cflags $(COMMON_H) tests/test.h ctl/unordered_set.h \
                          tests/func/test_unordered_set_sleep.c
	$(CC) $(CFLAGS) -O3 -finline tests/func/test_unordered_set_sleep.c -o $@
tests/func/test_unordered_map: .cflags $(COMMON_H) tests/test.h tests/func/strint.hh \
                          tests/func/test_unordered_map.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_swisstable: .cflags $(COMMON_H) tests/test.h tests/func/strint.hh \
                          tests/func/test_swisstable.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_stack:    .cflags $(COMMON_H) tests/test.h tests/func/digi.hh ctl/stack.h ctl/deque.h \
                          tests/func/test_stack.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_string:   .cflags $(COMMON_H) tests/test.h ctl/string.h ctl/vector.h \
                          tests/func/test_string.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_str_capacity: .cflags $(COMMON_H) tests/test.h ctl/string.h ctl/vector.h \
                          tests/func/test_str_capacity.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_vec_capacity: .cflags $(COMMON_H) tests/test.h ctl/vector.h \
                          tests/func/test_vec_capacity.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_vector:   .cflags $(COMMON_H) tests/test.h tests/func/digi.hh ctl/vector.h \
                          tests/func/test_vector.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_array:   .cflags $(COMMON_H) tests/test.h tests/func/digi.hh ctl/array.h \
                          tests/func/test_array.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_double_array:   .cflags $(COMMON_H) tests/test.h tests/func/digi.hh ctl/array.h \
                          tests/func/test_double_array.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_generic_iter: .cflags $(H) tests/test.h tests/func/test_generic_iter.h \
                          tests/func/test_generic_iter.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_generic_iter2: .cflags $(H) tests/test.h tests/func/test_generic_iter.h \
                          tests/func/test_generic_iter2.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/%: tests/func/%.c .cflags $(H) tests/test.h
	$(CC) $(CFLAGS) -o $@ $@.c
tests/func/%: tests/func/%.cc .cflags $(H) tests/test.h
	$(CXX) $(CXXFLAGS) -o $@ $@.cc

asan:
	$(MAKE) SANITIZE=1
debug:
	$(MAKE) DEBUG=1
gcov: clean
	${MAKE} GCOV=1
stress:
	if test -n "$(CTL)"; then timeout 10m sh -c "while $(MAKE) -s SANITIZE=1 \
	        tests/func/test_$(CTL) && tests/func/test_$(CTL); do true; done"; \
	else timeout 20m sh -c "while $(MAKE) -s SANITIZE=1; do true; done"; fi

stress-long:
	if test -n "$(CTL)"; then timeout 20m sh -c "while $(MAKE) -s SANITIZE=1 LONG=1 \
                tests/func/test_$(CTL) && tests/func/test_$(CTL); do true; done"; \
	else timeout 30m sh -c "while $(MAKE) -s SANITIZE=1 LONG=1; do true; done"; fi

# no -std=gnu++NN extensions
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

define expand
	@$(CC) $(CFLAGS) $(1).h -E $(2) | clang-format -style=webkit
endef

# we skip some git files per default: .github/ docs/subdirs
dist: man
	-rm docs/man/index.h.3
	-rm docs/man/memory.h.3
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
	mkdir -p $(DESTDIR)$(PREFIX)/share/man/man3
	cp docs/man/* $(DESTDIR)$(PREFIX)/share/man/man3/
	mkdir -p $(DESTDIR)$(PREFIX)/share/doc/ctl/images
	cp docs/*.md $(DESTDIR)$(PREFIX)/share/doc/ctl/
	cp docs/images/*.log.png $(DESTDIR)$(PREFIX)/share/doc/ctl/images/

# emacs flymake-mode
check-syntax:
	case "$(CHK_SOURCES)" in \
          ctl/bits/*.h) \
            nice $(CXX) $(CXXFLAGS) -O0 -c tests/func/test_vector ;; \
          ctl/*.h) \
            nice $(CXX) $(CXXFLAGS) -O0 -c tests/func/test_$(subst .h,.cc,$(subst ctl/,,${CHK_SOURCES})) ;; \
          *.c) \
            nice $(CC) $(CFLAGS) -O0 -c ${CHK_SOURCES} ;; \
          *.cc) \
            nice $(CXX) $(CXXFLAGS) -O0 -c ${CHK_SOURCES} ;; \
        esac

.PHONY: check-syntax

ALWAYS:
