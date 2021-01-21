PREFIX = /usr/local
CC ?= gcc
CXX ?= g++

.SUFFIXES: .cc .c .i .o .md .3
.PHONY: all man install clean doc images perf examples asan debug stress stress-long ALWAYS

TRY_CXX20 := $(shell $(CXX) -std=c++20 -I. tests/func/test_deque.cc -o /dev/null)
ifeq ($(.SHELLSTATUS),0)
CXX += -std=c++20
else
TRY_CXX2a := $(shell $(CXX) -std=c++2a -I. tests/func/test_deque.cc -o /dev/null)
ifeq ($(.SHELLSTATUS),0)
CXX += -std=c++2a
else
TRY_CXX17 := $(shell $(CXX) -std=c++17 -I. tests/func/test_deque.cc -o /dev/null)
ifeq ($(.SHELLSTATUS),0)
CXX += -std=c++17
else
TRY_CXX11 := $(shell $(CXX) -std=c++11 -I. tests/func/test_deque.cc -o /dev/null)
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

O0 = 0
O1 = 0
O2 = 0
O3 = 0
Og = 0
Ofast = 0
Os = 0

CFLAGS  = -I.
CFLAGS += -Wall -Wextra -Wpedantic -Wfatal-errors -Wshadow
CFLAGS += -march=native
CFLAGS += -g

ifeq (1, $(LONG))
CFLAGS += -Werror
CFLAGS += -DLONG
endif

ifeq (1, $(DEBUG))
O0 = 1
CFLAGS += -DDEBUG
endif

ifeq (1, $(SANITIZE))
CFLAGS += -fsanitize=address,undefined -fno-omit-frame-pointer
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

H        = $(wildcard ctl/*.h) ctl/bits/*.h
COMMON_H = ctl/ctl.h ctl/algorithm.h ctl/bits/container.h \
           ctl/bits/integral.h ctl/bits/iterators.h
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

all: $(TESTS) docs/index.md
	$(foreach bin,$(TESTS),./$(bin) &&) exit 0
	@$(CC) --version | head -n2
	@echo $(CC) $(CFLAGS)
	@$(CXX) --version | head -n2
	@echo $(CXX) $(CXXFLAGS)

check: all
.cflags: ALWAYS
	@echo "$(CC);$(CXX) $(CFLAGS)" >$@.tmp; cmp $@.tmp $@ || mv $@.tmp $@
images:
	./gen_images.sh

PERFS_C  = $(patsubst %.c,%, $(wildcard tests/perf/*/perf*.c) tests/perf/perf_compile_c11.c)
PERFS_CC = $(patsubst %.cc,%, $(wildcard tests/perf/*/perf*.cc) tests/perf/perf_compile_cc.cc)

perf: $(PERFS_C) $(PERFS_CC)

$(wildcard tests/perf/lst/perf*.c) : $(COMMON_H) ctl/list.h
$(wildcard tests/perf/set/perf*.c) : $(COMMON_H) ctl/set.h
$(wildcard tests/perf/deq/perf*.c) : $(COMMON_H) ctl/deque.h
$(wildcard tests/perf/pqu/perf*.c) : $(COMMON_H) ctl/priority_queue.h
$(wildcard tests/perf/vec/perf*.c) : $(COMMON_H) ctl/vector.h
$(wildcard tests/perf/uset/perf*.c): $(COMMON_H) ctl/unordered_set.h

examples: $(EXAMPLES)

MANPAGES = $(patsubst docs/%.md,docs/man/%.h.3, $(wildcard docs/*.md))

docs/index.md : README.md
	./update-index.pl

man: docs/man/ctl.h.3 $(MANPAGES)

docs/man/ctl.h.3: docs/index.md
	@mkdir -p docs/man
	ronn < $< > $@
docs/man/%.h.3 : docs/%.md
	ronn < $< > $@

install: man
	-rm docs/man/index.h.3
	mkdir -p $(DESTDIR)$(PREFIX)/include/ctl
	cp ctl/*.h $(DESTDIR)$(PREFIX)/include/ctl/
	mkdir -p $(DESTDIR)$(PREFIX)/share/man/man3
	cp docs/man/* $(DESTDIR)$(PREFIX)/share/man/man3/
	mkdir -p $(DESTDIR)$(PREFIX)/share/doc/ctl/images
	cp docs/*.md $(DESTDIR)$(PREFIX)/share/doc/ctl/
	cp -r docs/*/*.md $(DESTDIR)$(PREFIX)/share/doc/ctl/
	cp docs/images/*.log.png $(DESTDIR)$(PREFIX)/share/doc/ctl/images/

clean:
	@rm -f .cflags .cflags.tmp
	@rm -f $(TESTS)
	@rm -f $(EXAMPLES)
	@rm -f $(PERFS_C) $(PERFS_CC)
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
	$(call expand,$(subst .i,,$@),-DT=strint -DPOD)
ctl/unordered_map.i:
	$(call expand,$(subst .i,,$@),-DT=strint -DPOD)

%.i : %.h
	@$(CC) $(CFLAGS) -DT=int -DPOD $< -E | clang-format -style=webkit
%.i : %.c
	@$(CC) $(CFLAGS) $< -E | clang-format -style=webkit
%.i : %.cc
	@$(CXX) $(CFLAGS) $< -E | clang-format -style=webkit

examples/% : examples/%.c .cflags $(H)
	$(CC) $(CFLAGS) -o $@ $@.c

tests/func/test_deque:    .cflags $(COMMON_H) ctl/deque.h \
                          tests/func/test_deque.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_list:     .cflags $(COMMON_H) ctl/list.h \
                          tests/func/test_list.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_priority_queue: .cflags $(COMMON_H) ctl/priority_queue.h ctl/vector.h \
                          tests/func/test_priority_queue.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_queue:    .cflags $(COMMON_H) ctl/queue.h ctl/deque.h \
                          tests/func/test_queue.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_set:      .cflags $(COMMON_H) ctl/set.h \
                          tests/func/test_set.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_map:      .cflags $(COMMON_H) ctl/map.h ctl/set.h \
                          tests/func/test_map.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_unordered_set: .cflags $(COMMON_H) ctl/unordered_set.h \
                          tests/func/test_unordered_set.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_unordered_set_power2: .cflags $(COMMON_H) ctl/unordered_set.h \
                          tests/func/test_unordered_set.cc
	$(CXX) $(CXXFLAGS) -DCTL_USET_GROWTH_POWER2 tests/func/test_unordered_set.cc -o $@
tests/func/test_unordered_set_cached: .cflags $(COMMON_H) ctl/unordered_set.h \
                          tests/func/test_unordered_set.cc
	$(CXX) $(CXXFLAGS) -DCTL_USET_CACHED_HASH tests/func/test_unordered_set.cc -o $@
tests/func/test_unordered_map: .cflags $(COMMON_H) ctl/unordered_map.h ctl/unordered_set.h \
                          tests/func/test_unordered_map.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_stack:    .cflags $(COMMON_H) ctl/stack.h ctl/deque.h \
                          tests/func/test_stack.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_string:   .cflags $(COMMON_H) ctl/string.h ctl/vector.h \
                          tests/func/test_string.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_str_capacity: .cflags $(COMMON_H) ctl/string.h ctl/vector.h \
                          tests/func/test_str_capacity.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_vec_capacity: .cflags $(COMMON_H) ctl/vector.h \
                          tests/func/test_vec_capacity.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/test_vector:   .cflags $(COMMON_H) ctl/vector.h \
                          tests/func/test_vector.cc
	$(CXX) $(CXXFLAGS) -o $@ $@.cc
tests/func/%: tests/func/%.c .cflags $(H)
	$(CC) $(CFLAGS) -o $@ $@.c
tests/func/%: tests/func/%.cc .cflags $(H)
	$(CXX) $(CXXFLAGS) -o $@ $@.cc

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

ALWAYS:
