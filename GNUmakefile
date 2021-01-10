PREFIX = /usr/local
CC = gcc
CXX = g++

.SUFFIXES: .cc .c .i .o .md .3
.PHONY: all man install clean doc images perf examples ALWAYS

TRY_CXX20 := $(shell $(CXX) -std=c++20 -I. tests/func/test_deque.cc -o /dev/null)
ifneq ($(.SHELLSTATUS),0)
TRY_CXX17 := $(shell $(CXX) -std=c++17 -I. tests/func/test_deque.cc -o /dev/null)
ifeq ($(.SHELLSTATUS),0)
CXX += -std=c++17
endif
else
CXX += -std=c++20
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

CXXFLAGS=$(CFLAGS)

H        = $(wildcard ctl/*.h) ctl/bits/*.h
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
	tests/func/test_stack \
	tests/func/test_vec_capacity \
	tests/func/test_vector
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

all: $(TESTS)
	$(foreach bin,$(TESTS),./$(bin) &&) exit 0
	@$(CC) --version | head -n2
	@echo $(CC) $(CFLAGS)
	@$(CXX) --version | head -n2
	@echo $(CXX) $(CXXFLAGS)

check: all
.cflags: ALWAYS
	@echo "$(CFLAGS)" >$@.tmp; cmp $@.tmp $@ || mv $@.tmp $@
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

man: docs/man/ctl.h.3 $(MANPAGES)

docs/man/ctl.h.3: docs/index.md
	@mkdir -p docs/man
	ronn < $< > $@
docs/man/%.h.3 : docs/%.md
	ronn < $< > $@

install: man
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
	@$(CXX) $(CFLAGS) $< -P -E | clang-format -style=webkit

examples/% : examples/%.c .cflags $(H)
	$(CC) $(CFLAGS) -o $@ $@.c

tests/func/%: tests/func/%.c .cflags $(H)
	$(CC) $(CFLAGS) -o $@ $@.c
tests/func/%: tests/func/%.cc .cflags $(H)
	$(CXX) $(CFLAGS) -o $@ $@.cc
tests/func/test_deque:    .cflags $(COMMON_H) ctl/deque.h \
                          tests/func/test_deque.cc
	$(CXX) $(CFLAGS) -o $@ $@.cc
tests/func/test_list:     .cflags $(COMMON_H) ctl/list.h \
                          tests/func/test_list.cc
	$(CXX) $(CFLAGS) -o $@ $@.cc
tests/func/test_priority_queue: .cflags $(COMMON_H) ctl/priority_queue.h ctl/vector.h \
                          tests/func/test_priority_queue.cc
	$(CXX) $(CFLAGS) -o $@ $@.cc
tests/func/test_queue:    .cflags $(COMMON_H) ctl/queue.h ctl/deque.h \
                          tests/func/test_queue.cc
	$(CXX) $(CFLAGS) -o $@ $@.cc
tests/func/test_set:      .cflags $(COMMON_H) ctl/set.h \
                          tests/func/test_set.cc
	$(CXX) $(CFLAGS) -o $@ $@.cc
tests/func/test_map:      .cflags $(COMMON_H) ctl/map.h ctl/set.h \
                          tests/func/test_map.cc
	$(CXX) $(CFLAGS) -o $@ $@.cc
tests/func/test_unordered_set: .cflags $(COMMON_H) ctl/unordered_set.h \
                          tests/func/test_unordered_set.cc
	$(CXX) $(CFLAGS) -o $@ $@.cc
tests/func/test_unordered_set_power2: .cflags $(COMMON_H) ctl/unordered_set.h \
                          tests/func/test_unordered_set.cc
	$(CXX) $(CFLAGS) -DCTL_USET_GROWTH_POWER2 tests/func/test_unordered_set.cc -o $@
tests/func/test_unordered_map: .cflags $(COMMON_H) ctl/unordered_map.h ctl/unordered_set.h \
                          tests/func/test_unordered_map.cc
	$(CXX) $(CFLAGS) -o $@ $@.cc
tests/func/test_stack:    .cflags $(COMMON_H) ctl/stack.h ctl/deque.h \
                          tests/func/test_stack.cc
	$(CXX) $(CFLAGS) -o $@ $@.cc
tests/func/test_string:   .cflags $(COMMON_H) ctl/string.h ctl/vector.h \
                          tests/func/test_string.cc
	$(CXX) $(CFLAGS) -o $@ $@.cc
tests/func/test_vec_capacity: .cflags $(COMMON_H) ctl/vector.h \
                          tests/func/test_vec_capacity.cc
	$(CXX) $(CFLAGS) -o $@ $@.cc
tests/func/test_vector:   .cflags $(COMMON_H) ctl/vector.h \
                          tests/func/test_vector.cc
	$(CXX) $(CFLAGS) -o $@ $@.cc

define expand
	@$(CC) $(CFLAGS) $(1).h -E $(2) | clang-format -style=webkit
endef

ALWAYS:
