CC = gcc -std=c11
CXX = g++ -std=c++17

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

TESTS = \
	tests/func/test_c11 \
	tests/func/test_container_composing \
	tests/func/test_deque \
	tests/func/test_list \
	tests/func/test_string \
	tests/func/test_priority_queue \
	tests/func/test_queue \
	tests/func/test_set \
	tests/func/test_stack \
	tests/func/test_vec_capacity \
	tests/func/test_vector

EXAMPLES = \
	examples/astar \
	examples/postfix \
	examples/json \
	examples/snow \
	examples/6502

all: $(TESTS)
	$(foreach bin,$(TESTS),./$(bin) &&) exit 0
	@echo CFLAGS=$(CFLAGS)
	@$(CC) --version
	@echo CXXFLAGS=$(CXXFLAGS)
	@$(CXX) --version
	@rm -f $(TESTS)

PERFS_C  = $(patsubst %.c,%, $(wildcard tests/perf/*/perf*.c) tests/perf/perf_compile_c11.c)
PERFS_CC = $(patsubst %.cc,%, $(wildcard tests/perf/*/perf*.cc) tests/perf/perf_compile_cc.cc)

perf: $(PERFS_C) $(PERFS_CC)

examples: $(EXAMPLES)

clean:
	@rm -f $(TESTS)
	@rm -f $(EXAMPLES)

string.i:
	$(call expand,$(subst .i,,$@))
list.i:
	$(call expand,$(subst .i,,$@),-DT=int -DPOD)
vector.i:
	$(call expand,$(subst .i,,$@),-DT=int -DPOD)
deque.i:
	$(call expand,$(subst .i,,$@),-DT=int -DPOD)
stack.i:
	$(call expand,$(subst .i,,$@),-DT=int -DPOD)
queue.i:
	$(call expand,$(subst .i,,$@),-DT=int -DPOD)
priority_queue.i:
	$(call expand,$(subst .i,,$@),-DT=int -DPOD)
set.i:
	$(call expand,$(subst .i,,$@),-DT=int -DPOD)

examples/astar:                      ALWAYS; $(CC)  $(CFLAGS) $@.c  -o $@
examples/postfix:                    ALWAYS; $(CC)  $(CFLAGS) $@.c  -o $@
examples/json:                       ALWAYS; $(CC)  $(CFLAGS) $@.c  -o $@
examples/snow:                       ALWAYS; $(CC)  $(CFLAGS) $@.c  -o $@
examples/6502:                       ALWAYS; $(CC)  $(CFLAGS) $@.c  -o $@
tests/func/test_c11:                 ALWAYS; $(CC)  $(CFLAGS) $@.c  -o $@
tests/func/test_container_composing: ALWAYS; $(CXX) $(CFLAGS) $@.cc -o $@
tests/func/test_deque:               ALWAYS; $(CXX) $(CFLAGS) $@.cc -o $@
tests/func/test_list:                ALWAYS; $(CXX) $(CFLAGS) $@.cc -o $@
tests/func/test_priority_queue:      ALWAYS; $(CXX) $(CFLAGS) $@.cc -o $@
tests/func/test_queue:               ALWAYS; $(CXX) $(CFLAGS) $@.cc -o $@
tests/func/test_set:                 ALWAYS; $(CXX) $(CFLAGS) $@.cc -o $@
tests/func/test_stack:               ALWAYS; $(CXX) $(CFLAGS) $@.cc -o $@
tests/func/test_string:              ALWAYS; $(CXX) $(CFLAGS) $@.cc -o $@
tests/func/test_vec_capacity:        ALWAYS; $(CXX) $(CFLAGS) $@.cc -o $@
tests/func/test_vector:              ALWAYS; $(CXX) $(CFLAGS) $@.cc -o $@

define expand
	@$(CC) $(CFLAGS) ctl/$(1).h -E $(2) | clang-format -style=webkit
endef

ALWAYS:
