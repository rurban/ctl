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
CFLAGS += -fsanitize=address -fsanitize=undefined
endif

ifeq (1, $(Og))
CFLAGS += -Og
endif

ifeq (1, $(O0))
CFLAGS += -O0
endif

ifeq (1, $(O1))
CFLAGS += -O1
endif

ifeq (1, $(O2))
CFLAGS += -O2
endif

ifeq (1, $(O3))
CFLAGS += -O3
endif

ifeq (1, $(Ofast))
CFLAGS += -Ofast
endif

ifeq (1, $(Os))
CFLAGS += -Os
endif

ifeq (1, $(SRAND))
CFLAGS += -DSRAND
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
	@$(CC) --version
	@$(CXX) --version
	@rm -f $(TESTS)

examples: $(EXAMPLES)

clean:
	@rm -f $(TESTS)
	@rm -f $(EXAMPLES)

string:
	$(call expand,$@)
list:
	$(call expand,$@,-DT=int -DP)
vector:
	$(call expand,$@,-DT=int -DP)
deque:
	$(call expand,$@,-DT=int -DP)
stack:
	$(call expand,$@,-DT=int -DP)
queue:
	$(call expand,$@,-DT=int -DP)
priority_queue:
	$(call expand,$@,-DT=int -DP)
set:
	$(call expand,$@,-DT=int -DP)

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
