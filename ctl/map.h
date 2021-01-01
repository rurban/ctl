/* Unordered, in opposition to C++ STL. Derived from unordered_set */

#ifndef T
#error "Template type T undefined for <ctl/map.h>"
#endif

#include <ctl/ctl.h>

// TODO emplace

#define uset map
#include <ctl/unordered_set.h>
#undef uset
