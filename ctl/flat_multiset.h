/* flat_multiset (C++23): sorted contiguous associative container that keeps
   duplicate keys.  It is flat_set.h instantiated with CTL_FLAT_MULTI and the
   `fmset` prefix.  Equal keys keep their insertion order (upper-bound insert).
   SPDX-License-Identifier: MIT */

#ifndef T
#error "Template type T undefined for <ctl/flat_multiset.h>"
#endif

#include <ctl/ctl.h>

#define CTL_FLAT_MULTI
#define fset fmset
#include <ctl/flat_set.h>
#undef fset
