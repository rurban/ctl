/* flat_multimap (C++23): sorted contiguous associative container of key/value
   pairs that keeps duplicate keys.  It is flat_set.h instantiated with
   CTL_FLAT_MULTI and the `fmmap` prefix; `T` is a key/value struct ordered by
   the key only.  Equal keys keep their insertion order.
   SPDX-License-Identifier: MIT */

#ifndef T
#error "Template struct type T undefined for <ctl/flat_multimap.h>"
#endif

#include <ctl/ctl.h>

#define CTL_FLAT_MULTI
#define fset fmmap
#include <ctl/flat_set.h>
#undef fset
