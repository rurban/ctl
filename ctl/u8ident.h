/* POSIX std extension for people using utf-8 identifiers, but
   need security. See http://unicode.org/reports/tr39/
   Like a kernel filesystem or user database, in a UTF-8 terminal,
   wishes to present identifiers, like names, paths or files identifiable.
   I.e. normalized and with identifiable characters only. Most don't display
   names as puny-code.
   Implement the Moderately Restrictive restriction level as default.

   * All characters in the string are in the ASCII range, or
   * The string is single-script, according to the definition in Section 5.1, or
   * The string is covered by any of the following sets of scripts, according to
     the definition in TR29 Section 5.1:
        Latin + Han + Hiragana + Katakana; or equivalently: Latn + Jpan
        Latin + Han + Bopomofo; or equivalently: Latn + Hanb
        Latin + Han + Hangul; or equivalently: Latn + Kore, or
   * The string is covered by Latin and any one other Recommended script, except Cyrillic, Greek.
   * The string must be validated UTF-8 and normalized, and only consist of valid identifier
     characters.

   Reject violations, optionally warn about confusables.
   SPDX-License-Identifier: MIT */

#ifndef __CTL_U8IDENT_H__
#define __CTL_U8IDENT_H__

#ifdef T
#error "Template type T defined for <ctl/u8ident.h>"
#endif

#define HOLD
#define u8id_char8_t u8id
#define vec u8id
#define A u8id
#include <ctl/u8string.h>

// TODO Take my code from cperl, which has stable unicode security for some years.
// I'm also just adding this to my safeclib.
// The only other existing example of proper unicode security is Java.

#undef A
#undef I
#undef T
#undef POD
#undef HOLD

#endif
