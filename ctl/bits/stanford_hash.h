/* "stanford hash": Murmur3-style avalanche finalizer, optimal as a cheap,
   dependency-free default hash for plain integer/POD-scalar keys.

   The 32-bit step is hash32() from stanford-futuredata/index-baselines
   hashing.cpp (the SIMD bucketized cuckoo hashmap baseline for "The Case
   for Learned Index Structures", Kraska et al. 2018), itself the
   MurmurHash3 32-bit finalizer (fmix32).
   Copyright (c) 2017-present Peter Bailis, Kai Sheng Tai, Pratiksha
   Thaker, Matei Zaharia. MIT License.
   https://github.com/stanford-futuredata/index-baselines/blob/master/hashing.cpp

   The 64-bit step is the matching MurmurHash3 64-bit finalizer (fmix64),
   used here so size_t keys on LP64 platforms get full-width avalanche.

   SPDX-License-Identifier: MIT
*/
#ifndef CTL_STANFORD_HASH_H
#define CTL_STANFORD_HASH_H

#include <stddef.h>
#include <stdint.h>

static inline uint32_t stanford_hash32(uint32_t value)
{
    value ^= value >> 16;
    value *= 0x85ebca6bu;
    value ^= value >> 13;
    value *= 0xc2b2ae35u;
    value ^= value >> 16;
    return value;
}

static inline uint64_t stanford_hash64(uint64_t value)
{
    value ^= value >> 33;
    value *= 0xff51afd7ed558ccdULL;
    value ^= value >> 33;
    value *= 0xc4ceb9fe1a85ec53ULL;
    value ^= value >> 33;
    return value;
}

// Dispatches on the platform's size_t width.
static inline size_t stanford_hash(size_t value)
{
    return sizeof(size_t) > 4 ? (size_t)stanford_hash64((uint64_t)value) : (size_t)stanford_hash32((uint32_t)value);
}

#endif // CTL_STANFORD_HASH_H
