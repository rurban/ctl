# bvector

`<ctl/bvector.h>` provides `bvec`, a packed dynamic boolean vector. Values occupy one bit each; capacity is rounded to 64-bit words.

```c
bvec flags = bvec_init();
bvec_push_back(&flags, true);
bvec_set(&flags, 0, false);
bvec_free(&flags);
```

API: `init`, `size`, `capacity`, `empty`, `at`, `set`, `reserve`, `push_back`, `pop_back`, `clear`, and `free`. `at`, `set`, and `pop_back` require valid indices/non-empty storage.