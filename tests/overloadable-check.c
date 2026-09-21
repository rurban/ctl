/* Probes __attribute__((overloadable)) support (see #5, docs/overload.md).
   Only clang implements the attribute; every other compiler fails this
   deliberate, single-line #error instead of a noisy "conflicting types"
   diagnostic from two same-signature-looking `probe` definitions. */
#ifdef __clang__
static inline __attribute__((overloadable)) int probe(int x) { return x; }
static inline __attribute__((overloadable)) int probe(double x) { return (int)x; }
int main(void) { return probe(1) + probe(2.0); }
#else
#error "__attribute__((overloadable)) requires clang"
#endif
