/* Probes __attribute__((overloadable)) support (see #5, docs/overload.md).
   A compiler that ignores the attribute (e.g. plain gcc) rejects this as a
   duplicate definition of `probe`; clang accepts it as two overloads. */
static inline __attribute__((overloadable)) int probe(int x) { return x; }
static inline __attribute__((overloadable)) int probe(double x) { return (int)x; }
int main(void) { return probe(1) + probe(2.0); }
