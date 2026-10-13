extern int external_fn(int);
const char *binary_literal = "\031\377\000</script>&";
int callee(int x) { return x + 1; }
int main(void) {
  int (*fp)(int) = callee;
  int x = callee(2);
  x = fp(x);
  return external_fn(x);
}
int (*choose(int (*callback)(int), const char *label, ...))(int) {
  return callback;
}
