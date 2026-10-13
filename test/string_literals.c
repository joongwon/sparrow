extern unsigned long strlen(const char *s);
extern void external_sink(const char *s);
extern void defined_sink(const char *s);
extern void defined_sink(const char *s) { }

void table(void) {
  const char *strings[] = { "first", "second" };
  external_sink(strings[0]);
}
unsigned long length;
unsigned long literal_size;
int character;

int main(void) {
  defined_sink("return 1 + 2 * 3");
  external_sink("external");
  length = strlen("abc");
  literal_size = sizeof("abc");
  character = "xyz"[1];
  return 0;
}
