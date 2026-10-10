extern long long input(void);

int main(void) {
  int values[8];
  long long x = input();
  long long a = x + 4611686018427387904LL;
  long long b = x + 9223372036854775807LL;
  long long c = x - 4611686018427387905LL;
  long long d = x + (-9223372036854775807LL - 1LL);
  unsigned long long e = (unsigned long long)x + 9223372036854775808ULL;
  unsigned long long f = (unsigned long long)x + 18446744073709551615ULL;
  values[a] = 1;
  values[b] = 2;
  values[c] = 3;
  values[d] = 4;
  values[e] = 5;
  values[f] = 6;
  return 0;
}
