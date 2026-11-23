#include "flat_fire.h"
#include <stdio.h>
#include <string.h>

#define GUARD(i, j, i0, j0) \
  ((uint32_t)(i) | ((uint32_t)(j) << 8) | ((uint32_t)(i0) << 16) | ((uint32_t)(j0) << 24))
#define MAKE(i, j) GUARD(i, j, 0, 0)

static int failures;
static unsigned checks;

static void expect_words(const char *name, const uint32_t *got,
                         const uint32_t *want, uint64_t n) {
  checks++;
  if (memcmp(got, want, n * sizeof *got)) {
    fprintf(stderr, "%s: wrong words\n", name);
    failures++;
  }
}

static void expect_u64(const char *name, uint64_t got, uint64_t want) {
  checks++;
  if (got != want) {
    fprintf(stderr, "%s: got %llu, want %llu\n", name,
            (unsigned long long)got, (unsigned long long)want);
    failures++;
  }
}

int main(void) {
  const uint32_t rows[] = {0, 4, 8};
  const uint32_t fields[] = {11, 22, 33, 44, 55, 66, 22, 77, 33};
  const uint32_t guards[] = {GUARD(0, 1, 1, 2), GUARD(0, 2, 2, 0)};
  const uint32_t make[] = {MAKE(1, 0), MAKE(0, 0), MAKE(2, 0), MAKE(1, 3)};
  const uint32_t want[] = {55, 11, 33, 77};
  uint32_t dest[] = {90, 91, 92, 93};
  uint32_t scratch[4] = {0};

  expect_u64("positive firing", flat_fire(fields, rows, guards, 2, make, 4, dest, scratch), 1);
  expect_words("positive conclusion", dest, want, 4);
  expect_words("conclusion staged in scratch", scratch, want, 4);

  uint32_t failing_fields[9];
  memcpy(failing_fields, fields, sizeof failing_fields);
  failing_fields[6] = 23;
  uint32_t refused_dest[] = {90, 91, 92, 93};
  const uint32_t original_dest[] = {90, 91, 92, 93};
  memset(scratch, 0, sizeof scratch);
  expect_u64("repeated-hole refusal",
             flat_fire(failing_fields, rows, guards, 2, make, 4, refused_dest, scratch), 0);
  expect_words("refusal writes no conclusion", refused_dest, original_dest, 4);
  expect_words("refusal does not stage a conclusion", scratch, (uint32_t[4]){0}, 4);

  failing_fields[6] = 22;
  failing_fields[2] = 34;
  expect_u64("constant refusal",
             flat_fire(failing_fields, rows, guards, 2, make, 4, refused_dest, scratch), 0);
  expect_words("constant refusal writes nothing", refused_dest, original_dest, 4);

  uint32_t aliased[9];
  memcpy(aliased, fields, sizeof aliased);
  memset(scratch, 0, sizeof scratch);
  expect_u64("destination aliases a premise",
             flat_fire(aliased, rows, guards, 2, make, 4, aliased, scratch), 1);
  expect_words("aliased conclusion uses original fields", aliased, want, 4);

  const uint32_t no_guard_make[] = {MAKE(0, 3), MAKE(1, 1)};
  memset(scratch, 0, sizeof scratch);
  expect_u64("no guards", flat_fire(fields, rows, NULL, 0, no_guard_make, 2, dest, scratch), 1);
  expect_words("no-guard conclusion", dest, (uint32_t[]){44, 66}, 2);

  expect_u64("empty rule", flat_fire(NULL, NULL, NULL, 0, NULL, 0, NULL, NULL), 1);
  expect_u64("empty conclusion", flat_fire(fields, rows, guards, 2, NULL, 0, NULL, NULL), 1);
  expect_u64("empty refused conclusion",
             flat_fire(failing_fields, rows, guards, 2, NULL, 0, NULL, NULL), 0);

  /* uint32_t row/column addition is deliberately modular in the proved ABI. */
  const uint32_t wrap_rows[] = {UINT32_MAX};
  const uint32_t wrap_fields[] = {17, 17};
  const uint32_t wrap_guards[] = {GUARD(0, 1, 0, 2)};
  const uint32_t wrap_make[] = {MAKE(0, 1)};
  uint32_t wrap_dest[] = {91}, wrap_scratch[] = {92};
  expect_u64("wrapped offset admitted",
             flat_fire(wrap_fields, wrap_rows, wrap_guards, 1, wrap_make, 1,
                       wrap_dest, wrap_scratch), 1);
  expect_words("wrapped offset selected", wrap_dest, (uint32_t[]){17}, 1);
  const uint32_t wrap_bad[] = {17, 18};
  expect_u64("wrapped offset refusal",
             flat_fire(wrap_bad, wrap_rows, wrap_guards, 1, wrap_make, 1,
                       wrap_dest, wrap_scratch), 0);
  expect_words("wrapped refusal retains destination", wrap_dest, (uint32_t[]){17}, 1);
  expect_words("wrapped refusal retains scratch", wrap_scratch, (uint32_t[]){17}, 1);

  if (failures) return 1;
  printf("flat_fire: %u assertion checks passed (including wrapped offsets)\n", checks);
  return 0;
}
