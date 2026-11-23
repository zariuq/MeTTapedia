#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "tcalc_cesta.h"

#define SOURCE_CAP 192
#define PREMISE_CAP 32
#define CONSTANT_CAP 40
#define FIELD_CAP 160
#define ROW_CAP 32

void ordinary_flat_failure(void) {
  fputs("unexpected checked Cesta failure\n", stderr);
  exit(70);
}

static uint64_t state = UINT64_C(0x74ca1c5e57a11e09);
static uint64_t next(void) {
  state ^= state << 13;
  state ^= state >> 7;
  state ^= state << 17;
  return state;
}

static bool reference_pack(const uint32_t *source, size_t ns,
                           const uint32_t *premises, size_t nk,
                           const uint32_t *constants, size_t nc,
                           uint32_t *fields, size_t nf,
                           uint32_t *rows, size_t nr) {
  if (nk > 24 || nc > 32 || 4 * nk + nc > nf || nk + 1 > nr) return false;
  for (size_t i = 0; i < nk; i++)
    if ((size_t)premises[i] > ns || ns - (size_t)premises[i] < 4) return false;
  for (size_t i = 0; i < nk; i++) {
    rows[i] = (uint32_t)(4 * i);
    for (size_t j = 0; j < 4; j++) fields[4 * i + j] = source[premises[i] + j];
  }
  rows[nk] = (uint32_t)(4 * nk);
  for (size_t j = 0; j < nc; j++) fields[4 * nk + j] = constants[j];
  return true;
}

int main(void) {
  enum { CASES = 20000 };
  for (unsigned test = 0; test < CASES; test++) {
    uint32_t source[SOURCE_CAP], premises[PREMISE_CAP], constants[CONSTANT_CAP];
    uint32_t fields_a[FIELD_CAP], fields_b[FIELD_CAP];
    uint32_t rows_a[ROW_CAP], rows_b[ROW_CAP];
    size_t ns = next() % (SOURCE_CAP + 1);
    size_t nk = next() % 27;
    size_t nc = next() % 35;
    size_t nf = next() % (FIELD_CAP + 1);
    size_t nr = next() % (ROW_CAP + 1);
    for (size_t i = 0; i < SOURCE_CAP; i++) source[i] = (uint32_t)next();
    for (size_t i = 0; i < PREMISE_CAP; i++) {
      if ((test & 1) && nk && ns >= 4)
        premises[i] = (uint32_t)(4 * (next() % ((ns - 4) / 4 + 1)));
      else
        premises[i] = (uint32_t)(next() % (ns + 8));
    }
    for (size_t i = 0; i < CONSTANT_CAP; i++) constants[i] = (uint32_t)next();
    for (size_t i = 0; i < FIELD_CAP; i++) fields_a[i] = fields_b[i] = (uint32_t)next();
    for (size_t i = 0; i < ROW_CAP; i++) rows_a[i] = rows_b[i] = (uint32_t)next();
    if (test == 0 || test == 1) {
      ns = 96; nk = 24; nc = 32; nf = test == 0 ? 128 : 127; nr = 25;
      for (size_t i = 0; i < nk; i++) premises[i] = (uint32_t)(4 * i);
    } else if (test == 2) {
      ns = 8; nk = 2; nc = 0; nf = 8; nr = 3;
      premises[0] = 0; premises[1] = 5;
    }

    bool expected = reference_pack(source, ns, premises, nk, constants, nc,
                                   fields_b, nf, rows_b, nr);
    bool observed = ordinary_flat_pack(
      (cesta_read_u32_span){source, ns},
      (cesta_read_u32_span){premises, nk},
      (cesta_read_u32_span){constants, nc},
      (cesta_write_u32_span){fields_a, nf},
      (cesta_write_u32_span){rows_a, nr});
    if (observed != expected || memcmp(fields_a, fields_b, sizeof fields_a) ||
        memcmp(rows_a, rows_b, sizeof rows_a)) {
      fprintf(stderr, "pack divergence at case %u: nk=%zu nc=%zu ns=%zu nf=%zu nr=%zu\n",
              test, nk, nc, ns, nf, nr);
      return 1;
    }
  }
  printf("Cesta ordinary pack differential: %d cases passed\n", CASES);
  return 0;
}
