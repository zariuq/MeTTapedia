#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "ordinary_flat_cesta.h"

#define CHECK(x) do { if (!(x)) { printf("FAIL %s:%d: %s\n", __FILE__, __LINE__, #x); return 1; } } while (0)
#define GUARD(i,j,i0,j0) ((uint32_t)(i) | (uint32_t)(j)<<8 | (uint32_t)(i0)<<16 | (uint32_t)(j0)<<24)
#define MAKE(i,j) ((uint32_t)(i) | (uint32_t)(j)<<8)
#define MAX_PREMISES 24
#define MAX_CONSTANTS 32
#define MAX_GUARDS 32
#define MAX_OUTPUT 32
#define MAX_FIELDS (4 * MAX_PREMISES + MAX_CONSTANTS)

typedef struct {
  uint32_t fields[MAX_FIELDS], rows[MAX_PREMISES + 1];
  uint32_t dest[MAX_OUTPUT], scratch[MAX_OUTPUT];
} Workspace;

static Workspace ws;

static uint64_t fire(const uint32_t *source, size_t ns,
                     const uint32_t *premises, size_t nk,
                     const uint32_t *constants, size_t nc,
                     const uint32_t *guards, size_t ng,
                     const uint32_t *makes, size_t nm) {
  return ordinary_flat_adapter(
    (cesta_read_u32_span){source, ns},
    (cesta_read_u32_span){premises, nk},
    (cesta_read_u32_span){constants, nc},
    (cesta_read_u32_span){guards, ng},
    (cesta_read_u32_span){makes, nm},
    (cesta_write_u32_span){ws.fields, MAX_FIELDS},
    (cesta_write_u32_span){ws.rows, MAX_PREMISES + 1},
    (cesta_write_u32_span){ws.dest, MAX_OUTPUT},
    (cesta_write_u32_span){ws.scratch, MAX_OUTPUT});
}

static const uint32_t source[8] = { 1, 2, 3, 4, 9, 2, 7, 8 };
static const uint32_t offsets[2] = { 0, 4 };
static const uint32_t constants[2] = { 4, 42 };
static const uint32_t guards_ok[2] = { GUARD(0,1,1,1), GUARD(0,3,2,0) };
static const uint32_t guard_bad[1] = { GUARD(0,0,1,0) };
static const uint32_t make[3] = { MAKE(1,0), MAKE(2,1), MAKE(0,0) };

#define DIFF_SCENARIOS 20000
static uint32_t diff_source[4 * MAX_PREMISES];
static uint32_t diff_offsets[MAX_PREMISES];
static uint32_t diff_constants[MAX_CONSTANTS];
static uint32_t diff_guards[MAX_GUARDS];
static uint32_t diff_make[MAX_OUTPUT];
static uint8_t diff_arities[MAX_PREMISES];
static uint64_t diff_state = UINT64_C(0x9e3779b97f4a7c15);

static uint32_t diff_random(uint64_t n) {
  diff_state ^= diff_state >> 12;
  diff_state ^= diff_state << 25;
  diff_state ^= diff_state >> 27;
  return n ? (uint32_t)((diff_state * UINT64_C(0x2545f4914f6cdd1d)) % n) : 0;
}

static void diff_selector(uint32_t nk, uint32_t nc, uint32_t *i, uint32_t *j) {
  *i = nc ? diff_random(nk + 1) : diff_random(nk);
  *j = diff_random(*i < nk ? diff_arities[*i] : nc);
}

static uint32_t diff_value(uint32_t nk, const uint32_t *constants,
                           uint32_t i, uint32_t j) {
  return i < nk ? diff_source[diff_offsets[i] + j] : constants[j];
}

static void diff_store(uint32_t nk, uint32_t *constants,
                       uint32_t i, uint32_t j, uint32_t value) {
  if (i < nk) diff_source[diff_offsets[i] + j] = value;
  else constants[j] = value;
}

static uint64_t diff_reference(uint32_t nk, uint32_t ng, uint32_t nm,
                               uint32_t *out) {
  for (uint32_t k = 0; k < ng; k++) {
    uint32_t g = diff_guards[k];
    if (diff_value(nk, diff_constants, g & 255, (g >> 8) & 255) !=
        diff_value(nk, diff_constants, (g >> 16) & 255, g >> 24)) return 0;
  }
  for (uint32_t k = 0; k < nm; k++) {
    uint32_t m = diff_make[k];
    out[k] = diff_value(nk, diff_constants, m & 255, (m >> 8) & 255);
  }
  return 1;
}

static int differential(void) {
  uint32_t fired = 0, refused = 0;
  for (uint32_t scenario = 0; scenario < DIFF_SCENARIOS; scenario++) {
    uint32_t nk = diff_random(MAX_PREMISES + 1);
    uint32_t nc = diff_random(MAX_CONSTANTS + 1);
    uint32_t ng = diff_random(MAX_GUARDS + 1);
    uint32_t nm = diff_random(MAX_OUTPUT + 1);
    if (!nk && !nc) ng = nm = 0;
    if (!(scenario & 1) && (nk || nc)) ng = diff_random(2);
    for (uint32_t i = 0; i < MAX_PREMISES; i++) {
      diff_offsets[i] = nk ? 4 * diff_random(nk) : 0;
      diff_arities[i] = (uint8_t)(1 + diff_random(4));
    }
    for (uint32_t i = 0; i < 4 * MAX_PREMISES; i++) diff_source[i] = diff_random(16);
    for (uint32_t j = 0; j < nc; j++) diff_constants[j] = diff_random(16);
    for (uint32_t k = 0; k < ng; k++) {
      uint32_t i, j, i0, j0;
      diff_selector(nk, nc, &i, &j); diff_selector(nk, nc, &i0, &j0);
      diff_guards[k] = GUARD(i,j,i0,j0);
      if (!(scenario & 1) || diff_random(2))
        diff_store(nk, diff_constants, i0, j0, diff_value(nk, diff_constants, i, j));
    }
    for (uint32_t k = 0; k < nm; k++) {
      uint32_t i, j;
      diff_selector(nk, nc, &i, &j); diff_make[k] = MAKE(i,j);
    }

    uint32_t saved_source[4 * MAX_PREMISES], saved_constants[MAX_CONSTANTS];
    uint32_t saved_guards[MAX_GUARDS], saved_make[MAX_OUTPUT];
    uint32_t expected[MAX_OUTPUT];
    memcpy(saved_source, diff_source, sizeof diff_source);
    memcpy(saved_constants, diff_constants, sizeof diff_constants);
    memcpy(saved_guards, diff_guards, sizeof diff_guards);
    memcpy(saved_make, diff_make, sizeof diff_make);
    memset(&ws, 0xa5, sizeof ws);
    for (uint32_t k = 0; k < MAX_OUTPUT; k++)
      ws.dest[k] = ws.scratch[k] = UINT32_C(0x50000000) + k;
    uint64_t wanted = diff_reference(nk, ng, nm, expected);
    uint64_t got = fire(diff_source, 4 * MAX_PREMISES, diff_offsets, nk,
                        diff_constants, nc, diff_guards, ng, diff_make, nm);
    CHECK(got == wanted);
    if (got) fired++; else refused++;
    for (uint32_t i = 0; i <= nk; i++) CHECK(ws.rows[i] == 4 * i);
    for (uint32_t i = 0; i < nk; i++)
      for (uint32_t j = 0; j < 4; j++)
        CHECK(ws.fields[4 * i + j] == diff_source[diff_offsets[i] + j]);
    for (uint32_t j = 0; j < nc; j++) CHECK(ws.fields[4 * nk + j] == diff_constants[j]);
    for (uint32_t k = 0; k < MAX_OUTPUT; k++) {
      uint32_t wanted_word = got && k < nm ? expected[k] : UINT32_C(0x50000000) + k;
      CHECK(ws.dest[k] == wanted_word && ws.scratch[k] == wanted_word);
    }
    CHECK(!memcmp(saved_source, diff_source, sizeof diff_source));
    CHECK(!memcmp(saved_constants, diff_constants, sizeof diff_constants));
    CHECK(!memcmp(saved_guards, diff_guards, sizeof diff_guards));
    CHECK(!memcmp(saved_make, diff_make, sizeof diff_make));
  }
  printf("Cesta ordinary adapter differential: %u fired, %u refused\n", fired, refused);
  CHECK(fired > DIFF_SCENARIOS / 10 && refused > DIFF_SCENARIOS / 10);
  return 0;
}

int main(void) {
  CHECK(fire(source, 8, offsets, 2, constants, 2, guards_ok, 2, make, 3) == 1);
  CHECK(ws.rows[0] == 0 && ws.rows[1] == 4 && ws.rows[2] == 8);
  CHECK(ws.fields[0] == 1 && ws.fields[4] == 9 && ws.fields[8] == 4 && ws.fields[9] == 42);
  CHECK(ws.dest[0] == 9 && ws.dest[1] == 42 && ws.dest[2] == 1);
  CHECK(ws.scratch[0] == 9 && ws.scratch[1] == 42 && ws.scratch[2] == 1);

  for (uint32_t i = 0; i < 3; i++) ws.dest[i] = ws.scratch[i] = 100 + i;
  CHECK(fire(source, 8, offsets, 2, constants, 2, guard_bad, 1, make, 3) == 0);
  for (uint32_t i = 0; i < 3; i++) CHECK(ws.dest[i] == 100 + i && ws.scratch[i] == 100 + i);

  uint32_t many[40] = {0}, invalid_offsets[25] = {0};
  ws.fields[0] = 77;
  CHECK(fire(source, 8, invalid_offsets, 25, constants, 2, guards_ok, 2, make, 3) == 2 && ws.fields[0] == 77);
  CHECK(fire(source, 8, offsets, 2, many, 33, guards_ok, 2, make, 3) == 2 && ws.fields[0] == 77);
  CHECK(fire(source, 8, offsets, 2, constants, 2, many, 33, make, 3) == 2 && ws.fields[0] == 77);
  CHECK(fire(source, 8, offsets, 2, constants, 2, guards_ok, 2, many, 33) == 2 && ws.fields[0] == 77);
  invalid_offsets[0] = 1;
  CHECK(fire(source, 4, invalid_offsets, 1, constants, 0, guards_ok, 0, make, 0) == 2 && ws.fields[0] == 77);
  CHECK(ordinary_flat_adapter(
    (cesta_read_u32_span){source, 8}, (cesta_read_u32_span){offsets, 2},
    (cesta_read_u32_span){constants, 2}, (cesta_read_u32_span){guards_ok, 2},
    (cesta_read_u32_span){make, 3}, (cesta_write_u32_span){ws.fields, MAX_FIELDS},
    (cesta_write_u32_span){ws.rows, MAX_PREMISES + 1},
    (cesta_write_u32_span){ws.dest, 2}, (cesta_write_u32_span){ws.scratch, 3}) == 2 && ws.fields[0] == 77);

  CHECK(fire(source, 0, offsets, 0, constants, 0, guards_ok, 0, make, 0) == 1 && ws.rows[0] == 0);
  CHECK(differential() == 0);
  puts("Cesta ordinary adapter: acceptance, constants, refusal, unsupported, empty, and repeated-premise controls passed");
  return 0;
}
