#pragma once
#include "ordinary_flat_cesta.h"

/* Generic ordinary-row packing for the exact Cesta/flat_fire runtime. The
   caller supplies a contiguous source-word arena, uint32 premise word offsets,
   and distinct workspace for each invocation. Repeated premise offsets are
   valid. Borrowed inputs and workspace are not retained after return. */
enum {
  ORDINARY_FLAT_MAX_PREMISES = 24,
  ORDINARY_FLAT_MAX_CONSTANTS = 32,
  ORDINARY_FLAT_MAX_GUARDS = 32,
  ORDINARY_FLAT_MAX_OUTPUT = 32,
  ORDINARY_FLAT_MAX_FIELDS = 4 * ORDINARY_FLAT_MAX_PREMISES + ORDINARY_FLAT_MAX_CONSTANTS
};

typedef struct {
  uint32_t fields[ORDINARY_FLAT_MAX_FIELDS];
  uint32_t rows[ORDINARY_FLAT_MAX_PREMISES + 1];
  uint32_t dest[ORDINARY_FLAT_MAX_OUTPUT];
  uint32_t scratch[ORDINARY_FLAT_MAX_OUTPUT];
} OrdinaryFlatWorkspace;

enum {
  ORDINARY_FLAT_REFUSED = 0,
  ORDINARY_FLAT_FIRED = 1,
  ORDINARY_FLAT_UNSUPPORTED = 2
};

/* Returns UNSUPPORTED before packing when counts, capacities, or premise
   extents are invalid. Otherwise returns the leaf's FIRED/REFUSED bit. The
   generated prototype in ordinary_flat_cesta.h is the only adapter ABI. */
