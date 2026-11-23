#include "ordinary_flat_adapter.h"

/* Independent behavioral reference for the Cesta adapter, using the same span
   ABI but separate packing code. It is not linked into the proved runtime. */
uint64_t ordinary_flat_adapter(
  cesta_read_u32_span source, cesta_read_u32_span premises,
  cesta_read_u32_span constants, cesta_read_u32_span guards,
  cesta_read_u32_span makes, cesta_write_u32_span fields,
  cesta_write_u32_span rows, cesta_write_u32_span dest,
  cesta_write_u32_span scratch) {
  if (premises.len > ORDINARY_FLAT_MAX_PREMISES ||
      constants.len > ORDINARY_FLAT_MAX_CONSTANTS ||
      guards.len > ORDINARY_FLAT_MAX_GUARDS ||
      makes.len > ORDINARY_FLAT_MAX_OUTPUT ||
      makes.len > dest.len || makes.len > scratch.len) return ORDINARY_FLAT_UNSUPPORTED;
  if (4 * premises.len + constants.len > fields.len ||
      premises.len + 1 > rows.len) return ORDINARY_FLAT_UNSUPPORTED;
  for (size_t i = 0; i < premises.len; i++) {
    size_t offset = premises.data[i];
    if (offset > source.len || 4 > source.len - offset) return ORDINARY_FLAT_UNSUPPORTED;
  }
  for (size_t i = 0; i < premises.len; i++) {
    size_t base = 4 * i, offset = premises.data[i];
    rows.data[i] = (uint32_t)base;
    for (size_t j = 0; j < 4; j++) fields.data[base + j] = source.data[offset + j];
  }
  rows.data[premises.len] = (uint32_t)(4 * premises.len);
  for (size_t j = 0; j < constants.len; j++)
    fields.data[4 * premises.len + j] = constants.data[j];
  return flat_fire(fields.data, rows.data, guards.data, guards.len,
                   makes.data, makes.len, dest.data, scratch.data);
}
