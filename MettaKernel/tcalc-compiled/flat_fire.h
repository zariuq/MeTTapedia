#pragma once
#include <stdint.h>

/* Reference flat firing over a uint32_t word arena. A guard packs row, column,
   row, column into successive bytes; a make entry uses only its low two bytes.
   Effective offsets are uint32_t additions (modulo 2^32), as in flat_offset
   in the HOL specification. An adapter using mathematical offsets must separately
   exclude wrapping; bounds checks on a wider sum are not the same contract.

   Caller obligations from FLAT_FIRE_CORRECT:
   - Every descriptor row index exists, and each effective offset indexes fields.
   - The input arrays are readable; dest and scratch each hold arity writable
     words. All modeled array lengths are below 2^58. NULL is allowed only for
     an array whose length is zero and which is consequently not read/written.
   - Scratch is disjoint from fields, rows, guards, make, and dest. Destination
     may overlap input arrays: all input reads finish before destination writes.
   - All buffer ranges are disjoint from the code and the callee stack/return
     region [entry_rsp - 48, entry_rsp + 8); those two regions are also disjoint.
     The 56-byte exclusion includes the return address; only 48 bytes are written.

   Returns 1 with the selected words in dest and scratch, or 0 leaving both
   buffers unchanged when a guard fails. This entry point does not validate the
   caller obligations. The theorem concerns these exact assembly bytes and ABI;
   it is not a proof of a caller's packing adapter or arbitrary compiler output. */
uint64_t flat_fire(const uint32_t *fields, const uint32_t *rows,
                   const uint32_t *guards, uint64_t nguards,
                   const uint32_t *make, uint64_t arity,
                   uint32_t *dest, uint32_t *scratch);
