#ifndef METTAPEDIA_MM2_WIRE_H
#define METTAPEDIA_MM2_WIRE_H

#include "reader.h"
#include <stdbool.h>
#include <stdio.h>

/* These are encoders, not MM2 syntax interpolation. Names and bytes never
 * become executable tokens, variables, or quoted surface expressions. */
void mm2_wire_nat(FILE *out, size_t value);
void mm2_wire_string(FILE *out, const uint8_t *bytes, size_t len);
void mm2_wire_cstring(FILE *out, const char *text);
bool mm2_wire_valid_utf8(const uint8_t *bytes, size_t len);
void mm2_wire_bytes(FILE *out, const uint8_t *bytes, size_t len);
void mm2_wire_index(FILE *out, size_t value);
void mm2_wire_span(FILE *out, const mm2_source *source,
                   uint32_t source_id, size_t start, size_t end);
void mm2_wire_name(FILE *out, const mm2_source *source,
                   const mm2_token *token);
void mm2_wire_token(FILE *out, const mm2_source *source,
                    const mm2_token *token);

#endif
