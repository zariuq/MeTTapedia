#include "wire.h"
#include <string.h>

void mm2_wire_nat(FILE *out, size_t value) {
    fprintf(out, "(mm-nat %zu)", value);
}

/* Source names in the Zar profile are ASCII. Logical file names and owner
 * names can also be UTF-8; encode characters as Lean's stringAtom does. */
static uint32_t next_character(const uint8_t *bytes, size_t len, size_t *at,
                               bool *valid) {
    uint32_t value = bytes[(*at)++];
    unsigned count = 0;
    if (value < 128) return value;
    if (value >= 0xc2 && value <= 0xdf) { count = 1; value &= 0x1f; }
    else if (value >= 0xe0 && value <= 0xef) { count = 2; value &= 0x0f; }
    else if (value >= 0xf0 && value <= 0xf4) { count = 3; value &= 7; }
    else { *valid = false; return 0xfffd; }
    if (count > len - *at) { *valid = false; return 0xfffd; }
    for (unsigned i = 0; i < count; ++i) {
        uint8_t byte = bytes[*at];
        if ((byte & 0xc0) != 0x80) { *valid = false; return 0xfffd; }
        ++*at;
        value = (value << 6) | (byte & 0x3f);
    }
    if (value > 0x10ffff || (value >= 0xd800 && value <= 0xdfff) ||
        (count == 1 && value < 0x80) || (count == 2 && value < 0x800) ||
        (count == 3 && value < 0x10000)) { *valid = false; return 0xfffd; }
    return value;
}

bool mm2_wire_valid_utf8(const uint8_t *bytes, size_t len) {
    size_t at = 0;
    bool valid = true;
    while (at < len && valid) (void)next_character(bytes, len, &at, &valid);
    return valid;
}

void mm2_wire_string(FILE *out, const uint8_t *bytes, size_t len) {
    size_t count = 0, at = 0;
    fputs("(mm-string ", out);
    while (at < len) {
        bool valid = true;
        uint32_t character = next_character(bytes, len, &at, &valid);
        fputs("(mm-char-cons ", out);
        mm2_wire_nat(out, character);
        fputc(' ', out);
        ++count;
    }
    fputs("(mm-char-nil)", out);
    while (count--) fputc(')', out);
    fputc(')', out);
}

void mm2_wire_cstring(FILE *out, const char *text) {
    mm2_wire_string(out, (const uint8_t *)text, strlen(text));
}

void mm2_wire_bytes(FILE *out, const uint8_t *bytes, size_t len) {
    for (size_t i = 0; i < len; ++i) {
        fputs("(mm-cons ", out);
        mm2_wire_nat(out, bytes[i]);
        fputc(' ', out);
    }
    fputs("(mm-nil)", out);
    for (size_t i = 0; i < len; ++i) fputc(')', out);
}

/* Least-significant-first bijective base 5, with a base 20 terminal digit.
 * This emits a counter representation, not decoded compressed proof actions. */
void mm2_wire_index(FILE *out, size_t value) {
    size_t prefix = value / 20, count = 0;
    fputs("(mm-compressed-index-code ", out);
    while (prefix) {
        size_t digit = (prefix - 1) % 5 + 1;
        prefix = (prefix - digit) / 5;
        fputs("(mm-cons ", out);
        mm2_wire_nat(out, digit);
        fputc(' ', out);
        ++count;
    }
    fputs("(mm-nil)", out);
    while (count--) fputc(')', out);
    fputc(' ', out);
    mm2_wire_nat(out, value % 20);
    fputc(')', out);
}

void mm2_wire_span(FILE *out, const mm2_source *source,
                   uint32_t source_id, size_t start, size_t end) {
    fputs("(mm-source-span ", out);
    mm2_wire_cstring(out, source->files[source_id].name);
    fputc(' ', out);
    mm2_wire_nat(out, start);
    fputc(' ', out);
    mm2_wire_nat(out, end);
    fputc(')', out);
}

void mm2_wire_name(FILE *out, const mm2_source *source,
                   const mm2_token *token) {
    fputs("(mm-source-name ", out);
    mm2_wire_span(out, source, token->source_id, token->start, token->end);
    fputc(' ', out);
    mm2_wire_string(out, token->bytes, token->len);
    fputc(')', out);
}

void mm2_wire_token(FILE *out, const mm2_source *source,
                    const mm2_token *token) {
    fputs("(mm-source-token ", out);
    mm2_wire_span(out, source, token->source_id, token->start, token->end);
    fputc(' ', out);
    mm2_wire_bytes(out, token->bytes, token->len);
    fputc(')', out);
}
