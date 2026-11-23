#include "wire.h"
#include <assert.h>
#include <string.h>

static void expect(FILE *out, const char *expected) {
    char actual[4096];
    assert(!ferror(out));
    assert(fflush(out) == 0);
    rewind(out);
    size_t count = fread(actual, 1, sizeof(actual) - 1, out);
    actual[count] = 0;
    assert(feof(out));
    assert(strcmp(actual, expected) == 0);
    fclose(out);
}

int main(void) {
    FILE *out = tmpfile(); assert(out);
    mm2_wire_nat(out, 42);
    expect(out, "(mm-nat 42)");

    out = tmpfile(); assert(out);
    mm2_wire_cstring(out, "A");
    expect(out, "(mm-string (mm-char-cons (mm-nat 65) (mm-char-nil)))");

    out = tmpfile(); assert(out);
    mm2_wire_cstring(out, "\xce\xbb\xf0\x9f\x99\x82");
    expect(out, "(mm-string (mm-char-cons (mm-nat 955) (mm-char-cons "
                "(mm-nat 128578) (mm-char-nil))))");

    const uint8_t bytes[] = {0, 9, 255};
    out = tmpfile(); assert(out);
    mm2_wire_bytes(out, bytes, sizeof(bytes));
    expect(out, "(mm-cons (mm-nat 0) (mm-cons (mm-nat 9) "
                "(mm-cons (mm-nat 255) (mm-nil))))");

    out = tmpfile(); assert(out); mm2_wire_index(out, 0);
    expect(out, "(mm-compressed-index-code (mm-nil) (mm-nat 0))");
    out = tmpfile(); assert(out); mm2_wire_index(out, 19);
    expect(out, "(mm-compressed-index-code (mm-nil) (mm-nat 19))");
    out = tmpfile(); assert(out); mm2_wire_index(out, 20);
    expect(out, "(mm-compressed-index-code (mm-cons (mm-nat 1) "
                "(mm-nil)) (mm-nat 0))");
    out = tmpfile(); assert(out); mm2_wire_index(out, 120);
    expect(out, "(mm-compressed-index-code (mm-cons (mm-nat 1) "
                "(mm-cons (mm-nat 1) (mm-nil))) (mm-nat 0))");

    assert(mm2_wire_valid_utf8((const uint8_t *)"\xce\xbb", 2));
    assert(mm2_wire_valid_utf8((const uint8_t *)"\xef\xbf\xbd", 3));
    assert(!mm2_wire_valid_utf8((const uint8_t *)"\xe0\x80\xaf", 3));
    assert(!mm2_wire_valid_utf8((const uint8_t *)"\xc0\xaf", 2));
    assert(!mm2_wire_valid_utf8((const uint8_t *)"\xed\xa0\x80", 3));
    assert(!mm2_wire_valid_utf8((const uint8_t *)"\xf4\x90\x80\x80", 4));
    assert(!mm2_wire_valid_utf8((const uint8_t *)"\xf0\x9f", 2));
    assert(!mm2_wire_valid_utf8((const uint8_t *)"\xff", 1));
    puts("MM2 wire encoders: positive and negative controls passed");
    return 0;
}
