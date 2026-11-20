#define _GNU_SOURCE
#include "native/hol_light/hol_replay.h"
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct { FILE *out; uint64_t records; } Dump;
static void bytes(FILE *out, const uint8_t *xs, uint64_t n) {
    for (uint64_t i = 0; i < n; ++i) fprintf(out, "(LCons %u ", xs[i]);
    fputs("LNil", out);
    for (uint64_t i = 0; i < n; ++i) fputc(')', out);
}
static void words(FILE *out, const uint64_t *xs, uint64_t n) {
    for (uint64_t i = 0; i < n; ++i) fprintf(out, "(LCons %" PRIu64 " ", xs[i]);
    fputs("LNil", out);
    for (uint64_t i = 0; i < n; ++i) fputc(')', out);
}
/* Normalize only the values supplied by the existing structural scanner. */
static bool record(void *context, const HolScanRecord *r) {
    Dump *d = context;
    FILE *out = d->out;
    fprintf(out, "(LCons (BRecord %u ", r->opcode);
    unsigned fixed = 0, fields = 0;
    for (const char *p = r->layout; *p; ++p) {
        fputs("(LCons ", out); ++fields;
        if (*p == 'b') {
            fputs("(BBytes ", out); bytes(out, r->bytes, r->nbytes); fputc(')', out);
        } else if (*p == '*') {
            fputs("(BWords ", out); words(out, r->list, r->nlist); fputc(')', out); ++p;
        } else if (*p == '%') {
            if (r->nlist % 2) return false;
            fputs("(BPairs ", out);
            for (uint64_t i = 0; i < r->nlist; i += 2)
                fprintf(out, "(LCons (BPair %" PRIu64 " %" PRIu64 ") ", r->list[i], r->list[i+1]);
            fputs("LNil", out);
            for (uint64_t i = 0; i < r->nlist; i += 2) fputc(')', out);
            fputc(')', out); p += 2;
        } else {
            if (fixed >= r->nfixed) return false;
            fprintf(out, "(BWord %" PRIu64 ")", r->fixed[fixed++]);
        }
        fputc(' ', out);
    }
    fputs("LNil", out);
    for (unsigned i = 0; i < fields; ++i) fputc(')', out);
    fputs(") ", out); ++d->records;
    return true;
}
static const char *reason(HolReason r) {
    switch (r) {
    case HOL_R_STREAM_MAGIC: case HOL_R_STREAM_HEADER: return "BadHeader";
    case HOL_R_STREAM_VERSION: return "BadVersion";
    case HOL_R_STREAM_TRUNCATED: return "Truncated";
    case HOL_R_STREAM_INTEGER: return "IntegerEncoding";
    case HOL_R_STREAM_OPCODE: return "BadOpcode";
    case HOL_R_STREAM_COUNT: return "BadCount";
    case HOL_R_STREAM_CHECKSUM: return "BadChecksum";
    case HOL_R_STREAM_TRAILING: return "TrailingBytes";
    case HOL_R_STREAM_MISSING_END: return "MissingEnd";
    case HOL_R_STREAM_LIMIT: return "FieldLimit";
    default: return "OracleOtherReason";
    }
}
int main(int argc, char **argv) {
    int prefix = argc == 3 && !strcmp(argv[1], "--prefix");
    if (argc != 2 && !prefix) return 2;
    FILE *in = fopen(argv[prefix ? 2 : 1], "rb");
    if (!in || fseek(in, 0, SEEK_END)) return 2;
    long size = ftell(in);
    if (size < 0 || fseek(in, 0, SEEK_SET)) return 2;
    uint8_t *input = malloc(size ? (size_t)size : 1);
    if (!input || fread(input, 1, (size_t)size, in) != (size_t)size) return 2;
    fclose(in);
    char *text = NULL; size_t text_len = 0;
    FILE *records = open_memstream(&text, &text_len);
    if (!records) return 2;
    Dump dump = {records, 0};
    HolReason why; HolScanHeader header = {0};
    HolReplayState state = hol_stream_scan(input, (size_t)size, &header, record, &dump, &why);
    fputs("LNil", records);
    for (uint64_t i = 0; i < dump.records; ++i) fputc(')', records);
    if (fclose(records)) return 2;
    if (prefix && header.header_len &&
            (state == HOL_REPLAY_ACCEPTED || state == HOL_REPLAY_MALFORMED)) {
        fputs("(ByteFormatPrefix (HOLRHeader (BBytes ", stdout);
        bytes(stdout, input + 8, 32);
        printf(") 1 0 %u %u) %s ", header.policy, header.flags, text);
        if (state == HOL_REPLAY_ACCEPTED) puts("(ByteFormatEndOK))");
        else printf("(ByteFormatEndError (%s)))\n", reason(why));
    } else if (state == HOL_REPLAY_ACCEPTED) {
        fputs("(ByteFormatRead (HOLRHeader (BBytes ", stdout);
        bytes(stdout, input + 8, 32);
        printf(") 1 0 %u %u) %s)\n", header.policy, header.flags, text);
    } else if (state == HOL_REPLAY_MALFORMED) {
        printf("(ByteFormatRefused (%s))\n", reason(why));
    } else {
        fprintf(stderr, "oracle stopped: state %d reason %s\n", state, hol_reason_name(why));
        free(text); free(input); return 1;
    }
    free(text); free(input); return 0;
}
