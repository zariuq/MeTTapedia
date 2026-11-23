#ifndef METTAPEDIA_MM2_READER_H
#define METTAPEDIA_MM2_READER_H

#include <stddef.h>
#include <stdint.h>

#define MM2_READER_VERSION "1"
#define MM2_READER_PROFILE "zar"
#define MM2_SOURCE_DATA_SCHEMA "mm2-source-data-v1"

typedef enum {
    MM2_OK = 0,
    MM2_REJECTED = 1,
    MM2_ERROR = 2
} mm2_status;

typedef struct {
    mm2_status status;
    uint32_t source_id;
    size_t start;
    size_t end;
    char message[512];
} mm2_error;

/* Token storage is owned by mm2_source.  bytes[len] is a convenience NUL;
 * len and the half-open byte span retain the exact source occurrence. */
typedef struct {
    uint8_t *bytes;
    size_t len;
    uint32_t source_id;
    size_t start;
    size_t end;
} mm2_token;

typedef enum {
    MM2_CONST,
    MM2_VAR,
    MM2_SCOPE_OPEN,
    MM2_SCOPE_CLOSE,
    MM2_FLOAT,
    MM2_ESSENTIAL,
    MM2_DV,
    MM2_AXIOM,
    MM2_THEOREM
} mm2_statement_kind;

typedef enum {
    MM2_PROOF_NONE,
    MM2_PROOF_NORMAL,
    MM2_PROOF_COMPRESSED
} mm2_proof_kind;

typedef struct {
    mm2_statement_kind kind;
    uint32_t source_id;
    size_t start;
    size_t end;
    /* The directive token, not the label, is the statement's Lean site. */
    mm2_token site;
    mm2_token terminator;
    mm2_token separator;
    mm2_token open_paren;
    mm2_token close_paren;
    mm2_token label;
    mm2_token *symbols;
    size_t symbol_count;
    mm2_proof_kind proof_kind;
    /* Normal proof labels, or the undecoded compressed-proof header. */
    mm2_token *proof_labels;
    size_t proof_label_count;
    /* Original compressed body words; no indices or proof steps are decoded. */
    mm2_token *compressed_words;
    size_t compressed_word_count;
} mm2_statement;

typedef struct {
    char *name;
    /* Filesystem identity is used only to protect inputs from output aliases. */
    uintmax_t physical_device;
    uintmax_t physical_inode;
} mm2_source_file;

typedef struct {
    mm2_statement *statements;
    size_t statement_count;
    mm2_source_file *files;
    size_t file_count;
    char parser_digest[65];
    char source_digest[65];
    char include_digest[65];
} mm2_source;

typedef enum {
    MM2_INCLUDE_BOOK,
    MM2_INCLUDE_REJECT_ACTIVE
} mm2_include_policy;

typedef struct {
    const char *root_name;
    mm2_include_policy include_policy;
} mm2_reader_options;

/* The default options use logical root "unit.mm" and book include policy.
 * Statements are returned in expansion order, with source-owned payloads.
 * The reader performs no declaration-state fold or proof checking. */
mm2_status mm2_read_source(const char *path,
                          const mm2_reader_options *options,
                          mm2_source *out, mm2_error *error);
void mm2_source_free(mm2_source *source);
void mm2_error_clear(mm2_error *error);
void mm2_error_set(mm2_error *error, mm2_status status, uint32_t source_id,
                   size_t start, size_t end, const char *message);

#endif
