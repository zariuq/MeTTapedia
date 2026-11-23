#define _XOPEN_SOURCE 700

#include "reader.h"
#include "wire.h"

#include "native_sha256.h"
#include "parser_occurrence_fold_v1.h"
#include "parser_occurrence_span_mask_v1.h"
#include "parser_pack_guarded_lexical_exec_v1.h"
#include "symbol.h"

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

extern bool metamath_syntax_cursor_fold_v1_program_init(
    PPGuardedLexCursorV1Program *, char *, size_t);
extern const char *metamath_syntax_cursor_fold_v1_program_digest(void);
extern bool metamath_syntax_cursor_fold_v1_occurrence_fold_plan_init(
    const PPGuardedLexCursorV1Program *, PPOccurrenceFoldV1Plan *, char *, size_t);
extern bool metamath_syntax_cursor_fold_v1_occurrence_span_mask_plan_init(
    const PPGuardedLexCursorV1Program *, const PPOccurrenceFoldV1Plan *,
    PPOccurrenceSpanMaskV1Plan *, char *, size_t);

typedef struct { size_t start, end; } token_span;
typedef struct {
    char *canonical;
    uint8_t *bytes;
    uint8_t *cursor_bytes;
    size_t len;
    token_span *tokens;
    size_t token_count, token_capacity;
    bool active, completed;
} source_file;

typedef struct {
    mm2_source source;
    source_file *files;
    size_t file_capacity, source_capacity, statement_capacity;
    PPGuardedLexCursorV1Program program;
    PPOccurrenceFoldV1Plan fold;
    PPOccurrenceSpanMaskV1Plan mask;
    CettaNativeSha256 graph_hash;
    mm2_include_policy policy;
    mm2_error *error;
    uint32_t current;
    size_t depth;
    bool committed, aborted;
} reader_context;

void mm2_error_clear(mm2_error *error) {
    if (error) {
        memset(error, 0, sizeof(*error));
        error->source_id = UINT32_MAX;
    }
}

void mm2_error_set(mm2_error *error, mm2_status status, uint32_t source_id,
                   size_t start, size_t end, const char *message) {
    if (!error) return;
    error->status = status;
    error->source_id = source_id;
    error->start = start;
    error->end = end;
    (void)snprintf(error->message, sizeof(error->message), "%s", message);
}

static void token_free(mm2_token *token) {
    free(token->bytes);
    memset(token, 0, sizeof(*token));
}

static void statement_free(mm2_statement *statement) {
    size_t i;
    token_free(&statement->site);
    token_free(&statement->terminator);
    token_free(&statement->separator);
    token_free(&statement->open_paren);
    token_free(&statement->close_paren);
    token_free(&statement->label);
    for (i = 0; i < statement->symbol_count; ++i)
        token_free(&statement->symbols[i]);
    for (i = 0; i < statement->proof_label_count; ++i)
        token_free(&statement->proof_labels[i]);
    for (i = 0; i < statement->compressed_word_count; ++i)
        token_free(&statement->compressed_words[i]);
    free(statement->symbols);
    free(statement->proof_labels);
    free(statement->compressed_words);
    memset(statement, 0, sizeof(*statement));
}

void mm2_source_free(mm2_source *source) {
    size_t i;
    if (!source) return;
    for (i = 0; i < source->statement_count; ++i)
        statement_free(&source->statements[i]);
    for (i = 0; i < source->file_count; ++i) free(source->files[i].name);
    free(source->statements);
    free(source->files);
    memset(source, 0, sizeof(*source));
}

static bool grow(void **buffer, size_t *capacity, size_t need, size_t width) {
    size_t next;
    void *allocation;
    if (need <= *capacity) return true;
    if (need > SIZE_MAX / width) return false;
    next = *capacity ? *capacity : 16;
    while (next < need) {
        if (next > SIZE_MAX / 2) { next = need; break; }
        next *= 2;
    }
    if (next > SIZE_MAX / width) next = need;
    allocation = realloc(*buffer, next * width);
    if (!allocation) return false;
    *buffer = allocation;
    *capacity = next;
    return true;
}

static bool reject(reader_context *context, uint32_t source,
                    size_t start, size_t end, const char *message) {
    mm2_error_set(context->error, MM2_REJECTED, source, start, end, message);
    return false;
}

static bool internal_error(reader_context *context, const char *message) {
    mm2_error_set(context->error, MM2_ERROR, context->current, 0, 0, message);
    return false;
}

static bool space(uint8_t byte) {
    return byte == 9 || byte == 10 || byte == 12 || byte == 13 || byte == 32;
}

static bool exact(const uint8_t *bytes, size_t len, const char *text) {
    return len == strlen(text) && memcmp(bytes, text, len) == 0;
}

static bool mask_comment(reader_context *context, source_file *file,
                          size_t start, size_t end) {
    if (!file->cursor_bytes) {
        file->cursor_bytes = malloc(file->len);
        if (!file->cursor_bytes)
            return internal_error(context, "cannot allocate validated comment view");
        memcpy(file->cursor_bytes, file->bytes, file->len);
    }
    memset(file->cursor_bytes + start, ' ', end - start);
    return true;
}

/* This projection supplies punctuation spans absent from the semantic roles.
 * Statement recognition and role selection are still performed by the native
 * cursor. The Zar byte/comment guard is checked before UTF-8 scalar decoding.
 * Validated comments become same-length whitespace in the cursor view. This
 * preserves original token bytes and offsets, including a comment at EOF. */
static bool project_tokens(reader_context *context, uint32_t source_id) {
    source_file *file = &context->files[source_id];
    size_t cursor = 0, opening = 0;
    bool comment = false;
    while (cursor < file->len) {
        size_t start, end, i;
        while (cursor < file->len && space(file->bytes[cursor])) ++cursor;
        if (cursor == file->len) break;
        start = cursor;
        while (cursor < file->len && !space(file->bytes[cursor])) ++cursor;
        end = cursor;
        for (i = start; i < end; ++i)
            if (file->bytes[i] < 33 || file->bytes[i] > 126)
                return reject(context, source_id, i, i + 1,
                              "byte outside the Zar source profile");
        if (comment) {
            if (exact(file->bytes + start, end - start, "$)")) {
                if (!mask_comment(context, file, start, end)) return false;
                comment = false;
                continue;
            }
            for (i = start; i + 1 < end; ++i)
                if (file->bytes[i] == '$' &&
                    (file->bytes[i + 1] == '(' || file->bytes[i + 1] == ')'))
                    return reject(context, source_id, i, i + 2,
                                  "embedded comment delimiter");
            if (!mask_comment(context, file, start, end)) return false;
            continue;
        }
        if (exact(file->bytes + start, end - start, "$(")) {
            if (!mask_comment(context, file, start, end)) return false;
            comment = true;
            opening = start;
            continue;
        }
        if (exact(file->bytes + start, end - start, "$)"))
            return reject(context, source_id, start, end,
                          "comment close without comment open");
        if (!grow((void **)&file->tokens, &file->token_capacity,
                  file->token_count + 1, sizeof(*file->tokens)))
            return internal_error(context, "cannot allocate source token spans");
        file->tokens[file->token_count++] = (token_span){start, end};
    }
    if (comment)
        return reject(context, source_id, opening, opening + 2,
                      "unterminated comment");
    return true;
}

static bool read_bytes(reader_context *context, const char *path,
                       uint8_t **out, size_t *length, mm2_source_file *identity) {
    FILE *input = fopen(path, "rb");
    struct stat metadata;
    uint8_t *bytes = NULL;
    size_t len = 0, capacity = 0;
    if (!input) return internal_error(context, "cannot open source file");
    if (fstat(fileno(input), &metadata) != 0 || !S_ISREG(metadata.st_mode)) {
        fclose(input);
        return internal_error(context, "source input is not a readable regular file");
    }
    identity->physical_device = (uintmax_t)metadata.st_dev;
    identity->physical_inode = (uintmax_t)metadata.st_ino;
    for (;;) {
        size_t amount;
        if (len > UINT32_MAX || len > SIZE_MAX - 4096) {
            fclose(input);
            free(bytes);
            return internal_error(context, "source exceeds the native cursor byte range");
        }
        if (!grow((void **)&bytes, &capacity, len + 4096, 1)) {
            fclose(input);
            free(bytes);
            return internal_error(context, "cannot allocate source bytes");
        }
        amount = fread(bytes + len, 1, capacity - len, input);
        len += amount;
        if (amount) continue;
        if (ferror(input)) {
            fclose(input);
            free(bytes);
            return internal_error(context, "cannot read source file");
        }
        break;
    }
    if (fclose(input) != 0) {
        free(bytes);
        return internal_error(context, "cannot close source file");
    }
    if (len > UINT32_MAX) {
        free(bytes);
        return internal_error(context, "source exceeds the native cursor byte range");
    }
    *out = bytes;
    *length = len;
    return true;
}

static bool add_file(reader_context *context, char *canonical,
                     char *logical, uint32_t *source_id) {
    size_t index = context->source.file_count;
    if (!mm2_wire_valid_utf8((const uint8_t *)logical, strlen(logical)))
        return reject(context, context->current, 0, 0,
                      "source logical name is not valid UTF-8");
    if (index >= UINT32_MAX ||
        !grow((void **)&context->files, &context->file_capacity,
              index + 1, sizeof(*context->files)) ||
        !grow((void **)&context->source.files, &context->source_capacity,
              index + 1, sizeof(*context->source.files)))
        return internal_error(context, "cannot allocate source identities");
    memset(&context->files[index], 0, sizeof(context->files[index]));
    context->files[index].canonical = canonical;
    context->source.files[index] = (mm2_source_file){logical, 0, 0};
    context->source.file_count++;
    *source_id = (uint32_t)index;
    return true;
}

static bool copy_token(reader_context *context, mm2_token *out,
                       uint32_t source_id, size_t start, size_t end) {
    const source_file *file = &context->files[source_id];
    uint8_t *bytes;
    if (start > end || end > file->len)
        return internal_error(context, "native occurrence span outside source");
    bytes = malloc(end - start + 1);
    if (!bytes) return internal_error(context, "cannot allocate source token");
    memcpy(bytes, file->bytes + start, end - start);
    bytes[end - start] = 0;
    *out = (mm2_token){bytes, end - start, source_id, start, end};
    return true;
}

static bool copy_value(reader_context *context, mm2_token *out,
                       const PPOccurrenceFoldV1Value *value) {
    if (value->right_byte < value->left_byte ||
        value->byte_len != value->right_byte - value->left_byte ||
        value->right_byte > context->files[context->current].len ||
        memcmp(value->bytes,
               context->files[context->current].bytes + value->left_byte,
               value->byte_len) != 0)
        return internal_error(context, "native token projection changed source bytes");
    return copy_token(context, out, context->current,
                      value->left_byte, value->right_byte);
}

static bool copy_role(reader_context *context, const PPOccurrenceFoldV1Step *step,
                      const char *role, mm2_token **out, size_t *count) {
    size_t i, len = 0;
    for (i = 0; i < step->value_len; ++i) {
        const char *name = ppoccurrence_fold_v1_role_name(
            &context->fold, step->values[i].role_id);
        if (name && strcmp(name, role) == 0) ++len;
    }
    if (!len) return true;
    *out = calloc(len, sizeof(**out));
    if (!*out) return internal_error(context, "cannot allocate occurrence roles");
    for (i = 0; i < step->value_len; ++i) {
        const char *name = ppoccurrence_fold_v1_role_name(
            &context->fold, step->values[i].role_id);
        if (!name || strcmp(name, role) != 0) continue;
        if (!copy_value(context, &(*out)[*count], &step->values[i])) return false;
        ++*count;
    }
    return true;
}

static size_t token_lower_bound(const source_file *file, size_t position) {
    size_t low = 0, high = file->token_count;
    while (low < high) {
        size_t mid = low + (high - low) / 2;
        if (file->tokens[mid].start < position) low = mid + 1;
        else high = mid;
    }
    return low;
}

static bool punctuation(reader_context *context, mm2_statement *statement,
                         const char *directive, size_t left, size_t right) {
    const source_file *file = &context->files[context->current];
    size_t i = token_lower_bound(file, left);
    bool proof = false;
    for (; i < file->token_count && file->tokens[i].start < right; ++i) {
        token_span span = file->tokens[i];
        const uint8_t *bytes = file->bytes + span.start;
        size_t len = span.end - span.start;
        mm2_token *target = NULL;
        if (!statement->site.bytes && exact(bytes, len, directive))
            target = &statement->site;
        else if (exact(bytes, len, "$.") && !statement->terminator.bytes)
            target = &statement->terminator;
        else if (statement->kind == MM2_THEOREM && exact(bytes, len, "$=")) {
            target = &statement->separator;
            proof = true;
        } else if (proof && statement->proof_kind == MM2_PROOF_COMPRESSED &&
                   exact(bytes, len, "(") && !statement->open_paren.bytes)
            target = &statement->open_paren;
        else if (proof && statement->proof_kind == MM2_PROOF_COMPRESSED &&
                 exact(bytes, len, ")") && !statement->close_paren.bytes)
            target = &statement->close_paren;
        if (target && !copy_token(context, target, context->current,
                                   span.start, span.end)) return false;
    }
    if (!statement->site.bytes ||
        ((statement->kind != MM2_SCOPE_OPEN && statement->kind != MM2_SCOPE_CLOSE) &&
         !statement->terminator.bytes) ||
        (statement->kind == MM2_THEOREM && !statement->separator.bytes) ||
        (statement->proof_kind == MM2_PROOF_COMPRESSED &&
         (!statement->open_paren.bytes || !statement->close_paren.bytes)))
        return internal_error(context, "native occurrence lost punctuation provenance");
    statement->start = statement->label.bytes
        ? statement->label.start : statement->site.start;
    statement->end = statement->terminator.bytes
        ? statement->terminator.end : statement->site.end;
    return true;
}

static char *join_path(const char *parent, const uint8_t *path, size_t len) {
    const char *slash;
    size_t prefix = 0;
    char *result;
    if (!len || memchr(path, 0, len)) return NULL;
    if (path[0] != '/') {
        slash = strrchr(parent, '/');
        if (slash) prefix = (size_t)(slash - parent) + 1;
    }
    if (prefix > SIZE_MAX - len - 1) return NULL;
    result = malloc(prefix + len + 1);
    if (!result) return NULL;
    memcpy(result, parent, prefix);
    memcpy(result + prefix, path, len);
    result[prefix + len] = 0;
    return result;
}

static void graph_bytes(reader_context *context, const uint8_t *bytes, size_t len) {
    uint8_t encoded[8];
    uint64_t length = len;
    size_t i;
    for (i = 0; i < 8; ++i) encoded[7 - i] = (uint8_t)(length >> (i * 8));
    cetta_native_sha256_update(&context->graph_hash, encoded, sizeof(encoded));
    cetta_native_sha256_update(&context->graph_hash, bytes, len);
}

static bool parse_file(reader_context *, uint32_t, char *, size_t);

static bool include_file(reader_context *context,
                          const PPOccurrenceFoldV1Step *step,
                          char *diagnostic, size_t diagnostic_size) {
    const PPOccurrenceFoldV1Value *path = NULL;
    char *joined = NULL, *canonical = NULL, *logical = NULL;
    uint32_t parent = context->current, child;
    size_t i;
    bool ok = false;
    for (i = 0; i < step->value_len; ++i) {
        const char *role = ppoccurrence_fold_v1_role_name(
            &context->fold, step->values[i].role_id);
        if (role && strcmp(role, "mm-include-path") == 0) {
            if (path) return internal_error(context, "repeated include-path role");
            path = &step->values[i];
        }
    }
    if (!path) return internal_error(context, "missing include-path role");
    joined = join_path(context->files[parent].canonical, path->bytes, path->byte_len);
    if (!joined) return internal_error(context, "cannot allocate included path");
    canonical = realpath(joined, NULL);
    free(joined);
    if (!canonical)
        return reject(context, parent, path->left_byte, path->right_byte,
                      "included source does not exist");
    graph_bytes(context, path->bytes, path->byte_len);
    for (i = 0; i < context->source.file_count; ++i) {
        if (strcmp(context->files[i].canonical, canonical) != 0) continue;
        if (context->files[i].active && context->policy == MM2_INCLUDE_REJECT_ACTIVE)
            ok = reject(context, parent, path->left_byte, path->right_byte,
                        "active include cycle");
        else ok = true;
        goto done;
    }
    logical = join_path(context->source.files[parent].name, path->bytes, path->byte_len);
    if (!logical) {
        internal_error(context, "cannot allocate included source identity");
        goto done;
    }
    if (!add_file(context, canonical, logical, &child)) goto done;
    canonical = logical = NULL;
    if (!read_bytes(context, context->files[child].canonical,
                     &context->files[child].bytes, &context->files[child].len,
                     &context->source.files[child]) ||
        !project_tokens(context, child)) goto done;
    graph_bytes(context, context->files[child].bytes, context->files[child].len);
    ok = parse_file(context, child, diagnostic, diagnostic_size);
done:
    free(canonical);
    free(logical);
    return ok;
}

static bool capture(void *opaque, const PPOccurrenceFoldV1Step *step,
                     char *diagnostic, size_t diagnostic_size) {
    reader_context *context = opaque;
    const char *operation = ppoccurrence_fold_v1_operation_name(
        &context->fold, step->operation_id);
    const char *directive = NULL;
    mm2_statement statement = {0};
    mm2_token *labels = NULL;
    size_t label_count = 0;
    bool ok = false;
    if (!operation) return internal_error(context, "unknown native occurrence operation");
    if (strcmp(operation, "mm-complete-block") == 0) return true;
    if (strcmp(operation, "mm-resolve-include") == 0)
        return include_file(context, step, diagnostic, diagnostic_size);
    if (strcmp(operation, "mm-declare-constants") == 0) {
        statement.kind = MM2_CONST; directive = "$c";
    } else if (strcmp(operation, "mm-declare-variables") == 0) {
        statement.kind = MM2_VAR; directive = "$v";
    } else if (strcmp(operation, "mm-open-scope") == 0) {
        statement.kind = MM2_SCOPE_OPEN; directive = "${";
    } else if (strcmp(operation, "mm-close-scope") == 0) {
        statement.kind = MM2_SCOPE_CLOSE; directive = "$}";
    } else if (strcmp(operation, "mm-declare-floating") == 0) {
        statement.kind = MM2_FLOAT; directive = "$f";
    } else if (strcmp(operation, "mm-declare-essential") == 0) {
        statement.kind = MM2_ESSENTIAL; directive = "$e";
    } else if (strcmp(operation, "mm-declare-disjoint") == 0) {
        statement.kind = MM2_DV; directive = "$d";
    } else if (strcmp(operation, "mm-declare-axiom") == 0) {
        statement.kind = MM2_AXIOM; directive = "$a";
    } else if (strcmp(operation, "mm-check-theorem-normal") == 0) {
        statement.kind = MM2_THEOREM; directive = "$p";
        statement.proof_kind = MM2_PROOF_NORMAL;
    } else if (strcmp(operation, "mm-check-theorem-compressed") == 0) {
        statement.kind = MM2_THEOREM; directive = "$p";
        statement.proof_kind = MM2_PROOF_COMPRESSED;
    } else return internal_error(context, "unrecognized source occurrence operation");
    statement.source_id = context->current;
    if (!copy_role(context, step, "mm-label", &labels, &label_count)) goto done;
    if (label_count > 1) {
        internal_error(context, "native occurrence contains multiple labels");
        goto done;
    }
    if (label_count) { statement.label = labels[0]; memset(&labels[0], 0, sizeof(labels[0])); }
    if (!copy_role(context, step, "mm-symbol", &statement.symbols, &statement.symbol_count) ||
        !copy_role(context, step, "mm-proof-step", &statement.proof_labels,
                   &statement.proof_label_count) ||
        !copy_role(context, step, "mm-compressed-word", &statement.compressed_words,
                   &statement.compressed_word_count) ||
        !punctuation(context, &statement, directive, step->left_byte, step->right_byte))
        goto done;
    if (!grow((void **)&context->source.statements, &context->statement_capacity,
              context->source.statement_count + 1, sizeof(*context->source.statements))) {
        internal_error(context, "cannot allocate source statements");
        goto done;
    }
    context->source.statements[context->source.statement_count++] = statement;
    memset(&statement, 0, sizeof(statement));
    ok = true;
done:
    for (size_t i = 0; i < label_count; ++i) token_free(&labels[i]);
    free(labels);
    statement_free(&statement);
    return ok;
}

static bool commit(void *opaque, char *diagnostic, size_t diagnostic_size) {
    reader_context *context = opaque;
    (void)diagnostic;
    (void)diagnostic_size;
    if (context->aborted) return false;
    if (context->depth == 1) context->committed = true;
    return true;
}

static void abort_read(void *opaque) {
    ((reader_context *)opaque)->aborted = true;
}

static bool parse_file(reader_context *context, uint32_t source_id,
                        char *diagnostic, size_t diagnostic_size) {
    const PPOccurrenceFoldV1Backend backend = {context, capture, commit, abort_read};
    PPOccurrenceFoldV1Receipt receipt = {0};
    uint32_t parent = context->current;
    bool ok;
    if (context->depth >= 4096)
        return internal_error(context, "native include depth resource limit");
    context->current = source_id;
    context->files[source_id].active = true;
    ++context->depth;
    ok = ppoccurrence_fold_v1_run_bytes_with_span_mask(
        &context->program, &context->fold, &context->mask,
        context->files[source_id].cursor_bytes ? context->files[source_id].cursor_bytes :
            context->files[source_id].bytes,
        context->files[source_id].len,
        &backend, PPGUARDED_LEX_CURSOR_V1_COUNTERS_ONLY, UINT64_MAX,
        &receipt, diagnostic, diagnostic_size);
    --context->depth;
    context->files[source_id].active = false;
    context->files[source_id].completed = ok && receipt.committed;
    context->current = parent;
    if (!ok || !receipt.committed) {
        if (context->error && context->error->status != MM2_OK) return false;
        if (ok && receipt.parser_receipt.outcome == PPGUARDED_LEX_CURSOR_V1_REJECTED)
            return reject(context, source_id, 0, context->files[source_id].len,
                          "native Metamath parser rejected the source");
        mm2_error_set(context->error, MM2_ERROR, source_id, 0, 0,
                       diagnostic[0] ? diagnostic : "native source fold did not commit");
        return false;
    }
    return true;
}

mm2_status mm2_read_source(const char *path,
                          const mm2_reader_options *options,
                          mm2_source *out, mm2_error *error) {
    reader_context context = {0};
    SymbolTable symbols;
    char diagnostic[512] = {0};
    char *canonical = NULL, *logical = NULL;
    const char *root_name = options && options->root_name ? options->root_name : "unit.mm";
    static const uint8_t graph_domain[] = "MM2NativeReaderSourcesV1";
    uint32_t root;
    mm2_status result = MM2_ERROR;
    mm2_error local_error;
    if (!error) error = &local_error;
    mm2_error_clear(error);
    if (!path || !out || !root_name[0] ||
        (options && options->include_policy != MM2_INCLUDE_BOOK &&
         options->include_policy != MM2_INCLUDE_REJECT_ACTIVE)) {
        mm2_error_set(error, MM2_ERROR, UINT32_MAX, 0, 0, "invalid source-reader arguments");
        return MM2_ERROR;
    }
    memset(out, 0, sizeof(*out));
    context.error = error;
    context.policy = options ? options->include_policy : MM2_INCLUDE_BOOK;
    context.current = UINT32_MAX;
    symbol_table_init(&symbols);
    symbol_table_init_builtins(&symbols, &g_builtin_syms);
    g_symbols = &symbols;
    g_hashcons = NULL;
    g_var_intern = NULL;
    ppguarded_lex_cursor_v1_program_init(&context.program);
    ppoccurrence_fold_v1_plan_init(&context.fold);
    ppoccurrence_span_mask_v1_plan_init(&context.mask);
    cetta_native_sha256_init(&context.graph_hash);
    graph_bytes(&context, graph_domain, sizeof(graph_domain) - 1);
    canonical = realpath(path, NULL);
    logical = strdup(root_name);
    if (!canonical || !logical) {
        internal_error(&context, "cannot resolve the source root");
        goto done;
    }
    if (!add_file(&context, canonical, logical, &root)) goto done;
    canonical = logical = NULL;
    context.current = root;
    if (!read_bytes(&context, context.files[root].canonical,
                     &context.files[root].bytes, &context.files[root].len,
                     &context.source.files[root]) ||
        !project_tokens(&context, root)) goto done;
    cetta_native_sha256_hex(context.files[root].bytes, context.files[root].len,
                            context.source.source_digest);
    graph_bytes(&context, context.files[root].bytes, context.files[root].len);
    if (!metamath_syntax_cursor_fold_v1_program_init(
            &context.program, diagnostic, sizeof(diagnostic)) ||
        strcmp(context.program.program_digest,
               metamath_syntax_cursor_fold_v1_program_digest()) != 0 ||
        !metamath_syntax_cursor_fold_v1_occurrence_fold_plan_init(
            &context.program, &context.fold, diagnostic, sizeof(diagnostic)) ||
        !metamath_syntax_cursor_fold_v1_occurrence_span_mask_plan_init(
            &context.program, &context.fold, &context.mask, diagnostic, sizeof(diagnostic))) {
        internal_error(&context, diagnostic[0] ? diagnostic : "native cursor identity mismatch");
        goto done;
    }
    memcpy(context.source.parser_digest, context.program.program_digest, 65);
    if (!parse_file(&context, root, diagnostic, sizeof(diagnostic)) ||
        !context.committed || context.aborted) goto done;
    cetta_native_sha256_finish_hex(&context.graph_hash, context.source.include_digest);
    *out = context.source;
    memset(&context.source, 0, sizeof(context.source));
    result = MM2_OK;
done:
    if (result != MM2_OK) result = error->status == MM2_REJECTED ? MM2_REJECTED : MM2_ERROR;
    for (size_t i = 0; i < (result == MM2_OK ? out->file_count : context.source.file_count); ++i) {
        free(context.files[i].canonical);
        free(context.files[i].bytes);
        free(context.files[i].cursor_bytes);
        free(context.files[i].tokens);
    }
    free(context.files);
    free(canonical);
    free(logical);
    mm2_source_free(&context.source);
    ppoccurrence_span_mask_v1_plan_free(&context.mask);
    ppoccurrence_fold_v1_plan_free(&context.fold);
    ppguarded_lex_cursor_v1_program_free(&context.program);
    symbol_table_free(&symbols);
    g_symbols = NULL;
    return result;
}
