#include "emit.h"
#include "wire.h"

static void span(FILE *out, const mm2_source *source, const mm2_token *token) {
    mm2_wire_span(out, source, token->source_id, token->start, token->end);
}

static void names(FILE *out, const mm2_source *source,
                  const mm2_token *tokens, size_t count, int raw_bytes) {
    for (size_t i = 0; i < count; ++i) {
        fputs("(mm-cons ", out);
        if (raw_bytes) mm2_wire_token(out, source, &tokens[i]);
        else mm2_wire_name(out, source, &tokens[i]);
        fputc(' ', out);
    }
    fputs("(mm-nil)", out);
    for (size_t i = 0; i < count; ++i) fputc(')', out);
}

void mm2_emit_statement(FILE *out, const mm2_source *source,
                        const mm2_statement *statement) {
    static const char *const tags[] = {
        "mm-source-const", "mm-source-var", "mm-source-open-scope",
        "mm-source-close-scope", "mm-source-floating", "mm-source-essential",
        "mm-source-dv", "mm-source-axiom", "mm-source-theorem"
    };
    fprintf(out, "(%s ", tags[statement->kind]);
    span(out, source, &statement->site);
    if (statement->kind == MM2_SCOPE_OPEN || statement->kind == MM2_SCOPE_CLOSE) {
        fputc(')', out);
        return;
    }
    fputc(' ', out);
    if (statement->kind == MM2_CONST || statement->kind == MM2_VAR ||
        statement->kind == MM2_DV) {
        names(out, source, statement->symbols, statement->symbol_count, 0);
    } else {
        mm2_wire_name(out, source, &statement->label);
        fputc(' ', out);
        mm2_wire_name(out, source, &statement->symbols[0]);
        fputc(' ', out);
        if (statement->kind == MM2_FLOAT)
            mm2_wire_name(out, source, &statement->symbols[1]);
        else
            names(out, source, statement->symbols + 1,
                   statement->symbol_count - 1, 0);
        if (statement->kind == MM2_THEOREM) {
            fputc(' ', out);
            if (statement->proof_kind == MM2_PROOF_NORMAL) {
                fputs("(mm-source-normal-proof ", out);
                names(out, source, statement->proof_labels,
                       statement->proof_label_count, 0);
            } else {
                fputs("(mm-source-compressed-proof ", out);
                span(out, source, &statement->open_paren);
                fputc(' ', out);
                names(out, source, statement->proof_labels,
                       statement->proof_label_count, 0);
                fputc(' ', out);
                span(out, source, &statement->close_paren);
                fputc(' ', out);
                names(out, source, statement->compressed_words,
                       statement->compressed_word_count, 1);
            }
            fputs(") ", out);
            span(out, source, &statement->separator);
        }
    }
    fputc(' ', out);
    span(out, source, &statement->terminator);
    fputc(')', out);
}

void mm2_emit_event_rows(FILE *out, const mm2_source *source,
                         const char *owner) {
    fputs("(mm-source-start ", out);
    mm2_wire_cstring(out, owner);
    fputs(")\n", out);
    for (size_t i = 0; i < source->statement_count; ++i) {
        fputs("(mm-linked-row ", out);
        mm2_wire_cstring(out, "source-statement");
        fputc(' ', out);
        mm2_wire_cstring(out, owner);
        fputc(' ', out);
        mm2_wire_nat(out, i);
        fputc(' ', out);
        mm2_wire_nat(out, i + 1);
        fputc(' ', out);
        mm2_emit_statement(out, source, &source->statements[i]);
        fputs(")\n", out);
    }
    fputs("(mm-source-end ", out);
    mm2_wire_cstring(out, owner);
    fputc(' ', out);
    mm2_wire_nat(out, source->statement_count);
    fputs(")\n", out);

    /* Initial ledgers are empty. Source data never supplies an approved
     * runtime assertion, active hypothesis, or disjointness capability. */
    const char *const object_ledgers[] = {
        NULL, "mm-source-active-variable-ledger",
        "mm-source-variable-typecode-ledger"
    };
    for (size_t i = 0; i < 3; ++i) {
        fputs("(mm-source-object-frontier ", out);
        if (object_ledgers[i]) fprintf(out, "(%s ", object_ledgers[i]);
        mm2_wire_cstring(out, owner);
        if (object_ledgers[i]) fputc(')', out);
        fputs(" (mm-source-object-root))\n", out);
    }
    const char *const activity_ledgers[] = {
        "mm-source-active-hypothesis-ledger", "mm-source-active-distinct-ledger"
    };
    for (size_t i = 0; i < 2; ++i) {
        fprintf(out, "(mm-source-activity-frontier (%s ", activity_ledgers[i]);
        mm2_wire_cstring(out, owner);
        fputs(") (mm-source-object-root))\n", out);
    }
    fputs("(mm-source-dv-occurrence-frontier ", out);
    mm2_wire_cstring(out, owner);
    fputs(" (mm-nat 0))\n", out);
}
