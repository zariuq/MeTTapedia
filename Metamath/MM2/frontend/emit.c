#include "emit.h"
#include "model.h"
#include "wire.h"

#include <stdint.h>

typedef struct {
    FILE *out;
    const mm2_source *source;
    const char *owner;
    const mm2_model *model;
} emitter;

static void space(emitter *e) { fputc(' ', e->out); }
static void nat(emitter *e, size_t value) { mm2_wire_nat(e->out, value); }
static void scope(emitter *e) { mm2_wire_cstring(e->out, e->owner); }
static void name(emitter *e, mm2_id id) {
    mm2_wire_string(e->out, (const uint8_t *)mm2_model_name(e->model, id),
                    mm2_model_name_length(e->model, id));
}
static void token_name(emitter *e, const mm2_token *token) {
    mm2_wire_string(e->out, token->bytes, token->len);
}
static void end_row(emitter *e) { fputs(")\n", e->out); }
static void positioned_owner(emitter *e, const char *tag, size_t position) {
    fprintf(e->out, "(%s ", tag);
    scope(e); space(e); nat(e, position); fputc(')', e->out);
}
static void proof_owner(emitter *e, size_t position) {
    positioned_owner(e, "mm-source-proof-owner", position);
}
static void action_owner(emitter *e, size_t position) {
    positioned_owner(e, "mm-source-action-owner", position);
}
static void publication_owner(emitter *e, size_t position) {
    positioned_owner(e, "mm-source-assertion-publication-owner", position);
}
static void dv_owner(emitter *e, size_t position) {
    positioned_owner(e, "mm-source-dv-pair-plan-owner", position);
}
static void list_end(emitter *e, size_t count) {
    fputs("(mm-nil)", e->out);
    for (size_t i = 0; i < count; ++i) fputc(')', e->out);
}
static void id_list(emitter *e, const mm2_id *values, size_t count) {
    for (size_t i = 0; i < count; ++i) {
        fputs("(mm-cons ", e->out); name(e, values[i]); space(e);
    }
    list_end(e, count);
}
static void pair(emitter *e, mm2_pair value) {
    fputs("(mm-pair ", e->out); name(e, value.left); space(e);
    name(e, value.right); fputc(')', e->out);
}
static void pair_list(emitter *e, const mm2_pair *values, size_t count) {
    for (size_t i = 0; i < count; ++i) {
        fputs("(mm-cons ", e->out); pair(e, values[i]); space(e);
    }
    list_end(e, count);
}
static void body(emitter *e, const mm2_formula *value) {
    for (size_t i = 0; i < value->body_count; ++i) {
        fprintf(e->out, "(mm-cons (%s ",
                value->body[i].kind == MM2_MATH_CONSTANT ? "mm-const" : "mm-variable");
        name(e, value->body[i].name); fputs(") ", e->out);
    }
    list_end(e, value->body_count);
}
static void formula(emitter *e, const mm2_formula *value) {
    fputs("(mm-formula ", e->out); name(e, value->typecode); space(e);
    body(e, value); fputc(')', e->out);
}
static void hypothesis(emitter *e, const mm2_hypothesis *value) {
    if (value->kind == MM2_HYP_FLOATING) {
        fputs("(mm-floating ", e->out); name(e, value->label); space(e);
        name(e, value->formula.typecode); space(e); name(e, value->variable);
    } else {
        fputs("(mm-essential ", e->out); name(e, value->label); space(e);
        formula(e, &value->formula);
    }
    fputc(')', e->out);
}
static void source_assertion(emitter *e, const mm2_assertion *value) {
    fputs("(mm-assertion ", e->out); name(e, value->label); space(e);
    formula(e, &value->formula); fputs(" (mm-frame ", e->out);
    pair_list(e, value->dv, value->dv_count); space(e);
    for (size_t i = 0; i < value->hypothesis_count; ++i) {
        fputs("(mm-cons ", e->out); name(e, value->hypotheses[i]->label); space(e);
    }
    list_end(e, value->hypothesis_count); fputs(") ", e->out);
    for (size_t i = 0; i < value->hypothesis_count; ++i) {
        fputs("(mm-cons ", e->out); hypothesis(e, value->hypotheses[i]); space(e);
    }
    list_end(e, value->hypothesis_count); fputc(')', e->out);
}

static size_t assertion_row_count(const mm2_assertion *value) {
    return 2 * value->hypothesis_count + 2 * value->dv_count + 3;
}

/* Exact assertionExecutionRowsFor order. A row can be emitted directly as
 * proof-neutral support, or enclosed in a proof-gated publication action. */
static void assertion_row(emitter *e, const mm2_assertion *value, size_t index) {
    if (index == 0) {
        fputs("(mm-assertion-header ", e->out); scope(e); space(e);
        nat(e, value->index); space(e); name(e, value->label); space(e);
        nat(e, value->hypothesis_count);
    } else if (--index < value->hypothesis_count) {
        fputs("(mm-assertion-hypothesis ", e->out); scope(e); space(e);
        name(e, value->label); space(e); nat(e, index); space(e);
        hypothesis(e, value->hypotheses[index]);
    } else if ((index -= value->hypothesis_count) < value->hypothesis_count) {
        fputs("(mm-assertion-hypothesis-successor ", e->out); scope(e); space(e);
        name(e, value->label); space(e); nat(e, index); space(e); nat(e, index + 1);
    } else if ((index -= value->hypothesis_count) == 0) {
        fputs("(mm-assertion-dv-header ", e->out); scope(e); space(e);
        name(e, value->label); space(e); nat(e, value->dv_count);
    } else if (--index < value->dv_count) {
        fputs("(mm-assertion-dv-pair ", e->out); scope(e); space(e);
        name(e, value->label); space(e); nat(e, index); space(e);
        name(e, value->dv[index].left); space(e); name(e, value->dv[index].right);
    } else if ((index -= value->dv_count) < value->dv_count) {
        fputs("(mm-assertion-dv-successor ", e->out); scope(e); space(e);
        name(e, value->label); space(e); nat(e, index); space(e); nat(e, index + 1);
    } else {
        fputs("(mm-assertion-result ", e->out); scope(e); space(e);
        name(e, value->label); space(e); name(e, value->formula.typecode); space(e);
        body(e, &value->formula);
    }
    fputc(')', e->out);
}

static void statement_prefix(emitter *e, const char *tag,
                              const mm2_prepare_event *event) {
    fprintf(e->out, "(%s ", tag); scope(e); space(e);
    nat(e, event->statement_index); space(e); nat(e, event->statement_index + 1);
    space(e); mm2_emit_statement(e->out, e->source, event->statement); space(e);
}
static void assertion_candidate(emitter *e, const mm2_prepare_event *event) {
    const mm2_assertion *value = event->assertion;
    statement_prefix(e, "mm-source-assertion-candidate", event);
    nat(e, value->index); space(e); nat(e, value->index + 1); space(e);
    fputs(value->is_theorem ? "mm-source-action-after-proof " :
                             "mm-source-action-immediate ", e->out);
    id_list(e, value->mandatory_names, value->mandatory_name_count); space(e);
    source_assertion(e, value); end_row(e);
}
static void successor(emitter *e, void (*owner)(emitter *, size_t),
                       size_t source_position, size_t position) {
    fputs("(mm-index-successor ", e->out); owner(e, source_position); space(e);
    nat(e, position); space(e); nat(e, position + 1); end_row(e);
}
static void publication(emitter *e, const mm2_prepare_event *event) {
    const mm2_assertion *value = event->assertion;
    size_t count = assertion_row_count(value);
    statement_prefix(e, "mm-source-assertion-publication-plan", event);
    nat(e, value->index); space(e); nat(e, value->index + 1); space(e);
    id_list(e, value->mandatory_names, value->mandatory_name_count); space(e);
    source_assertion(e, value); space(e); nat(e, count); end_row(e);
    for (size_t i = 0; i < count; ++i) {
        fputs("(mm-linked-row ", e->out);
        mm2_wire_cstring(e->out, "source-assertion-publication"); space(e);
        publication_owner(e, event->statement_index); space(e);
        nat(e, i); space(e); nat(e, i + 1); space(e);
        assertion_row(e, value, i); end_row(e);
    }
    for (size_t i = 0; i < count; ++i)
        successor(e, publication_owner, event->statement_index, i);
}
static void theorem_actions(emitter *e, const mm2_prepare_event *event) {
    const mm2_assertion *value = event->assertion;
    size_t count = assertion_row_count(value);
    statement_prefix(e, "mm-source-action-plan", event);
    fputs("mm-source-action-after-proof ", e->out); nat(e, count); end_row(e);
    for (size_t i = 0; i < count; ++i) {
        fputs("(mm-linked-row ", e->out);
        mm2_wire_cstring(e->out, "source-action"); space(e);
        action_owner(e, event->statement_index); space(e);
        nat(e, i); space(e); nat(e, i + 1); fputs(" (mm-source-action-add ", e->out);
        assertion_row(e, value, i); fputc(')', e->out); end_row(e);
    }
    for (size_t i = 0; i < count; ++i)
        successor(e, action_owner, event->statement_index, i);
    for (size_t i = 0; i < count; ++i) {
        fputs("(mm-source-action-kind ", e->out);
        action_owner(e, event->statement_index); space(e); nat(e, i);
        fputs(" mm-source-action-add", e->out); end_row(e);
    }
}
static void normal_inventory(emitter *e, const mm2_prepare_event *event) {
    size_t total = event->before.active_hypothesis_count + event->before.assertion_count;
    for (size_t i = 0; i < total; ++i) {
        int is_hypothesis = i < event->before.active_hypothesis_count;
        mm2_id label = is_hypothesis ? event->before.active_hypotheses[i]->label :
            event->before.assertions[i - event->before.active_hypothesis_count]->label;
        fputs("(mm-linked-row ", e->out);
        mm2_wire_cstring(e->out, "normal-label-candidate"); space(e);
        proof_owner(e, event->statement_index); space(e);
        nat(e, i); space(e); nat(e, i + 1); fputs(" (mm-normal-label-entry ", e->out);
        name(e, label); fprintf(e->out, " %s)",
            is_hypothesis ? "mm-normal-label-hypothesis" : "mm-normal-label-assertion");
        end_row(e);
    }
    fputs("(mm-normal-label-frontier ", e->out);
    proof_owner(e, event->statement_index); space(e); nat(e, total); end_row(e);
}
static void normal_proof(emitter *e, const mm2_prepare_event *event) {
    const mm2_statement *statement = event->statement;
    for (size_t i = 0; i < statement->proof_label_count; ++i) {
        fputs("(mm-linked-row ", e->out);
        mm2_wire_cstring(e->out, "normal-proof-label"); space(e);
        proof_owner(e, event->statement_index); space(e);
        nat(e, i); space(e); nat(e, i + 1); space(e);
        token_name(e, &statement->proof_labels[i]); end_row(e);
    }
    for (size_t i = 0; i < statement->proof_label_count; ++i)
        successor(e, proof_owner, event->statement_index, i);
    fputs("(mm-proof-end ", e->out); proof_owner(e, event->statement_index); space(e);
    nat(e, statement->proof_label_count); end_row(e);
    fputs("(mm-source-proof-control-prepared ", e->out); scope(e); space(e);
    proof_owner(e, event->statement_index); fputs(" (mm-normal-control ", e->out);
    scope(e); space(e); proof_owner(e, event->statement_index);
    fputs(" (mm-nat 0) (mm-nat 0))", e->out); end_row(e);
    normal_inventory(e, event);
}
static void compact_successors(emitter *e, size_t source_position,
                               const char *owner_tag, size_t count) {
    for (size_t i = 0; i < count; ++i) {
        fputs(owner_tag ? "(mm-compressed-index-successor " : "(mm-index-successor ", e->out);
        if (owner_tag) fprintf(e->out, "(%s ", owner_tag);
        proof_owner(e, source_position);
        if (owner_tag) fputc(')', e->out);
        space(e); mm2_wire_index(e->out, i); space(e);
        mm2_wire_index(e->out, i + 1); end_row(e);
    }
}
static mm2_status compressed_proof(emitter *e, const mm2_prepare_event *event,
                                   mm2_error *error) {
    const mm2_statement *statement = event->statement;
    const mm2_assertion *value = event->assertion;
    size_t bytes = 0;
    for (size_t i = 0; i < statement->compressed_word_count; ++i) {
        if (statement->compressed_words[i].len > SIZE_MAX - bytes)
            goto overflow;
        bytes += statement->compressed_words[i].len;
    }
    if (value->hypothesis_count > SIZE_MAX - statement->proof_label_count)
        goto overflow;
    size_t header_count = value->hypothesis_count + statement->proof_label_count;
    if (header_count > SIZE_MAX - bytes || bytes == SIZE_MAX) goto overflow;
    for (size_t i = 0; i < header_count; ++i) {
        fputs("(mm-linked-row ", e->out);
        mm2_wire_cstring(e->out, "compressed-header-item"); space(e);
        proof_owner(e, event->statement_index); space(e);
        nat(e, i); space(e); nat(e, i + 1); space(e);
        if (i < value->hypothesis_count) {
            const mm2_hypothesis *hyp = value->hypotheses[i];
            fputs("(mm-compressed-header-mandatory ", e->out);
            name(e, hyp->label); space(e); formula(e, &hyp->formula);
        } else {
            fputs("(mm-compressed-header-explicit ", e->out);
            token_name(e, &statement->proof_labels[i - value->hypothesis_count]);
        }
        fputc(')', e->out); end_row(e);
    }
    fputs("(mm-compressed-header-end ", e->out);
    proof_owner(e, event->statement_index); space(e); nat(e, header_count); end_row(e);
    for (size_t i = 0; i < statement->compressed_word_count; ++i) {
        fputs("(mm-row ", e->out);
        mm2_wire_cstring(e->out, "compressed-body-word"); space(e);
        proof_owner(e, event->statement_index); space(e); nat(e, i); space(e);
        mm2_wire_bytes(e->out, statement->compressed_words[i].bytes,
                        statement->compressed_words[i].len); end_row(e);
    }
    for (size_t i = 0; i < statement->compressed_word_count; ++i)
        successor(e, proof_owner, event->statement_index, i);
    fputs("(mm-proof-end ", e->out); proof_owner(e, event->statement_index); space(e);
    nat(e, statement->compressed_word_count); end_row(e);
    compact_successors(e, event->statement_index, "mm-compressed-heap-owner", header_count + bytes);
    compact_successors(e, event->statement_index, "mm-compressed-node-owner", value->hypothesis_count + bytes);
    compact_successors(e, event->statement_index, "mm-compressed-stack-owner", bytes + 1);
    compact_successors(e, event->statement_index, NULL, bytes + 1);
    fputs("(mm-compressed-machine ", e->out); scope(e); space(e);
    proof_owner(e, event->statement_index);
    for (size_t i = 0; i < 3; ++i) { space(e); mm2_wire_index(e->out, 0); }
    end_row(e);
    fputs("(mm-source-proof-control-prepared ", e->out); scope(e); space(e);
    proof_owner(e, event->statement_index); fputs(" (mm-compressed-header-control ", e->out);
    scope(e); space(e); proof_owner(e, event->statement_index);
    fputs(" (mm-nat 0))", e->out); end_row(e);
    return MM2_OK;
overflow:
    mm2_error_set(error, MM2_ERROR, statement->source_id, statement->start,
                   statement->end, "compressed source capacity overflow");
    return MM2_ERROR;
}
static mm2_status theorem(emitter *e, const mm2_prepare_event *event, mm2_error *error) {
    const mm2_assertion *value = event->assertion;
    statement_prefix(e, "mm-source-theorem-prepared", event);
    proof_owner(e, event->statement_index); space(e); name(e, value->label); space(e);
    formula(e, &value->formula); end_row(e);
    fputs("(mm-proof ", e->out); scope(e); space(e); proof_owner(e, event->statement_index);
    fputs(event->statement->proof_kind == MM2_PROOF_NORMAL ? " normal " : " compressed ", e->out);
    name(e, value->label); space(e); formula(e, &value->formula); end_row(e);
    if (event->statement->proof_kind == MM2_PROOF_NORMAL) normal_proof(e, event);
    else {
        mm2_status status = compressed_proof(e, event, error);
        if (status != MM2_OK) return status;
    }
    fputs("(mm-source-theorem-assertion-header ", e->out); scope(e); space(e);
    nat(e, event->statement_index); space(e); proof_owner(e, event->statement_index); space(e);
    assertion_row(e, value, 0); end_row(e);
    for (size_t i = 1; i < assertion_row_count(value); ++i) {
        assertion_row(e, value, i); fputc('\n', e->out);
    }
    theorem_actions(e, event);
    return MM2_OK;
}
static void dv_plan(emitter *e, const mm2_prepare_event *event) {
    size_t count = event->name_count * (event->name_count - 1) / 2;
    fputs("(mm-source-dv-pair-plan-header ", e->out); scope(e); space(e);
    nat(e, event->statement_index); space(e);
    mm2_emit_statement(e->out, e->source, event->statement); space(e); nat(e, count); end_row(e);
    size_t position = 0;
    for (size_t current = 1; current < event->name_count; ++current) {
        for (size_t earlier = 0; earlier < current; ++earlier, ++position) {
            mm2_id left = event->names[earlier], right = event->names[current];
            /* Lexicographic ASCII orientation, independent of intern IDs. */
            const char *a = mm2_model_name(e->model, left);
            const char *b = mm2_model_name(e->model, right);
            size_t i = 0;
            while (a[i] && a[i] == b[i]) ++i;
            mm2_pair canonical = (unsigned char)a[i] <= (unsigned char)b[i] ?
                (mm2_pair){left, right} : (mm2_pair){right, left};
            fputs("(mm-linked-row ", e->out); dv_owner(e, event->statement_index);
            fputs(" source-dv-pair-plan ", e->out); nat(e, position); space(e);
            nat(e, position + 1); space(e); pair(e, canonical); end_row(e);
            fputs("(mm-linked-row ", e->out); dv_owner(e, event->statement_index);
            fputs(" source-dv-pair-witness ", e->out); nat(e, position); space(e);
            nat(e, position + 1); fputs(" (mm-source-dv-pair-witness ", e->out);
            name(e, left); space(e); name(e, right); space(e); pair(e, canonical);
            fputc(')', e->out); end_row(e);
        }
    }
    fputs("(mm-source-dv-pair-plan-frontier ", e->out);
    dv_owner(e, event->statement_index); space(e); nat(e, count); end_row(e);
}
static mm2_status emit_event(const mm2_prepare_event *event, void *userdata,
                              mm2_error *error) {
    emitter *e = userdata;
    if (event->kind != MM2_PREPARE_STATEMENT) return MM2_OK;
    e->model = event->before.model;
    switch (event->statement->kind) {
        case MM2_DV: dv_plan(e, event); break;
        case MM2_ESSENTIAL:
            statement_prefix(e, "mm-source-essential-candidate", event);
            formula(e, &event->hypothesis->formula); fputs(" (mm-hypothesis-lookup ", e->out);
            scope(e); space(e); name(e, event->hypothesis->label); space(e);
            formula(e, &event->hypothesis->formula); fputc(')', e->out); end_row(e);
            break;
        case MM2_AXIOM:
            assertion_candidate(e, event); publication(e, event); break;
        case MM2_THEOREM:
            assertion_candidate(e, event);
            if (theorem(e, event, error) != MM2_OK) return MM2_ERROR;
            break;
        default: break;
    }
    if (ferror(e->out)) {
        mm2_error_set(error, MM2_ERROR, event->statement->source_id,
                       event->statement->start, event->statement->end,
                       "cannot write source-data rows");
        return MM2_ERROR;
    }
    return MM2_OK;
}

mm2_status mm2_emit_data(FILE *out, const mm2_source *source,
                         const char *owner, mm2_error *error) {
    emitter e = {out, source, owner, NULL};
    mm2_emit_event_rows(out, source, owner);
    mm2_status status = mm2_prepare(source, emit_event, &e, error);
    if (status == MM2_OK && ferror(out)) {
        mm2_error_set(error, MM2_ERROR, 0, 0, 0, "cannot write source data");
        return MM2_ERROR;
    }
    return status;
}
