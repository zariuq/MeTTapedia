#ifndef METTAPEDIA_MM2_MODEL_H
#define METTAPEDIA_MM2_MODEL_H

#include "reader.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef size_t mm2_id;
#define MM2_NO_ID SIZE_MAX

typedef struct mm2_model mm2_model;

typedef enum {
    MM2_MATH_CONSTANT,
    MM2_MATH_VARIABLE
} mm2_symbol_kind;

typedef struct {
    mm2_symbol_kind kind;
    mm2_id name;
} mm2_symbol;

typedef struct {
    mm2_id typecode;
    const mm2_symbol *body;
    size_t body_count;
} mm2_formula;

typedef struct {
    mm2_id left;
    mm2_id right;
} mm2_pair;

typedef enum {
    MM2_HYP_FLOATING,
    MM2_HYP_ESSENTIAL
} mm2_hypothesis_kind;

typedef struct {
    mm2_hypothesis_kind kind;
    mm2_id label;
    mm2_formula formula;
    /* A floating formula is its typecode followed by this one variable.
     * Essential hypotheses use MM2_NO_ID here. */
    mm2_id variable;
} mm2_hypothesis;

/* An immutable source assertion preview, never a proof-admission receipt.
 * Hypotheses and DV pairs retain the source state's mandatory order. */
typedef struct {
    size_t index;
    mm2_id label;
    bool is_theorem;
    mm2_formula formula;
    const mm2_id *mandatory_names;
    size_t mandatory_name_count;
    const mm2_hypothesis *const *hypotheses;
    size_t hypothesis_count;
    const mm2_pair *dv;
    size_t dv_count;
} mm2_assertion;

/* Views borrow the mutable model's backing arrays. They are valid only for
 * the duration of the synchronous callback, not after mm2_prepare returns.
 * Prior proof-label inventory is active_hypotheses followed by assertions;
 * before excludes the current assertion/theorem preview. */
typedef struct {
    const mm2_model *model;
    const mm2_id *declared_constants;
    size_t declared_constant_count;
    const mm2_id *declared_variables;
    size_t declared_variable_count;
    const mm2_id *active_variables;
    size_t active_variable_count;
    const mm2_hypothesis *const *active_hypotheses;
    size_t active_hypothesis_count;
    /* All active source $d pairs. Proof-facing caller DV additionally
     * requires active floating hypotheses for both endpoints. */
    const mm2_pair *active_dv;
    size_t active_dv_count;
    const mm2_assertion *const *assertions;
    size_t assertion_count;
    size_t scope_depth;
} mm2_state_view;

typedef enum {
    MM2_PREPARE_BEGIN,
    MM2_PREPARE_STATEMENT,
    MM2_PREPARE_END
} mm2_prepare_event_kind;

typedef struct {
    mm2_prepare_event_kind kind;
    const mm2_source *source;
    const mm2_statement *statement;
    /* Zero-based expanded source order; END uses statement_count. */
    size_t statement_index;
    mm2_state_view before;
    mm2_state_view after;
    const mm2_hypothesis *hypothesis;
    const mm2_assertion *assertion;
    /* Interned names of statement.symbols, without proof-token processing. */
    const mm2_id *names;
    size_t name_count;
    /* Exact append-only DV delta for $d, empty for all other statements. */
    const mm2_pair *added_dv;
    size_t added_dv_count;
} mm2_prepare_event;

typedef mm2_status (*mm2_prepare_callback)(const mm2_prepare_event *event,
                                         void *userdata, mm2_error *error);

/* Fold declarations in expanded order. Proof payloads remain source-owned,
 * unresolved and undecoded; no proof execution or oracle is performed.
 * Theorem preparation appends a preview only. Its proof-gated runtime delta
 * consists of the new assertion's rows, not an admission in this model. */
mm2_status mm2_prepare(const mm2_source *source, mm2_prepare_callback callback,
                       void *userdata, mm2_error *error);

/* Interned ASCII names remain stable while mm2_prepare invokes callbacks. */
const char *mm2_model_name(const mm2_model *model, mm2_id name);
size_t mm2_model_name_length(const mm2_model *model, mm2_id name);

#endif
