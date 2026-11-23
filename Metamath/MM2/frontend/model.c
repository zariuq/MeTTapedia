#include "model.h"

#include <stdlib.h>
#include <string.h>

typedef enum {
    NAME_UNDECLARED,
    NAME_CONSTANT,
    NAME_VARIABLE,
    NAME_LABEL
} name_kind;

typedef struct {
    char *text;
    size_t length;
    uint64_t hash;
    name_kind kind;
    bool active;
    bool floating;
    size_t batch_mark;
    size_t mandatory_mark;
} name_entry;

typedef struct {
    size_t variables;
    size_t hypotheses;
    size_t distinct;
    mm2_token site;
} scope_boundary;

struct mm2_model {
    name_entry *names;
    size_t name_count, name_capacity;
    mm2_id *buckets;
    size_t bucket_count;
    mm2_id *constants;
    size_t constant_count, constant_capacity;
    mm2_id *variables;
    size_t variable_count, variable_capacity;
    mm2_id *active_variables;
    size_t active_variable_count, active_variable_capacity;
    const mm2_hypothesis **hypotheses;
    size_t hypothesis_count, hypothesis_capacity;
    const mm2_hypothesis **active_hypotheses;
    size_t active_hypothesis_count, active_hypothesis_capacity;
    mm2_pair *distinct;
    size_t distinct_count, distinct_capacity;
    const mm2_assertion **assertions;
    size_t assertion_count, assertion_capacity;
    scope_boundary *scopes;
    size_t scope_count, scope_capacity;
    mm2_id *statement_names;
    size_t statement_name_capacity;
    size_t batch_epoch, mandatory_epoch;
};

/* A before-view keeps only lengths, not a second copy of the state. Backing
 * arrays are rebound after an append, so realloc cannot invalidate it. */
typedef struct {
    size_t constants, variables, active_variables, hypotheses, distinct;
    size_t assertions, scopes;
} state_lengths;

static void *reserve_array(void *data, size_t *capacity, size_t needed,
                           size_t item_size) {
    if (needed <= *capacity) return data;
    if (needed > SIZE_MAX / item_size) return NULL;
    size_t next = *capacity ? *capacity : 16;
    while (next < needed) {
        if (next > SIZE_MAX / 2) {
            next = needed;
            break;
        }
        next *= 2;
    }
    if (next > SIZE_MAX / item_size) next = needed;
    void *grown = realloc(data, next * item_size);
    if (grown) *capacity = next;
    return grown;
}

#define RESERVE(array, capacity, needed) do { \
    void *grown_array = reserve_array((array), &(capacity), (needed), \
                                      sizeof(*(array))); \
    if (!grown_array) goto allocation_failure; \
    (array) = grown_array; \
} while (0)

static mm2_status error_at(mm2_error *error, mm2_status status,
                           const mm2_token *site, const char *message) {
    mm2_error_set(error, status, site ? site->source_id : 0,
                   site ? site->start : 0, site ? site->end : 0, message);
    return status;
}

static mm2_status allocation_error(mm2_error *error, const mm2_token *site) {
    return error_at(error, MM2_ERROR, site,
                    "source model allocation or size overflow");
}

static uint64_t name_hash(const uint8_t *bytes, size_t count) {
    uint64_t hash = UINT64_C(14695981039346656037);
    for (size_t i = 0; i < count; ++i) {
        hash ^= bytes[i];
        hash *= UINT64_C(1099511628211);
    }
    return hash;
}

static bool grow_buckets(mm2_model *model) {
    size_t count = model->bucket_count ? model->bucket_count : 32;
    if (model->bucket_count) {
        if (count > SIZE_MAX / 2) return false;
        count *= 2;
    }
    if (count > SIZE_MAX / sizeof(mm2_id)) return false;
    mm2_id *buckets = malloc(count * sizeof(*buckets));
    if (!buckets) return false;
    for (size_t i = 0; i < count; ++i) buckets[i] = MM2_NO_ID;
    for (size_t i = 0; i < model->name_count; ++i) {
        size_t slot = (size_t)model->names[i].hash & (count - 1);
        while (buckets[slot] != MM2_NO_ID) slot = (slot + 1) & (count - 1);
        buckets[slot] = i;
    }
    free(model->buckets);
    model->buckets = buckets;
    model->bucket_count = count;
    return true;
}

static bool intern_name(mm2_model *model, const mm2_token *token, mm2_id *id) {
    if (!model->bucket_count && !grow_buckets(model)) return false;
    uint64_t hash = name_hash(token->bytes, token->len);
    size_t slot = (size_t)hash & (model->bucket_count - 1);
    while (model->buckets[slot] != MM2_NO_ID) {
        mm2_id candidate = model->buckets[slot];
        const name_entry *entry = &model->names[candidate];
        if (entry->hash == hash && entry->length == token->len &&
            memcmp(entry->text, token->bytes, token->len) == 0) {
            *id = candidate;
            return true;
        }
        slot = (slot + 1) & (model->bucket_count - 1);
    }
    if (model->name_count == SIZE_MAX || token->len == SIZE_MAX) return false;
    if (model->name_count + 1 > model->bucket_count / 2) {
        if (!grow_buckets(model)) return false;
        slot = (size_t)hash & (model->bucket_count - 1);
        while (model->buckets[slot] != MM2_NO_ID)
            slot = (slot + 1) & (model->bucket_count - 1);
    }
    RESERVE(model->names, model->name_capacity, model->name_count + 1);
    char *text = malloc(token->len + 1);
    if (!text) return false;
    memcpy(text, token->bytes, token->len);
    text[token->len] = '\0';
    *id = model->name_count++;
    model->names[*id] = (name_entry){
        .text = text, .length = token->len, .hash = hash,
        .kind = NAME_UNDECLARED
    };
    model->buckets[slot] = *id;
    return true;

allocation_failure:
    return false;
}

const char *mm2_model_name(const mm2_model *model, mm2_id id) {
    return model && id < model->name_count ? model->names[id].text : NULL;
}

size_t mm2_model_name_length(const mm2_model *model, mm2_id id) {
    return model && id < model->name_count ? model->names[id].length : 0;
}

static state_lengths lengths(const mm2_model *model) {
    return (state_lengths){
        model->constant_count, model->variable_count,
        model->active_variable_count, model->active_hypothesis_count,
        model->distinct_count, model->assertion_count, model->scope_count
    };
}

static mm2_state_view view(const mm2_model *model, state_lengths sizes) {
    return (mm2_state_view){
        .model = model,
        .declared_constants = model->constants,
        .declared_constant_count = sizes.constants,
        .declared_variables = model->variables,
        .declared_variable_count = sizes.variables,
        .active_variables = model->active_variables,
        .active_variable_count = sizes.active_variables,
        .active_hypotheses = model->active_hypotheses,
        .active_hypothesis_count = sizes.hypotheses,
        .active_dv = model->distinct,
        .active_dv_count = sizes.distinct,
        .assertions = model->assertions,
        .assertion_count = sizes.assertions,
        .scope_depth = sizes.scopes
    };
}

static void free_model(mm2_model *model) {
    for (size_t i = 0; i < model->name_count; ++i) free(model->names[i].text);
    for (size_t i = 0; i < model->hypothesis_count; ++i) {
        free((void *)model->hypotheses[i]->formula.body);
        free((void *)model->hypotheses[i]);
    }
    for (size_t i = 0; i < model->assertion_count; ++i) {
        const mm2_assertion *assertion = model->assertions[i];
        free((void *)assertion->formula.body);
        free((void *)assertion->mandatory_names);
        free((void *)assertion->hypotheses);
        free((void *)assertion->dv);
        free((void *)assertion);
    }
    free(model->names);
    free(model->buckets);
    free(model->constants);
    free(model->variables);
    free(model->active_variables);
    free(model->hypotheses);
    free(model->active_hypotheses);
    free(model->distinct);
    free(model->assertions);
    free(model->scopes);
    free(model->statement_names);
}

static bool math_name_valid(const mm2_token *token) {
    if (!token->bytes || !token->len) return false;
    for (size_t i = 0; i < token->len; ++i)
        if (token->bytes[i] < 33 || token->bytes[i] > 126 ||
            token->bytes[i] == '$') return false;
    return true;
}

static bool label_valid(const mm2_token *token) {
    if (!token->bytes || !token->len) return false;
    for (size_t i = 0; i < token->len; ++i) {
        uint8_t c = token->bytes[i];
        if (!((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') ||
              (c >= '0' && c <= '9') || c == '-' || c == '_' || c == '.'))
            return false;
    }
    return true;
}

static bool distinct_batch(mm2_model *model, size_t count) {
    if (++model->batch_epoch == 0) {
        for (size_t i = 0; i < model->name_count; ++i)
            model->names[i].batch_mark = 0;
        model->batch_epoch = 1;
    }
    for (size_t i = 0; i < count; ++i) {
        name_entry *entry = &model->names[model->statement_names[i]];
        if (entry->batch_mark == model->batch_epoch) return false;
        entry->batch_mark = model->batch_epoch;
    }
    return true;
}

static mm2_status prepare_names(mm2_model *model, const mm2_statement *statement,
                                mm2_id *label, mm2_error *error) {
    size_t count = statement->symbol_count;
    if (count) {
        if (!statement->symbols)
            return error_at(error, MM2_ERROR, &statement->site,
                            "statement has no symbol storage");
        RESERVE(model->statement_names, model->statement_name_capacity, count);
    }
    for (size_t i = 0; i < count; ++i) {
        const mm2_token *token = &statement->symbols[i];
        if (!math_name_valid(token))
            return error_at(error, MM2_REJECTED, token, "invalid math symbol");
        if (!intern_name(model, token, &model->statement_names[i]))
            return allocation_error(error, token);
    }
    *label = MM2_NO_ID;
    if (statement->kind == MM2_FLOAT || statement->kind == MM2_ESSENTIAL ||
        statement->kind == MM2_AXIOM || statement->kind == MM2_THEOREM) {
        if (!label_valid(&statement->label))
            return error_at(error, MM2_REJECTED, &statement->label,
                            "invalid statement label");
        if (!intern_name(model, &statement->label, label))
            return allocation_error(error, &statement->label);
    }
    return MM2_OK;

allocation_failure:
    return allocation_error(error, &statement->site);
}

/* Tagging is a separate pass, before the declaration gate, just as in
 * applyStatement. An undeclared later token must not be hidden by an earlier
 * variable lacking its floating hypothesis. */
static mm2_status prepare_formula(mm2_model *model,
                                  const mm2_statement *statement,
                                  mm2_formula *formula, mm2_error *error) {
    size_t count = statement->symbol_count - 1;
    mm2_symbol *body = NULL;
    if (count) {
        if (count > SIZE_MAX / sizeof(*body))
            return allocation_error(error, &statement->site);
        body = malloc(count * sizeof(*body));
        if (!body) return allocation_error(error, &statement->site);
    }
    for (size_t i = 0; i < count; ++i) {
        mm2_id id = model->statement_names[i + 1];
        const name_entry *entry = &model->names[id];
        mm2_symbol_kind kind;
        if (entry->kind == NAME_VARIABLE && entry->active)
            kind = MM2_MATH_VARIABLE;
        else if (entry->kind == NAME_CONSTANT)
            kind = MM2_MATH_CONSTANT;
        else {
            free(body);
            return error_at(error, MM2_REJECTED, &statement->symbols[i + 1],
                            "undeclared or inactive formula symbol");
        }
        body[i] = (mm2_symbol){kind, id};
    }
    *formula = (mm2_formula){model->statement_names[0], body, count};
    return MM2_OK;
}

static bool formula_admissible(const mm2_model *model,
                               const mm2_formula *formula) {
    if (model->names[formula->typecode].kind != NAME_CONSTANT) return false;
    for (size_t i = 0; i < formula->body_count; ++i)
        if (formula->body[i].kind == MM2_MATH_VARIABLE &&
            !model->names[formula->body[i].name].floating) return false;
    return true;
}

static bool append_mandatory(mm2_model *model, mm2_id id, mm2_id **names,
                              size_t *count, size_t *capacity) {
    if (model->names[id].mandatory_mark == model->mandatory_epoch) return true;
    if (*count == SIZE_MAX) return false;
    RESERVE(*names, *capacity, *count + 1);
    (*names)[(*count)++] = id;
    model->names[id].mandatory_mark = model->mandatory_epoch;
    return true;

allocation_failure:
    return false;
}

static bool formula_mandatory(mm2_model *model, const mm2_formula *formula,
                              mm2_id **names, size_t *count, size_t *capacity) {
    for (size_t i = 0; i < formula->body_count; ++i)
        if (formula->body[i].kind == MM2_MATH_VARIABLE &&
            !append_mandatory(model, formula->body[i].name,
                               names, count, capacity)) return false;
    return true;
}

static bool prepare_assertion(mm2_model *model, mm2_assertion *assertion) {
    if (++model->mandatory_epoch == 0) {
        for (size_t i = 0; i < model->name_count; ++i)
            model->names[i].mandatory_mark = 0;
        model->mandatory_epoch = 1;
    }
    mm2_id *mandatory = NULL;
    size_t count = 0, capacity = 0;
    bool ok = formula_mandatory(model, &assertion->formula,
                                &mandatory, &count, &capacity);
    for (size_t i = 0; ok && i < model->active_hypothesis_count; ++i) {
        const mm2_hypothesis *hypothesis = model->active_hypotheses[i];
        if (hypothesis->kind == MM2_HYP_ESSENTIAL)
            ok = formula_mandatory(model, &hypothesis->formula,
                                    &mandatory, &count, &capacity);
    }
    assertion->mandatory_names = mandatory;
    assertion->mandatory_name_count = count;
    if (!ok) return false;

    size_t hyp_count = 0, dv_count = 0;
    for (size_t i = 0; i < model->active_hypothesis_count; ++i) {
        const mm2_hypothesis *hypothesis = model->active_hypotheses[i];
        if (hypothesis->kind == MM2_HYP_ESSENTIAL ||
            model->names[hypothesis->variable].mandatory_mark ==
              model->mandatory_epoch) ++hyp_count;
    }
    if (hyp_count > SIZE_MAX / sizeof(*assertion->hypotheses)) return false;
    const mm2_hypothesis **hypotheses = hyp_count ?
        malloc(hyp_count * sizeof(*hypotheses)) : NULL;
    if (hyp_count && !hypotheses) return false;
    assertion->hypotheses = hypotheses;
    assertion->hypothesis_count = hyp_count;
    for (size_t i = 0, next = 0; i < model->active_hypothesis_count; ++i) {
        const mm2_hypothesis *hypothesis = model->active_hypotheses[i];
        if (hypothesis->kind == MM2_HYP_ESSENTIAL ||
            model->names[hypothesis->variable].mandatory_mark ==
              model->mandatory_epoch) hypotheses[next++] = hypothesis;
    }
    for (size_t i = 0; i < model->distinct_count; ++i) {
        mm2_pair pair = model->distinct[i];
        if (model->names[pair.left].mandatory_mark == model->mandatory_epoch &&
            model->names[pair.right].mandatory_mark == model->mandatory_epoch)
            ++dv_count;
    }
    if (dv_count > SIZE_MAX / sizeof(*assertion->dv)) return false;
    mm2_pair *dv = dv_count ? malloc(dv_count * sizeof(*dv)) : NULL;
    if (dv_count && !dv) return false;
    assertion->dv = dv;
    assertion->dv_count = dv_count;
    for (size_t i = 0, next = 0; i < model->distinct_count; ++i) {
        mm2_pair pair = model->distinct[i];
        if (model->names[pair.left].mandatory_mark == model->mandatory_epoch &&
            model->names[pair.right].mandatory_mark == model->mandatory_epoch)
            dv[next++] = pair;
    }
    return true;
}

static mm2_status apply_statement(mm2_model *model,
                                   const mm2_statement *statement,
                                   mm2_prepare_event *event, mm2_error *error) {
    const mm2_token *site = &statement->site;
    mm2_id label;
    mm2_status status = prepare_names(model, statement, &label, error);
    if (status != MM2_OK) return status;
    size_t count = statement->symbol_count;
    event->names = model->statement_names;
    event->name_count = count;

    switch (statement->kind) {
    case MM2_SCOPE_OPEN:
        if (model->scope_count == SIZE_MAX) goto allocation_failure;
        RESERVE(model->scopes, model->scope_capacity, model->scope_count + 1);
        model->scopes[model->scope_count++] = (scope_boundary){
            model->active_variable_count, model->active_hypothesis_count,
            model->distinct_count, *site
        };
        return MM2_OK;
    case MM2_SCOPE_CLOSE: {
        if (!model->scope_count)
            return error_at(error, MM2_REJECTED, site,
                            "scope close without an open scope");
        scope_boundary boundary = model->scopes[--model->scope_count];
        for (size_t i = boundary.hypotheses;
             i < model->active_hypothesis_count; ++i) {
            const mm2_hypothesis *hypothesis = model->active_hypotheses[i];
            if (hypothesis->kind == MM2_HYP_FLOATING)
                model->names[hypothesis->variable].floating = false;
        }
        for (size_t i = boundary.variables;
             i < model->active_variable_count; ++i)
            model->names[model->active_variables[i]].active = false;
        model->active_variable_count = boundary.variables;
        model->active_hypothesis_count = boundary.hypotheses;
        model->distinct_count = boundary.distinct;
        return MM2_OK;
    }
    case MM2_CONST:
        if (!count || model->scope_count)
            return error_at(error, MM2_REJECTED, site,
                            "constant declaration is empty or scoped");
        if (!distinct_batch(model, count))
            return error_at(error, MM2_REJECTED, site,
                            "duplicate symbol in constant declaration");
        for (size_t i = 0; i < count; ++i)
            if (model->names[model->statement_names[i]].kind != NAME_UNDECLARED)
                return error_at(error, MM2_REJECTED, site,
                                "constant name is already occupied");
        if (count > SIZE_MAX - model->constant_count) goto allocation_failure;
        RESERVE(model->constants, model->constant_capacity,
                model->constant_count + count);
        for (size_t i = 0; i < count; ++i) {
            mm2_id id = model->statement_names[i];
            model->names[id].kind = NAME_CONSTANT;
            model->constants[model->constant_count++] = id;
        }
        return MM2_OK;
    case MM2_VAR: {
        if (!count || !distinct_batch(model, count))
            return error_at(error, MM2_REJECTED, site,
                            "variable declaration is empty or repeated");
        size_t new_count = 0;
        for (size_t i = 0; i < count; ++i) {
            const name_entry *entry = &model->names[model->statement_names[i]];
            if (entry->active || (entry->kind != NAME_UNDECLARED &&
                                   entry->kind != NAME_VARIABLE))
                return error_at(error, MM2_REJECTED, site,
                                "variable is active or its name is occupied");
            if (entry->kind == NAME_UNDECLARED) ++new_count;
        }
        if (new_count > SIZE_MAX - model->variable_count ||
            count > SIZE_MAX - model->active_variable_count)
            goto allocation_failure;
        if (new_count)
            RESERVE(model->variables, model->variable_capacity,
                    model->variable_count + new_count);
        RESERVE(model->active_variables, model->active_variable_capacity,
                model->active_variable_count + count);
        for (size_t i = 0; i < count; ++i) {
            mm2_id id = model->statement_names[i];
            if (model->names[id].kind == NAME_UNDECLARED)
                model->variables[model->variable_count++] = id;
            model->names[id].kind = NAME_VARIABLE;
            model->names[id].active = true;
            model->active_variables[model->active_variable_count++] = id;
        }
        return MM2_OK;
    }
    case MM2_DV: {
        if (count < 2 || !distinct_batch(model, count))
            return error_at(error, MM2_REJECTED, site,
                            "disjoint declaration needs distinct variables");
        for (size_t i = 0; i < count; ++i) {
            const name_entry *entry = &model->names[model->statement_names[i]];
            if (entry->kind != NAME_VARIABLE || !entry->active)
                return error_at(error, MM2_REJECTED, site,
                                "disjoint declaration uses an inactive variable");
        }
        size_t left = count, right = count - 1;
        if (left % 2 == 0) left /= 2;
        else right /= 2;
        if (left > SIZE_MAX / right) goto allocation_failure;
        size_t added = left * right, start = model->distinct_count;
        if (added > SIZE_MAX - start) goto allocation_failure;
        RESERVE(model->distinct, model->distinct_capacity, start + added);
        for (size_t j = 1; j < count; ++j)
            for (size_t i = 0; i < j; ++i) {
                mm2_id a = model->statement_names[i];
                mm2_id b = model->statement_names[j];
                if (strcmp(model->names[a].text, model->names[b].text) > 0) {
                    mm2_id swap = a;
                    a = b;
                    b = swap;
                }
                model->distinct[model->distinct_count++] = (mm2_pair){a, b};
            }
        event->added_dv = model->distinct + start;
        event->added_dv_count = added;
        return MM2_OK;
    }
    case MM2_FLOAT: {
        /* The zar reader checks floating uniqueness in the active frame.
         * Old hypothesis objects keep their own types in stored assertions;
         * they do not impose a permanent type on the variable's name. */
        if (count != 2)
            return error_at(error, MM2_REJECTED, site,
                            "floating hypothesis needs a typecode and variable");
        mm2_id typecode = model->statement_names[0];
        mm2_id variable = model->statement_names[1];
        const name_entry *entry = &model->names[variable];
        if (model->names[label].kind != NAME_UNDECLARED ||
            model->names[typecode].kind != NAME_CONSTANT ||
            entry->kind != NAME_VARIABLE || !entry->active || entry->floating)
            return error_at(error, MM2_REJECTED, site,
                            "floating hypothesis violates label, type, or scope");
        if (model->hypothesis_count == SIZE_MAX ||
            model->active_hypothesis_count == SIZE_MAX) goto allocation_failure;
        RESERVE(model->hypotheses, model->hypothesis_capacity,
                model->hypothesis_count + 1);
        RESERVE(model->active_hypotheses, model->active_hypothesis_capacity,
                model->active_hypothesis_count + 1);
        mm2_hypothesis *hypothesis = calloc(1, sizeof(*hypothesis));
        if (!hypothesis) goto allocation_failure;
        model->hypotheses[model->hypothesis_count++] = hypothesis;
        mm2_symbol *body = malloc(sizeof(*body));
        if (!body) goto allocation_failure;
        *body = (mm2_symbol){MM2_MATH_VARIABLE, variable};
        *hypothesis = (mm2_hypothesis){
            MM2_HYP_FLOATING, label, {typecode, body, 1}, variable
        };
        model->names[label].kind = NAME_LABEL;
        model->names[variable].floating = true;
        model->active_hypotheses[model->active_hypothesis_count++] = hypothesis;
        event->hypothesis = hypothesis;
        return MM2_OK;
    }
    case MM2_ESSENTIAL:
    case MM2_AXIOM:
    case MM2_THEOREM: {
        if (!count)
            return error_at(error, MM2_REJECTED, site,
                            "formula has no typecode");
        mm2_formula formula;
        status = prepare_formula(model, statement, &formula, error);
        if (status != MM2_OK) return status;
        if (model->names[label].kind != NAME_UNDECLARED ||
            !formula_admissible(model, &formula)) {
            free((void *)formula.body);
            return error_at(error, MM2_REJECTED, site,
                            "formula violates label, type, or floating frame");
        }
        if (statement->kind == MM2_ESSENTIAL) {
            if (model->hypothesis_count == SIZE_MAX ||
                model->active_hypothesis_count == SIZE_MAX) {
                free((void *)formula.body);
                goto allocation_failure;
            }
            mm2_hypothesis *hypothesis = calloc(1, sizeof(*hypothesis));
            if (!hypothesis) {
                free((void *)formula.body);
                goto allocation_failure;
            }
            *hypothesis = (mm2_hypothesis){
                MM2_HYP_ESSENTIAL, label, formula, MM2_NO_ID
            };
            void *grown = reserve_array(model->hypotheses,
                &model->hypothesis_capacity, model->hypothesis_count + 1,
                sizeof(*model->hypotheses));
            if (!grown) {
                free((void *)formula.body);
                free(hypothesis);
                goto allocation_failure;
            }
            model->hypotheses = grown;
            model->hypotheses[model->hypothesis_count++] = hypothesis;
            RESERVE(model->active_hypotheses, model->active_hypothesis_capacity,
                    model->active_hypothesis_count + 1);
            model->active_hypotheses[model->active_hypothesis_count++] = hypothesis;
            event->hypothesis = hypothesis;
        } else {
            if (model->assertion_count == SIZE_MAX) {
                free((void *)formula.body);
                goto allocation_failure;
            }
            mm2_assertion *assertion = calloc(1, sizeof(*assertion));
            if (!assertion) {
                free((void *)formula.body);
                goto allocation_failure;
            }
            *assertion = (mm2_assertion){
                .index = model->assertion_count, .label = label,
                .is_theorem = statement->kind == MM2_THEOREM, .formula = formula
            };
            void *grown = reserve_array(model->assertions,
                &model->assertion_capacity, model->assertion_count + 1,
                sizeof(*model->assertions));
            if (!grown) {
                free((void *)formula.body);
                free(assertion);
                goto allocation_failure;
            }
            model->assertions = grown;
            model->assertions[model->assertion_count++] = assertion;
            if (!prepare_assertion(model, assertion)) goto allocation_failure;
            event->assertion = assertion;
        }
        model->names[label].kind = NAME_LABEL;
        return MM2_OK;
    }
    default:
        return error_at(error, MM2_ERROR, site, "invalid statement kind");
    }

allocation_failure:
    return allocation_error(error, site);
}

mm2_status mm2_prepare(const mm2_source *source, mm2_prepare_callback callback,
                       void *userdata, mm2_error *error) {
    mm2_error_clear(error);
    if (!source || (source->statement_count && !source->statements))
        return error_at(error, MM2_ERROR, NULL, "missing source statement array");
    mm2_model model = {0};
    mm2_status status = MM2_OK;
    mm2_prepare_event event = {
        .kind = MM2_PREPARE_BEGIN, .source = source,
        .before = view(&model, lengths(&model)),
        .after = view(&model, lengths(&model))
    };
    if (callback) status = callback(&event, userdata, error);
    for (size_t i = 0; status == MM2_OK && i < source->statement_count; ++i) {
        const mm2_statement *statement = &source->statements[i];
        state_lengths before = lengths(&model);
        event = (mm2_prepare_event){
            .kind = MM2_PREPARE_STATEMENT, .source = source,
            .statement = statement, .statement_index = i
        };
        status = apply_statement(&model, statement, &event, error);
        if (status != MM2_OK) break;
        event.before = view(&model, before);
        event.after = view(&model, lengths(&model));
        if (callback) status = callback(&event, userdata, error);
    }
    if (status == MM2_OK && model.scope_count)
        status = error_at(error, MM2_REJECTED,
                          &model.scopes[model.scope_count - 1].site,
                          "unclosed scope at end of source");
    if (status == MM2_OK && callback) {
        event = (mm2_prepare_event){
            .kind = MM2_PREPARE_END, .source = source,
            .statement_index = source->statement_count,
            .before = view(&model, lengths(&model)),
            .after = view(&model, lengths(&model))
        };
        status = callback(&event, userdata, error);
    }
    free_model(&model);
    return status;
}

#undef RESERVE
