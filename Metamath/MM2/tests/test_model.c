#include "../frontend/model.h"

#include <assert.h>
#include <stdio.h>
#include <string.h>

/* Standalone error plumbing only: the integrated frontend supplies these
 * functions from reader.c. No parser or model behavior is replaced here. */
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

typedef struct {
    mm2_source source;
    mm2_statement statements[256];
    mm2_token symbols[4096];
    size_t symbol_count, offset;
} fixture;

static mm2_token tok(fixture *fixture, const char *text) {
    mm2_token token = {
        .bytes = (uint8_t *)text, .len = strlen(text), .source_id = 0,
        .start = fixture->offset, .end = fixture->offset + strlen(text)
    };
    fixture->offset = token.end + 1;
    return token;
}

static mm2_statement *stmt(fixture *fixture, mm2_statement_kind kind,
                           const char *label, const char *const *symbols,
                           size_t count) {
    static const char *const keywords[] = {
        "$c", "$v", "${", "$}", "$f", "$e", "$d", "$a", "$p"
    };
    assert(fixture->source.statement_count < 256);
    assert(count <= 4096 - fixture->symbol_count);
    fixture->source.statements = fixture->statements;
    mm2_statement *statement =
        &fixture->statements[fixture->source.statement_count++];
    memset(statement, 0, sizeof(*statement));
    statement->kind = kind;
    statement->start = fixture->offset;
    if (label) statement->label = tok(fixture, label);
    statement->site = tok(fixture, keywords[kind]);
    statement->symbols = fixture->symbols + fixture->symbol_count;
    statement->symbol_count = count;
    for (size_t i = 0; i < count; ++i)
        fixture->symbols[fixture->symbol_count++] = tok(fixture, symbols[i]);
    if (kind != MM2_SCOPE_OPEN && kind != MM2_SCOPE_CLOSE)
        statement->terminator = tok(fixture, "$.");
    statement->end = fixture->offset - 1;
    return statement;
}

#define STMT(fixture, kind, label, ...) \
    stmt((fixture), (kind), (label), (const char *const[]){__VA_ARGS__}, \
         sizeof((const char *const[]){__VA_ARGS__}) / sizeof(const char *))

static void initial(fixture *fixture) {
    STMT(fixture, MM2_CONST, NULL, "wff", "|-", "class");
    STMT(fixture, MM2_VAR, NULL, "ph");
    STMT(fixture, MM2_FLOAT, "wph", "wff", "ph");
}

static void expect_id(const mm2_model *model, mm2_id id, const char *name) {
    assert(strcmp(mm2_model_name(model, id), name) == 0);
    assert(mm2_model_name_length(model, id) == strlen(name));
}

static void expect_hypotheses(const mm2_model *model,
                              const mm2_hypothesis *const *hypotheses,
                              size_t count, const char *const *names,
                              size_t expected_count) {
    assert(count == expected_count);
    for (size_t i = 0; i < count; ++i)
        expect_id(model, hypotheses[i]->label, names[i]);
}

static unsigned callback_count;

static mm2_status empty_event(const mm2_prepare_event *event, void *unused,
                               mm2_error *error) {
    (void)unused;
    (void)error;
    assert(event->kind == (callback_count ? MM2_PREPARE_END : MM2_PREPARE_BEGIN));
    assert(event->before.active_hypothesis_count == 0);
    assert(event->after.assertion_count == 0);
    assert(event->statement == NULL);
    assert(event->statement_index == 0);
    ++callback_count;
    return MM2_OK;
}

static void empty_test(void) {
    fixture fixture = {0};
    mm2_error error;
    callback_count = 0;
    assert(mm2_prepare(&fixture.source, empty_event, NULL, &error) == MM2_OK);
    assert(callback_count == 2);
}

static mm2_status mandatory_event(const mm2_prepare_event *event, void *unused,
                                   mm2_error *error) {
    (void)unused;
    (void)error;
    const mm2_model *model = event->before.model;
    if (event->kind != MM2_PREPARE_STATEMENT) return MM2_OK;
    if (event->statement->kind == MM2_DV) {
        if (event->name_count == 2) {
            assert(event->added_dv_count == 1);
            expect_id(model, event->added_dv[0].left, "ph");
            expect_id(model, event->added_dv[0].right, "z");
            return MM2_OK;
        }
        const char *const left[] = {"ph", "ch", "ch"};
        const char *const right[] = {"ps", "ps", "ph"};
        assert(event->added_dv_count == 3);
        assert(event->after.active_dv_count == event->before.active_dv_count + 3);
        for (size_t i = 0; i < 3; ++i) {
            expect_id(model, event->added_dv[i].left, left[i]);
            expect_id(model, event->added_dv[i].right, right[i]);
        }
    }
    if (!event->assertion) return MM2_OK;
    const mm2_assertion *assertion = event->assertion;
    const char *const mandatory[] = {"ps", "ph", "ch"};
    const char *const hypotheses[] = {"wph", "wps", "wch", "h1"};
    const char *const active[] = {"wph", "wps", "wch", "wz", "h1"};
    assert(assertion->mandatory_name_count == 3);
    for (size_t i = 0; i < 3; ++i)
        expect_id(model, assertion->mandatory_names[i], mandatory[i]);
    expect_hypotheses(model, assertion->hypotheses, assertion->hypothesis_count,
                      hypotheses, 4);
    expect_hypotheses(model, event->before.active_hypotheses,
                      event->before.active_hypothesis_count, active, 5);
    assert(assertion->dv_count == 6);
    for (size_t i = 0; i < 3; ++i) {
        assert(assertion->dv[i].left == assertion->dv[i + 3].left);
        assert(assertion->dv[i].right == assertion->dv[i + 3].right);
    }
    assert(event->after.assertion_count == event->before.assertion_count + 1);
    assert(assertion->index == event->before.assertion_count);
    assert(event->before.active_hypothesis_count ==
           event->after.active_hypothesis_count);
    assert(event->before.active_dv_count == event->after.active_dv_count);
    if (assertion->is_theorem) {
        expect_id(model, assertion->label, "th");
        assert(event->before.assertion_count == 1);
        expect_id(model, event->before.assertions[0]->label, "a1");
        assert(event->after.assertions[1] == assertion);
        assert(event->statement->proof_label_count == 3);
        assert(strcmp((char *)event->statement->proof_labels[0].bytes, "th") == 0);
        assert(strcmp((char *)event->statement->proof_labels[1].bytes, "missing") == 0);
        assert(strcmp((char *)event->statement->proof_labels[2].bytes, "?") == 0);
    } else {
        expect_id(model, assertion->label, "a1");
        assert(event->before.assertion_count == 0);
    }
    ++callback_count;
    return MM2_OK;
}

static void mandatory_test(void) {
    fixture fixture = {0};
    STMT(&fixture, MM2_CONST, NULL, "wff", "|-");
    STMT(&fixture, MM2_VAR, NULL, "ph", "ps", "ch", "z");
    STMT(&fixture, MM2_FLOAT, "wph", "wff", "ph");
    STMT(&fixture, MM2_FLOAT, "wps", "wff", "ps");
    STMT(&fixture, MM2_FLOAT, "wch", "wff", "ch");
    STMT(&fixture, MM2_FLOAT, "wz", "wff", "z");
    STMT(&fixture, MM2_DV, NULL, "ps", "ph", "ch");
    STMT(&fixture, MM2_DV, NULL, "ps", "ph", "ch");
    STMT(&fixture, MM2_DV, NULL, "ph", "z");
    STMT(&fixture, MM2_ESSENTIAL, "h1", "wff", "ch", "ph");
    STMT(&fixture, MM2_AXIOM, "a1", "|-", "ps", "ph", "ps");
    mm2_statement *theorem = STMT(&fixture, MM2_THEOREM, "th", "|-", "ps", "ph", "ps");
    mm2_token proof[] = {tok(&fixture, "th"), tok(&fixture, "missing"), tok(&fixture, "?")};
    theorem->proof_kind = MM2_PROOF_NORMAL;
    theorem->proof_labels = proof;
    theorem->proof_label_count = 3;
    mm2_token original[3];
    memcpy(original, proof, sizeof(proof));
    mm2_error error;
    callback_count = 0;
    assert(mm2_prepare(&fixture.source, mandatory_event, NULL, &error) == MM2_OK);
    assert(callback_count == 2);
    assert(memcmp(original, proof, sizeof(proof)) == 0);
}

static mm2_status scope_event(const mm2_prepare_event *event, void *unused,
                               mm2_error *error) {
    (void)unused;
    (void)error;
    if (event->kind != MM2_PREPARE_STATEMENT) return MM2_OK;
    const mm2_model *model = event->before.model;
    if (event->statement->kind == MM2_SCOPE_CLOSE) {
        const char *const before[] = {"wph", "wps", "hps"};
        const char *const after[] = {"wph"};
        expect_hypotheses(model, event->before.active_hypotheses,
                          event->before.active_hypothesis_count, before, 3);
        expect_hypotheses(model, event->after.active_hypotheses,
                          event->after.active_hypothesis_count, after, 1);
        assert(event->before.scope_depth == 1 && event->after.scope_depth == 0);
        assert(event->before.active_variable_count == 2);
        assert(event->after.active_variable_count == 1);
        assert(event->before.active_dv_count == 1);
        assert(event->after.active_dv_count == 0);
        assert(event->after.declared_variable_count == 2);
        assert(event->after.assertion_count == 1);
        ++callback_count;
    }
    if (event->assertion && event->assertion->is_theorem) {
        const char *const scoped[] = {"wph", "wps", "hps"};
        const mm2_assertion *prior = event->before.assertions[0];
        expect_id(model, prior->label, "scoped");
        expect_hypotheses(model, prior->hypotheses, prior->hypothesis_count,
                          scoped, 3);
        assert(prior->dv_count == 1);
        assert(event->assertion->mandatory_name_count == 1);
        expect_id(model, event->assertion->mandatory_names[0], "ph");
        assert(event->assertion->hypothesis_count == 1);
        assert(event->assertion->dv_count == 0);
        ++callback_count;
    }
    return MM2_OK;
}

static void scope_test(void) {
    fixture fixture = {0};
    initial(&fixture);
    stmt(&fixture, MM2_SCOPE_OPEN, NULL, NULL, 0);
    STMT(&fixture, MM2_VAR, NULL, "ps");
    STMT(&fixture, MM2_FLOAT, "wps", "wff", "ps");
    STMT(&fixture, MM2_DV, NULL, "ps", "ph");
    STMT(&fixture, MM2_ESSENTIAL, "hps", "wff", "ps");
    STMT(&fixture, MM2_AXIOM, "scoped", "|-", "ph");
    stmt(&fixture, MM2_SCOPE_CLOSE, NULL, NULL, 0);
    mm2_statement *theorem = STMT(&fixture, MM2_THEOREM, "after", "|-", "ph");
    mm2_token header[] = {tok(&fixture, "scoped"), tok(&fixture, "unknown")};
    mm2_token words[] = {tok(&fixture, "AZ?")};
    theorem->proof_kind = MM2_PROOF_COMPRESSED;
    theorem->proof_labels = header;
    theorem->proof_label_count = 2;
    theorem->compressed_words = words;
    theorem->compressed_word_count = 1;
    mm2_error error;
    callback_count = 0;
    assert(mm2_prepare(&fixture.source, scope_event, NULL, &error) == MM2_OK);
    assert(callback_count == 2);
    assert(strcmp((char *)words[0].bytes, "AZ?") == 0);
}

static mm2_status untyped_dv_event(const mm2_prepare_event *event, void *unused,
                                    mm2_error *error) {
    (void)unused;
    (void)error;
    if (!event->assertion) return MM2_OK;
    assert(event->before.active_dv_count == 1);
    assert(event->assertion->dv_count == 0);
    assert(event->assertion->mandatory_name_count == 1);
    assert(event->assertion->hypothesis_count == 1);
    expect_id(event->before.model, event->assertion->mandatory_names[0], "ph");
    ++callback_count;
    return MM2_OK;
}

static void untyped_dv_test(void) {
    fixture fixture = {0};
    STMT(&fixture, MM2_CONST, NULL, "wff", "|-");
    STMT(&fixture, MM2_VAR, NULL, "ph", "x");
    STMT(&fixture, MM2_DV, NULL, "ph", "x");
    STMT(&fixture, MM2_FLOAT, "wph", "wff", "ph");
    STMT(&fixture, MM2_AXIOM, "without-x", "|-", "ph");
    STMT(&fixture, MM2_FLOAT, "wx", "wff", "x");
    STMT(&fixture, MM2_AXIOM, "optional-x", "|-", "ph");
    mm2_error error;
    callback_count = 0;
    assert(mm2_prepare(&fixture.source, untyped_dv_event, NULL, &error) == MM2_OK);
    assert(callback_count == 2);
}

static mm2_status reactivation_event(const mm2_prepare_event *event,
                                      void *second_type, mm2_error *error) {
    (void)error;
    if (!event->assertion) return MM2_OK;
    const mm2_model *model = event->before.model;
    const mm2_assertion *assertion = event->assertion;
    assert(assertion->hypothesis_count == 1);
    if (assertion->index == 0) {
        expect_id(model, assertion->formula.typecode, "wff");
        expect_id(model, assertion->hypotheses[0]->formula.typecode, "wff");
    } else {
        assert(assertion->index == 1);
        expect_id(model, assertion->formula.typecode, second_type);
        expect_id(model, assertion->hypotheses[0]->formula.typecode, second_type);
        const mm2_assertion *prior = event->before.assertions[0];
        expect_id(model, prior->formula.typecode, "wff");
        expect_id(model, prior->hypotheses[0]->formula.typecode, "wff");
        expect_id(model, prior->hypotheses[0]->label, "wx");
    }
    ++callback_count;
    return MM2_OK;
}

static void reactivation_test(void) {
    /* Both a globally active variable and a reactivated scoped variable may
     * have a new floating type after the earlier hypothesis leaves scope.
     * Stored assertion frames retain the old hypothesis's exact type. */
    const char *const second_types[] = {"wff", "class"};
    for (size_t scoped = 0; scoped < 2; ++scoped)
        for (size_t type = 0; type < 2; ++type) {
            fixture fixture = {0};
            initial(&fixture);
            if (!scoped) STMT(&fixture, MM2_VAR, NULL, "x");
            stmt(&fixture, MM2_SCOPE_OPEN, NULL, NULL, 0);
            if (scoped) STMT(&fixture, MM2_VAR, NULL, "x");
            STMT(&fixture, MM2_FLOAT, "wx", "wff", "x");
            STMT(&fixture, MM2_AXIOM, "first", "wff", "x");
            stmt(&fixture, MM2_SCOPE_CLOSE, NULL, NULL, 0);
            stmt(&fixture, MM2_SCOPE_OPEN, NULL, NULL, 0);
            if (scoped) STMT(&fixture, MM2_VAR, NULL, "x");
            STMT(&fixture, MM2_FLOAT, "wx-again", second_types[type], "x");
            STMT(&fixture, MM2_AXIOM, "second", second_types[type], "x");
            stmt(&fixture, MM2_SCOPE_CLOSE, NULL, NULL, 0);
            mm2_error error;
            callback_count = 0;
            assert(mm2_prepare(&fixture.source, reactivation_event,
                                (void *)second_types[type], &error) == MM2_OK);
            assert(callback_count == 2);
        }
}

static void expect_rejected(fixture *fixture, const mm2_token *site) {
    mm2_error error;
    assert(mm2_prepare(&fixture->source, NULL, NULL, &error) == MM2_REJECTED);
    assert(error.status == MM2_REJECTED);
    assert(error.source_id == site->source_id);
    assert(error.start == site->start && error.end == site->end);
}

static void rejection_tests(void) {
    fixture fixture;
    mm2_statement *bad;
#define RESET() do { memset(&fixture, 0, sizeof(fixture)); initial(&fixture); } while (0)
#define REJECT(kind, label, ...) do { \
    RESET(); bad = STMT(&fixture, kind, label, __VA_ARGS__); \
    expect_rejected(&fixture, &bad->site); \
} while (0)
    REJECT(MM2_CONST, NULL, "new", "new");
    REJECT(MM2_CONST, NULL, "ph");
    REJECT(MM2_CONST, NULL, "wph");
    REJECT(MM2_VAR, NULL, "ph");
    REJECT(MM2_VAR, NULL, "new", "new");
    REJECT(MM2_VAR, NULL, "wff");
    REJECT(MM2_DV, NULL, "ph");
    REJECT(MM2_DV, NULL, "ph", "ph");
    REJECT(MM2_DV, NULL, "ph", "unknown");
    REJECT(MM2_FLOAT, "new", "wff", "unknown");
    REJECT(MM2_FLOAT, "new", "unknown", "ph");
    REJECT(MM2_FLOAT, "new", "wff", "ph");
    REJECT(MM2_FLOAT, "new", "class", "ph");
    REJECT(MM2_FLOAT, "wph", "wff", "ph");
    REJECT(MM2_ESSENTIAL, "wph", "wff", "ph");
    REJECT(MM2_ESSENTIAL, "ph", "wff", "ph");
    REJECT(MM2_AXIOM, "wff", "|-", "ph");
    REJECT(MM2_AXIOM, "new", "ph", "ph");
    RESET();
    bad = stmt(&fixture, MM2_CONST, NULL, NULL, 0);
    expect_rejected(&fixture, &bad->site);
    RESET();
    bad = stmt(&fixture, MM2_VAR, NULL, NULL, 0);
    expect_rejected(&fixture, &bad->site);
    RESET();
    stmt(&fixture, MM2_SCOPE_OPEN, NULL, NULL, 0);
    bad = STMT(&fixture, MM2_CONST, NULL, "new");
    expect_rejected(&fixture, &bad->site);
    RESET();
    bad = stmt(&fixture, MM2_SCOPE_CLOSE, NULL, NULL, 0);
    expect_rejected(&fixture, &bad->site);
    RESET();
    bad = stmt(&fixture, MM2_SCOPE_OPEN, NULL, NULL, 0);
    expect_rejected(&fixture, &bad->site);
    RESET();
    STMT(&fixture, MM2_VAR, NULL, "x");
    bad = STMT(&fixture, MM2_ESSENTIAL, "new", "wff", "x");
    expect_rejected(&fixture, &bad->site);
    RESET();
    STMT(&fixture, MM2_VAR, NULL, "x");
    bad = STMT(&fixture, MM2_AXIOM, "wph", "unknown", "x", "absent");
    expect_rejected(&fixture, &bad->symbols[2]);
    RESET();
    stmt(&fixture, MM2_SCOPE_OPEN, NULL, NULL, 0);
    STMT(&fixture, MM2_VAR, NULL, "x");
    STMT(&fixture, MM2_FLOAT, "wx", "wff", "x");
    stmt(&fixture, MM2_SCOPE_CLOSE, NULL, NULL, 0);
    bad = STMT(&fixture, MM2_AXIOM, "new", "|-", "x");
    expect_rejected(&fixture, &bad->symbols[1]);
    RESET();
    stmt(&fixture, MM2_SCOPE_OPEN, NULL, NULL, 0);
    STMT(&fixture, MM2_ESSENTIAL, "old", "wff", "ph");
    stmt(&fixture, MM2_SCOPE_CLOSE, NULL, NULL, 0);
    bad = STMT(&fixture, MM2_AXIOM, "old", "|-", "ph");
    expect_rejected(&fixture, &bad->site);
#undef REJECT
#undef RESET
}

static mm2_status growth_event(const mm2_prepare_event *event, void *unused,
                                mm2_error *error) {
    (void)unused;
    (void)error;
    if (!event->assertion) return MM2_OK;
    const mm2_model *model = event->before.model;
    assert(event->assertion->index == callback_count);
    assert(event->before.assertion_count == callback_count);
    assert(event->after.assertion_count == callback_count + 1);
    for (size_t i = 0; i < event->before.assertion_count; ++i) {
        char label[32];
        (void)snprintf(label, sizeof(label), "a%zu", i);
        expect_id(model, event->before.assertions[i]->label, label);
        assert(event->before.assertions[i]->index == i);
    }
    ++callback_count;
    return MM2_OK;
}

static void growth_test(void) {
    fixture fixture = {0};
    initial(&fixture);
    char labels[100][32];
    for (size_t i = 0; i < 100; ++i) {
        (void)snprintf(labels[i], sizeof(labels[i]), "a%zu", i);
        STMT(&fixture, MM2_AXIOM, labels[i], "|-", "ph");
    }
    mm2_error error;
    callback_count = 0;
    assert(mm2_prepare(&fixture.source, growth_event, NULL, &error) == MM2_OK);
    assert(callback_count == 100);
}

static mm2_status abort_event(const mm2_prepare_event *event, void *unused,
                               mm2_error *error) {
    (void)unused;
    if (!event->assertion) return MM2_OK;
    ++callback_count;
    mm2_error_set(error, MM2_ERROR, event->statement->source_id,
                   event->statement->start, event->statement->end,
                   "test callback failure");
    return MM2_ERROR;
}

static void callback_abort_test(void) {
    fixture fixture = {0};
    initial(&fixture);
    mm2_statement *assertion = STMT(&fixture, MM2_AXIOM, "a", "|-", "ph");
    STMT(&fixture, MM2_AXIOM, "not-reached", "|-", "ph");
    mm2_error error;
    callback_count = 0;
    assert(mm2_prepare(&fixture.source, abort_event, NULL, &error) == MM2_ERROR);
    assert(callback_count == 1);
    assert(error.start == assertion->start && error.end == assertion->end);
    assert(strcmp(error.message, "test callback failure") == 0);
}

int main(void) {
    empty_test();
    mandatory_test();
    scope_test();
    untyped_dv_test();
    reactivation_test();
    rejection_tests();
    growth_test();
    callback_abort_test();
    puts("model regression checks passed");
    return 0;
}
