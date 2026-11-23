#define _GNU_SOURCE
#include "finite_horn_ground_term_v1.h"
#include "parser_pack_abi_stream_v1.h"
#include "parser_pack_gll_v1.h"
#include "native_sha256.h"
#include "symbol.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "source_plan_identity.h"

#ifdef GSLT_SOURCE_SELECTION
#include "source_family_selection.h"
#endif

static bool read_bytes(const char *path, uint8_t **bytes, size_t *length) {
    FILE *stream = fopen(path, "rb");
    long end;
    *bytes = NULL;
    *length = 0;
    if (!stream) return false;
    if (fseek(stream, 0, SEEK_END) != 0 || (end = ftell(stream)) < 0 ||
        fseek(stream, 0, SEEK_SET) != 0) { fclose(stream); return false; }
    *bytes = malloc((size_t)end + 1u);
    if (!*bytes) { fclose(stream); return false; }
    if (fread(*bytes, 1u, (size_t)end, stream) != (size_t)end) {
        free(*bytes); *bytes = NULL; fclose(stream); return false;
    }
    (*bytes)[end] = 0u;
    *length = (size_t)end;
    return fclose(stream) == 0;
}

static bool write_forest(const char *path, const CettaLpNativeUtf8Forest *forest,
                         char *error, size_t error_size, size_t *size_out) {
    size_t size = 0u, written = 0u;
    uint8_t *bytes = NULL;
    FILE *stream = NULL;
    bool ok = false;
    if (!cetta_lp_native_utf8_forest_wire_size(forest, &size, error, error_size)) return false;
    bytes = malloc(size ? size : 1u);
    if (!bytes || !cetta_lp_native_utf8_forest_wire_write(
            forest, bytes, size, &written, error, error_size) || written != size) goto done;
    stream = fopen(path, "wb");
    if (!stream || fwrite(bytes, 1u, size, stream) != size) goto done;
    ok = true;
    *size_out = size;
done:
    if (stream && fclose(stream) != 0) ok = false;
    free(bytes);
    return ok;
}

static bool read_terms(Arena *arena, const char *path, Atom ***terms, size_t *count,
                       char digest[65], char *error, size_t error_size) {
    uint8_t *bytes = NULL;
    size_t length = 0u, begin = 0u;
    bool ok = false;
    *terms = NULL;
    *count = 0u;
    if (!read_bytes(path, &bytes, &length)) goto done;
    cetta_native_sha256_hex(bytes, length, digest);
    for (size_t end = 0u; end <= length; ++end) {
        if (end < length && bytes[end] != '\n') continue;
        if (end > begin) {
            Atom *term = NULL;
            if (!fh_ground_term_v1_parse(arena, bytes + begin, end - begin,
                                          &term, error, error_size)) goto done;
            if (*count >= SIZE_MAX / sizeof(**terms)) goto done;
            Atom **next = realloc(*terms, (*count + 1u) * sizeof(**terms));
            if (!next) goto done;
            *terms = next;
            (*terms)[(*count)++] = term;
        }
        begin = end + 1u;
    }
    ok = true;
done:
    free(bytes);
    if (!ok) { free(*terms); *terms = NULL; *count = 0u; }
    return ok;
}

static bool load_direct(PPABIV1Pack *pack, Arena *arena,
                        const char *productions_path, const char *classes_path,
                        char *error, size_t error_size) {
    Atom **productions = NULL, **classes = NULL;
    size_t production_count = 0u, class_count = 0u;
    char production_digest[65], class_digest[65], adapter_digest[65];
    static const uint8_t adapter[] = "GSLTDirectParserPackV1";
    bool ok = false;
    if (!read_terms(arena, productions_path, &productions, &production_count,
                    production_digest, error, error_size) ||
        !read_terms(arena, classes_path, &classes, &class_count,
                    class_digest, error, error_size)) goto done;
    cetta_native_sha256_hex(adapter, sizeof(adapter) - 1u, adapter_digest);
    ok = ppabi_v1_pack_load_structural(pack, productions, production_count,
            classes, class_count, production_digest, adapter_digest, class_digest,
            error, error_size);
done:
    free(productions);
    free(classes);
    return ok;
}

/* GLL exports every start-state prefix root. Source files observe only roots
   spanning the whole input. Restore the original root array after replay so
   the retained forest still describes exactly what the backend exported. */
#ifdef GSLT_SOURCE_SELECTION
static bool finish_source_values(PPNativeV1Result *result, const PPABIV1Pack *pack,
                                  uint32_t limit, const PPNativeV1FamilySelection *selection,
                                  bool whole_input, char *error, size_t error_size) {
    uint32_t *saved = result->forest.roots, count = result->forest.root_len;
    uint32_t *whole = NULL, whole_count = 0u;
    if (whole_input) {
        whole = calloc(count ? count : 1u, sizeof(*whole));
        if (!whole) return false;
        for (uint32_t i = 0u; i < count; ++i) {
            if (saved[i] >= result->forest.node_len) { free(whole); return false; }
            const CettaLpNativeUtf8ForestNode *node = &result->forest.nodes[saved[i]];
            if (node->scalar_left == 0u && node->scalar_right == result->forest.scalar_len)
                whole[whole_count++] = saved[i];
        }
        result->forest.roots = whole;
        result->forest.root_len = whole_count;
    }
    bool ok = ppnative_v1_finish_values_selected(result, pack, NULL, 4096u,
                                                  limit, selection, error, error_size);
    result->forest.roots = saved;
    result->forest.root_len = count;
    free(whole);
    return ok;
}
#endif

static bool run(const char *abi_path, const char *start_path,
                const char *input_path, const char *forest_path,
                bool recognize_only, const char *policy_path, uint32_t result_limit,
                const char *classes_path) {
    PPABIV1Wire wire;
    PPABIV1Pack pack;
    PPNativeV1Result result;
    Arena arena;
    Atom *start = NULL;
    uint8_t *start_bytes = NULL, *input = NULL;
    size_t start_length = 0u, input_length = 0u, wire_size = 0u;
    char error[1024] = {0};
    bool ok = false;
#ifdef GSLT_SOURCE_SELECTION
    SourceFamilyPolicy policy = {0};
    uint8_t *policy_bytes = NULL;
    size_t policy_length = 0u;
#endif
    ppabi_v1_wire_init(&wire);
    ppabi_v1_pack_init(&pack);
    ppnative_v1_result_init(&result);
    arena_init(&arena);
    if (classes_path) {
        if (!load_direct(&pack, &arena, abi_path, classes_path, error, sizeof(error))) goto done;
    } else if (!ppabi_v1_wire_read(&wire, abi_path, error, sizeof(error)) ||
               !ppabi_v1_wire_load_pack(&wire, &pack, error, sizeof(error))) goto done;
    if (!read_bytes(start_path, &start_bytes, &start_length) ||
        !fh_ground_term_v1_parse(&arena, start_bytes, start_length,
                                  &start, error, sizeof(error)) ||
        !ppabi_v1_pack_start_is_closed(&pack, start, error, sizeof(error)) ||
        !read_bytes(input_path, &input, &input_length)) goto done;
    if (classes_path || recognize_only || policy_path) {
        if (!ppgll_v1_recognize(&pack, start, input, input_length, 4000000u,
                                &result, error, sizeof(error))) goto done;
    } else if (!ppgll_v1_parse(&pack, start, input, input_length, 4000000u, 4096u, 2u,
                               &result, error, sizeof(error))) goto done;
#ifdef GSLT_SOURCE_SELECTION
    if (policy_path && result.outcome == PPNATIVE_V1_COMPLETED) {
        Atom *data = NULL;
        if (!read_bytes(policy_path, &policy_bytes, &policy_length) ||
            !fh_ground_term_v1_read_source(&arena, policy_bytes, policy_length, &data, error, sizeof(error)))
            goto done;
        if (!source_policy_read(&policy, &pack, data)) {
            snprintf(error, sizeof(error), "refused source family-selection policy");
            goto done;
        }
        PPNativeV1FamilySelection selection = {.accepts = source_family_accepts, .context = &policy};
        if (!finish_source_values(&result, &pack, result_limit, &selection,
                classes_path != NULL, error, sizeof(error))) goto done;
    }
    if (classes_path && !recognize_only && !policy_path && result.outcome == PPNATIVE_V1_COMPLETED &&
        !finish_source_values(&result, &pack, result_limit, NULL, true, error, sizeof(error))) goto done;
#else
    (void)result_limit;
    if (policy_path || (classes_path && !recognize_only)) {
        snprintf(error, sizeof(error), "source value replay requires source selection support"); goto done;
    }
#endif
    if ((result.outcome == PPNATIVE_V1_COMPLETED ||
         result.outcome == PPNATIVE_V1_REPLAY_DEPTH ||
         result.outcome == PPNATIVE_V1_RESULT_LIMIT ||
         result.outcome == PPNATIVE_V1_CYCLIC_FOREST) &&
        (!write_forest(forest_path, &result.forest, error, sizeof(error), &wire_size) ||
         (classes_path && !write_plan_identity(forest_path, &pack, error, sizeof(error))))) goto done;
    printf("{\"outcome\":%u,\"accepted\":%s,\"inputBytes\":%u,\"inputScalars\":%u,"
           "\"nodes\":%u,\"choices\":%u,\"roots\":%u,\"descriptors\":%u,"
           "\"farthestScalar\":%u,\"sourcePasses\":%u,\"forestWireBytes\":%zu,"
           "\"semanticResults\":%u,\"selected\":%s%s}\n",
           (unsigned)result.outcome, result.accepted ? "true" : "false",
           result.forest.input_byte_len, result.forest.scalar_len,
           result.forest.node_len, result.forest.choice_len, result.forest.root_len,
           result.forest.work_item_len, result.forest.farthest_scalar,
           result.forest.source_pass_count, wire_size, result.semantic_result_len,
           policy_path ? "true" : "false",
           recognize_only ? ",\"recognitionOnly\":true" : "");
    for (uint32_t i = 0; i < result.semantic_result_len; ++i) { atom_print_petta(result.semantic_results[i], stdout); fputc('\n', stdout); }
    ok = true;
done:
    if (!ok) fprintf(stderr, "%s\n", error[0] ? error : "existing packed API call failed");
    free(start_bytes);
    free(input);
#ifdef GSLT_SOURCE_SELECTION
    free(policy_bytes);
    free(policy.filters);
#endif
    arena_free(&arena);
    ppnative_v1_result_free(&result);
    ppabi_v1_pack_free(&pack);
    ppabi_v1_wire_free(&wire);
    return ok;
}

int main(int argc, char **argv) {
    SymbolTable symbols;
    bool ok;
    bool direct = argc > 1 && strcmp(argv[1], "--direct") == 0;
    char **args = argv + (direct ? 2 : 1);
    int count = argc - (direct ? 2 : 1);
    int paths = direct ? 5 : 4;
    bool recognize_only = count == paths + 1 && strcmp(args[paths], "--recognize-only") == 0;
    bool selected = count == paths + 3 && strcmp(args[paths], "--select") == 0;
    uint32_t result_limit = 2u;
    if (selected) {
        char *end = NULL;
        unsigned long parsed = strtoul(args[paths + 2], &end, 10);
        if (!args[paths + 2][0] || !end || *end || parsed == 0u || parsed > UINT32_MAX) return 2;
        result_limit = (uint32_t)parsed;
    }
    if (count != paths && !recognize_only && !selected) {
        fprintf(stderr, "expected ABI START INPUT FOREST, or --direct PRODUCTIONS CLASSES START INPUT FOREST; optionally --recognize-only or --select POLICY LIMIT\n");
        return 2;
    }
    symbol_table_init(&symbols);
    symbol_table_init_builtins(&symbols, &g_builtin_syms);
    g_symbols = &symbols;
    g_hashcons = NULL;
    g_var_intern = NULL;
    int offset = direct ? 1 : 0;
    ok = run(args[0], args[1 + offset], args[2 + offset], args[3 + offset], recognize_only,
             selected ? args[paths + 1] : NULL, result_limit, direct ? args[1] : NULL);
    symbol_table_free(&symbols);
    g_symbols = NULL;
    return ok ? 0 : 1;
}
