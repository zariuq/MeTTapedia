#include "native/module_value_v1.h"
#include "parser.h"
#include "symbol.h"
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static int form(Atom *a, const char *name, size_t fields) {
    return a && a->kind == ATOM_EXPR && a->expr.len == fields + 1 &&
           atom_is_symbol(a->expr.elems[0], name);
}

/* A generic module-authoring client of the existing C API. It contains no
 * binary-format decoder, evaluator or changes to the runtime dispatch. */
int main(int argc, char **argv) {
    if (argc != 4) {
        fputs("usage: module-authoring WORK REQUEST OUTPUT\n", stderr);
        return 2;
    }
    char *end = NULL;
    errno = 0;
    unsigned long budget = strtoul(argv[1], &end, 10);
    if (errno || !end || *end || !budget || budget > UINT32_MAX) return 2;
    SymbolTable symbols;
    symbol_table_init(&symbols);
    symbol_table_init_builtins(&symbols, &g_builtin_syms);
    g_symbols = &symbols;
    Arena arena;
    arena_init(&arena);
    Atom **requests = NULL;
    int count = parse_metta_file(argv[2], &arena, &requests);
    if (count != 1 || !form(requests[0], "ModuleCompilePipeline", 5)) {
        fputs("expected one ModuleCompilePipeline datum\n", stderr);
        free(requests);
        return 2;
    }
    Atom *request = requests[0];
    free(requests);
    Atom *module = request->expr.elems[1];
    Atom *stages = request->expr.elems[2];
    Atom *arguments = request->expr.elems[3];
    Atom *catalog = request->expr.elems[4];
    Atom *instance = request->expr.elems[5];
    Atom *presentation = NULL, *refusal = NULL, *exported = NULL;
    int status = 0;
    while (form(stages, "LCons", 2)) {
        Atom *theory = stages->expr.elems[1];
        if (!cetta_module_value_v1_assemble(&arena, module, theory, arguments,
                catalog, CETTA_GSLT_ORIGIN_VIEW_V1, instance, (uint32_t)budget,
                &presentation, &refusal)) {
            status = 1;
            break;
        }
        arguments = atom_expr3(&arena, atom_symbol(&arena, "LCons"),
                              presentation, atom_symbol(&arena, "LNil"));
        stages = stages->expr.elems[2];
    }
    if (!status && (!atom_is_symbol(stages, "LNil") || !presentation)) status = 2;
    if (!status && !cetta_module_value_v1_rewrite_rules(&arena, presentation,
            instance, (uint32_t)budget, &exported, &refusal)) status = 1;
    FILE *out = fopen(argv[3], "wb");
    if (!out) return 2;
    if (status) {
        if (refusal) atom_print(refusal, out);
        else fputs("(ModuleAuthoringRefused MalformedPipeline)", out);
    } else {
        atom_print(exported, out);
    }
    fputc('\n', out);
    if (fclose(out)) status = 2;
    fprintf(stderr, "module-authoring: status %d, work limit %lu\n", status, budget);
    arena_free(&arena);
    g_symbols = NULL;
    symbol_table_free(&symbols);
    return status;
}
