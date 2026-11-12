/* Production Atom/GMP borrowing and publication probe. The implementation
 * under test is included to reach its private arithmetic helper; no arithmetic
 * helper or lifetime implementation is copied into this test. */
#include "src/grounded.c"
#include <assert.h>

#ifdef NDEBUG
#error This qualification requires assertions.
#endif

static Atom *calculate(Arena *arena, const char *operation, Atom *left, Atom *right) {
    NumArg lhs = {0}, rhs = {0};
    assert(get_numeric_arg(left, &lhs) && get_numeric_arg(right, &rhs));
    Atom *head = atom_symbol(arena, operation);
    Atom *arguments[2] = {left, right};
    return eval_integer_binary_gmp(arena, head, head->sym_id, arguments, 2,
                                   &lhs, &rhs, false, false);
}

static void read_integer(Atom *value, mpz_t result) {
    NumArg argument = {0};
    assert(value && get_numeric_arg(value, &argument));
    assert(!argument.is_float && !argument.is_rational);
    assert(num_arg_to_mpz(&argument, result));
}

static void lifecycle(void) {
    Arena arena, copied;
    arena_init(&arena);
    arena_init(&copied);
    Atom *large = atom_bigint(&arena, "18446744073709551616");
    NumArg argument = {0};
    assert(get_numeric_arg(large, &argument));
    IntegerMpzView borrowed;
    assert(integer_mpz_view_init(&argument, &borrowed));
    assert(!borrowed.owns_storage);
    assert(borrowed.value == atom_bigint_mpz_view(large));
    integer_mpz_view_clear(&borrowed);
    mpz_t expected, observed, temporary;
    mpz_inits(expected, observed, temporary, NULL);
    assert(mpz_set_str(expected, "18446744073709551616", 10) == 0);
    assert(mpz_cmp(atom_bigint_mpz_view(large), expected) == 0);

    Atom *minimum = atom_int(&arena, INT64_MIN);
    assert(get_numeric_arg(minimum, &argument));
    IntegerMpzView promoted;
    assert(integer_mpz_view_init(&argument, &promoted));
    assert(promoted.owns_storage && promoted.value == promoted.storage);
    assert(mpz_set_str(expected, "-9223372036854775808", 10) == 0);
    assert(mpz_cmp(promoted.value, expected) == 0);
    integer_mpz_view_clear(&promoted);
    NumArg floating = {0};
    floating.is_float = true;
    assert(!integer_mpz_view_init(&floating, &promoted));
    assert(!integer_mpz_view_init(NULL, &promoted));
    assert(atom_bigint_mpz_view(minimum) == NULL);

    /* Large publication moves the limb owner; the initialized source is
     * left safe to clear. Small publication keeps a word and leaves the
     * temporary owned by its caller. */
    mpz_set_ui(temporary, 1);
    mpz_mul_2exp(temporary, temporary, 257);
    mpz_add_ui(temporary, temporary, 19);
    mpz_set(expected, temporary);
    mp_srcptr limbs = mpz_limbs_read(temporary);
    Atom *moved = atom_bigint_take_mpz(&arena, temporary);
    assert(moved && moved->ground.gkind == GV_BIGINT);
    assert(mpz_limbs_read(atom_bigint_mpz_view(moved)) == limbs);
    assert(mpz_sgn(temporary) == 0);
    assert(mpz_cmp(atom_bigint_mpz_view(moved), expected) == 0);
    Atom *clone = atom_deep_copy(&copied, moved);
    assert(clone && atom_bigint_mpz_view(clone) != atom_bigint_mpz_view(moved));
    assert(mpz_cmp(atom_bigint_mpz_view(clone), expected) == 0);

    mpz_set_si(temporary, -7);
    Atom *small = atom_bigint_take_mpz(&arena, temporary);
    assert(small && small->ground.gkind == GV_INT && small->ground.ival == -7);
    assert(mpz_cmp_si(temporary, -7) == 0);
    assert(atom_bigint_take_mpz(NULL, temporary) == NULL);
    assert(mpz_cmp_si(temporary, -7) == 0);

    ArenaMark mark = arena_mark(&arena);
    Atom *one = atom_int(&arena, 1);
    Atom *current = large;
    mpz_set_ui(expected, 1);
    mpz_mul_2exp(expected, expected, 64);
    for (unsigned i = 0; i < 512; ++i) {
        Atom *previous = current;
        current = calculate(&arena, "+", current, one);
        read_integer(previous, observed);
        assert(mpz_cmp(observed, expected) == 0);
        mpz_add_ui(expected, expected, 1);
        read_integer(current, observed);
        assert(mpz_cmp(observed, expected) == 0);
    }
    Atom *negative = atom_bigint(&arena, "-18446744073709552128");
    Atom *zero = calculate(&arena, "+", current, negative);
    assert(zero && zero->ground.gkind == GV_INT && zero->ground.ival == 0);
    Atom *again = calculate(&arena, "+", large, large);
    read_integer(again, observed);
    mpz_set_ui(expected, 1);
    mpz_mul_2exp(expected, expected, 65);
    assert(mpz_cmp(observed, expected) == 0);
    arena_reset(&arena, mark);
    read_integer(large, observed);
    mpz_fdiv_q_2exp(expected, expected, 1);
    assert(mpz_cmp(observed, expected) == 0);
    arena_free(&arena);
    /* A deep copy in another arena outlives the original owner's reset/free. */
    read_integer(clone, observed);
    mpz_set_ui(expected, 1);
    mpz_mul_2exp(expected, expected, 257);
    mpz_add_ui(expected, expected, 19);
    assert(mpz_cmp(observed, expected) == 0);
    arena_free(&copied);
    mpz_clears(expected, observed, temporary, NULL);
    puts("lifecycle\tpassed");
}

int main(void) {
    SymbolTable symbols;
    symbol_table_init(&symbols);
    g_symbols = &symbols;
    symbol_table_init_builtins(&symbols, &g_builtin_syms);
    assert(g_builtin_syms.op_plus != g_builtin_syms.op_minus);
    assert(g_builtin_syms.op_minus != g_builtin_syms.op_mul);
    lifecycle();
    char *line = NULL;
    size_t capacity = 0;
    while (getline(&line, &capacity, stdin) >= 0) {
        char *operation = strtok(line, "\t\n");
        char *left_text = strtok(NULL, "\t\n");
        char *right_text = strtok(NULL, "\t\n");
        assert(operation && left_text && right_text && !strtok(NULL, "\t\n"));
        assert(strcmp(operation, "+") == 0 || strcmp(operation, "-") == 0 ||
               strcmp(operation, "*") == 0);
        Arena arena;
        arena_init(&arena);
        Atom *left = atom_bigint(&arena, left_text);
        Atom *right = atom_bigint(&arena, right_text);
        mpz_t before_left, before_right, after, result;
        mpz_inits(before_left, before_right, after, result, NULL);
        read_integer(left, before_left);
        read_integer(right, before_right);
        mpz_srcptr borrowed_left = atom_bigint_mpz_view(left);
        mpz_srcptr borrowed_right = atom_bigint_mpz_view(right);
        Atom *answer = calculate(&arena, operation, left, right);
        read_integer(answer, result);
        read_integer(left, after);
        assert(mpz_cmp(before_left, after) == 0);
        read_integer(right, after);
        assert(mpz_cmp(before_right, after) == 0);
        assert(atom_bigint_mpz_view(left) == borrowed_left);
        assert(atom_bigint_mpz_view(right) == borrowed_right);
        gmp_printf("%Zd\t%s\n", result,
                   answer->ground.gkind == GV_INT ? "word" : "storage");
        mpz_clears(before_left, before_right, after, result, NULL);
        arena_free(&arena);
    }
    free(line);
    symbol_table_free(&symbols);
    g_symbols = NULL;
    return 0;
}
