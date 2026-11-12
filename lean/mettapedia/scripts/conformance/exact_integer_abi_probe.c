/* Qualification of the existing CeTTa ABI, not a production provider.
 * The provider object is compiled with its seven entry points renamed to
 * real_*. Wrappers below permit fault injection without changing GMP code.
 */
#include <stdio.h>
#include "native/external_call_gmp_exact_integer_v1.h"
#include <string.h>

typedef CettaExternalCallGeneratedExternalV1 External;
typedef CettaExternalCallGeneratedOutcomeV1 Outcome;
typedef CettaExternalCallExactIntegerV1 Integer;
typedef CettaExternalCallGeneratedReceiptV1 Receipt;
typedef Outcome (*Operation)(const Integer *, const Integer *, Integer *, Receipt *);
typedef External (*Provider)(const Integer *, const Integer *, Integer *);

static int injected = -1;
static unsigned calls = 0;

#define OP(name) \
    extern External real_##name(const Integer *, const Integer *, Integer *); \
    External cetta_external_call_exact_integer_##name##_v1( \
        const Integer *a, const Integer *b, Integer *r) { \
        ++calls; \
        return injected < 0 ? real_##name(a, b, r) : (External)injected; \
    } \
    extern Outcome cetta_generated_exact_integer_##name##_v1( \
        const Integer *, const Integer *, Integer *, Receipt *);
OP(add) OP(sub) OP(mul) OP(tquot) OP(fquot) OP(trem) OP(frem)
#undef OP

static const struct { const char *name; Operation run; Provider direct; } ops[] = {
#define ROW(name) {#name, cetta_generated_exact_integer_##name##_v1, real_##name},
    ROW(add) ROW(sub) ROW(mul) ROW(tquot) ROW(fquot) ROW(trem) ROW(frem)
#undef ROW
};

int main(void) {
    char op[16], a[4096], b[4096];
    unsigned alias, capacity, mode;
    Integer first, second, separate;
    cetta_external_call_gmp_exact_integer_init_v1(&first);
    cetta_external_call_gmp_exact_integer_init_v1(&second);
    cetta_external_call_gmp_exact_integer_init_v1(&separate);
    while (scanf("%15s %4095s %4095s %u %u %d %u",
                 op, a, b, &alias, &capacity, &injected, &mode) == 7) {
        size_t index = 0;
        while (index < sizeof(ops) / sizeof(ops[0]) && strcmp(op, ops[index].name))
            ++index;
        if (index == sizeof(ops) / sizeof(ops[0]) || alias > 2 || capacity > 4 || mode > 3)
            return 2;
        if (!cetta_external_call_gmp_exact_integer_set_decimal_v1(&first, a) ||
            !cetta_external_call_gmp_exact_integer_set_decimal_v1(&second, b))
            return 3;
        mpz_set_si(separate.value, 777);
        Integer *output = alias == 1 ? &first : alias == 2 ? &second : &separate;
        CettaExternalCallGeneratedEventV1 storage[4];
        Receipt receipt;
        cetta_external_call_generated_receipt_init_v1(
            &receipt, mode == 2 ? NULL : storage, capacity);
        calls = 0;
        int status = mode == 3
            ? (int)ops[index].direct(&first, &second, output)
            : (int)ops[index].run(&first, &second, output, mode == 1 ? NULL : &receipt);
        printf("%d\t", status);
        mpz_out_str(stdout, 10, output->value);
        printf("\t%u\t%u\t%u\t", receipt.event_count, receipt.complete, calls);
        if (receipt.events)
            for (uint32_t i = 0; i < receipt.event_count && i < capacity; ++i) {
                const CettaExternalCallGeneratedEventV1 *event = &receipt.events[i];
                if (i) putchar(',');
                if (event->kind == CETTA_EXTERNAL_CALL_GENERATED_EVENT_STEP_V1)
                    printf("S:%u", event->instruction);
                else
                    printf("E:%u:%u:%d", event->instruction, event->external,
                           (int)event->external_outcome);
            }
        putchar('\t'); mpz_out_str(stdout, 10, first.value);
        putchar('\t'); mpz_out_str(stdout, 10, second.value);
        printf("\t%d\n", (int)receipt.outcome);
    }
    cetta_external_call_gmp_exact_integer_clear_v1(&separate);
    cetta_external_call_gmp_exact_integer_clear_v1(&second);
    cetta_external_call_gmp_exact_integer_clear_v1(&first);
    return ferror(stdin) ? 4 : 0;
}
