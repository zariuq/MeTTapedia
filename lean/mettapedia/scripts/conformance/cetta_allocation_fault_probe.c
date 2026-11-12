/* Test-link instrumentation: refuse one large allocation after SIGUSR2.
 * The runtime's own allocator and fatal-completion path remain under test. */
#define _POSIX_C_SOURCE 200809L
#include "src/atom.h"
#include <errno.h>
#include <signal.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

_Static_assert(ATOMIC_INT_LOCK_FREE == 2, "signal arming requires lock-free atomics");
static _Atomic int fault_armed;
static _Atomic int fault_injected;

static void arm_fault(int signal_number) {
    (void)signal_number;
    atomic_store_explicit(&fault_armed, 1, memory_order_relaxed);
}

__attribute__((constructor)) static void initialize_fault_probe(void) {
    struct sigaction action = {0};
    action.sa_handler = arm_fault;
    sigemptyset(&action.sa_mask);
    if (sigaction(SIGUSR2, &action, NULL) != 0)
        _exit(125);
    /* The supervisor arms only after the emitted client reaches its marker. */
    if (setvbuf(stdout, NULL, _IOLBF, 0) != 0)
        _exit(125);
}

extern void *__real_malloc(size_t size);
void *__wrap_malloc(size_t size) {
    int expected = 0;
    if (size >= ARENA_BLOCK_SIZE &&
        atomic_load_explicit(&fault_armed, memory_order_relaxed) &&
        atomic_compare_exchange_strong_explicit(&fault_injected, &expected, 1,
            memory_order_relaxed, memory_order_relaxed)) {
        static const char message[] = "qualification: allocation refusal injected\n";
        ssize_t written = write(STDERR_FILENO, message, sizeof(message) - 1);
        (void)written;
        errno = ENOMEM;
        return NULL;
    }
    return __real_malloc(size);
}
