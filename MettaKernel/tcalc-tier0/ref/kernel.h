#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>

typedef uint64_t Symbol;
typedef uint64_t Theorem;
typedef struct { uint64_t out, f, x, y; } ThmBody;

bool init(); // needs to be executed at the start, and succeed (return true)
const ThmBody *get_thm(uint64_t thm_i);

// add a "new axiom": out = f(x,y), generally unsafe, return true on success
bool _set_thm(uint64_t out, uint64_t f, uint64_t x, uint64_t y, uint64_t thm_i);

Symbol get_last_const();
Theorem get_thm_limit();
Theorem get_thm_used_space(); // truncate trailing zeros

// new constants, zero on failure, otherwise the new constant index
uint64_t new_node_opaque();
uint64_t new_node_def(uint64_t f, uint64_t x, uint64_t y, uint64_t thm_i);

// rules
bool rule_proj1(uint64_t x, uint64_t y, uint64_t thm_i); // x = X(x,y)
bool rule_proj2(uint64_t x, uint64_t y, uint64_t thm_i); // y = Y(x,y)
bool rule_refl(uint64_t a, uint64_t thm_i); // a = a(X,Y)

// x(A,B) = t(u(A,B), v(A,B)) -> x(a,b) = t(u(a,b), v(a,b))
bool rule_substitute1(uint64_t main_i, uint64_t subst_u_i, uint64_t subst_v_i, uint64_t subst_x_i, uint64_t dest_i);
bool rule_substitute2(uint64_t main_i, uint64_t subst_u_i, uint64_t subst_v_i, uint64_t subst_x_i, uint64_t dest_i);

// Dump & Load

bool dump_symbol(Symbol s, FILE *f);
bool load_symbol(Symbol *s, FILE *f);
bool dump_thmi(Theorem thmi, FILE *f);
bool load_thmi(Theorem *thmi, FILE *f);
bool dump_theorem(ThmBody *thm, FILE *f);
bool load_theorem(ThmBody *thm, FILE *f);

bool dump_theorems(FILE *f);
bool load_theorems(FILE *f);
