#include <endian.h>
#include <string.h>
#include <stdlib.h>

#include "kernel.h"

#define MIN_THM_LIMIT 1000

static ThmBody *thms = NULL;

static Theorem thm_limit;
static Symbol last_const;

bool init() {
  thm_limit = MIN_THM_LIMIT;
  last_const = 1;
  if (thms) free(thms);
  thms = calloc(thm_limit, sizeof(ThmBody));
  return thms != NULL;
}

const ThmBody dummy_thm = {0,0,0,0};
const ThmBody *get_thm(Theorem thm_i) {
  if (thm_i < thm_limit) return &thms[thm_i];
  else return &dummy_thm;
}

bool _set_thm(Symbol out, Symbol f, Symbol x, Symbol y, Theorem thm_i) {
  if (thm_i >= thm_limit) { // extend the array if needed
    Theorem next_limit = thm_limit*3/2;
    if (thm_i >= next_limit) next_limit = thm_i+1;
    if (thm_i >= next_limit || next_limit < thm_limit) return 0; // overflow
    ThmBody *next_thms = reallocarray(thms, next_limit, sizeof(ThmBody));
    if (!next_thms) return 0; // allocation failure
    memset(next_thms + thm_limit, 0, (next_limit - thm_limit) * sizeof(ThmBody));
    thms = next_thms;
    thm_limit = next_limit;
  }
  thms[thm_i] = (ThmBody){ out, f, x, y };
  return true;
}

Symbol get_last_const() { return last_const; }
Theorem get_thm_limit() { return thm_limit; }
Theorem get_thm_used_space() {
  Theorem n = thm_limit;
  while (n > 0 && !thms[n-1].out && !thms[n-1].f && !thms[n-1].x && !thms[n-1].y) n--;
  return n;
}

//    Logical rules
//

Symbol new_node_opaque() {
  if (!(last_const+1)) return 0; // overflow
  return ++last_const;
}

Symbol new_node_def(Symbol f, Symbol x, Symbol y, Theorem thm_i) {
  if (f <= last_const && x <= last_const && y <= last_const) {
    Symbol out = new_node_opaque();
    if (out) {
      if(_set_thm(out, f, x, y, thm_i)) return out;
      last_const--; // error, reverting
    }
  }
  return 0;
}

// x = X(x,y)
bool rule_proj1(Symbol x, Symbol y, Theorem thm_i) { return _set_thm(x, 0, x, y, thm_i); }
// y = Y(x,y)
bool rule_proj2(Symbol x, Symbol y, Theorem thm_i) { return _set_thm(y, 1, x, y, thm_i); }
// a = a(X,Y)
bool rule_refl(Symbol a, Theorem thm_i) { return _set_thm(a, a, 0, 1, thm_i); }

// x(A,B) = t(u(A,B), v(A,B)) -> x(a,b) = t(u(a,b), v(a,b))
bool rule_substitute1(Theorem main_i, Theorem subst_u_i, Theorem subst_v_i, Theorem subst_x_i, Theorem dest_i) {
  const ThmBody *main = get_thm(main_i);       // x = t(u,v)
  const ThmBody *subst_u = get_thm(subst_u_i); // u1 = u(a,b)
  const ThmBody *subst_v = get_thm(subst_v_i); // v1 = v(a,b)
  const ThmBody *subst_x = get_thm(subst_x_i); // x1 = x(a,b)
  if (subst_u->f == main->x &&
      subst_v->f == main->y && subst_v->x == subst_u->x && subst_v->y == subst_u->y &&
      subst_x->f == main->out && subst_x->x == subst_u->x && subst_x->y == subst_u->y)
    return _set_thm(subst_x->out, main->f, subst_u->out, subst_v->out, dest_i); // x1 = t(u1,v1)
  else return false;
}
bool rule_substitute2(Theorem main_i, Theorem subst_u_i, Theorem subst_v_i, Theorem subst_x_i, Theorem dest_i) {
  const ThmBody *main = get_thm(main_i);       // x = t(u,v)
  const ThmBody *subst_u = get_thm(subst_u_i); // u1 = u(a,b)
  const ThmBody *subst_v = get_thm(subst_v_i); // v1 = v(a,b)
  const ThmBody *subst_x = get_thm(subst_x_i); // x1 = t(u1,v1)
  if (subst_u->f == main->x &&
      subst_v->f == main->y && subst_v->x == subst_u->x && subst_v->y == subst_u->y &&
      subst_x->f == main->f && subst_x->x == subst_u->out && subst_x->y == subst_v->out)
    return _set_thm(subst_x->out, main->out, subst_u->x, subst_u->y, dest_i); // x1 = x(a,b)
  else return false;
}

//    Dump & Load
//

bool dump_symbol(Symbol s, FILE *f) {
  s = htole64(s);
  return fwrite(&s, sizeof(Symbol), 1, f);
}
bool load_symbol(Symbol *s, FILE *f) {
  if (!fread(s, sizeof(Symbol), 1, f)) return false;
  *s = le64toh(*s);
  return true;
}
// here the same since Theorem = Symbol, but separate functions in case of a change
bool dump_thmi(Theorem thmi, FILE *f) {
  thmi = htole64(thmi);
  return fwrite(&thmi, sizeof(Theorem), 1, f);
}
bool load_thmi(Theorem *thmi, FILE *f) {
  if (!fread(thmi, sizeof(Theorem), 1, f)) return false;
  *thmi = le64toh(*thmi);
  return true;
}

bool dump_theorem(ThmBody *thm, FILE *f) {
  return dump_symbol(thm->out, f) && dump_symbol(thm->f, f) &&
    dump_symbol(thm->x, f) && dump_symbol(thm->y, f);
}
bool load_theorem(ThmBody *thm, FILE *f) {
  return load_symbol(&thm->out, f) && load_symbol(&thm->f, f) &&
    load_symbol(&thm->x, f) && load_symbol(&thm->y, f);
}

bool dump_theorems(FILE *f) {
  Theorem n = get_thm_used_space();
  if (!dump_symbol(last_const, f) || !dump_thmi(n, f)) return false;
  for (Theorem thmi = 0; thmi < n; thmi++)
    if (!dump_theorem(&thms[thmi], f)) return false;
  return true;
}
bool load_theorems(FILE *f) {
  Theorem n;
  if (!load_symbol(&last_const, f) || !load_thmi(&n, f)) return false;
  if (last_const < 1) return false;
  thm_limit = n;
  if (thm_limit < MIN_THM_LIMIT) thm_limit = MIN_THM_LIMIT;
  if (thms) free(thms);
  thms = calloc(thm_limit, sizeof(ThmBody));
  if (!thms) return false;
  for (Theorem thmi = 0; thmi < n; thmi++)
    if (!load_theorem(&thms[thmi], f)) {
      free(thms);
      thms = NULL;
      return false;
    }
  return true;
}
