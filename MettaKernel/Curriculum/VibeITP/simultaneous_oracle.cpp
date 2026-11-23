// External oracle controls for Spec.SimultaneousInstantiationControls.
// Links the selected upstream kernel; implements no substitute checking rules.
#include "logic.h"
#include <cstdint>
#include <initializer_list>
#include <iostream>
#include <vector>

struct Owned {
  std::vector<symbol *> symbols;
  std::vector<term *> terms;
  std::vector<theorem *> theorems;
  ~Owned() {
    for (auto *p : theorems) logic_theorem_free(p);
    for (auto *p : terms) logic_term_free(p);
    for (auto *p : symbols) logic_symbol_free(p);
  }
  symbol *fvar(uint64_t arity) {
    auto *p = logic_symbol_fvar_new(arity); symbols.push_back(p); return p;
  }
  symbol *binder(uint64_t count) {
    auto *p = logic_symbol_const_new(1, &count); symbols.push_back(p); return p;
  }
  term *keep(term *p) { terms.push_back(p); return p; }
  term *app(symbol *s, std::initializer_list<term *> children = {}) {
    std::vector<term *> args(children);
    return keep(logic_term_new_app(s, args.empty() ? nullptr : args.data()));
  }
  term *lit(uint64_t n) { return keep(logic_term_new_literal_u64(n)); }
  term *bound(uint64_t n) { return keep(logic_term_new_bvar(n)); }
  term *many(term *source, std::initializer_list<symbol *> heads,
             std::initializer_list<term *> values) {
    std::vector<symbol *> fs(heads); std::vector<term *> vs(values);
    return keep(logic_term_substitute_fvars(fs.size(), fs.data(), vs.data(), source));
  }
  term *one(term *source, symbol *head, term *value) {
    return keep(logic_term_substitute_fvar(head, value, source));
  }
  theorem *manyProof(theorem *source, std::initializer_list<symbol *> heads,
                     std::initializer_list<term *> values) {
    std::vector<symbol *> fs(heads); std::vector<term *> vs(values);
    auto *p = logic_thm_instantiate_n(source, fs.size(), fs.data(), vs.data());
    theorems.push_back(p); return p;
  }
};

int main() {
  Owned o;
  auto *F=o.fvar(0), *G=o.fvar(0), *H=o.fvar(2), *T=o.fvar(0), *U=o.fvar(0);
  auto *K=o.binder(1), *largeBinder=o.binder(UINT64_MAX), *innerBinder=o.binder(1);
  auto *f=o.app(F), *g=o.app(G), *pair=o.app(&logic_eq_symbol,{f,g});
  auto *three=o.lit(3), *four=o.lit(4), *seven=o.lit(7), *eight=o.lit(8), *nine=o.lit(9);
  auto *zero=o.bound(0), *one=o.bound(1);
  int failures=0;
  auto test=[&](const char *name,bool passed) {
    std::cout<<name<<" "<<(passed?"true":"false")<<"\n";
    failures+=!passed;
  };
  auto eq=[](term *a,term *b) {return a && b && logic_term_eq(a,b);};
  test("crossing",eq(o.many(pair,{F,G},{g,seven}),o.app(&logic_eq_symbol,{g,seven})));
  test("swap",eq(o.many(pair,{F,G},{g,f}),o.app(&logic_eq_symbol,{g,f})));
  test("duplicate-first",eq(o.many(f,{F,F},{eight,nine}),eight));
  auto *basis=logic_thm_litIsNat(3); o.theorems.push_back(basis);
  test("invalid-shadow",o.manyProof(basis,{F,F},{eight,zero})==nullptr);
  test("unused-invalid",o.manyProof(basis,{F},{zero})==nullptr);
  test("constant-target",o.manyProof(basis,{K},{three})==nullptr);
  auto *body=o.app(&logic_eq_symbol,{one,zero});
  test("higher-order",eq(o.many(o.app(H,{three,four}),{H},{body}),o.app(&logic_eq_symbol,{three,four})));
  test("binder",eq(o.many(o.app(K,{o.app(H,{zero,four})}),{H},{body}),o.app(K,{o.app(&logic_eq_symbol,{zero,four})})));
  auto *large=o.app(largeBinder,{o.app(innerBinder,{f})});
  test("large-closed",large && large->bvar_depth==0);
  test("simultaneous-large",eq(o.many(pair,{F,G},{large,seven}),o.app(&logic_eq_symbol,{large,seven})));
  auto *r1=o.one(pair,F,o.app(T));
  auto *r2=o.one(r1,G,o.app(U));
  auto *r3=o.one(r2,T,large);
  test("fresh-sequential-refuses",r1 && r2 && r3 && o.one(r3,U,seven)==nullptr);
  test("zero-copy",eq(o.many(pair,{},{}),pair));
  test("sequential-differs",eq(o.one(o.one(pair,F,g),G,seven),o.app(&logic_eq_symbol,{seven,seven})));
  return failures ? 1 : 0;
}
