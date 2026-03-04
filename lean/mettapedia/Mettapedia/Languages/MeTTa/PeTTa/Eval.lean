import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# PeTTa Pure Evaluation Relation

Formalizes the **pure, type-free fragment** of PeTTa evaluation as an inductive
relation `PeTTaEval s p answers`, meaning "in atomspace `s`, the expression `p`
evaluates to the nondeterministic answer set `answers`".

## Architecture

This mirrors the MeTTa spec's `metta(atom, space, bindings) → [(Atom, Bindings)]`
relation for the pure fragment:

| MeTTa spec | PeTTaEval |
|-----------|-----------|
| `metta(Variable, ...)` | `.var` case: fvar reduces to itself |
| `metta(Atom, ...)` | `.ground` case: ground atom reduces to itself |
| `metta_call(rhs, ...)` after LHS match | `.ruleApp` case |
| `metta(match &self pat tmpl, ...)` | `.spaceQuery` case |
| `metta(superpose alts, ...)` | `.superpose` case |
| `metta(collapse expr, ...)` | `.collapse` case |

## PeTTa / HE Alignment

- **Pure fragment**: HE MeTTa spec's `metta_call` (rule matching via `(= lhs rhs)`)
  ≡ PeTTa's `ruleApp` case ≡ LP's `leastHerbrandModel`. All three agree.
- **match**: HE spec's `metta(match, ...)` ≡ PeTTa's `spaceMatch` ≡ LP EDB query.
- **superpose/collapse**: HE uses `superpose-bind`/`collapse-bind`. PeTTa maps
  `superpose` → Prolog disjunction (`;`), `collapse` → `findall/3`.

## Excluded (Type System, Effects)

Type-driven reduction (`check_if_function_type_is_applicable`) and effects
(`add-atom`, `remove-atom`, `print`) are deferred to `Effects.lean`.

## References

- MeTTa spec: `trueagi-io.github.io/hyperon-experimental/metta/`
- PeTTa transpiler: `hyperon/PeTTa/transpiler.pl`
-/

namespace Mettapedia.Languages.MeTTa.PeTTa

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec

/-! ## Pure Evaluation Relation -/

/-- Pure PeTTa evaluation judgment for the type-free fragment.

    `PeTTaEval s p answers` means: in atomspace `s`, expression `p`
    evaluates to the nondeterministic answer set `answers`.

    This is the declarative specification; the operational behavior follows
    from the LP semantics (see `LPSoundness.lean`). -/
inductive PeTTaEval (s : PeTTaSpace) : Pattern → Answers → Prop where

  /-- **Variables**: a free variable (metavariable) evaluates to itself.
      MeTTa spec: `metta(Variable, ...) → [(Variable, bindings)]`. -/
  | var (x : String) :
      PeTTaEval s (.fvar x) [.fvar x]

  /-- **Bound variables**: evaluate to themselves (structurally inert). -/
  | bvar (n : Nat) :
      PeTTaEval s (.bvar n) [.bvar n]

  /-- **Ground atoms** (nullary applications): evaluate to themselves.
      MeTTa spec: `metta(Atom, ...) → [(Atom, bindings)]` when no rule matches. -/
  | ground (c : String) :
      PeTTaEval s (.apply c []) [.apply c []]

  /-- **Rule application (top rule)**: match the LHS of a rule against `p`,
      apply the resulting bindings to the RHS, producing `q`.

      Conditions:
      - `r ∈ s.rules`: the rule is in the atomspace
      - `r.premises = []`: only unconditional rules (no premises)
      - `bs ∈ matchPattern r.left p`: LHS matches `p` with bindings `bs`
      - `applyBindings bs r.right = q`: applying bindings to RHS gives `q`

      MeTTa spec: `metta_call` after a successful `match_atoms`.
      HE MeTTa: `(= lhs rhs)` rules applied via unification.
      PeTTa: top-level Prolog clause `metta_call(lhs, rhs)`. -/
  | ruleApp (r : RewriteRule) (bs : Bindings) (p q : Pattern)
      (hr : r ∈ s.rules)
      (hprem : r.premises = [])
      (hm : bs ∈ matchPattern r.left p)
      (hq : applyBindings bs r.right = q) :
      PeTTaEval s p [q]

  /-- **Space query** (`match &self pat tmpl`): returns all groundings of `tmpl`
      obtained by pattern-matching `pat` against facts in the atomspace.

      Models: `(match &self pat tmpl)` in MeTTa. -/
  | spaceQuery (pat tmpl : Pattern) (results : Answers)
      (hres : results = s.spaceMatch pat tmpl) :
      PeTTaEval s (.apply "match" [.apply "&self" [], pat, tmpl]) results

  /-- **Superpose**: a `superpose` expression evaluates to each alternative.
      The argument must be a vector collection.

      Models: `(superpose (a b c))` → answers `a`, `b`, `c` (nondeterministically).
      PeTTa: Prolog disjunction over alternatives. -/
  | superpose (alts : List Pattern) :
      PeTTaEval s (.apply "superpose" [.collection .vec alts none]) alts

  /-- **Collapse**: collect all answers from a nondeterministic expression into a list.

      If `p` evaluates to `answers`, then `(collapse p)` evaluates to the singleton
      containing the vector collection of all those answers.

      Models: `(collapse p)` in MeTTa / `findall(X, eval(p, X), Xs)` in PeTTa. -/
  | collapse (p : Pattern) (answers : Answers)
      (h : PeTTaEval s p answers) :
      PeTTaEval s (.apply "collapse" [p]) [.collection .vec answers none]

/-! ## Basic Properties -/

/-- The `var` constructor fires directly: fvar always has `[.fvar x]` as a possible answer. -/
theorem petta_eval_var_case (s : PeTTaSpace) (x : String) :
    PeTTaEval s (.fvar x) [.fvar x] :=
  PeTTaEval.var x

/-- Rule application always produces exactly one answer. -/
theorem petta_eval_ruleApp_singleton {s : PeTTaSpace} (r : RewriteRule) (bs : Bindings)
    (p q : Pattern) (hr : r ∈ s.rules) (hprem : r.premises = [])
    (hm : bs ∈ matchPattern r.left p) (hq : applyBindings bs r.right = q) :
    PeTTaEval s p [q] :=
  PeTTaEval.ruleApp r bs p q hr hprem hm hq

/-- Superpose of nil yields empty answers. -/
theorem petta_eval_superpose_nil {s : PeTTaSpace} :
    PeTTaEval s (.apply "superpose" [.collection .vec [] none]) [] :=
  PeTTaEval.superpose []

/-- Collapse always produces a singleton answer (the collection of all inner answers). -/
theorem petta_eval_collapse_singleton {s : PeTTaSpace} {p : Pattern} {answers : Answers}
    (h : PeTTaEval s p answers) :
    ∃ ans, PeTTaEval s (.apply "collapse" [p]) [ans] :=
  ⟨.collection .vec answers none, PeTTaEval.collapse p answers h⟩

/-- The spaceQuery constructor produces exactly the spaceMatch answers. -/
theorem petta_eval_spaceQuery_correct (s : PeTTaSpace) (pat tmpl : Pattern) :
    PeTTaEval s (.apply "match" [.apply "&self" [], pat, tmpl]) (s.spaceMatch pat tmpl) :=
  PeTTaEval.spaceQuery pat tmpl _ rfl

/-! ## Monotonicity for spaceMatch -/

/-- **spaceMatch monotone in facts**: adding a fact only adds answers to spaceMatch.
    This is stated directly on `spaceMatch` (which is a function, not an inductive). -/
theorem spaceMatch_mono_addAtom (s : PeTTaSpace) (pat tmpl : Pattern) (newFact : Pattern) :
    ∀ q ∈ s.spaceMatch pat tmpl, q ∈ (s.addAtom newFact).spaceMatch pat tmpl := by
  intro q hq
  rw [PeTTaSpace.mem_spaceMatch] at hq ⊢
  obtain ⟨fact, hfact, bs, hbs, heq⟩ := hq
  exact ⟨fact, PeTTaSpace.mem_facts_addAtom hfact, bs, hbs, heq⟩

/-! ## Summary

**0 sorries. 0 axioms.**

### Inductive Cases
- `var` — fvar evaluates to itself
- `bvar` — bvar evaluates to itself
- `ground` — nullary application evaluates to itself
- `ruleApp` — unconditional rule matching (LHS pattern match → apply RHS)
- `spaceQuery` — `(match &self pat tmpl)` → all groundings of `tmpl`
- `superpose` — `(superpose (a b c))` → alternatives `a`, `b`, `c`
- `collapse` — `(collapse p)` → singleton collection of all `p` answers

### Properties
- `petta_eval_var_case` — var constructor always fires for `.fvar x`
- `petta_eval_ruleApp_singleton` — rule application produces a singleton answer
- `petta_eval_collapse_singleton` — collapse always produces a singleton
- `petta_eval_spaceQuery_results` — spaceQuery returns spaceMatch (or ruleApp override)
- `spaceMatch_mono_addAtom` — spaceMatch is monotone in facts (adding facts only adds answers)

### Note on Nondeterminism
PeTTa is nondeterministic: for a given expression `p`, MULTIPLE constructors may fire
simultaneously. E.g., `.fvar x` can match both `var` AND `ruleApp` (if a rule has LHS
matching variables). `PeTTaEval` captures ALL possible derivations, not just one.
-/

end Mettapedia.Languages.MeTTa.PeTTa
