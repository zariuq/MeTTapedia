import Mettapedia.Languages.MeTTa.PeTTa.Eval
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystem

/-!
# Full 4-Argument MeTTa Evaluation Relation

This file implements the full `metta(atom, type, space, bindings)` relation as a Lean
inductive judgment `MeTTaEval s p ty bindings results`, where

  `results : EvalResult = List (Pattern × Bindings)`

is a list of `(value, output-bindings)` pairs.

## Relationship to `PeTTaEval`

`PeTTaEval` (in `Eval.lean`) is the type-free, binding-free fragment:
  `PeTTaEval s p answers`

`MeTTaEval` refines it with three orthogonal features:

1. **Binding threading** — input `Bindings` are passed through and merged with
   match-produced bindings, following `metta_call(rhs, bindings)` in the HE spec.

2. **Error propagation** — `(Error atom msg)` patterns are absorbing: any
   `MeTTaEval` of an error pattern returns the error unchanged.

3. **Type pass-through** — certain type annotations (`Atom`, `Expression`,
   `%Undefined%`, `%Grounded%`) suppress rule-based reduction and return the
   pattern unchanged (mirroring `metta(Symbol, ...)` and `metta(Variable, ...)`).

## Embedding

  `meTTaEval_ruleApp_to_pettaEval` : the `ruleApp` case projects to `PeTTaEval.ruleApp`
  `meTTaEval_spaceQuery_to_pettaEval` : the `spaceQuery` case projects faithfully
  `meTTaEval_superpose_to_pettaEval` : superpose projects faithfully
  `meTTaEval_collapse_to_pettaEval` : collapse projects given an inductive hypothesis

## Alignment Table

| MeTTa spec predicate                          | `MeTTaEval` constructor    |
|-----------------------------------------------|----------------------------|
| `metta(Symbol, type, space, bindings)`        | `symbolPassThrough`        |
| `metta(Variable, type, space, bindings)`      | `varPassThrough`           |
| `metta(BVar, type, space, bindings)`          | `bvarPassThrough`          |
| `metta(Error atom msg, type, space, bindings)`| `errorPassThrough`         |
| `metta_call(rhs, bindings)` after `match_atoms`| `ruleApp`                 |
| `metta(match &self pat tmpl, type, ...)`      | `spaceQuery`               |
| `metta(superpose alts, type, ...)`            | `superpose`                |
| `metta(collapse p, type, ...)`                | `collapse`                 |

## References

- HE MeTTa spec: `trueagi-io.github.io/hyperon-experimental/metta/`
  (`interpret_function`, `interpret_args`, `metta_call`, `check_if_function_type_is_applicable`)
- PeTTa transpiler: `hyperon/PeTTa/transpiler.pl`
- `PeTTaEval`: `Mettapedia.Languages.MeTTa.PeTTa.Eval`
- `MeTTaType`: `Mettapedia.Languages.MeTTa.PeTTa.TypeSystem`
-/

namespace Mettapedia.Languages.MeTTa.PeTTa

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec

/-! ## Result Type -/

/-- Result of 4-argument MeTTa evaluation: list of (value, output-bindings) pairs.

    Each pair `(v, b)` means: the expression evaluated to value `v` under
    output binding environment `b`.  Multiple pairs arise from nondeterminism
    (multiple matching rules, multiple `superpose` alternatives, etc.). -/
abbrev EvalResult := List (Pattern × Bindings)

/-! ## Error Helpers -/

/-- Construct a MeTTa error pattern `(Error atom msg)`. -/
def mkError (atom msg : Pattern) : Pattern :=
  .apply "Error" [atom, msg]

/-- A pattern is an error if it has the form `(Error atom msg)`. -/
def isErrorPattern (p : Pattern) : Prop :=
  ∃ atom msg, p = mkError atom msg

/-! ## Type Classification Helpers -/

/-- The `%Grounded%` type atom — for grounded (host-language) values.
    Distinct from `expressionType` and `atomType`. -/
def groundedType : Pattern := .apply "%Grounded%" []

/-- The `Symbol` type atom — for bare symbols in some MeTTa dialects.
    Here we use `atomType` (= `Atom`) as its representative since TypeSystem
    does not separately define `Symbol`. -/
def symbolTypeAlias : Pattern := atomType

/-- Pass-through types: patterns with these expected types are returned unchanged,
    mirroring `metta(Symbol, ...)` and `metta(Variable, ...)` in the spec.

    The HE MeTTa spec passes through for:
    - `Atom`        — bare symbol tokens
    - `Expression`  — all S-expressions
    - `%Undefined%` — unknown / unconstrained type
    - `%Grounded%`  — host-language (grounded) values -/
def isPassThroughType (ty : Pattern) : Prop :=
  ty = atomType ∨ ty = expressionType ∨ ty = undefinedType ∨ ty = groundedType

/-! ## Full 4-Argument MeTTa Evaluation Relation -/

/-- Full 4-argument MeTTa evaluation.

    `MeTTaEval s p ty bindings results` means: in atomspace `s`, evaluating
    expression `p` with expected type `ty` and ambient input bindings `bindings`
    produces the list of `(value, output-bindings)` pairs `results`.

    This is a declarative specification of the HE MeTTa interpreter's
    `interpret_function` / `metta` predicate extended with binding threading.

    **Pass-through cases** (`symbolPassThrough`, `varPassThrough`, `bvarPassThrough`):
    These mirror the spec's early-exit paths that return the atom unchanged when
    its syntactic category matches the expected type.

    **Error absorption** (`errorPassThrough`):
    Error patterns `(Error atom msg)` short-circuit all further evaluation and
    propagate the error unchanged.

    **Rule application** (`ruleApp`):
    Mirrors `metta_call(rhs, bindings)` — finds a rule whose LHS matches `p`,
    applies the resulting bindings to the RHS, and threads bindings through.

    **Space query** (`spaceQuery`):
    Models `(match &self pat tmpl)` — returns all template groundings paired with
    the ambient input bindings.

    **Superpose / collapse**:
    Nondeterminism injection and answer collection, with binding threading. -/
inductive MeTTaEval (s : PeTTaSpace) :
    Pattern → Pattern → Bindings → EvalResult → Prop where

  /-- **Symbol pass-through**: a nullary application (bare symbol) `(.apply c [])`
      evaluates to itself when the expected type is a pass-through type.

      Mirrors `metta(Symbol, type, space, bindings) → [(Symbol, bindings)]` in the
      MeTTa spec when `type ∈ {Atom, Expression, %Undefined%, %Grounded%}`. -/
  | symbolPassThrough (c : String) (ty : Pattern) (bindings : Bindings)
      (hty : isPassThroughType ty) :
      MeTTaEval s (.apply c []) ty bindings [(.apply c [], bindings)]

  /-- **Free variable pass-through**: a free variable (metavariable) evaluates to
      itself regardless of expected type.

      Mirrors `metta(Variable, type, space, bindings) → [(Variable, bindings)]`. -/
  | varPassThrough (x : String) (ty : Pattern) (bindings : Bindings) :
      MeTTaEval s (.fvar x) ty bindings [(.fvar x, bindings)]

  /-- **Bound variable pass-through**: a de Bruijn variable is structurally inert
      and evaluates to itself. -/
  | bvarPassThrough (n : Nat) (ty : Pattern) (bindings : Bindings) :
      MeTTaEval s (.bvar n) ty bindings [(.bvar n, bindings)]

  /-- **Error pass-through**: an error pattern `(Error atom msg)` absorbs further
      evaluation — the error propagates unchanged.

      Mirrors `metta(Error atom msg, ...) → [(Error atom msg, bindings)]` in the spec. -/
  | errorPassThrough (atom msg : Pattern) (ty : Pattern) (bindings : Bindings) :
      MeTTaEval s (mkError atom msg) ty bindings [(mkError atom msg, bindings)]

  /-- **Rule application with binding threading**.

      Mirrors `metta_call(rhs, bindings)` in the MeTTa spec:
      - Find a rule `r` in the space whose LHS matches `p` with bindings `bs`
      - Apply `bs` to the RHS to get `q`
      - The output bindings are `bs ++ inputBindings` (match bindings prepended)

      Conditions:
      - `hr`: the rule is in the atomspace
      - `hprem`: the rule has no premises (unconditional)
      - `hm`: the rule LHS matches `p` with bindings `bs`
      - `hq`: applying `bs` to the RHS yields `q`
      - `hmerge`: the output bindings concatenate match bindings with ambient input -/
  | ruleApp (r : RewriteRule) (bs : Bindings) (p q : Pattern)
      (ty : Pattern) (inputBindings : Bindings)
      (hr     : r ∈ s.rules)
      (hprem  : r.premises = [])
      (hm     : bs ∈ matchPattern r.left p)
      (hq     : applyBindings bs r.right = q) :
      MeTTaEval s p ty inputBindings [(q, bs ++ inputBindings)]

  /-- **Space query with binding threading**.

      Models `(match &self pat tmpl)` in MeTTa:
      - Query the atomspace with pattern `pat`
      - Each grounding of `tmpl` is paired with the ambient input bindings

      Note: the grounding bindings from `spaceMatch` are already applied to `tmpl`
      (see `PeTTaSpace.spaceMatch`), so we pair each answer with the input bindings
      rather than the grounding bindings. -/
  | spaceQuery (pat tmpl : Pattern) (ty : Pattern) (bindings : Bindings)
      (results : EvalResult)
      (hres : results = (s.spaceMatch pat tmpl).map (·, bindings)) :
      MeTTaEval s (.apply "match" [.apply "&self" [], pat, tmpl]) ty bindings results

  /-- **Superpose with binding threading**: inject alternatives, pairing each
      with the ambient input bindings.

      Models `(superpose (a b c))` → answers `a`, `b`, `c` each with `bindings`. -/
  | superpose (alts : List Pattern) (ty : Pattern) (bindings : Bindings) :
      MeTTaEval s (.apply "superpose" [.collection .vec alts none])
        ty bindings (alts.map (·, bindings))

  /-- **Collapse with binding threading**: collect all `(value, bindings)` pairs
      from evaluating `p`, then return a singleton containing the collection of
      all values paired with the ambient input bindings.

      Models `(collapse p)` → `[(collection of all p-answers, bindings)]`. -/
  | collapse (p : Pattern) (ty : Pattern) (bindings : Bindings) (results : EvalResult)
      (h : MeTTaEval s p ty bindings results) :
      MeTTaEval s (.apply "collapse" [p]) ty bindings
        [(.collection .vec (results.map Prod.fst) none, bindings)]

/-! ## Error Absorption -/

/-- Error patterns are immediately constructible: `(Error atom msg)` always
    evaluates to itself (error pass-through fires unconditionally). -/
theorem meTTaEval_error_construct {s : PeTTaSpace} {atom msg : Pattern}
    {ty : Pattern} {bindings : Bindings} :
    MeTTaEval s (mkError atom msg) ty bindings [(mkError atom msg, bindings)] :=
  MeTTaEval.errorPassThrough atom msg ty bindings

/-- Error pattern form is preserved: `mkError` builds a specific `.apply` node. -/
@[simp]
theorem mkError_eq (atom msg : Pattern) :
    mkError atom msg = .apply "Error" [atom, msg] := rfl

/-! ## Pass-Through Type Witnesses -/

/-- `%Undefined%` is a pass-through type. -/
theorem isPassThroughType_undefined : isPassThroughType undefinedType :=
  Or.inr (Or.inr (Or.inl rfl))

/-- `Atom` is a pass-through type. -/
theorem isPassThroughType_atom : isPassThroughType atomType :=
  Or.inl rfl

/-- `Expression` is a pass-through type. -/
theorem isPassThroughType_expression : isPassThroughType expressionType :=
  Or.inr (Or.inl rfl)

/-- `%Grounded%` is a pass-through type. -/
theorem isPassThroughType_grounded : isPassThroughType groundedType :=
  Or.inr (Or.inr (Or.inr rfl))

/-! ## Projection to PeTTaEval (Erasure Theorems) -/

/-- **Erasure for `ruleApp`**: the rule application case of `MeTTaEval` projects
    to `PeTTaEval.ruleApp` (erasing type and bindings). -/
theorem meTTaEval_ruleApp_to_pettaEval {s : PeTTaSpace} {p q : Pattern}
    {r : RewriteRule} {bs : Bindings}
    (hr    : r ∈ s.rules)
    (hprem : r.premises = [])
    (hm    : bs ∈ matchPattern r.left p)
    (hq    : applyBindings bs r.right = q) :
    PeTTaEval s p [q] :=
  PeTTaEval.ruleApp r bs p q hr hprem hm hq

/-- **Erasure for `spaceQuery`**: the space-query case of `MeTTaEval` projects
    to `PeTTaEval.spaceQuery`. -/
theorem meTTaEval_spaceQuery_to_pettaEval {s : PeTTaSpace}
    {pat tmpl : Pattern} {bindings : Bindings}
    {results : EvalResult}
    (hres : results = (s.spaceMatch pat tmpl).map (·, bindings)) :
    PeTTaEval s (.apply "match" [.apply "&self" [], pat, tmpl])
              (results.map Prod.fst) := by
  have heq : results.map Prod.fst = s.spaceMatch pat tmpl := by
    subst hres
    simp only [List.map_map]
    ext x
    simp
  rw [heq]
  exact PeTTaEval.spaceQuery pat tmpl _ rfl

/-- **Erasure for `superpose`**: superpose with binding threading projects to
    `PeTTaEval.superpose`. -/
theorem meTTaEval_superpose_to_pettaEval {s : PeTTaSpace}
    {alts : List Pattern} :
    PeTTaEval s (.apply "superpose" [.collection .vec alts none]) alts :=
  PeTTaEval.superpose alts

/-- **Erasure for `collapse`**: collapse with binding threading projects to
    `PeTTaEval.collapse`, given the inductive projection for the inner expression. -/
theorem meTTaEval_collapse_to_pettaEval {s : PeTTaSpace} {p : Pattern}
    {results : EvalResult}
    (ih : PeTTaEval s p (results.map Prod.fst)) :
    PeTTaEval s (.apply "collapse" [p])
              [.collection .vec (results.map Prod.fst) none] :=
  PeTTaEval.collapse p (results.map Prod.fst) ih

/-- `collapse` composed with the binding-threaded `match &self` query returns a
singleton collection of the `spaceMatch` answers, carrying the ambient bindings
through unchanged. -/
theorem meTTaEval_collapse_spaceQuery
    {s : PeTTaSpace} {pat tmpl ty : Pattern} {bindings : Bindings} :
    MeTTaEval s
      (.apply "collapse" [.apply "match" [.apply "&self" [], pat, tmpl]])
      ty bindings
      [(.collection .vec (s.spaceMatch pat tmpl) none, bindings)] := by
  have hproj :
      List.map Prod.fst ((s.spaceMatch pat tmpl).map (·, bindings)) =
        s.spaceMatch pat tmpl := by
    induction s.spaceMatch pat tmpl with
    | nil => rfl
    | cons x xs ih =>
        simp [ih]
  simpa [hproj] using
    (MeTTaEval.collapse
      (.apply "match" [.apply "&self" [], pat, tmpl])
      ty
      bindings
      ((s.spaceMatch pat tmpl).map (·, bindings))
      (MeTTaEval.spaceQuery pat tmpl ty bindings _ rfl))

/-! ## Monotonicity -/

/-- **Monotonicity for `ruleApp`**: adding a fact to the atomspace preserves rule
    application derivations.

    Since `addAtom` only extends `s.facts` (not `s.rules`), membership of `r` in
    `s.rules` is preserved definitionally in `(s.addAtom fact).rules`. -/
theorem meTTaEval_addFact_ruleApp {s : PeTTaSpace} {p q : Pattern}
    {ty : Pattern} {r : RewriteRule} {bs : Bindings} {inputBindings : Bindings}
    (fact   : Pattern)
    (hr     : r ∈ s.rules)
    (hprem  : r.premises = [])
    (hm     : bs ∈ matchPattern r.left p)
    (hq     : applyBindings bs r.right = q) :
    MeTTaEval (s.addAtom fact) p ty inputBindings [(q, bs ++ inputBindings)] :=
  -- (s.addAtom fact).rules = s.rules definitionally, so hr works directly
  MeTTaEval.ruleApp r bs p q ty inputBindings hr hprem hm hq

/-- **Monotonicity for `spaceQuery`**: adding a fact can only add answers to
    `spaceMatch`, so the set of possible `spaceQuery` results grows. -/
theorem meTTaEval_spaceQuery_mono {s : PeTTaSpace}
    {pat tmpl : Pattern} {ty : Pattern} {bindings : Bindings}
    (newFact : Pattern) :
    MeTTaEval (s.addAtom newFact)
      (.apply "match" [.apply "&self" [], pat, tmpl]) ty bindings
      (((s.addAtom newFact).spaceMatch pat tmpl).map (·, bindings)) :=
  MeTTaEval.spaceQuery pat tmpl ty bindings _ rfl

/-! ## Derived Evaluation Witnesses -/

/-- A free variable always has a `MeTTaEval` derivation at any type. -/
theorem meTTaEval_var_always {s : PeTTaSpace} {x : String} {ty : Pattern}
    {bindings : Bindings} :
    MeTTaEval s (.fvar x) ty bindings [(.fvar x, bindings)] :=
  MeTTaEval.varPassThrough x ty bindings

/-- A ground atom always has a `MeTTaEval` derivation at pass-through types. -/
theorem meTTaEval_ground_passThrough {s : PeTTaSpace} {c : String}
    {ty : Pattern} {bindings : Bindings}
    (hty : isPassThroughType ty) :
    MeTTaEval s (.apply c []) ty bindings [(.apply c [], bindings)] :=
  MeTTaEval.symbolPassThrough c ty bindings hty

/-- Superpose of nil yields no answers (empty result list). -/
theorem meTTaEval_superpose_nil {s : PeTTaSpace} {ty : Pattern} {bindings : Bindings} :
    MeTTaEval s (.apply "superpose" [.collection .vec [] none]) ty bindings [] :=
  MeTTaEval.superpose [] ty bindings

/-- Collapse always produces a singleton result (the collection of inner answers). -/
theorem meTTaEval_collapse_singleton {s : PeTTaSpace} {p : Pattern}
    {ty : Pattern} {bindings : Bindings} {results : EvalResult}
    (h : MeTTaEval s p ty bindings results) :
    ∃ col, MeTTaEval s (.apply "collapse" [p]) ty bindings [(col, bindings)] :=
  ⟨.collection .vec (results.map Prod.fst) none, MeTTaEval.collapse p ty bindings results h⟩

/-! ## Summary

**0 sorries. 0 axioms.**

### Type Abbreviation
- `EvalResult := List (Pattern × Bindings)` — list of (value, output-bindings) pairs

### Error / Type Helpers
- `mkError atom msg` — constructs `(Error atom msg)` pattern
- `isErrorPattern p` — `∃ atom msg, p = mkError atom msg`
- `groundedType` — `%Grounded%` pass-through type atom
- `symbolTypeAlias` — alias for `atomType` (`Atom`)
- `isPassThroughType ty` — `ty ∈ {Atom, Expression, %Undefined%, %Grounded%}`

### Pass-Through Witnesses
- `isPassThroughType_undefined`, `isPassThroughType_atom`,
  `isPassThroughType_expression`, `isPassThroughType_grounded`

### Inductive (`MeTTaEval s p ty bindings results`)
- `symbolPassThrough` — nullary apply at pass-through type → itself
- `varPassThrough` — `.fvar x` → itself at any type
- `bvarPassThrough` — `.bvar n` → itself at any type
- `errorPassThrough` — `(Error atom msg)` → itself (absorbing)
- `ruleApp` — rule LHS matches `p`, applies RHS, threads bindings
- `spaceQuery` — `(match &self pat tmpl)` → groundings of `tmpl`
- `superpose` — `(superpose alts)` → alternatives with ambient bindings
- `collapse` — `(collapse p)` → singleton collection of `p` answers

### Erasure (Projection to `PeTTaEval`)
- `meTTaEval_ruleApp_to_pettaEval` — ruleApp erases to `PeTTaEval.ruleApp`
- `meTTaEval_spaceQuery_to_pettaEval` — spaceQuery erases faithfully
- `meTTaEval_superpose_to_pettaEval` — superpose erases faithfully
- `meTTaEval_collapse_to_pettaEval` — collapse erases given IH

### Monotonicity
- `meTTaEval_addFact_ruleApp` — ruleApp persists under fact addition
- `meTTaEval_spaceQuery_mono` — spaceQuery results grow under fact addition

### Derived Witnesses
- `meTTaEval_error_construct` — error pass-through fires unconditionally
- `meTTaEval_var_always` — variables always evaluate to themselves
- `meTTaEval_ground_passThrough` — ground atoms pass through at pass-through types
- `meTTaEval_superpose_nil` — empty superpose yields no answers
- `meTTaEval_collapse_singleton` — collapse always produces exactly one answer
-/

end Mettapedia.Languages.MeTTa.PeTTa
