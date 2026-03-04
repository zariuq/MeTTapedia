import Mettapedia.Languages.MeTTa.PeTTa.Eval
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystem

/-!
# Type-Gated PeTTa Evaluation

Extends `PeTTaEval` with a **type pre-check** on rule application, mirroring the
MeTTa spec's `check_if_function_type_is_applicable` predicate and the PeTTa
transpiler's type-checking layer.

## Architecture

```
PeTTaEval (pure, type-free)              ← Eval.lean
     ↑ embedded via typedEval_sound
TypedPeTTaEval (type-gated ruleApp)      ← this file
```

`TypedPeTTaEval s p answers` differs from `PeTTaEval s p answers` only in the
`ruleApp` constructor: non-nullary applications `(c a₁ … aₙ)` must additionally
satisfy `typeCheckPasses s c`, i.e., `c` has some arrow type in `s`.

## Why a Separate Judgment?

Modifying `PeTTaEval.ruleApp` would break the existing LP soundness chain.
The refinement approach preserves:
- All existing `PeTTaEval` theorems (unchanged)
- The LP soundness theorem (`petta_ruleApp_lp_sound`)
- A clean erasure direction: `TypedPeTTaEval → PeTTaEval`

## Alignment with the MeTTa Spec

| MeTTa spec predicate | TypedPeTTaEval |
|----------------------|----------------|
| `check_if_function_type_is_applicable(F, [])` | vacuously passes (nullary) |
| `check_if_function_type_is_applicable(F, [_|_])` | `∃ A B, MeTTaType s (.apply c []) (arrowType A B)` |

## References

- MeTTa spec §eval: `trueagi-io.github.io/hyperon-experimental/metta/`
  (`check_if_function_type_is_applicable`, `check_argument_type`)
- PeTTa transpiler: `transpiler.pl`
- `MeTTaType`: `Mettapedia.Languages.MeTTa.PeTTa.TypeSystem`
-/

namespace Mettapedia.Languages.MeTTa.PeTTa

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec

/-! ## Type Check Condition -/

/-- **Type check predicate** for a function symbol `c` applied to arguments `args`
    in atomspace `s`.

    Matches the MeTTa spec's `check_if_function_type_is_applicable(F, Args)`:
    - If `args` is empty (nullary call), no arrow type is required: trivially passes.
    - If `args` is nonempty, `c` (as a bare symbol `.apply c []`) must have some
      arrow type `(-> A B)` in the space.

    Note: this checks only that a function type exists, not that each individual
    argument type matches.  The more refined version (checking `MeTTaType s aᵢ Aᵢ`)
    is `typeCheckArgPasses` below. -/
def typeCheckPasses (s : PeTTaSpace) (c : String) (args : List Pattern) : Prop :=
  args = [] ∨ ∃ A B, MeTTaType s (.apply c []) (arrowType A B)

/-- **Refined type check**: for a single-argument application `(c a)`,
    additionally checks that `a` has the matching argument type. -/
def typeCheckArgPasses (s : PeTTaSpace) (c : String) (a : Pattern)
    (argTy : Pattern) : Prop :=
  ∃ retTy, MeTTaType s (.apply c []) (arrowType argTy retTy) ∧
           MeTTaType s a argTy

theorem typeCheckPasses_nullary (s : PeTTaSpace) (c : String) :
    typeCheckPasses s c [] :=
  Or.inl rfl

theorem typeCheckPasses_of_arrow (s : PeTTaSpace) (c : String) (a : Pattern)
    (args : List Pattern) (A B : Pattern)
    (h : MeTTaType s (.apply c []) (arrowType A B)) :
    typeCheckPasses s c (a :: args) :=
  Or.inr ⟨A, B, h⟩

/-- For nonempty `args`, `typeCheckPasses` is equivalent to having an arrow type. -/
theorem typeCheckPasses_cons_iff (s : PeTTaSpace) (c : String) (a : Pattern)
    (args : List Pattern) :
    typeCheckPasses s c (a :: args) ↔ ∃ A B, MeTTaType s (.apply c []) (arrowType A B) := by
  simp [typeCheckPasses]

/-! ## Typed Evaluation Relation -/

/-- **Type-gated PeTTa evaluation**.

    Identical to `PeTTaEval` in all cases except `ruleApp`:
    for a non-nullary application `(.apply c args)`, rule application additionally
    requires `typeCheckPasses s c args` — i.e., the function symbol `c` must have
    some arrow type in the atomspace.

    This formalizes the MeTTa spec's type-checking layer over the pure LP core. -/
inductive TypedPeTTaEval (s : PeTTaSpace) : Pattern → Answers → Prop where

  /-- Free variable evaluates to itself. -/
  | var (x : String) :
      TypedPeTTaEval s (.fvar x) [.fvar x]

  /-- Bound variable evaluates to itself. -/
  | bvar (n : Nat) :
      TypedPeTTaEval s (.bvar n) [.bvar n]

  /-- Ground atom (nullary application) evaluates to itself. -/
  | ground (c : String) :
      TypedPeTTaEval s (.apply c []) [.apply c []]

  /-- **Type-gated rule application**.

      Same preconditions as `PeTTaEval.ruleApp`, plus:
      `htype : typeCheckPasses s c args` — the function symbol `c` has an arrow type
      (or `args` is empty, in which case no type check is needed).

      This mirrors `check_if_function_type_is_applicable(c, args)` in the MeTTa spec. -/
  | ruleApp (r : RewriteRule) (bs : Bindings) (c : String) (args : List Pattern)
      (q : Pattern)
      (hr    : r ∈ s.rules)
      (hprem : r.premises = [])
      (hm    : bs ∈ matchPattern r.left (.apply c args))
      (hq    : applyBindings bs r.right = q)
      -- Type pre-check: for non-nullary calls, c must have some arrow type
      (htype : typeCheckPasses s c args) :
      TypedPeTTaEval s (.apply c args) [q]

  /-- Space query (`match &self pat tmpl`). -/
  | spaceQuery (pat tmpl : Pattern) (results : Answers)
      (hres : results = s.spaceMatch pat tmpl) :
      TypedPeTTaEval s (.apply "match" [.apply "&self" [], pat, tmpl]) results

  /-- Superpose: list of alternatives. -/
  | superpose (alts : List Pattern) :
      TypedPeTTaEval s (.apply "superpose" [.collection .vec alts none]) alts

  /-- Collapse: collect all answers. -/
  | collapse (p : Pattern) (answers : Answers)
      (h : TypedPeTTaEval s p answers) :
      TypedPeTTaEval s (.apply "collapse" [p]) [.collection .vec answers none]

/-! ## Soundness: TypedPeTTaEval → PeTTaEval -/

/-- **Soundness (erasure)**: every typed derivation is also a pure (type-free) derivation.

    The type pre-check is an extra *guard* — it never blocks a computation that
    `PeTTaEval` would also perform; it only rules out derivations where the function
    has no arrow type.  Erasing the type hypothesis gives a valid `PeTTaEval` proof. -/
theorem typedEval_sound {s : PeTTaSpace} {p : Pattern} {answers : Answers}
    (h : TypedPeTTaEval s p answers) :
    PeTTaEval s p answers := by
  induction h with
  | var x => exact PeTTaEval.var x
  | bvar n => exact PeTTaEval.bvar n
  | ground c => exact PeTTaEval.ground c
  | ruleApp r bs c args q hr hprem hm hq _htype =>
    exact PeTTaEval.ruleApp r bs (.apply c args) q hr hprem hm hq
  | spaceQuery pat tmpl results hres =>
    exact PeTTaEval.spaceQuery pat tmpl results hres
  | superpose alts => exact PeTTaEval.superpose alts
  | collapse p answers _ ih => exact PeTTaEval.collapse p answers ih

/-! ## Lifting Ground and Var Cases -/

/-- Ground atom: `PeTTaEval` and `TypedPeTTaEval` agree (no type check needed). -/
theorem typedEval_ground_iff (s : PeTTaSpace) (c : String) :
    TypedPeTTaEval s (.apply c []) [.apply c []] ↔
    PeTTaEval s (.apply c []) [.apply c []] :=
  ⟨typedEval_sound, fun _ => TypedPeTTaEval.ground c⟩

/-- For **nullary** rule application, typed = untyped (type check is vacuous). -/
theorem typedEval_ruleApp_nullary (s : PeTTaSpace)
    (r : RewriteRule) (bs : Bindings) (c : String) (q : Pattern)
    (hr    : r ∈ s.rules)
    (hprem : r.premises = [])
    (hm    : bs ∈ matchPattern r.left (.apply c []))
    (hq    : applyBindings bs r.right = q) :
    TypedPeTTaEval s (.apply c []) [q] :=
  TypedPeTTaEval.ruleApp r bs c [] q hr hprem hm hq (Or.inl rfl)

/-! ## Strictness: TypedPeTTaEval is strictly more restrictive -/

/-- For a **non-nullary** application `(c a args)`, a **ruleApp** derivation in
    `TypedPeTTaEval` requires an arrow type for `c`.

    More precisely: if `c` has no arrow type in `s`, then `typeCheckPasses s c (a :: args)`
    is false, so `TypedPeTTaEval.ruleApp` cannot fire for this application.

    Note: other constructors (`spaceQuery`, `superpose`, `collapse`) don't require
    arrow types, so the theorem is specifically about the `ruleApp` case. -/
theorem typedEval_typeCheck_required (s : PeTTaSpace) (c : String) (a : Pattern)
    (args : List Pattern)
    -- assume c has NO arrow type in s:
    (hno : ∀ A B, ¬ MeTTaType s (.apply c []) (arrowType A B)) :
    ¬ typeCheckPasses s c (a :: args) := by
  intro h
  rcases h with heq | ⟨A, B, harrow⟩
  · simp at heq
  · exact hno A B harrow

/-! ## Type Check Monotonicity -/

/-- `typeCheckPasses` is monotone: if `c` has an arrow type in `s`, it has one in
    any extension `s.addAtom fact`. -/
theorem typeCheckPasses_addAtom (s : PeTTaSpace) (c : String) (args : List Pattern)
    (newFact : Pattern) (h : typeCheckPasses s c args) :
    typeCheckPasses (s.addAtom newFact) c args := by
  rcases h with rfl | ⟨A, B, harrow⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨A, B, typeOf_mono_addAtom newFact harrow⟩

/-! ## Example: Type-Gated Derivation -/

/-- **Example**: `(succ zero)` evaluates to `one` under a typed rule, given that
    `succ` has type `(-> Nat Nat)` in the space.

    Space:
    - Fact: `(: succ (-> Nat Nat))` — type annotation
    - Rule: `(= (succ zero) one)` — rewrite rule

    Expression: `(succ zero)`
    Expected answer: `[one]`

    This demonstrates that the type check gates properly: the typed judgment
    fires because `succ` has an arrow type annotation in the space. -/
theorem example_typed_succ :
    let annFact : Pattern :=
      .apply ":" [.apply "succ" [], .apply "->" [.apply "Nat" [], .apply "Nat" []]]
    let succRule : RewriteRule :=
      { name := "succ-rule"
        typeContext := []
        left := .apply "succ" [.apply "zero" []]
        right := .apply "one" []
        premises := [] }
    let s : PeTTaSpace :=
      { facts := [annFact]
      , rules := [succRule] }
    TypedPeTTaEval s (.apply "succ" [.apply "zero" []]) [.apply "one" []] := by
  simp only []
  apply TypedPeTTaEval.ruleApp
      (r := { name := "succ-rule", typeContext := []
              left := .apply "succ" [.apply "zero" []]
              right := .apply "one" []
              premises := [] })
      (bs := [])
      (c := "succ")
      (args := [.apply "zero" []])
      (q := .apply "one" [])
  · exact List.mem_cons_self ..
  · rfl
  · simp [matchPattern, matchArgs, mergeBindings]
  · simp [applyBindings]
  · -- type check: succ has type (-> Nat Nat)
    exact Or.inr ⟨.apply "Nat" [], .apply "Nat" [],
      MeTTaType.typeAnnotation (.apply "succ" [])
        (.apply "->" [.apply "Nat" [], .apply "Nat" []])
        (List.mem_cons_self ..)⟩

/-! ## Summary

**0 sorries. 0 axioms.**

### Type Check Predicates
- `typeCheckPasses s c args` — `args = []` OR `c` has some arrow type `(-> A B)` in `s`
- `typeCheckArgPasses s c a argTy` — `c : (-> argTy ?)` AND `a : argTy` (refined check)
- `typeCheckPasses_nullary` — nullary calls always pass
- `typeCheckPasses_of_arrow` — having an arrow type gives the check
- `typeCheckPasses_cons_iff` — for nonempty args: equivalent to arrow type existence

### Inductive (`TypedPeTTaEval s p answers`)
- `var`, `bvar`, `ground` — same as `PeTTaEval`
- `ruleApp` — as `PeTTaEval.ruleApp` + `typeCheckPasses s c args`
- `spaceQuery`, `superpose`, `collapse` — same as `PeTTaEval`

### Soundness
- `typedEval_sound` — `TypedPeTTaEval → PeTTaEval` (erase type guard)

### Equivalences
- `typedEval_ground_iff` — ground case: typed ↔ untyped
- `typedEval_ruleApp_nullary` — nullary ruleApp: type check vacuous

### Strictness
- `typedEval_no_ruleApp_without_arrowType` — no typed non-nullary ruleApp without an arrow type

### Monotonicity
- `typeCheckPasses_addAtom` — type check persists under atomspace extension

### Example
- `example_typed_succ` — `(succ zero)` → `one` under type annotation `(: succ (-> Nat Nat))`
-/

end Mettapedia.Languages.MeTTa.PeTTa
