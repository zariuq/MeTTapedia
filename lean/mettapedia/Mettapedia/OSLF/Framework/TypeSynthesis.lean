import Mettapedia.OSLF.Framework.RewriteSystem
import Mettapedia.OSLF.Framework.DerivedModalities
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.Engine

/-!
# OSLF Type Synthesis: LanguageDef → OSLFTypeSystem

The OSLF algorithm (Meredith & Stay) mechanically generates a spatial-behavioral
type system from a rewrite system. This file implements the full pipeline:

```
LanguageDef ──→ RewriteSystem ──→ ReductionSpan ──→ OSLFTypeSystem
  (Syntax)       (sorts, terms,    (edges=reduction    (Pred, ◇, □,
                   reduction)        steps)              Galois connection)
```

## Key Insight

The Galois connection `◇ ⊣ □` is **automatic** — it follows from the generic
`derived_galois` theorem in `DerivedModalities.lean` applied to the reduction span.
No manual proof is needed for any specific language!

## Architecture

1. `langReduces` — propositional reduction from the executable engine
2. `langRewriteSystem` — wraps a LanguageDef as a RewriteSystem
3. `langSpan` — the reduction graph as a ReductionSpan
4. `langOSLF` — the full OSLFTypeSystem with proven Galois connection
5. `langNativeType` — native types as (sort, predicate) pairs

## References

- Meredith & Stay, "Operational Semantics in Logical Form" §6 (the algorithm)
- Williams & Stay, "Native Type Theory" (ACT 2021) §3
-/

namespace Mettapedia.OSLF.Framework.TypeSynthesis

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.DerivedModalities

/-! ## Step 1: Reduction Relation from Executable Engine -/

/-- The reduction relation induced by a LanguageDef.

    `langReducesUsing relEnv lang p q` holds when the generic rewrite engine can
    produce `q` from `p` in one step (including premise checks and
    congruence/subterm rewrites), using an explicit relation environment
    for `relationQuery`.

    This wraps executable `rewriteWithContextWithPremisesUsing` as a `Prop`. -/
def langReducesUsing (relEnv : RelationEnv) (lang : LanguageDef) (p q : Pattern) : Prop :=
  q ∈ rewriteWithContextWithPremisesUsing relEnv lang p

/-- Default reduction relation induced by a LanguageDef.

    `langReduces lang p q` holds when the generic rewrite engine can
    produce `q` from `p` in one step (including premise checks and
    congruence/subterm rewrites).

    This is `langReducesUsing RelationEnv.empty`. -/
def langReduces (lang : LanguageDef) (p q : Pattern) : Prop :=
  langReducesUsing RelationEnv.empty lang p q

/-! ## Step 2: RewriteSystem from LanguageDef -/

/-- Convert a LanguageDef into a RewriteSystem, parameterized by relation env.

    - **Sorts**: `String` (from `lang.types`, e.g., "Proc", "Name")
    - **procSort**: the designated process sort (typically "Proc")
    - **Term**: `Pattern` at every sort (shared AST from MeTTaIL)
    - **Reduces**: wraps the generic rewrite engine

    The `procSort` parameter specifies which sort carries the reduction relation.
    For the ρ-calculus, this is `"Proc"`. -/
def langRewriteSystemUsing (relEnv : RelationEnv) (lang : LanguageDef)
    (procSort : String := "Proc") :
    RewriteSystem where
  Sorts := String
  procSort := procSort
  Term := fun _ => Pattern
  Reduces := langReducesUsing relEnv lang

/-- Default rewrite-system wrapper using `RelationEnv.empty`. -/
def langRewriteSystem (lang : LanguageDef) (procSort : String := "Proc") :
    RewriteSystem :=
  langRewriteSystemUsing RelationEnv.empty lang procSort

/-! ## Step 3: Reduction Span -/

/-- The reduction span for a LanguageDef and relation env.

    Edges are pairs `(p, q)` witnessed by a premise-aware one-step reduction.
    This is the input to the change-of-base adjunction machinery from DerivedModalities.lean. -/
def langSpanUsing (relEnv : RelationEnv) (lang : LanguageDef) : ReductionSpan Pattern where
  Edge := { pair : Pattern × Pattern // langReducesUsing relEnv lang pair.1 pair.2 }
  source := fun e => e.val.1
  target := fun e => e.val.2

/-- Default reduction span using `RelationEnv.empty`. -/
def langSpan (lang : LanguageDef) : ReductionSpan Pattern :=
  langSpanUsing RelationEnv.empty lang

/-! ## Step 4: Modal Operators -/

/-- The step-future modal operator ◇ for a LanguageDef and relation env.

    `langDiamond lang φ p` = "p can reduce (via lang's rules) to some q satisfying φ"

    Defined via the generic derivedDiamond construction. -/
def langDiamondUsing (relEnv : RelationEnv) (lang : LanguageDef) :
    (Pattern → Prop) → (Pattern → Prop) :=
  derivedDiamond (langSpanUsing relEnv lang)

/-- Default step-future modal operator using `RelationEnv.empty`. -/
def langDiamond (lang : LanguageDef) : (Pattern → Prop) → (Pattern → Prop) :=
  langDiamondUsing RelationEnv.empty lang

/-- The step-past modal operator □ for a LanguageDef and relation env.

    `langBox lang φ p` = "all predecessors of p (via lang's rules) satisfy φ"

    Defined via the generic derivedBox construction. -/
def langBoxUsing (relEnv : RelationEnv) (lang : LanguageDef) :
    (Pattern → Prop) → (Pattern → Prop) :=
  derivedBox (langSpanUsing relEnv lang)

/-- Default step-past modal operator using `RelationEnv.empty`. -/
def langBox (lang : LanguageDef) : (Pattern → Prop) → (Pattern → Prop) :=
  langBoxUsing RelationEnv.empty lang

/-- The Galois connection ◇ ⊣ □ for any LanguageDef and relation env.

    This is an **automatic** consequence of the adjoint composition
    from DerivedModalities.lean. No manual proof needed! -/
theorem langGaloisUsing (relEnv : RelationEnv) (lang : LanguageDef) :
    GaloisConnection (langDiamondUsing relEnv lang) (langBoxUsing relEnv lang) :=
  derived_galois (langSpanUsing relEnv lang)

/-- Default Galois connection using `RelationEnv.empty`. -/
theorem langGalois (lang : LanguageDef) :
    GaloisConnection (langDiamond lang) (langBox lang) :=
  langGaloisUsing RelationEnv.empty lang

/-! ## Step 5: OSLFTypeSystem -/

/-- The diamond specification: `langDiamondUsing` computes the step-future modality. -/
theorem langDiamondUsing_spec (relEnv : RelationEnv) (lang : LanguageDef)
    (φ : Pattern → Prop) (p : Pattern) :
    langDiamondUsing relEnv lang φ p ↔ ∃ q, langReducesUsing relEnv lang p q ∧ φ q := by
  simp only [langDiamondUsing, derivedDiamond, di, pb, Function.comp, langSpanUsing]
  constructor
  · rintro ⟨⟨⟨p', q⟩, hred⟩, hp_eq, hφ⟩
    simp at hp_eq
    exact ⟨q, hp_eq ▸ hred, hφ⟩
  · rintro ⟨q, hred, hφ⟩
    exact ⟨⟨⟨p, q⟩, hred⟩, rfl, hφ⟩

/-- The default diamond specification (`RelationEnv.empty`). -/
theorem langDiamond_spec (lang : LanguageDef) (φ : Pattern → Prop) (p : Pattern) :
    langDiamond lang φ p ↔ ∃ q, langReduces lang p q ∧ φ q := by
  simpa [langDiamond, langReduces] using
    (langDiamondUsing_spec RelationEnv.empty lang φ p)

/-- The box specification: `langBoxUsing` computes the step-past modality. -/
theorem langBoxUsing_spec (relEnv : RelationEnv) (lang : LanguageDef)
    (φ : Pattern → Prop) (p : Pattern) :
    langBoxUsing relEnv lang φ p ↔ ∀ q, langReducesUsing relEnv lang q p → φ q := by
  simp only [langBoxUsing, derivedBox, ui, pb, Function.comp, langSpanUsing]
  constructor
  · intro h q hred
    exact h ⟨⟨q, p⟩, hred⟩ rfl
  · rintro h ⟨⟨q, p'⟩, hred⟩ (hp_eq : p' = p)
    subst hp_eq
    exact h q hred

/-- The default box specification (`RelationEnv.empty`). -/
theorem langBox_spec (lang : LanguageDef) (φ : Pattern → Prop) (p : Pattern) :
    langBox lang φ p ↔ ∀ q, langReduces lang q p → φ q := by
  simpa [langBox, langReduces] using
    (langBoxUsing_spec RelationEnv.empty lang φ p)

/-- The full OSLF type system generated from a LanguageDef.

    This is the **main result**: given any LanguageDef, we mechanically produce
    an OSLFTypeSystem with:
    - Predicates: `Pattern → Prop` at every sort (a Frame via Mathlib)
    - Modal operators: derived from the reduction span
    - Galois connection: **proven automatically** by adjoint composition
    - Specs: diamond and box characterized by their operational meaning -/
def langOSLF (lang : LanguageDef) (procSort : String := "Proc") :
    OSLFTypeSystem (langRewriteSystem lang procSort) where
  Pred := fun _ => Pattern → Prop
  frame := fun _ => inferInstance
  satisfies := fun t φ => φ t
  diamond := langDiamond lang
  diamond_spec := fun φ p => langDiamond_spec lang φ p
  box := langBox lang
  box_spec := fun φ p => langBox_spec lang φ p
  galois := by
    intro φ ψ
    have h := (langGalois lang) φ ψ
    simp only [Pi.le_def] at h
    exact h

/-! ## Step 6: Native Types -/

/-- A native type for a generated type system: a (sort, predicate) pair. -/
def langNativeType (lang : LanguageDef) (procSort : String := "Proc") :=
  NativeTypeOf (langOSLF lang procSort)

/-! ## Executable Tests -/

open Mettapedia.OSLF.RhoCalculus.Engine (patternToString)

instance : ToString Pattern := ⟨patternToString⟩

-- Test: langReduces on rhoCalc COMM
#eval! do
  let x := Pattern.fvar "x"
  let term : Pattern := .collection .hashBag [
    .apply "POutput" [x, .apply "PZero" []],
    .apply "PInput" [x, .lambda (.bvar 0)]
  ] none
  let reducts := rewriteWithContextWithPremises rhoCalc term
  IO.println s!"langReduces rhoCalc COMM test:"
  IO.println s!"  term: {term}"
  IO.println s!"  reducts ({reducts.length}):"
  for r in reducts do
    IO.println s!"    -> {r}"
  IO.println s!"  langReduces holds: {!reducts.isEmpty}"

-- Test: langDiamond on rhoCalc — check that diamond returns True for reducible terms
#eval! do
  let x := Pattern.fvar "x"
  let p : Pattern := .collection .hashBag [
    .apply "POutput" [x, .apply "PZero" []],
    .apply "PInput" [x, .lambda (.bvar 0)]
  ] none
  -- diamond (fun _ => True) p should be True (p can reduce to something)
  let canReduce := !(rewriteWithContextWithPremises rhoCalc p).isEmpty
  IO.println s!"langDiamond test: can {p} reduce? {canReduce}"

-- Test: langOSLF instantiation succeeds (type-checking is the test)
#check langOSLF rhoCalc
#check langGalois rhoCalc

end Mettapedia.OSLF.Framework.TypeSynthesis
