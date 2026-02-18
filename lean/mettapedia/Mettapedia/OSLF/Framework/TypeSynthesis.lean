import Mettapedia.OSLF.Framework.RewriteSystem
import Mettapedia.OSLF.Framework.DerivedModalities
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.MeTTaIL.DeclReducesWithPremises
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

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
open Mettapedia.OSLF.MeTTaIL.DeclReducesWithPremises
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

/-! ## Step 1: Reduction Relation from Executable Engine -/

/-- Executable one-step reduction induced by a `LanguageDef`.

    This keeps the computational path available for model checking and extraction. -/
def langReducesExecUsing (relEnv : RelationEnv) (lang : LanguageDef) (p q : Pattern) : Prop :=
  q ∈ rewriteWithContextWithPremisesUsing relEnv lang p

/-- Declarative/internal one-step reduction induced by a `LanguageDef`.

    This is the primary semantics used by the OSLF synthesis layer:
    a premise-aware declarative relation (internal/propositional), not direct
    list-membership in the executable reducer.

    The executable path is bridged by
    `langReducesUsing_iff_execUsing`. -/
def langReducesUsing (relEnv : RelationEnv) (lang : LanguageDef) (p q : Pattern) : Prop :=
  DeclReducesWithPremises relEnv lang p q

/-- Soundness/completeness bridge: declarative/internal and executable
    premise-aware one-step reduction coincide. -/
theorem langReducesUsing_iff_execUsing (relEnv : RelationEnv) (lang : LanguageDef)
    (p q : Pattern) :
    langReducesUsing relEnv lang p q ↔ langReducesExecUsing relEnv lang p q := by
  simpa [langReducesUsing, langReducesExecUsing] using
    (declReducesWithPremises_iff_langReducesWithPremisesUsing
      (relEnv := relEnv) (lang := lang) (p := p) (q := q))

/-- Declarative/internal reduction implies executable reduction. -/
theorem langReducesUsing_to_exec (relEnv : RelationEnv) (lang : LanguageDef)
    {p q : Pattern} :
    langReducesUsing relEnv lang p q → langReducesExecUsing relEnv lang p q :=
  (langReducesUsing_iff_execUsing relEnv lang p q).1

/-- Executable reduction implies declarative/internal reduction. -/
theorem exec_to_langReducesUsing (relEnv : RelationEnv) (lang : LanguageDef)
    {p q : Pattern} :
    langReducesExecUsing relEnv lang p q → langReducesUsing relEnv lang p q :=
  (langReducesUsing_iff_execUsing relEnv lang p q).2

/-- Default declarative/internal reduction relation induced by a `LanguageDef`.

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

/-! ## ρ Empty-Bag Irreducibility (OSLF Operational Level)

These lemmas capture irreducibility at the level actually used by the OSLF
pipeline (`langReduces`/`langReducesUsing`), i.e. the premise-aware executable
engine bridged to declarative semantics.
-/

/-- Executable one-step rewrite on the empty ρ-process bag yields no reducts. -/
theorem rhoCalc_emptyBag_rewrite_nil :
    rewriteWithContextWithPremisesUsing RelationEnv.empty rhoCalc
      (.collection .hashBag [] none) = [] := by
  native_decide

/-- No one-step `langReduces` successor exists from the empty ρ-process bag. -/
theorem rhoCalc_emptyBag_langReduces_irreducible (q : Pattern) :
    ¬ langReduces rhoCalc (.collection .hashBag [] none) q := by
  intro hred
  have hmem :
      q ∈ rewriteWithContextWithPremisesUsing RelationEnv.empty rhoCalc
        (.collection .hashBag [] none) :=
    langReducesUsing_to_exec (relEnv := RelationEnv.empty) (lang := rhoCalc) hred
  simp [rhoCalc_emptyBag_rewrite_nil] at hmem

/-- Concrete restricted bridge instance (assumption-free):
    whenever a `langReduces` step is known to come from the specialized
    executable ρ stepper (`reduceStep`), it is propositionally sound. -/
theorem rhoCalc_soundBridge_restricted
    {p q : Pattern}
    (_hred : langReduces rhoCalc p q)
    (hstep : q ∈ Mettapedia.Languages.ProcessCalculi.RhoCalculus.Engine.reduceStep p) :
    Nonempty (p ⇝ q) := by
  exact Mettapedia.Languages.ProcessCalculi.RhoCalculus.Engine.reduceStep_sound p q _ hstep

/-- SC-empty representatives have no specialized one-step ρ reducts. -/
theorem rhoCalc_SC_emptyBag_reduceStep_irreducible
    {p q : Pattern}
    (hsc : Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
      (.collection .hashBag [] none) p) :
    ¬ q ∈ Mettapedia.Languages.ProcessCalculi.RhoCalculus.Engine.reduceStep p := by
  intro hstep
  exact emptyBag_SC_irreducible hsc
    (Mettapedia.Languages.ProcessCalculi.RhoCalculus.Engine.reduceStep_sound p q _ hstep).some

/-- Direct contradiction form at `langReduces` call sites, using the
    specialized-step restricted bridge. -/
theorem rhoCalc_SC_emptyBag_langReduces_false_of_reduceStep
    {p q : Pattern}
    (hsc : Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
      (.collection .hashBag [] none) p)
    (hred : langReduces rhoCalc p q)
    (hstep : q ∈ Mettapedia.Languages.ProcessCalculi.RhoCalculus.Engine.reduceStep p) :
    False := by
  have hρ : Nonempty (p ⇝ q) := rhoCalc_soundBridge_restricted hred hstep
  exact emptyBag_SC_irreducible hsc hρ.some

/-- SC-empty irreducibility lifted to `langReduces`, given a sound bridge
    from the generated ρ-language reduction to propositional `Reduces`.

    This theorem is intentionally bridge-parameterized: it connects the
    SC-quotiented metatheory result (`emptyBag_SC_irreducible`) to the OSLF
    generated path without hard-coding a specific engine-agreement proof here. -/
theorem rhoCalc_SC_emptyBag_langReduces_irreducible_of_soundBridge
    (soundBridge :
      ∀ {p q : Pattern}, langReduces rhoCalc p q → Nonempty (p ⇝ q))
    {p q : Pattern}
    (hsc : Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
      (.collection .hashBag [] none) p) :
    ¬ langReduces rhoCalc p q := by
  intro hred
  rcases soundBridge hred with ⟨hρ⟩
  exact emptyBag_SC_irreducible hsc hρ

/-- OSLF-modal corollary of SC-empty irreducibility: no `◇⊤` at SC-empty
    representatives, under the same sound bridge assumption. -/
theorem rhoCalc_SC_emptyBag_no_diamondTop_of_soundBridge
    (soundBridge :
      ∀ {p q : Pattern}, langReduces rhoCalc p q → Nonempty (p ⇝ q))
    {p : Pattern}
    (hsc : Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
      (.collection .hashBag [] none) p) :
    ¬ langDiamond rhoCalc (fun _ => True) p := by
  intro hdia
  rcases (langDiamond_spec (lang := rhoCalc) (φ := fun _ => True) (p := p)).1 hdia with
    ⟨q, hred, _⟩
  exact (rhoCalc_SC_emptyBag_langReduces_irreducible_of_soundBridge soundBridge hsc) hred

/-! ## Canonical vs Extension Policy Witness

`rhoCalc` is canonical (bag-only congruence contexts), while `rhoCalcSetExt`
optionally enables set-context congruence descent.
-/

/-- A concrete set-context DROP witness used to compare canonical vs extension
    one-step semantics. -/
def rhoSetDropWitness : Pattern :=
  .collection .hashSet [.apply "PDrop" [.apply "NQuote" [.apply "PZero" []]]] none

/-- Canonical one-step normal-form target for `rhoSetDropWitness` under set-context DROP. -/
def rhoSetDropWitnessNF : Pattern :=
  .collection .hashSet [.apply "PZero" []] none

/-- In canonical `rhoCalc`, set-context congruence descent is blocked. -/
theorem rhoSetDropWitness_exec_nil_canonical :
    rewriteWithContextWithPremisesUsing RelationEnv.empty rhoCalc rhoSetDropWitness = [] := by
  native_decide

/-- Corollary: canonical `rhoCalc` has no one-step `langReduces` successor from
    the set-context DROP witness. -/
theorem rhoSetDropWitness_no_langReduces_canonical (q : Pattern) :
    ¬ langReduces rhoCalc rhoSetDropWitness q := by
  intro hred
  have hmem :
      q ∈ rewriteWithContextWithPremisesUsing RelationEnv.empty rhoCalc rhoSetDropWitness :=
    langReducesUsing_to_exec (relEnv := RelationEnv.empty) (lang := rhoCalc) hred
  simp [rhoSetDropWitness_exec_nil_canonical] at hmem

/-- In `rhoCalcSetExt`, the concrete set-context DROP step is executable. -/
theorem rhoSetDropWitness_exec_mem_setExt :
    rhoSetDropWitnessNF ∈
      rewriteWithContextWithPremisesUsing RelationEnv.empty rhoCalcSetExt rhoSetDropWitness := by
  native_decide

/-- Corollary: `rhoCalcSetExt` admits the corresponding one-step `langReduces`. -/
theorem rhoSetDropWitness_langReduces_setExt :
    langReduces rhoCalcSetExt rhoSetDropWitness rhoSetDropWitnessNF := by
  exact exec_to_langReducesUsing (relEnv := RelationEnv.empty) (lang := rhoCalcSetExt)
    rhoSetDropWitness_exec_mem_setExt

/-- Existential form of the extension witness used in policy comparisons. -/
theorem rhoSetDropWitness_exists_langReduces_setExt :
    ∃ q, langReduces rhoCalcSetExt rhoSetDropWitness q := by
  exact ⟨rhoSetDropWitnessNF, rhoSetDropWitness_langReduces_setExt⟩

/-- Named theorem-level comparison: canonical blocks set descent, extension allows it. -/
theorem rhoSetDropWitness_canonical_vs_setExt :
    (∀ q, ¬ langReduces rhoCalc rhoSetDropWitness q) ∧
      (∃ q, langReduces rhoCalcSetExt rhoSetDropWitness q) := by
  constructor
  · intro q
    exact rhoSetDropWitness_no_langReduces_canonical q
  · exact rhoSetDropWitness_exists_langReduces_setExt

/-! ## Executable Tests -/

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Engine (patternToString)

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

-- Test: rhoCalc congruence policy blocks Vec-context descent.
#eval! do
  let p : Pattern :=
    .collection .vec [.apply "PDrop" [.apply "NQuote" [.apply "PZero" []]]] none
  let reducts := rewriteWithContextWithPremises rhoCalc p
  IO.println s!"langReduces rhoCalc Vec-context policy test:"
  IO.println s!"  term: {p}"
  IO.println s!"  reducts ({reducts.length}): {reducts}"

-- Test: canonical rhoCalc vs optional rhoCalcSetExt on set-context descent.
#eval! do
  let pSet : Pattern :=
    .collection .hashSet [.apply "PDrop" [.apply "NQuote" [.apply "PZero" []]]] none
  let reductsCanonical := rewriteWithContextWithPremises rhoCalc pSet
  let reductsSetExt := rewriteWithContextWithPremises rhoCalcSetExt pSet
  IO.println s!"rhoCalc set-context comparison:"
  IO.println s!"  term: {pSet}"
  IO.println s!"  canonical rhoCalc reducts ({reductsCanonical.length}): {reductsCanonical}"
  IO.println s!"  rhoCalcSetExt reducts ({reductsSetExt.length}): {reductsSetExt}"

-- Test: langOSLF instantiation succeeds (type-checking is the test)
#check langOSLF rhoCalc
#check langGalois rhoCalc

end Mettapedia.OSLF.Framework.TypeSynthesis
