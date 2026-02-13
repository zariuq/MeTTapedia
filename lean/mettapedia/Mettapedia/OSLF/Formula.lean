import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.RhoCalculus.Engine
import Mettapedia.OSLF.RhoCalculus.Reduction
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.CategoryBridge
import Mettapedia.OSLF.Framework.ToposReduction

/-!
# OSLF Formula Language + Verified Bounded Model Checker

The "output artifact" of the OSLF algorithm: a formula language for writing
behavioral properties of terms, together with an executable bounded model
checker and a proven-sound denotational semantics.

## Architecture

```
OSLFFormula (data)           -- behavioral property language
    |
    ├── sem : Formula → Pattern → Prop    (denotational semantics)
    │     connects to langDiamond/langBox from TypeSynthesis.lean
    |
    └── check : Formula → Pattern → CheckResult  (executable checker)
          proven sound: check = .sat → sem holds
```

## Formula Language

- `top`, `bot` — trivially true/false
- `atom a` — named atomic predicate (interpretation provided separately)
- `and φ ψ`, `or φ ψ`, `imp φ ψ` — Boolean connectives
- `dia φ` — step-future ◇: "can step to a state satisfying φ"
- `box φ` — step-past □: "all predecessors satisfy φ"

## Three-Valued Checker

The checker uses three-valued logic because:
- `box` (step-past) requires enumerating predecessors (not computable from a
  forward step function), so it returns `.unknown`
- `imp` is conservative: only returns `.sat` when the consequent is provably `.sat`
  (because checker `.unsat` doesn't imply semantic falsity)

Soundness: `check = .sat → sem` (proven generically).

## References

- Meredith & Stay, "Operational Semantics in Logical Form" §4, §6
- Williams & Stay, "Native Type Theory" (ACT 2021)
-/

namespace Mettapedia.OSLF.Formula

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.RhoCalculus.Reduction
open Mettapedia.OSLF.RhoCalculus.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis

/-! ## Formula AST -/

/-- Behavioral property formulas for OSLF type systems.

    This is the "output artifact" of the OSLF algorithm: a concrete formula
    language for expressing behavioral properties of terms in any `LanguageDef`.

    Atomic predicates are named strings; their interpretation is provided
    separately via `AtomSem` (for proofs) or `AtomCheck` (for checking). -/
inductive OSLFFormula where
  | top : OSLFFormula
  | bot : OSLFFormula
  | atom : String → OSLFFormula
  | and : OSLFFormula → OSLFFormula → OSLFFormula
  | or : OSLFFormula → OSLFFormula → OSLFFormula
  | imp : OSLFFormula → OSLFFormula → OSLFFormula
  | dia : OSLFFormula → OSLFFormula
  | box : OSLFFormula → OSLFFormula
  deriving DecidableEq, Repr, BEq

namespace OSLFFormula

/-- Negation: ¬φ ≡ φ → ⊥ -/
abbrev neg (φ : OSLFFormula) : OSLFFormula := .imp φ .bot

partial def toStr : OSLFFormula → String
  | .top => "⊤"
  | .bot => "⊥"
  | .atom a => a
  | .and φ ψ => "(" ++ toStr φ ++ " ∧ " ++ toStr ψ ++ ")"
  | .or φ ψ => "(" ++ toStr φ ++ " ∨ " ++ toStr ψ ++ ")"
  | .imp φ ψ => "(" ++ toStr φ ++ " → " ++ toStr ψ ++ ")"
  | .dia φ => "◇" ++ toStr φ
  | .box φ => "□" ++ toStr φ

instance : ToString OSLFFormula := ⟨toStr⟩

end OSLFFormula

/-! ## Denotational Semantics -/

/-- Semantic interpretation of atomic predicates: maps names to Prop-valued predicates. -/
abbrev AtomSem := String → Pattern → Prop

/-- Denotational semantics of OSLF formulas.

    Interprets a formula as a `Pattern → Prop` predicate, given:
    - `R : Pattern → Pattern → Prop` — the reduction relation
    - `I : AtomSem` — interpretation of atomic predicates

    The modal operators match the OSLF paper:
    - `◇ φ` (dia) = step-future: ∃ q, p ⇝ q ∧ φ(q)
    - `□ φ` (box) = step-past: ∀ q, q ⇝ p → φ(q)
-/
def sem (R : Pattern → Pattern → Prop) (I : AtomSem) :
    OSLFFormula → Pattern → Prop
  | .top, _ => True
  | .bot, _ => False
  | .atom a, p => I a p
  | .and φ ψ, p => sem R I φ p ∧ sem R I ψ p
  | .or φ ψ, p => sem R I φ p ∨ sem R I ψ p
  | .imp φ ψ, p => sem R I φ p → sem R I ψ p
  | .dia φ, p => ∃ q, R p q ∧ sem R I φ q
  | .box φ, p => ∀ q, R q p → sem R I φ q

/-! ## Connection to OSLF Framework

We show that `sem` of modal formulas equals `langDiamond`/`langBox`
from TypeSynthesis.lean. This connects the formula language to the
existing categorical OSLF infrastructure. -/

/-- `sem` of `◇ φ` equals `langDiamond` applied to `sem φ`.

    This follows from the definitions: both compute
    `fun p => ∃ q, langReduces lang p q ∧ (sem ... φ) q`. -/
theorem sem_dia_eq_langDiamond (lang : LanguageDef) (I : AtomSem) (φ : OSLFFormula) :
    sem (langReduces lang) I (.dia φ) = langDiamond lang (sem (langReduces lang) I φ) := by
  ext p
  simp only [sem]
  rw [langDiamond_spec]

/-- `sem` of `◇ φ` equals `langDiamondUsing` for an explicit relation env. -/
theorem sem_dia_eq_langDiamondUsing (relEnv : RelationEnv) (lang : LanguageDef)
    (I : AtomSem) (φ : OSLFFormula) :
    sem (langReducesUsing relEnv lang) I (.dia φ) =
      langDiamondUsing relEnv lang (sem (langReducesUsing relEnv lang) I φ) := by
  ext p
  simp only [sem]
  rw [langDiamondUsing_spec]

/-- `sem` of `□ φ` equals `langBox` applied to `sem φ`. -/
theorem sem_box_eq_langBox (lang : LanguageDef) (I : AtomSem) (φ : OSLFFormula) :
    sem (langReduces lang) I (.box φ) = langBox lang (sem (langReduces lang) I φ) := by
  ext p
  simp only [sem]
  rw [langBox_spec]

/-- `sem` of `□ φ` equals `langBoxUsing` for an explicit relation env. -/
theorem sem_box_eq_langBoxUsing (relEnv : RelationEnv) (lang : LanguageDef)
    (I : AtomSem) (φ : OSLFFormula) :
    sem (langReducesUsing relEnv lang) I (.box φ) =
      langBoxUsing relEnv lang (sem (langReducesUsing relEnv lang) I φ) := by
  ext p
  simp only [sem]
  rw [langBoxUsing_spec]

/-- Formula-layer `◇` interpreted directly over the internal reduction graph.

This routes formula semantics through the presheaf graph object
(`reductionGraphUsing`) rather than only the binary relation presentation. -/
theorem sem_dia_eq_graphStepUsing
    (C : Type _) [CategoryTheory.Category C]
    (relEnv : RelationEnv) (lang : LanguageDef)
    (I : AtomSem) (φ : OSLFFormula) {X : Opposite C} :
    sem (langReducesUsing relEnv lang) I (.dia φ) =
      (fun p =>
        ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := C) relEnv lang).Edge.obj X,
          ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
            (C := C) relEnv lang).source.app X e).down = p ∧
          sem (langReducesUsing relEnv lang) I φ
            (((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
              (C := C) relEnv lang).target.app X e).down)) := by
  funext p
  rw [sem_dia_eq_langDiamondUsing]
  simpa using
    (Mettapedia.OSLF.Framework.ToposReduction.langDiamondUsing_iff_exists_graphStep
      (C := C) (relEnv := relEnv) (lang := lang) (X := X)
      (φ := sem (langReducesUsing relEnv lang) I φ) (p := p))

/-- Formula-layer `□` interpreted directly over incoming internal graph edges.

This routes box semantics through the presheaf reduction graph object
(`reductionGraphUsing`) instead of only the binary relation presentation. -/
theorem sem_box_eq_graphIncomingUsing
    (C : Type _) [CategoryTheory.Category C]
    (relEnv : RelationEnv) (lang : LanguageDef)
    (I : AtomSem) (φ : OSLFFormula) {X : Opposite C} :
    sem (langReducesUsing relEnv lang) I (.box φ) =
      (fun p =>
        ∀ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := C) relEnv lang).Edge.obj X,
          ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
            (C := C) relEnv lang).target.app X e).down = p →
          sem (langReducesUsing relEnv lang) I φ
            (((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
              (C := C) relEnv lang).source.app X e).down)) := by
  funext p
  rw [sem_box_eq_langBoxUsing]
  simpa using
    (Mettapedia.OSLF.Framework.ToposReduction.langBoxUsing_iff_forall_graphIncoming
      (C := C) (relEnv := relEnv) (lang := lang) (X := X)
      (φ := sem (langReducesUsing relEnv lang) I φ) (p := p))

/-- Formula-layer `□` semantics over a packaged `ReductionGraphObj`.

This is the reusable graph-object form, independent of the concrete
`reductionGraphUsing` construction. -/
theorem sem_box_eq_graphObjIncomingUsing
    (C : Type _) [CategoryTheory.Category C]
    (relEnv : RelationEnv) (lang : LanguageDef)
    (G : Mettapedia.OSLF.Framework.ToposReduction.ReductionGraphObj C relEnv lang)
    (I : AtomSem) (φ : OSLFFormula) {X : Opposite C} :
    sem (langReducesUsing relEnv lang) I (.box φ) =
      (fun p =>
        ∀ e : G.Edge.obj X,
          (G.target.app X e).down = p →
          sem (langReducesUsing relEnv lang) I φ
            ((G.source.app X e).down)) := by
  funext p
  rw [sem_box_eq_langBoxUsing]
  exact propext <|
    (Mettapedia.OSLF.Framework.ToposReduction.langBoxUsing_iff_forall_graphObjIncoming
      (C := C) (relEnv := relEnv) (lang := lang) (G := G) (X := X)
      (φ := sem (langReducesUsing relEnv lang) I φ) (p := p))

/-- Default-env wrapper for graph-form `□` formula semantics. -/
theorem sem_box_eq_graphIncoming
    (C : Type _) [CategoryTheory.Category C]
    (lang : LanguageDef)
    (I : AtomSem) (φ : OSLFFormula) {X : Opposite C} :
    sem (langReduces lang) I (.box φ) =
      (fun p =>
        ∀ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraph
          (C := C) lang).Edge.obj X,
          ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraph
            (C := C) lang).target.app X e).down = p →
          sem (langReduces lang) I φ
            (((Mettapedia.OSLF.Framework.ToposReduction.reductionGraph
              (C := C) lang).source.app X e).down)) := by
  simpa [langReduces, Mettapedia.OSLF.Framework.ToposReduction.reductionGraph] using
    (sem_box_eq_graphIncomingUsing (C := C) (relEnv := RelationEnv.empty)
      (lang := lang) (I := I) (φ := φ) (X := X))

/-- The formula-level Galois connection follows from the framework.

    Since `sem (.dia φ) = langDiamond (sem φ)` and `sem (.box φ) = langBox (sem φ)`,
    the Galois connection `langGalois` lifts directly to formulas. -/
theorem formula_galois (lang : LanguageDef) (I : AtomSem) (φ ψ : OSLFFormula) :
    (∀ p, sem (langReduces lang) I (.dia φ) p → sem (langReduces lang) I ψ p) ↔
    (∀ p, sem (langReduces lang) I φ p → sem (langReduces lang) I (.box ψ) p) := by
  rw [sem_dia_eq_langDiamond, sem_box_eq_langBox]
  have hg := langGalois lang
  exact hg (sem (langReduces lang) I φ) (sem (langReduces lang) I ψ)

/-- Formula-level Galois connection for explicit relation env. -/
theorem formula_galoisUsing (relEnv : RelationEnv) (lang : LanguageDef)
    (I : AtomSem) (φ ψ : OSLFFormula) :
    (∀ p, sem (langReducesUsing relEnv lang) I (.dia φ) p →
      sem (langReducesUsing relEnv lang) I ψ p) ↔
    (∀ p, sem (langReducesUsing relEnv lang) I φ p →
      sem (langReducesUsing relEnv lang) I (.box ψ) p) := by
  rw [sem_dia_eq_langDiamondUsing, sem_box_eq_langBoxUsing]
  have hg := langGaloisUsing relEnv lang
  exact hg (sem (langReducesUsing relEnv lang) I φ)
    (sem (langReducesUsing relEnv lang) I ψ)

/-- SC-empty representatives are unsatisfiable for `◇⊤` over the specialized
    executable ρ one-step relation (`reduceStep`). -/
theorem rhoCalc_SC_empty_sem_diaTop_unsat_reduceStep
    (I : AtomSem) {p : Pattern}
    (hsc : Mettapedia.OSLF.RhoCalculus.StructuralCongruence
      (.collection .hashBag [] none) p) :
    ¬ sem (fun a b => b ∈ reduceStep a) I (.dia .top) p := by
  intro hsem
  rcases hsem with ⟨q, hstep, _⟩
  exact (rhoCalc_SC_emptyBag_reduceStep_irreducible (hsc := hsc) (q := q)) hstep

/-- SC-empty representatives are unsatisfiable for generated `langReduces`
    `◇⊤`, provided a restricted executable-path witness from `langReduces`
    into the specialized stepper. -/
theorem rhoCalc_SC_empty_sem_diaTop_unsat_langReduces_of_reduceStep
    (I : AtomSem) {p : Pattern}
    (hsc : Mettapedia.OSLF.RhoCalculus.StructuralCongruence
      (.collection .hashBag [] none) p)
    (hToStep : ∀ {q : Pattern}, langReduces rhoCalc p q → q ∈ reduceStep p) :
    ¬ sem (langReduces rhoCalc) I (.dia .top) p := by
  intro hsem
  rcases hsem with ⟨q, hred, _⟩
  have hstep : q ∈ reduceStep p := hToStep hred
  exact (rhoCalc_SC_emptyBag_reduceStep_irreducible (hsc := hsc) (q := q)) hstep

/-! ## Bounded Model Checker -/

/-- Result of checking a formula against a term. -/
inductive CheckResult where
  | sat     : CheckResult
  | unsat   : CheckResult
  | unknown : CheckResult
  deriving DecidableEq, Repr, BEq

instance : ToString CheckResult where
  toString
    | .sat => "sat"
    | .unsat => "unsat"
    | .unknown => "unknown"

/-- Decidable interpretation of atomic predicates for the checker. -/
abbrev AtomCheck := String → Pattern → Bool

/-- Aggregate check results for disjunctive (◇) checking.

    Given a list of check results from checking φ on each successor:
    - If any is `.sat`, return `.sat` (witness found)
    - If all are `.unsat`, return `.unsat` (no witness possible)
    - Otherwise return `.unknown` -/
def aggregateDia : List CheckResult → CheckResult
  | [] => .unsat
  | .sat :: _ => .sat
  | .unsat :: rest => aggregateDia rest
  | .unknown :: rest =>
    match aggregateDia rest with
    | .sat => .sat
    | _ => .unknown

/-- Bounded model checker for OSLF formulas.

    Evaluates whether a term `p` satisfies a formula `φ` using:
    - `step`: forward step function producing successors
    - `I`: decidable atomic predicate checker
    - `fuel`: depth bound (decremented on every recursive call)

    Returns `.sat` / `.unsat` / `.unknown`.

    **Soundness**: when `check` returns `.sat`, the denotational semantics `sem`
    holds (proven in `check_sat_sound`).

    **Design**: `fuel` decreases on EVERY recursive call (not just `dia`) to
    keep the termination argument simple. With `fuel = 100`, formulas with up to
    ~50 nesting levels work fine.

    **Limitations**:
    - `box` always returns `.unknown` (step-past □ requires enumerating predecessors)
    - `imp` only returns `.sat` when the consequent is `.sat` (conservative but sound) -/
def check (step : Pattern → List Pattern) (I : AtomCheck)
    (fuel : Nat) (p : Pattern) (φ : OSLFFormula) : CheckResult :=
  match fuel with
  | 0 => .unknown
  | fuel + 1 =>
    match φ with
    | .top => .sat
    | .bot => .unsat
    | .atom a => if I a p then .sat else .unsat
    | .and φ₁ φ₂ =>
      match check step I fuel p φ₁, check step I fuel p φ₂ with
      | .sat, .sat => .sat
      | .unsat, _ => .unsat
      | _, .unsat => .unsat
      | _, _ => .unknown
    | .or φ₁ φ₂ =>
      match check step I fuel p φ₁, check step I fuel p φ₂ with
      | .sat, _ => .sat
      | _, .sat => .sat
      | .unsat, .unsat => .unsat
      | _, _ => .unknown
    | .imp _ φ₂ =>
      -- Sound: only return .sat when the consequent is provably .sat.
      -- (.unsat from checker doesn't guarantee ¬sem, so can't use vacuous truth)
      match check step I fuel p φ₂ with
      | .sat => .sat
      | _ => .unknown
    | .dia φ' =>
      aggregateDia ((step p).map fun q => check step I fuel q φ')
    | .box _ => .unknown

/-- Formula checker entrypoint bound to a `LanguageDef` and explicit relation env. -/
def checkLangUsing (relEnv : RelationEnv) (lang : LanguageDef) (I : AtomCheck)
    (fuel : Nat) (p : Pattern) (φ : OSLFFormula) : CheckResult :=
  check (rewriteWithContextWithPremisesUsing relEnv lang) I fuel p φ

/-- Formula checker entrypoint bound to a `LanguageDef` (default env). -/
def checkLang (lang : LanguageDef) (I : AtomCheck)
    (fuel : Nat) (p : Pattern) (φ : OSLFFormula) : CheckResult :=
  checkLangUsing RelationEnv.empty lang I fuel p φ

/-! ## Soundness -/

/-- `aggregateDia` returning `.sat` means some input element is `.sat`. -/
theorem aggregateDia_sat {results : List CheckResult}
    (h : aggregateDia results = .sat) :
    ∃ r ∈ results, r = CheckResult.sat := by
  induction results with
  | nil => simp [aggregateDia] at h
  | cons hd tl ih =>
    cases hd with
    | sat => exact ⟨.sat, List.mem_cons_self, rfl⟩
    | unsat =>
      -- aggregateDia (.unsat :: tl) = aggregateDia tl
      simp only [aggregateDia] at h
      obtain ⟨r, hr, heq⟩ := ih h
      exact ⟨r, List.mem_cons_of_mem _ hr, heq⟩
    | unknown =>
      -- aggregateDia (.unknown :: tl) = match aggregateDia tl with | .sat => .sat | _ => .unknown
      have hagg : aggregateDia tl = .sat := by
        simp only [aggregateDia] at h
        cases htl : aggregateDia tl with
        | sat => rfl
        | unsat => rw [htl] at h; simp at h
        | unknown => rw [htl] at h; simp at h
      obtain ⟨r, hr, heq⟩ := ih hagg
      exact ⟨r, List.mem_cons_of_mem _ hr, heq⟩

/-- Helper: if `check` returns `.sat` at a decreased fuel level,
    and the result is in a mapped list, we can extract the witness. -/
private theorem check_sat_of_map {step : Pattern → List Pattern}
    {I : AtomCheck} {fuel : Nat} {φ : OSLFFormula}
    {succs : List Pattern} {r : CheckResult}
    (hr_mem : r ∈ succs.map (fun q => check step I fuel q φ))
    (hr_sat : r = CheckResult.sat) :
    ∃ q ∈ succs, check step I fuel q φ = .sat := by
  rw [List.mem_map] at hr_mem
  obtain ⟨q, hq_mem, hq_eq⟩ := hr_mem
  exact ⟨q, hq_mem, hr_sat ▸ hq_eq⟩

/-- Soundness of the bounded model checker.

    If `check` returns `.sat`, then the denotational semantics `sem` holds.

    **Hypotheses**:
    - `h_atoms`: atom checker is sound w.r.t. atom semantics
    - `h_step`: step function is sound w.r.t. reduction relation R

    The proof proceeds by induction on `fuel`. -/
theorem check_sat_sound
    {R : Pattern → Pattern → Prop}
    {step : Pattern → List Pattern}
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    (h_step : ∀ p q, q ∈ step p → R p q)
    {fuel : Nat} {p : Pattern} {φ : OSLFFormula}
    (h : check step I_check fuel p φ = .sat) :
    sem R I_sem φ p := by
  induction fuel generalizing p φ with
  | zero => simp [check] at h
  | succ n ih =>
    cases φ with
    | top => exact trivial
    | bot => simp [check] at h
    | atom a =>
      unfold check at h
      simp at h
      exact h_atoms a p h
    | and φ₁ φ₂ =>
      simp only [sem]
      have hand : check step I_check n p φ₁ = .sat ∧ check step I_check n p φ₂ = .sat := by
        simp only [check] at h; revert h; split <;> intro h <;> simp_all
      exact ⟨ih hand.1, ih hand.2⟩
    | or φ₁ φ₂ =>
      simp only [sem]
      have hor : check step I_check n p φ₁ = .sat ∨ check step I_check n p φ₂ = .sat := by
        simp only [check] at h; revert h; split <;> intro h <;> simp_all
      cases hor with
      | inl h₁ => exact Or.inl (ih h₁)
      | inr h₂ => exact Or.inr (ih h₂)
    | imp φ₁ φ₂ =>
      simp only [sem]
      have hφ₂ : check step I_check n p φ₂ = .sat := by
        simp only [check] at h; revert h; split <;> intro h <;> simp_all
      intro _
      exact ih hφ₂
    | dia φ' =>
      unfold check at h
      simp only [sem]
      obtain ⟨r, hr_mem, hr_sat⟩ := aggregateDia_sat h
      obtain ⟨q, hq_mem, hq_check⟩ := check_sat_of_map hr_mem hr_sat
      exact ⟨q, h_step p q hq_mem, ih hq_check⟩
    | box _ =>
      simp [check] at h

/-- Soundness of `checkLangUsing` with explicit relation env. -/
theorem checkLangUsing_sat_sound
    {relEnv : RelationEnv} {lang : LanguageDef}
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    {fuel : Nat} {p : Pattern} {φ : OSLFFormula}
    (h : checkLangUsing relEnv lang I_check fuel p φ = .sat) :
    sem (langReducesUsing relEnv lang) I_sem φ p := by
  apply (check_sat_sound (R := langReducesUsing relEnv lang)
      (step := rewriteWithContextWithPremisesUsing relEnv lang)
      (I_check := I_check) (I_sem := I_sem) h_atoms)
  · intro p q hq
    exact exec_to_langReducesUsing relEnv lang hq
  · exact h

/-- Proc-fiber corollary for checker soundness on `rhoCalc`.

When `checkLangUsing` establishes formula satisfaction at a concrete process
state `p`, any representable arrow whose semantic action yields `p` is a member
of the corresponding executable `Pattern → Prop`-induced Proc fiber. -/
theorem checkLangUsing_sat_sound_sort_fiber
    {relEnv : RelationEnv} {lang : LanguageDef}
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    {fuel : Nat} {p : Pattern} {φf : OSLFFormula}
    (hSat : checkLangUsing relEnv lang I_check fuel p φf = .sat)
    (s : Mettapedia.OSLF.Framework.ConstructorCategory.LangSort lang)
    (seed : Pattern)
    (hNat :
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
        lang s seed (sem (langReducesUsing relEnv lang) I_sem φf))
    {X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)}
    (hArrow :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s).obj X)
    (hp : Mettapedia.OSLF.Framework.ConstructorCategory.pathSem lang hArrow seed = p) :
    hArrow ∈
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred
        lang s
        seed (sem (langReducesUsing relEnv lang) I_sem φf) hNat).obj X := by
  have hsem : sem (langReducesUsing relEnv lang) I_sem φf p :=
    checkLangUsing_sat_sound (relEnv := relEnv) (lang := lang)
      (I_check := I_check) (I_sem := I_sem) h_atoms hSat
  change sem (langReducesUsing relEnv lang) I_sem φf
      (Mettapedia.OSLF.Framework.ConstructorCategory.pathSem lang hArrow seed)
  simpa [hp] using hsem

/-- Generic `satisfies` corollary from checker soundness through
`languageSortFiber_ofPatternPred` membership equivalence. -/
theorem checkLangUsing_sat_sound_sort_fiber_mem_iff
    {relEnv : RelationEnv} {lang : LanguageDef}
    (procSort : String := "Proc")
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    {fuel : Nat} {p : Pattern} {φf : OSLFFormula}
    (hSat : checkLangUsing relEnv lang I_check fuel p φf = .sat)
    (s : Mettapedia.OSLF.Framework.ConstructorCategory.LangSort lang)
    (seed : Pattern)
    (hNat :
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
        lang s seed (sem (langReducesUsing relEnv lang) I_sem φf))
    {X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj lang)}
    (hArrow :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        lang s).obj X)
    (hp : Mettapedia.OSLF.Framework.ConstructorCategory.pathSem lang hArrow seed = p) :
    (langOSLF lang procSort).satisfies (S := s.val)
      (Mettapedia.OSLF.Framework.ConstructorCategory.pathSem lang hArrow seed)
      (sem (langReducesUsing relEnv lang) I_sem φf) := by
  have hmem :
      hArrow ∈
        (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred
          lang s
          seed (sem (langReducesUsing relEnv lang) I_sem φf) hNat).obj X :=
    checkLangUsing_sat_sound_sort_fiber
      (relEnv := relEnv) (lang := lang)
      (I_check := I_check) (I_sem := I_sem)
      h_atoms hSat s seed hNat hArrow hp
  exact
    (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred_mem_iff_satisfies
      (lang := lang) (procSort := procSort)
      (s := s) (seed := seed)
      (φ := sem (langReducesUsing relEnv lang) I_sem φf)
      (hNat := hNat) (h := hArrow)).1 hmem

/-- Proc-fiber corollary for checker soundness on `rhoCalc`.

When `checkLangUsing` establishes formula satisfaction at a concrete process
state `p`, any representable arrow whose semantic action yields `p` is a member
of the corresponding executable `Pattern → Prop`-induced Proc fiber. -/
theorem checkLangUsing_sat_sound_proc_fiber
    {relEnv : RelationEnv}
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    {fuel : Nat} {p : Pattern} {φf : OSLFFormula}
    (hSat : checkLangUsing relEnv rhoCalc I_check fuel p φf = .sat)
    (seed : Pattern)
    (hNat :
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
        rhoCalc Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
        seed (sem (langReducesUsing relEnv rhoCalc) I_sem φf))
    {X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj rhoCalc)}
    (hArrow :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        rhoCalc Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc).obj X)
    (hp : Mettapedia.OSLF.Framework.ConstructorCategory.pathSem rhoCalc hArrow seed = p) :
    hArrow ∈
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred
        rhoCalc Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
        seed (sem (langReducesUsing relEnv rhoCalc) I_sem φf) hNat).obj X := by
  simpa using
    (checkLangUsing_sat_sound_sort_fiber
      (relEnv := relEnv) (lang := rhoCalc)
      (I_check := I_check) (I_sem := I_sem)
      h_atoms hSat
      Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
      seed hNat hArrow hp)

/-- Interface-selected Proc-fiber corollary.

This is the same checker soundness-to-fiber statement as
`checkLangUsing_sat_sound_proc_fiber`, but routed through the
`oslf_fibrationUsing` Proc predicate bridge into canonical representable fibers.
-/
theorem checkLangUsing_sat_sound_proc_fiber_using
    {relEnv : RelationEnv}
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    {fuel : Nat} {p : Pattern} {φf : OSLFFormula}
    (hSat : checkLangUsing relEnv rhoCalc I_check fuel p φf = .sat)
    (seed : Pattern)
    (hNat :
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
        rhoCalc Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
        seed (sem (langReducesUsing relEnv rhoCalc) I_sem φf))
    {X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj rhoCalc)}
    (hArrow :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        rhoCalc Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc).obj X)
    (hp : Mettapedia.OSLF.Framework.ConstructorCategory.pathSem rhoCalc hArrow seed = p) :
    hArrow ∈
      (Mettapedia.OSLF.Framework.CategoryBridge.rhoProcOSLFUsingPred_to_languageSortFiber
        seed (φ := sem (langReducesUsing relEnv rhoCalc) I_sem φf) hNat).obj X := by
  simpa [Mettapedia.OSLF.Framework.CategoryBridge.rhoProcOSLFUsingPred_to_languageSortFiber] using
    (checkLangUsing_sat_sound_proc_fiber
      (relEnv := relEnv) (I_check := I_check) (I_sem := I_sem)
      h_atoms hSat seed hNat hArrow hp)

/-- Direct `satisfies` corollary from checker soundness through the
interface-selected Proc-fiber bridge membership equivalence. -/
theorem checkLangUsing_sat_sound_proc_fiber_using_mem_iff
    {relEnv : RelationEnv}
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    {fuel : Nat} {p : Pattern} {φf : OSLFFormula}
    (hSat : checkLangUsing relEnv rhoCalc I_check fuel p φf = .sat)
    (seed : Pattern)
    (hNat :
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
        rhoCalc Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
        seed (sem (langReducesUsing relEnv rhoCalc) I_sem φf))
    {X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj rhoCalc)}
    (hArrow :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        rhoCalc Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc).obj X)
    (hp : Mettapedia.OSLF.Framework.ConstructorCategory.pathSem rhoCalc hArrow seed = p) :
    (langOSLF rhoCalc "Proc").satisfies (S := "Proc")
      (Mettapedia.OSLF.Framework.ConstructorCategory.pathSem rhoCalc hArrow seed)
      (sem (langReducesUsing relEnv rhoCalc) I_sem φf) := by
  have hmem :
      hArrow ∈
        (Mettapedia.OSLF.Framework.CategoryBridge.rhoProcOSLFUsingPred_to_languageSortFiber
          seed (φ := sem (langReducesUsing relEnv rhoCalc) I_sem φf) hNat).obj X :=
    checkLangUsing_sat_sound_proc_fiber_using
      (relEnv := relEnv) (I_check := I_check) (I_sem := I_sem)
      h_atoms hSat seed hNat hArrow hp
  exact
    (Mettapedia.OSLF.Framework.CategoryBridge.rhoProcOSLFUsingPred_to_languageSortFiber_mem_iff
      (seed := seed) (φ := sem (langReducesUsing relEnv rhoCalc) I_sem φf)
      (hNat := hNat) (h := hArrow)).1 hmem

/-- Default-env wrapper of `checkLangUsing_sat_sound_proc_fiber`. -/
theorem checkLang_sat_sound_proc_fiber
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    {fuel : Nat} {p : Pattern} {φf : OSLFFormula}
    (hSat : checkLang rhoCalc I_check fuel p φf = .sat)
    (seed : Pattern)
    (hNat :
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
        rhoCalc Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
        seed (sem (langReduces rhoCalc) I_sem φf))
    {X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj rhoCalc)}
    (hArrow :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        rhoCalc Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc).obj X)
    (hp : Mettapedia.OSLF.Framework.ConstructorCategory.pathSem rhoCalc hArrow seed = p) :
    hArrow ∈
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortFiber_ofPatternPred
        rhoCalc Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
        seed (sem (langReduces rhoCalc) I_sem φf) hNat).obj X := by
  simpa [checkLang, checkLangUsing, langReduces] using
    (checkLangUsing_sat_sound_proc_fiber
      (relEnv := RelationEnv.empty) (I_check := I_check) (I_sem := I_sem)
      h_atoms hSat seed hNat hArrow hp)

/-- Default-env wrapper of `checkLangUsing_sat_sound_proc_fiber_using`. -/
theorem checkLang_sat_sound_proc_fiber_using
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    {fuel : Nat} {p : Pattern} {φf : OSLFFormula}
    (hSat : checkLang rhoCalc I_check fuel p φf = .sat)
    (seed : Pattern)
    (hNat :
      Mettapedia.OSLF.Framework.CategoryBridge.languageSortPredNaturality
        rhoCalc Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc
        seed (sem (langReduces rhoCalc) I_sem φf))
    {X : Opposite (Mettapedia.OSLF.Framework.ConstructorCategory.ConstructorObj rhoCalc)}
    (hArrow :
      (Mettapedia.OSLF.Framework.CategoryBridge.languageSortRepresentableObj
        rhoCalc Mettapedia.OSLF.Framework.ConstructorCategory.rhoProc).obj X)
    (hp : Mettapedia.OSLF.Framework.ConstructorCategory.pathSem rhoCalc hArrow seed = p) :
    hArrow ∈
      (Mettapedia.OSLF.Framework.CategoryBridge.rhoProcOSLFUsingPred_to_languageSortFiber
        seed (φ := sem (langReduces rhoCalc) I_sem φf) hNat).obj X := by
  simpa [checkLang, checkLangUsing, langReduces] using
    (checkLangUsing_sat_sound_proc_fiber_using
      (relEnv := RelationEnv.empty) (I_check := I_check) (I_sem := I_sem)
      h_atoms hSat seed hNat hArrow hp)

/-- Checker soundness corollary in graph form for `◇` formulas.

If `checkLangUsing` proves `.dia φ` as `sat`, then we get an explicit
internal reduction edge witness in the presheaf graph semantics. -/
theorem checkLangUsing_sat_sound_graph
    (C : Type _) [CategoryTheory.Category C]
    {relEnv : RelationEnv} {lang : LanguageDef}
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    {fuel : Nat} {p : Pattern} {φ : OSLFFormula} {X : Opposite C}
    (h : checkLangUsing relEnv lang I_check fuel p (.dia φ) = .sat) :
    ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
      (C := C) relEnv lang).Edge.obj X,
      ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := C) relEnv lang).source.app X e).down = p ∧
      sem (langReducesUsing relEnv lang) I_sem φ
        (((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := C) relEnv lang).target.app X e).down) := by
  have hsem : sem (langReducesUsing relEnv lang) I_sem (.dia φ) p :=
    checkLangUsing_sat_sound (relEnv := relEnv) (lang := lang)
      (I_check := I_check) (I_sem := I_sem) h_atoms h
  have hgraph :
      (fun p =>
        ∃ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := C) relEnv lang).Edge.obj X,
          ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
            (C := C) relEnv lang).source.app X e).down = p ∧
          sem (langReducesUsing relEnv lang) I_sem φ
            (((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
              (C := C) relEnv lang).target.app X e).down)) p := by
    simpa [sem_dia_eq_graphStepUsing (C := C) (relEnv := relEnv) (lang := lang)
      (I := I_sem) (φ := φ) (X := X)] using hsem
  exact hgraph

/-- Checker soundness corollary in graph form for `□` formulas.

If `checkLangUsing` proves `.box φ` as `sat`, then every incoming internal
reduction edge into `p` has source satisfying `φ`. -/
theorem checkLangUsing_sat_sound_graph_box
    (C : Type _) [CategoryTheory.Category C]
    {relEnv : RelationEnv} {lang : LanguageDef}
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    {fuel : Nat} {p : Pattern} {φ : OSLFFormula} {X : Opposite C}
    (h : checkLangUsing relEnv lang I_check fuel p (.box φ) = .sat) :
    ∀ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
      (C := C) relEnv lang).Edge.obj X,
      ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := C) relEnv lang).target.app X e).down = p →
      sem (langReducesUsing relEnv lang) I_sem φ
        (((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := C) relEnv lang).source.app X e).down) := by
  have hsem : sem (langReducesUsing relEnv lang) I_sem (.box φ) p :=
    checkLangUsing_sat_sound (relEnv := relEnv) (lang := lang)
      (I_check := I_check) (I_sem := I_sem) h_atoms h
  have hgraph :
      (fun p =>
        ∀ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := C) relEnv lang).Edge.obj X,
          ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
            (C := C) relEnv lang).target.app X e).down = p →
          sem (langReducesUsing relEnv lang) I_sem φ
            (((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
              (C := C) relEnv lang).source.app X e).down)) p := by
    simpa [sem_box_eq_graphIncomingUsing (C := C) (relEnv := relEnv) (lang := lang)
      (I := I_sem) (φ := φ) (X := X)] using hsem
  exact hgraph

/-- Soundness of `checkLang` (default env). -/
theorem checkLang_sat_sound
    {lang : LanguageDef}
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    {fuel : Nat} {p : Pattern} {φ : OSLFFormula}
    (h : checkLang lang I_check fuel p φ = .sat) :
    sem (langReduces lang) I_sem φ p := by
  simpa [checkLang, checkLangUsing, langReduces] using
    (checkLangUsing_sat_sound (relEnv := RelationEnv.empty)
      (lang := lang) (I_check := I_check) (I_sem := I_sem) h_atoms h)

/-! ## Enhanced Checker with Bounded Box

The base `check` always returns `.unknown` for `box`. When a predecessor
function is available, we can check `box φ` by verifying `φ` on all
predecessors. This is **proven sound** when the predecessor function is
complete (returns ALL predecessors). -/

/-- Aggregate check results for conjunctive (□) checking.

    Given a list of check results from checking φ on each predecessor:
    - If all are `.sat`, return `.sat` (all predecessors satisfy φ)
    - If any is `.sat` is missing and we see `.unknown`/`.unsat`, return `.unknown`
      (checker `.unsat` doesn't guarantee ¬sem, so we can't return `.unsat`) -/
def aggregateBox : List CheckResult → CheckResult
  | [] => .sat
  | .sat :: rest => aggregateBox rest
  | _ :: _ => .unknown

/-- `aggregateBox` returning `.sat` means every input element is `.sat`. -/
theorem aggregateBox_sat {results : List CheckResult}
    (h : aggregateBox results = .sat) :
    ∀ r ∈ results, r = CheckResult.sat := by
  induction results with
  | nil => intro r hr; simp at hr
  | cons hd tl ih =>
    intro r hr
    cases hd with
    | sat =>
      simp only [aggregateBox] at h
      rcases List.mem_cons.mp hr with rfl | hmem
      · rfl
      · exact ih h r hmem
    | unsat => simp [aggregateBox] at h
    | unknown => simp [aggregateBox] at h

/-- Enhanced model checker that can handle `box` when predecessors are available.

    Parameters:
    - `step`: forward step function producing successors
    - `pred`: backward step function producing predecessors
    - `I`: decidable atomic predicate checker
    - `fuel`: depth bound

    Compared to `check`, this handles `box φ` by checking φ on all predecessors.
    Falls back to the base `check` for all other cases. -/
def checkWithPred (step : Pattern → List Pattern) (pred : Pattern → List Pattern)
    (I : AtomCheck) (fuel : Nat) (p : Pattern) (φ : OSLFFormula) : CheckResult :=
  match fuel with
  | 0 => .unknown
  | fuel + 1 =>
    match φ with
    | .top => .sat
    | .bot => .unsat
    | .atom a => if I a p then .sat else .unsat
    | .and φ₁ φ₂ =>
      match checkWithPred step pred I fuel p φ₁,
            checkWithPred step pred I fuel p φ₂ with
      | .sat, .sat => .sat
      | .unsat, _ => .unsat
      | _, .unsat => .unsat
      | _, _ => .unknown
    | .or φ₁ φ₂ =>
      match checkWithPred step pred I fuel p φ₁,
            checkWithPred step pred I fuel p φ₂ with
      | .sat, _ => .sat
      | _, .sat => .sat
      | .unsat, .unsat => .unsat
      | _, _ => .unknown
    | .imp _ φ₂ =>
      match checkWithPred step pred I fuel p φ₂ with
      | .sat => .sat
      | _ => .unknown
    | .dia φ' =>
      aggregateDia ((step p).map fun q => checkWithPred step pred I fuel q φ')
    | .box φ' =>
      aggregateBox ((pred p).map fun q => checkWithPred step pred I fuel q φ')

/-- Soundness of the enhanced checker.

    If `checkWithPred` returns `.sat`, then the denotational semantics holds.

    **Hypotheses**:
    - `h_atoms`: atom checker is sound w.r.t. atom semantics
    - `h_step`: step function is sound w.r.t. R (forward)
    - `h_pred`: predecessor function is complete w.r.t. R (all predecessors are listed) -/
theorem checkWithPred_sat_sound
    {R : Pattern → Pattern → Prop}
    {step : Pattern → List Pattern}
    {pred : Pattern → List Pattern}
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    (h_step : ∀ p q, q ∈ step p → R p q)
    (h_pred : ∀ p q, R q p → q ∈ pred p)
    {fuel : Nat} {p : Pattern} {φ : OSLFFormula}
    (h : checkWithPred step pred I_check fuel p φ = .sat) :
    sem R I_sem φ p := by
  induction fuel generalizing p φ with
  | zero => simp [checkWithPred] at h
  | succ n ih =>
    cases φ with
    | top => exact trivial
    | bot => simp [checkWithPred] at h
    | atom a =>
      unfold checkWithPred at h
      simp at h
      exact h_atoms a p h
    | and φ₁ φ₂ =>
      simp only [sem]
      have hand : checkWithPred step pred I_check n p φ₁ = .sat ∧
                  checkWithPred step pred I_check n p φ₂ = .sat := by
        simp only [checkWithPred] at h; revert h; split <;> intro h <;> simp_all
      exact ⟨ih hand.1, ih hand.2⟩
    | or φ₁ φ₂ =>
      simp only [sem]
      have hor : checkWithPred step pred I_check n p φ₁ = .sat ∨
                 checkWithPred step pred I_check n p φ₂ = .sat := by
        simp only [checkWithPred] at h; revert h; split <;> intro h <;> simp_all
      cases hor with
      | inl h₁ => exact Or.inl (ih h₁)
      | inr h₂ => exact Or.inr (ih h₂)
    | imp φ₁ φ₂ =>
      simp only [sem]
      have hφ₂ : checkWithPred step pred I_check n p φ₂ = .sat := by
        simp only [checkWithPred] at h; revert h; split <;> intro h <;> simp_all
      intro _
      exact ih hφ₂
    | dia φ' =>
      unfold checkWithPred at h
      simp only [sem]
      obtain ⟨r, hr_mem, hr_sat⟩ := aggregateDia_sat h
      rw [List.mem_map] at hr_mem
      obtain ⟨q, hq_mem, hq_eq⟩ := hr_mem
      exact ⟨q, h_step p q hq_mem, ih (hr_sat ▸ hq_eq)⟩
    | box φ' =>
      unfold checkWithPred at h
      simp only [sem]
      intro q hRqp
      have hq_mem := h_pred p q hRqp
      have hall := aggregateBox_sat h
      have hq_in_map : checkWithPred step pred I_check n q φ' ∈
          (pred p).map (fun x => checkWithPred step pred I_check n x φ') := by
        rw [List.mem_map]; exact ⟨q, hq_mem, rfl⟩
      have hq_check := hall _ hq_in_map
      exact ih hq_check

/-! ## Language-Level Checker with Predecessors

These wrappers connect the executable predecessor-aware checker to language
semantics (`langReducesUsing`), enabling a non-trivial `.box` path. -/

/-- Language-level predecessor-aware checker with explicit relation environment. -/
def checkLangUsingWithPred (relEnv : RelationEnv) (lang : LanguageDef)
    (pred : Pattern → List Pattern)
    (I : AtomCheck) (fuel : Nat) (p : Pattern) (φ : OSLFFormula) : CheckResult :=
  checkWithPred (rewriteWithContextWithPremisesUsing relEnv lang ·) pred I fuel p φ

/-- Default-env predecessor-aware checker. -/
def checkLangWithPred (lang : LanguageDef)
    (pred : Pattern → List Pattern)
    (I : AtomCheck) (fuel : Nat) (p : Pattern) (φ : OSLFFormula) : CheckResult :=
  checkLangUsingWithPred RelationEnv.empty lang pred I fuel p φ

/-- Soundness of predecessor-aware checker at language level. -/
theorem checkLangUsingWithPred_sat_sound
    {relEnv : RelationEnv} {lang : LanguageDef}
    {pred : Pattern → List Pattern}
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    (h_pred_complete : ∀ p q, langReducesUsing relEnv lang q p → q ∈ pred p)
    {fuel : Nat} {p : Pattern} {φ : OSLFFormula}
    (h : checkLangUsingWithPred relEnv lang pred I_check fuel p φ = .sat) :
    sem (langReducesUsing relEnv lang) I_sem φ p := by
  simpa [checkLangUsingWithPred] using
    (checkWithPred_sat_sound
      (R := langReducesUsing relEnv lang)
      (step := rewriteWithContextWithPremisesUsing relEnv lang)
      (pred := pred)
      (I_check := I_check) (I_sem := I_sem)
      (h_atoms := h_atoms)
      (h_step := fun p q hq => exec_to_langReducesUsing relEnv lang hq)
      (h_pred := h_pred_complete)
      (h := h))

/-- Checker graph-soundness for executable `.box` via predecessor semantics.

Unlike `checkLangUsing`, this route can actually produce `.sat` for `.box`
when `pred` is complete for one-step predecessors. -/
theorem checkLangUsingWithPred_sat_sound_graph_box
    (C : Type _) [CategoryTheory.Category C]
    {relEnv : RelationEnv} {lang : LanguageDef}
    {pred : Pattern → List Pattern}
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    (h_pred_complete : ∀ p q, langReducesUsing relEnv lang q p → q ∈ pred p)
    {fuel : Nat} {p : Pattern} {φ : OSLFFormula} {X : Opposite C}
    (h : checkLangUsingWithPred relEnv lang pred I_check fuel p (.box φ) = .sat) :
    ∀ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
      (C := C) relEnv lang).Edge.obj X,
      ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
        (C := C) relEnv lang).target.app X e).down = p →
      sem (langReducesUsing relEnv lang) I_sem φ
        (((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := C) relEnv lang).source.app X e).down) := by
  have hsem : sem (langReducesUsing relEnv lang) I_sem (.box φ) p :=
    checkLangUsingWithPred_sat_sound
      (relEnv := relEnv) (lang := lang)
      (pred := pred)
      (I_check := I_check) (I_sem := I_sem)
      h_atoms h_pred_complete h
  have hgraph :
      (fun p =>
        ∀ e : (Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
          (C := C) relEnv lang).Edge.obj X,
          ((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
            (C := C) relEnv lang).target.app X e).down = p →
          sem (langReducesUsing relEnv lang) I_sem φ
            (((Mettapedia.OSLF.Framework.ToposReduction.reductionGraphUsing
              (C := C) relEnv lang).source.app X e).down)) p := by
    simpa [sem_box_eq_graphIncomingUsing (C := C) (relEnv := relEnv)
      (lang := lang) (I := I_sem) (φ := φ) (X := X)] using hsem
  exact hgraph

/-- Checker graph-soundness for executable `.dia` over a packaged graph object.

This keeps the checker-facing existence witness in the reusable
`ReductionGraphObj` abstraction. -/
theorem checkLangUsingWithPred_sat_sound_graphObj_dia
    (C : Type _) [CategoryTheory.Category C]
    {relEnv : RelationEnv} {lang : LanguageDef}
    {pred : Pattern → List Pattern}
    {I_check : AtomCheck} {I_sem : AtomSem}
    (G : Mettapedia.OSLF.Framework.ToposReduction.ReductionGraphObj C relEnv lang)
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    (h_pred_complete : ∀ p q, langReducesUsing relEnv lang q p → q ∈ pred p)
    {fuel : Nat} {p : Pattern} {φ : OSLFFormula} {X : Opposite C}
    (h : checkLangUsingWithPred relEnv lang pred I_check fuel p (.dia φ) = .sat) :
    ∃ e : G.Edge.obj X,
      (G.source.app X e).down = p ∧
      sem (langReducesUsing relEnv lang) I_sem φ ((G.target.app X e).down) := by
  have hsem : sem (langReducesUsing relEnv lang) I_sem (.dia φ) p :=
    checkLangUsingWithPred_sat_sound
      (relEnv := relEnv) (lang := lang)
      (pred := pred)
      (I_check := I_check) (I_sem := I_sem)
      h_atoms h_pred_complete h
  have hdia : langDiamondUsing relEnv lang
      (sem (langReducesUsing relEnv lang) I_sem φ) p := by
    simpa [sem_dia_eq_langDiamondUsing (relEnv := relEnv) (lang := lang)
      (I := I_sem) (φ := φ)] using hsem
  exact
    (Mettapedia.OSLF.Framework.ToposReduction.langDiamondUsing_iff_exists_graphObjStep
      (C := C) (relEnv := relEnv) (lang := lang) (G := G) (X := X)
      (φ := sem (langReducesUsing relEnv lang) I_sem φ) (p := p)).1 hdia

/-- Checker graph-soundness for executable `.box` over a packaged graph object.

This variant avoids committing to the concrete `reductionGraphUsing`; it
consumes any `ReductionGraphObj` carrying the endpoint law. -/
theorem checkLangUsingWithPred_sat_sound_graphObj_box
    (C : Type _) [CategoryTheory.Category C]
    {relEnv : RelationEnv} {lang : LanguageDef}
    {pred : Pattern → List Pattern}
    {I_check : AtomCheck} {I_sem : AtomSem}
    (G : Mettapedia.OSLF.Framework.ToposReduction.ReductionGraphObj C relEnv lang)
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    (h_pred_complete : ∀ p q, langReducesUsing relEnv lang q p → q ∈ pred p)
    {fuel : Nat} {p : Pattern} {φ : OSLFFormula} {X : Opposite C}
    (h : checkLangUsingWithPred relEnv lang pred I_check fuel p (.box φ) = .sat) :
    ∀ e : G.Edge.obj X,
      (G.target.app X e).down = p →
      sem (langReducesUsing relEnv lang) I_sem φ
        ((G.source.app X e).down) := by
  have hsem : sem (langReducesUsing relEnv lang) I_sem (.box φ) p :=
    checkLangUsingWithPred_sat_sound
      (relEnv := relEnv) (lang := lang)
      (pred := pred)
      (I_check := I_check) (I_sem := I_sem)
      h_atoms h_pred_complete h
  have hbox : langBoxUsing relEnv lang (sem (langReducesUsing relEnv lang) I_sem φ) p := by
    simpa [sem_box_eq_langBoxUsing (relEnv := relEnv) (lang := lang)
      (I := I_sem) (φ := φ)] using hsem
  exact
    (Mettapedia.OSLF.Framework.ToposReduction.langBoxUsing_iff_forall_graphObjIncoming
      (C := C) (relEnv := relEnv) (lang := lang) (G := G) (X := X)
      (φ := sem (langReducesUsing relEnv lang) I_sem φ) (p := p)).1 hbox

/-- Default-env predecessor-aware checker soundness. -/
theorem checkLangWithPred_sat_sound
    {lang : LanguageDef}
    {pred : Pattern → List Pattern}
    {I_check : AtomCheck} {I_sem : AtomSem}
    (h_atoms : ∀ a p, I_check a p = true → I_sem a p)
    (h_pred_complete : ∀ p q, langReduces lang q p → q ∈ pred p)
    {fuel : Nat} {p : Pattern} {φ : OSLFFormula}
    (h : checkLangWithPred lang pred I_check fuel p φ = .sat) :
    sem (langReduces lang) I_sem φ p := by
  simpa [checkLangWithPred, checkLangUsingWithPred, langReduces] using
    (checkLangUsingWithPred_sat_sound
      (relEnv := RelationEnv.empty) (lang := lang)
      (pred := pred) (I_check := I_check) (I_sem := I_sem)
      h_atoms h_pred_complete h)

/-! ## ρ-Calculus Instantiation -/

-- Helpers (re-using names from Engine.lean for pattern construction)
private def pzero' : Pattern := .apply "PZero" []
private def pdrop' (n : Pattern) : Pattern := .apply "PDrop" [n]
private def nquote' (p : Pattern) : Pattern := .apply "NQuote" [p]
private def poutput' (n q : Pattern) : Pattern := .apply "POutput" [n, q]
private def pinput' (n : Pattern) (_x : String) (body : Pattern) : Pattern :=
  .apply "PInput" [n, .lambda body]
private def ppar' (elems : List Pattern) : Pattern :=
  .collection .hashBag elems none

/-- ρ-calculus atomic predicate checker. -/
def rhoAtoms : AtomCheck
  | "isZero", p => p == .apply "PZero" []
  | "isOutput", p => match p with | .apply "POutput" _ => true | _ => false
  | "isInput", p => match p with | .apply "PInput" _ => true | _ => false
  | _, _ => false

/-- ρ-calculus atomic predicate semantics (matching the checker). -/
def rhoAtomSem : AtomSem
  | "isZero", p => p = .apply "PZero" []
  | "isOutput", p => ∃ args, p = .apply "POutput" args
  | "isInput", p => ∃ args, p = .apply "PInput" args
  | _, _ => False

/-- Soundness of `rhoAtoms` w.r.t. `rhoAtomSem`. -/
theorem rhoAtoms_sound : ∀ a p, rhoAtoms a p = true → rhoAtomSem a p := by
  intro a p h
  by_cases ha : a = "isZero"
  · subst ha; simp only [rhoAtoms] at h; simp only [rhoAtomSem]; exact of_decide_eq_true h
  · by_cases hb : a = "isOutput"
    · subst hb; simp only [rhoAtoms] at h; simp only [rhoAtomSem]
      split at h
      · next args => exact ⟨args, rfl⟩
      · simp at h
    · by_cases hc : a = "isInput"
      · subst hc; simp only [rhoAtoms] at h; simp only [rhoAtomSem]
        split at h
        · next args => exact ⟨args, rfl⟩
        · simp at h
      · -- a ∉ {"isZero", "isOutput", "isInput"} → rhoAtoms a p = false
        exfalso
        have hf : rhoAtoms a p = false := by unfold rhoAtoms; split <;> simp_all
        rw [hf] at h; exact absurd h (by decide)

/-! ## Executable Demos -/

-- Use patternToString for display
instance : ToString Pattern := ⟨patternToString⟩

-- Demo 1: COMM term can reduce (◇ ⊤)
#eval! do
  let x := Pattern.fvar "x"
  let term := ppar' [poutput' x pzero', pinput' x "y" (.bvar 0)]
  let result := check (reduceStep · 100) rhoAtoms 50 term (.dia .top)
  IO.println s!"Demo 1: Can {term} reduce?"
  IO.println s!"  check (◇⊤) = {result}"

-- Demo 2: 0 cannot reduce (◇ ⊤ should be unsat)
#eval! do
  let result := check (reduceStep · 100) rhoAtoms 50 pzero' (.dia .top)
  IO.println s!"Demo 2: Can 0 reduce?"
  IO.println s!"  check (◇⊤) = {result}"

-- Demo 3: *(@0) can reduce (DROP)
#eval! do
  let term := pdrop' (nquote' pzero')
  let result := check (reduceStep · 100) rhoAtoms 50 term (.dia .top)
  IO.println s!"Demo 3: Can *(@0) reduce?"
  IO.println s!"  check (◇⊤) = {result}"

-- Demo 4: *(@0) can reduce to 0 specifically
#eval! do
  let term := pdrop' (nquote' pzero')
  let result := check (reduceStep · 100) rhoAtoms 50 term (.dia (.atom "isZero"))
  IO.println s!"Demo 4: Can *(@0) reduce to 0?"
  IO.println s!"  check (◇isZero) = {result}"

-- Demo 5: conjunction — *(@0) can reduce to something that is zero AND can't reduce further
#eval! do
  let term := pdrop' (nquote' pzero')
  let φ := OSLFFormula.and (.atom "isZero") (.imp (.dia .top) .bot)
  let result := check (reduceStep · 100) rhoAtoms 50 term (.dia φ)
  IO.println s!"Demo 5: Can *(@0) reach a state that is zero?"
  IO.println s!"  check (◇(isZero ∧ (◇⊤ → ⊥))) = {result}"

-- Demo 6: Language-bound checker on rhoCalc (premise-aware default env)
#eval! do
  let x := Pattern.fvar "x"
  let term := ppar' [poutput' x pzero', pinput' x "y" (.bvar 0)]
  let result := checkLang rhoCalc rhoAtoms 50 term (.dia .top)
  IO.println s!"Demo 6: Lang checker — can COMM term reduce?"
  IO.println s!"  check (◇⊤) = {result}"

-- Demo 7: Formula display
#eval! do
  let φ : OSLFFormula := .dia (.and (.atom "isZero") (.box (.atom "isOutput")))
  IO.println s!"Demo 7: Formula display"
  IO.println s!"  {φ}"

end Mettapedia.OSLF.Formula
