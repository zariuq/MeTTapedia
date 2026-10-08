import Mettapedia.GSLT.Core.GSLTConstructions
import Mettapedia.GSLT.Core.UltrainfiniteTransport
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Nat

/-!
# The writer object is a GSLT; erasure is a morphism

Meredith's reversible envelope is a path-category description
(`ReversibleStep`, `EnvelopePath`).  That is not evaluator state and it is
not this file.

The GSLT *value* of history/cost is the existing `spendLift` writer: one
theory re-run on `Term × V`.  Under a total grading it is an object of the
behavioral category of GSLTs, with:

* `π` (`eraseMorphism`) — a `StepCover`, hence a `GSLT.Morphism`;
* `η` (`embedMorphism`) — a `GSLT.Morphism` that is *not* a step homomorphism
  unless every grade is the monoid unit;
* `π ∘ η = id` on the nose (Meredith Proposition 3.1);
* `η ∘ π ≠ id` on the nose, while every fibre of `π` is a single bisimilarity
  class (history is not observational).

Functoriality of the writer on *step-preserving* maps already lives on
`CostedTheory ⥤ OperationalTheory` (`spendLiftFunctor`, `eraseCost`).  It is
not an endofunctor of the behavioral category: a `GSLT.Morphism` need not
preserve steps, so it cannot be applied to grades.

Prime zoom is this object plus a lattice of coarser erasures (Mazurkiewicz,
term-key).  The evaluator still keys on `π`.  No LanguageDef.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.WriterGSLT

open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite

universe u v

/-! ## Constant total gradings -/

/-- Concatenation monoid on words. Local so it does not orphan a global
`List` instance. -/
local instance listAppendMonoid {α : Type*} : Monoid (List α) where
  mul := List.append
  mul_assoc := List.append_assoc
  one := []
  one_mul := List.nil_append
  mul_one := List.append_nil

/-- Every authentic step spends a chosen grade.  Always total: the grade does
not depend on the source or target, so equation-transport is free. -/
def constGrading (S : GSLT) {V : Type v} [Monoid V] (grade : V) :
    S.StepSpend V where
  graded := fun source target value => S.Step source target ∧ value = grade
  sound := And.left
  resp_left := by
    intro source source' target value equivalent ⟨step, valueEq⟩
    obtain ⟨target', step', targetEq⟩ := S.rewrites_resp_left equivalent step
    exact ⟨target', ⟨step', valueEq⟩, targetEq⟩
  resp_right := by
    intro source target target' value ⟨step, valueEq⟩ equivalent
    exact ⟨S.rewrites_resp_right step equivalent, valueEq⟩

theorem constGrading_total {S : GSLT} {V : Type v} [Monoid V] (grade : V) :
    (constGrading S grade).Total := by
  intro source target step
  exact ⟨grade, step, rfl⟩


/-- Neutral grading preserves every authentic step and its accumulator.
This applies to any base language, including stateful operational graphs. -/
theorem constGrading_unit_step_iff {S : GSLT} {V : Type v} [Monoid V]
    {source target : S.Term} {before after : V} :
    (S.spendLift (constGrading S (1 : V))).Step (source, before) (target, after) ↔
      S.Step source target ∧ after = before := by
  constructor
  · rintro ⟨grade, ⟨step, rfl⟩, accumulated⟩
    exact ⟨step, by simpa only [mul_one] using accumulated⟩
  · rintro ⟨step, rfl⟩
    exact ⟨1, ⟨step, rfl⟩, by simp only [mul_one]⟩


/-- Neutral grading also preserves arbitrary finite runs, not merely one
selected reduction. Observations of the base state retain their full scope. -/
theorem constGrading_unit_multiStep_iff {S : GSLT} {V : Type v} [Monoid V]
    {source target : S.Term} {before after : V} :
    (S.spendLift (constGrading S (1 : V))).MultiStep (source, before) (target, after) ↔
      S.MultiStep source target ∧ after = before := by
  constructor
  · intro path
    have project (first last : S.Term × V)
        (run : (S.spendLift (constGrading S (1 : V))).MultiStep first last) :
        S.MultiStep first.1 last.1 ∧ last.2 = first.2 := by
      refine @GSLT.MultiStep.rec (S.spendLift (constGrading S (1 : V)))
        (fun first last _ => S.MultiStep first.1 last.1 ∧ last.2 = first.2)
        ?_ ?_ first last run
      · intro state
        exact ⟨.refl _, rfl⟩
      · intro first middle last transition _ ih
        have oneStep := constGrading_unit_step_iff.mp transition
        exact ⟨.step oneStep.1 ih.1, ih.2.trans oneStep.2⟩
    exact project _ _ path
  · rintro ⟨path, equal⟩
    rw [equal]
    refine @GSLT.MultiStep.rec S
      (fun first last _ =>
        (S.spendLift (constGrading S (1 : V))).MultiStep (first, before) (last, before))
      ?_ ?_ source target path
    · intro state
      exact .refl _
    · intro first middle last transition _ ih
      exact .step (constGrading_unit_step_iff.mpr ⟨transition, rfl⟩) ih


/-- One-letter word as a grade: the free writer of “a step happened”. -/
def tickGrading (S : GSLT) : S.StepSpend (List Unit) :=
  constGrading S [()]

theorem tickGrading_total (S : GSLT) : (tickGrading S).Total :=
  constGrading_total [()]

/-- The writer object: `spendLift` of a selected grading.  This is S† as a
GSLT value.  It is not stored machine state. -/
abbrev writerGSLT {V : Type v} [Monoid V] (S : GSLT) (grading : S.StepSpend V) :
    GSLT :=
  S.spendLift grading

/-! ## Bisimilarity ignores the accumulator

When every step is graded, a writer state is bisimilar to another exactly
when the erased terms are.  Distinct histories of the same term are one
observation. -/

theorem spendLift_bisimilar_erase {S : GSLT} {V : Type v} [Monoid V]
    (grading : S.StepSpend V) (total : grading.Total)
    {source target : S.Term × V}
    (related : (S.spendLift grading).Bisimilar source target) :
    S.Bisimilar source.1 target.1 := by
  obtain ⟨relation, ⟨forward, backward⟩, initial⟩ := related
  refine
    ⟨fun left right => ∃ sourceAcc targetAcc,
        relation (left, sourceAcc) (right, targetAcc), ⟨?_, ?_⟩,
      source.2, target.2, initial⟩
  · intro left right ⟨sourceAcc, targetAcc, relatedStates⟩ next step
    obtain ⟨grade, graded⟩ := total step
    have lifted :
        (S.spendLift grading).Step (left, sourceAcc)
          (next, sourceAcc * grade) :=
      ⟨grade, graded, rfl⟩
    obtain ⟨image, imageStep, imageRelated⟩ :=
      forward relatedStates lifted
    refine ⟨image.1, GSLT.spendLift_erase_step grading imageStep,
      sourceAcc * grade, image.2, ?_⟩
    cases image
    exact imageRelated
  · intro left right ⟨sourceAcc, targetAcc, relatedStates⟩ next step
    obtain ⟨grade, graded⟩ := total step
    have lifted :
        (S.spendLift grading).Step (right, targetAcc)
          (next, targetAcc * grade) :=
      ⟨grade, graded, rfl⟩
    obtain ⟨image, imageStep, imageRelated⟩ :=
      backward relatedStates lifted
    refine ⟨image.1, GSLT.spendLift_erase_step grading imageStep,
      image.2, targetAcc * grade, ?_⟩
    cases image
    exact imageRelated

theorem spendLift_bisimilar_of_erased {S : GSLT} {V : Type v} [Monoid V]
    (grading : S.StepSpend V) (total : grading.Total)
    {source target : S.Term × V}
    (related : S.Bisimilar source.1 target.1) :
    (S.spendLift grading).Bisimilar source target := by
  obtain ⟨relation, ⟨forward, backward⟩, initial⟩ := related
  refine ⟨fun first second => relation first.1 second.1, ⟨?_, ?_⟩, initial⟩
  · intro first second relatedTerms next nextStep
    obtain ⟨grade, graded, _⟩ := nextStep
    obtain ⟨other, otherStep, otherRelated⟩ :=
      forward relatedTerms (grading.sound graded)
    obtain ⟨otherGrade, otherGraded⟩ := total otherStep
    exact ⟨(other, second.2 * otherGrade), ⟨otherGrade, otherGraded, rfl⟩,
      otherRelated⟩
  · intro first second relatedTerms next nextStep
    obtain ⟨grade, graded, _⟩ := nextStep
    obtain ⟨other, otherStep, otherRelated⟩ :=
      backward relatedTerms (grading.sound graded)
    obtain ⟨otherGrade, otherGraded⟩ := total otherStep
    exact ⟨(other, first.2 * otherGrade), ⟨otherGrade, otherGraded, rfl⟩,
      otherRelated⟩

theorem spendLift_bisimilar_iff {S : GSLT} {V : Type v} [Monoid V]
    (grading : S.StepSpend V) (total : grading.Total)
    (source target : S.Term × V) :
    (S.spendLift grading).Bisimilar source target ↔
      S.Bisimilar source.1 target.1 :=
  ⟨spendLift_bisimilar_erase grading total,
    spendLift_bisimilar_of_erased grading total⟩

/-- Distinct accumulators of one term are one bisimilarity class.  This is
the CALF non-interference law at the GSLT-morphism layer: the writer is a
GSLT, and it is observationally the base theory. -/
theorem history_not_observational {S : GSLT} {V : Type v} [Monoid V]
    (grading : S.StepSpend V) (total : grading.Total)
    (term : S.Term) (first second : V) :
    (S.spendLift grading).Bisimilar (term, first) (term, second) :=
  (spendLift_bisimilar_iff grading total (term, first) (term, second)).2
    (S.bisimilar_refl term)

/-! ## π is a cover; η is a section of π -/

/-- Erasure of the accumulator is a local step cover, hence a behavioral
morphism, once every base step is graded. -/
theorem eraseCover {S : GSLT} {V : Type v} [Monoid V]
    (grading : S.StepSpend V) (total : grading.Total) :
    StepCover (S.spendLift grading) S Prod.fst where
  mapStep := fun step => GSLT.spendLift_erase_step grading step
  liftStep := fun {sourceTerm} {targetTerm} step => by
    obtain ⟨value, lifted⟩ :=
      GSLT.spendLift_lift_step grading total step sourceTerm.2
    exact ⟨(targetTerm, value), lifted, rfl⟩

/-- `π : S† → S`, Meredith Proposition 3.1.  A morphism in the category of
GSLTs. -/
def eraseMorphism {S : GSLT} {V : Type v} [Monoid V]
    (grading : S.StepSpend V) (total : grading.Total) :
    GSLT.Morphism (S.spendLift grading) S :=
  (eraseCover grading total).toMorphism

/-- `η : S → S†`, Meredith Proposition 3.1.  Bisimilarity-preserving because
the writer is observationally the base; not a step homomorphism in general
(the successor of `η t` records a grade, while `η t'` has empty spend). -/
def embedMorphism {S : GSLT} {V : Type v} [Monoid V]
    (grading : S.StepSpend V) (total : grading.Total) :
    GSLT.Morphism S (S.spendLift grading) where
  toFun := fun term => (term, 1)
  preserves_bisim := fun related =>
    spendLift_bisimilar_of_erased grading total related

/-- `π ∘ η = id`. -/
theorem erase_comp_embed {S : GSLT} {V : Type v} [Monoid V]
    (grading : S.StepSpend V) (total : grading.Total) :
    GSLT.Morphism.comp (eraseMorphism grading total)
        (embedMorphism grading total) =
      GSLT.Morphism.id S := by
  apply GSLT.Morphism.ext
  rfl

/-- Embedding lands on the monoid unit of the accumulator. -/
theorem embed_toFun {S : GSLT} {V : Type v} [Monoid V]
    (grading : S.StepSpend V) (total : grading.Total) (term : S.Term) :
    (embedMorphism grading total).toFun term = (term, 1) :=
  rfl

/-- Erasure is first projection. -/
theorem erase_toFun {S : GSLT} {V : Type v} [Monoid V]
    (grading : S.StepSpend V) (total : grading.Total)
    (state : S.Term × V) :
    (eraseMorphism grading total).toFun state = state.1 :=
  rfl

/-! ## Canary: a one-step bit -/

def bitFlip : GSLT where
  Term := Bool
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => source = false ∧ target = true
  rewrites_resp_left := by
    rintro source source' target rfl step
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    rintro source target target' step rfl
    exact step

def bitSpend : bitFlip.StepSpend (List Unit) := tickGrading bitFlip

theorem bitSpend_total : bitSpend.Total := tickGrading_total bitFlip

theorem bit_step : bitFlip.Step false true :=
  ⟨rfl, rfl⟩

/-- `η` does not send steps to steps: the successor records a tick, the
image of the successor does not. -/
theorem embed_not_step_hom :
    ¬ (bitFlip.spendLift bitSpend).Step
        ((embedMorphism bitSpend bitSpend_total).toFun false)
        ((embedMorphism bitSpend bitSpend_total).toFun true) := by
  rintro ⟨grade, ⟨_, gradeEq⟩, accumulated⟩
  subst gradeEq
  simp at accumulated
  exact List.cons_ne_nil () [] accumulated.symm

/-- Consequently `η` is not a local step cover. -/
theorem embed_not_cover :
    ¬ Nonempty
        (StepCover bitFlip (bitFlip.spendLift bitSpend)
          (embedMorphism bitSpend bitSpend_total).toFun) := by
  rintro ⟨cover⟩
  exact embed_not_step_hom (cover.mapStep bit_step)

/-- `η ∘ π ≠ id` as morphisms: a nonempty spend is sent to the unit. -/
theorem embed_comp_erase_ne_id :
    GSLT.Morphism.comp (embedMorphism bitSpend bitSpend_total)
        (eraseMorphism bitSpend bitSpend_total) ≠
      GSLT.Morphism.id (bitFlip.spendLift bitSpend) := by
  intro equal
  have h := congrFun (congrArg GSLT.Morphism.toFun equal) (false, [()])
  -- left: `(false, [])`; right: `(false, [()])`.
  exact List.cons_ne_nil _ _ (congrArg Prod.snd h).symm

/-- The nonempty spend of `false` is still bisimilar to the unit spend. -/
theorem bit_history_not_observational :
    (bitFlip.spendLift bitSpend).Bisimilar (false, []) (false, [()]) :=
  history_not_observational bitSpend bitSpend_total false [] [()]

theorem bit_erase_comp_embed :
    GSLT.Morphism.comp (eraseMorphism bitSpend bitSpend_total)
        (embedMorphism bitSpend bitSpend_total) =
      GSLT.Morphism.id bitFlip :=
  erase_comp_embed bitSpend bitSpend_total

/-- `π` really is a cover: the unique bit-step lifts from every spend. -/
theorem bit_erase_lifts :
    ∃ state, (bitFlip.spendLift bitSpend).Step (false, []) state ∧
      (eraseMorphism bitSpend bitSpend_total).toFun state = true := by
  obtain ⟨value, lifted⟩ :=
    GSLT.spendLift_lift_step bitSpend bitSpend_total bit_step []
  exact ⟨(true, value), lifted, rfl⟩

#print axioms spendLift_bisimilar_iff
#print axioms erase_comp_embed
#print axioms history_not_observational
#print axioms embed_not_step_hom
#print axioms embed_not_cover
#print axioms embed_comp_erase_ne_id
#print axioms bit_history_not_observational
#print axioms bit_erase_comp_embed
#print axioms bit_erase_lifts

end Mettapedia.GSLT.WriterGSLT
