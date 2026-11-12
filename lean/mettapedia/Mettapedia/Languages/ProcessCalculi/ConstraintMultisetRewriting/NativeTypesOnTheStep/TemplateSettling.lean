import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.TemplateConversion
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.ComputableSettler

/-!
# The templating step does not depend on the representative

The template rule is closed under agreement and decided at every principal answer
(`template_iff_of_principal`), so, as for the converting step:

* read at a settled answer, the templating shapes ask each row to be typed by a template along it
  (`templatingShapes_iff_of_settled`), and postponed, to be typed in its frame
  (`templatingShapes_iff_of_postponed`);
* two settlers that both settle a firing's information give the same admission
  (`templating_admits_iff_of_both_settled`);
* on the union of the decided fragments the computable settler's templating step admits exactly what
  the semantic one's admits (`ofFamilies_templating_iff_ideal`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep

open _root_.CategoryTheory Opposite Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull (Make State Firing)
open UnificationWithLevels (InitialSolution)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L) {O : Type} [DecidableEq O] (settler : Settler levels)

omit [DecidableEq O] in
/-- **Read at a settled answer, the templating shapes ask each row to be typed by a template along
it.** -/
theorem templatingShapes_iff_of_settled {s : State rules O} {f : Firing levels s} {M : Context rules}
    {σ : M ⟶ f.helpers.frame} {initial : InitialSolution (frames levels) f.information σ}
    (verdict : settler f.information = .settled M σ initial) :
    TemplatingShapes levels settler f ↔
      f.taken.Nodup ∧ f.made.Nodup ∧ f.takes.length = f.taken.length ∧ f.reads.length = f.read.length ∧
        ∀ m ∈ f.makes, TemplatedAlong m.2 σ := by
  unfold TemplatingShapes
  by_cases typed : FrameTyped levels f
  · rw [plan_of_frameTyped levels settler typed]
    constructor
    · rintro ⟨a, b, c, d, _⟩
      exact ⟨a, b, c, d, fun m member => template_of_convertsAlong (convertsAlong_of_wellTyped (typed m member) σ)⟩
    · rintro ⟨a, b, c, d, _⟩
      exact ⟨a, b, c, d, fun m member => template_of_convertsAlong (convertsAlong_of_wellTyped (typed m member) _)⟩
  · rw [plan_of_not_frameTyped levels settler typed, verdict]
    rfl

omit [DecidableEq O] in
/-- **Postponed, the templating shapes ask each row to be typed in its frame.** -/
theorem templatingShapes_iff_of_postponed {s : State rules O} {f : Firing levels s}
    (verdict : settler f.information = .postponed) : TemplatingShapes levels settler f ↔ f.Shapes := by
  have identity : plan levels settler f = ⟨f.helpers.frame, 𝟙 _⟩ := by
    by_cases typed : FrameTyped levels f
    · exact plan_of_frameTyped levels settler typed
    · rw [plan_of_not_frameTyped levels settler typed, verdict]
      rfl
  unfold TemplatingShapes Firing.Shapes
  rw [identity]
  constructor
  · rintro ⟨a, b, c, d, rows⟩
    refine ⟨a, b, c, d, fun m member => ?_⟩
    obtain ⟨t, holds⟩ := rows m member
    have typed := t.typed_of_holds holds
    rwa [Make.reindex_id'] at typed
  · rintro ⟨a, b, c, d, rows⟩
    exact ⟨a, b, c, d, fun m member => template_of_convertsAlong (convertsAlong_of_wellTyped (rows m member) _)⟩

/-- **Postponed, the templating step admits what the present step admits.** -/
theorem templating_admits_iff_of_postponed {s : State rules O} {f : Firing levels s}
    (verdict : settler f.information = .postponed) :
    (templatingStep levels O settler).Admits f ↔ (DependentFull.step levels O).Admits f := by
  constructor
  · rintro ⟨shapes, enabled, solvable, holds⟩
    exact ⟨(templatingShapes_iff_of_postponed levels settler verdict).mp shapes, enabled, solvable, holds⟩
  · rintro ⟨shapes, enabled, solvable, holds⟩
    exact ⟨(templatingShapes_iff_of_postponed levels settler verdict).mpr shapes, enabled, solvable, holds⟩

/-- **Representative independence**: two settlers that both settle a firing's information give the
templating step the same admission. -/
theorem templating_admits_iff_of_both_settled (settler' : Settler levels) {s : State rules O}
    {f : Firing levels s} {M M' : Context rules} {σ : M ⟶ f.helpers.frame} {σ' : M' ⟶ f.helpers.frame}
    {initial : InitialSolution (frames levels) f.information σ}
    {initial' : InitialSolution (frames levels) f.information σ'}
    (verdict : settler f.information = .settled M σ initial)
    (verdict' : settler' f.information = .settled M' σ' initial') :
    (templatingStep levels O settler).Admits f ↔ (templatingStep levels O settler').Admits f := by
  have rows : ∀ m ∈ f.makes, TemplatedAlong m.2 σ ↔ TemplatedAlong m.2 σ' := by
    intro m _
    constructor
    · rintro ⟨t, holds⟩
      exact ⟨t, (template_iff_of_principal levels (principal_of_initial levels initial) t).mp holds M' σ'
        initial'.solves⟩
    · rintro ⟨t, holds⟩
      exact ⟨t, (template_iff_of_principal levels (principal_of_initial levels initial') t).mp holds M σ
        initial.solves⟩
  constructor
  · rintro ⟨shapes, enabled, solvable, holds⟩
    obtain ⟨a, b, c, d, along⟩ := (templatingShapes_iff_of_settled levels settler verdict).mp shapes
    exact ⟨(templatingShapes_iff_of_settled levels settler' verdict').mpr
      ⟨a, b, c, d, fun m member => (rows m member).mp (along m member)⟩, enabled, solvable, holds⟩
  · rintro ⟨shapes, enabled, solvable, holds⟩
    obtain ⟨a, b, c, d, along⟩ := (templatingShapes_iff_of_settled levels settler' verdict').mp shapes
    exact ⟨(templatingShapes_iff_of_settled levels settler verdict).mpr
      ⟨a, b, c, d, fun m member => (rows m member).mpr (along m member)⟩, enabled, solvable, holds⟩

/-- **On the union of the decided fragments the computable settler's templating step admits exactly
what the semantic settler's admits.** -/
theorem ofFamilies_templating_iff_ideal (families : List (Family levels)) {s : State rules O}
    {f : Firing levels s} (decided : DecidedBy levels families f.information) :
    (templatingStep levels O (Settler.ofFamilies levels families)).Admits f ↔
      (templatingStep levels O (Settler.ideal levels)).Admits f := by
  have decisive := firstDecisionAt_decisive levels decided
  cases first : firstDecisionAt levels f.information families with
  | settled M σ initial =>
      have verdict : Settler.ofFamilies levels families f.information = .settled M σ initial := by
        unfold Settler.ofFamilies
        rw [first]
        rfl
      obtain ⟨M', σ', initial', verdict'⟩ := Settler.ideal_settles levels initial
      exact templating_admits_iff_of_both_settled levels _ _ verdict verdict'
  | refuted none =>
      have verdict : Settler.ofFamilies levels families f.information = .postponed := by
        unfold Settler.ofFamilies
        rw [first]
        rfl
      have verdict' : Settler.ideal levels f.information = .postponed :=
        Verdict.eq_postponed levels
          (fun M σ initial => none (principal_of_initial levels initial).solvable) _
      exact (templating_admits_iff_of_postponed levels _ verdict).trans
        (templating_admits_iff_of_postponed levels _ verdict').symm
  | undecided =>
      rw [first] at decisive
      exact decisive.elim

end NativeTypesOnTheStep

#print axioms NativeTypesOnTheStep.templatingShapes_iff_of_settled
#print axioms NativeTypesOnTheStep.templatingShapes_iff_of_postponed
#print axioms NativeTypesOnTheStep.templating_admits_iff_of_postponed
#print axioms NativeTypesOnTheStep.templating_admits_iff_of_both_settled
#print axioms NativeTypesOnTheStep.ofFamilies_templating_iff_ideal

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
