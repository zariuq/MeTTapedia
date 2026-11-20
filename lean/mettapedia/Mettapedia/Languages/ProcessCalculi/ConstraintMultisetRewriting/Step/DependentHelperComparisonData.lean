import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullRaceHelpers

/-!
# Helper comparisons retaining the original block projections

Existence of alike firings does not choose a helper provenance map. Here
the comparison retains both pullback legs, and its result comparison uses
that same data. This supports coherence statements even when a firing's
payload does not observe every helper.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual

variable {Head : Type} {rules : Rules Head} {Γ Δ : Context rules}
  {substitution : Δ ⟶ Γ} {original : Helpers Γ} {first second : Helpers Δ}
  {firstLeg : first.frame ⟶ original.frame} {secondLeg : second.frame ⟶ original.frame}

noncomputable def liftComparison (one : IsLift substitution original first firstLeg)
    (two : IsLift substitution original second secondLeg) :
    {comparison : first.frame ≅ second.frame //
      comparison.hom ≫ second.weaken = first.weaken ∧ comparison.hom ≫ secondLeg = firstLeg} :=
  ⟨(one.compare two).choose, (one.compare two).choose_spec⟩

variable {L : Type} [UniverseLevel.LevelOrder L] {levels : LevelModel rules L} {O : Type}

noncomputable def alikeDataOfLifts {state : State rules O} {Γ : Context rules}
    {substitution : state.frame ⟶ Γ} {original : Helpers Γ}
    {data : Natural levels O original.frame}
    {first second : HelperFiring levels O state}
    {firstLeg : first.helpers.frame ⟶ original.frame} {secondLeg : second.helpers.frame ⟶ original.frame}
    (one : IsLift substitution original first.helpers firstLeg)
    (two : IsLift substitution original second.helpers secondLeg)
    (firstData : first.data = data.move firstLeg) (secondData : second.data = data.move secondLeg) :
    AlikeData levels O first second where
  frame := (liftComparison one two).val
  commutes := (liftComparison one two).property.1
  data := by
    rw [firstData, secondData, Natural.move_comp, (liftComparison one two).property.2]

theorem alikeDataOfLifts_original {state : State rules O} {Γ : Context rules}
    {substitution : state.frame ⟶ Γ} {original : Helpers Γ}
    {data : Natural levels O original.frame}
    {first second : HelperFiring levels O state}
    {firstLeg : first.helpers.frame ⟶ original.frame} {secondLeg : second.helpers.frame ⟶ original.frame}
    (one : IsLift substitution original first.helpers firstLeg)
    (two : IsLift substitution original second.helpers secondLeg)
    (firstData : first.data = data.move firstLeg) (secondData : second.data = data.move secondLeg) :
    (alikeDataOfLifts one two firstData secondData).frame.hom ≫ secondLeg = firstLeg :=
  (liftComparison one two).property.2

namespace AlikeData

variable [DecidableEq O] {state : State rules O} {first second : HelperFiring levels O state}

def resultComparison (comparison : AlikeData levels O first second)
    (accepted : (helperStep levels O).Admits first) (accepted' : (helperStep levels O).Admits second) :
    PlainIso levels ((helperStep levels O).result first accepted) ((helperStep levels O).result second accepted') :=
  PlainIso.symm (PlainIso.ofAgree comparison.frame (by
    show Local.AgreeAlong comparison.frame.hom (first.toFiring.after accepted).toLocal
      (second.toFiring.after accepted').toLocal
    rw [Natural.toLocal_after_withHelpers, Natural.toLocal_after_withHelpers]
    have reading : first.reading = second.reading.move comparison.frame.hom := by
      show state.toLocal.move first.helpers.weaken =
        (state.toLocal.move second.helpers.weaken).move comparison.frame.hom
      rw [Local.move_comp, comparison.commutes]
    have agree : Local.AgreeAlong (levels := levels) comparison.frame.hom first.reading second.reading :=
      ⟨by rw [reading]; exact fun _ _ => Iff.rfl, by rw [reading], by rw [reading]⟩
    have moved := after_agree second.data comparison.frame.hom agree accepted'.1.2.2.2.2
      (by rw [← comparison.data]; exact accepted.1.2.2.2.2)
    exact (Plain.after_congr (congrArg Natural.toPlain comparison.data) rfl _ _) ▸ moved))

theorem resultComparison_frame (comparison : AlikeData levels O first second)
    (accepted : (helperStep levels O).Admits first) (accepted' : (helperStep levels O).Admits second) :
    (comparison.resultComparison accepted accepted').frame.hom = comparison.frame.inv := rfl

end AlikeData

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.alikeDataOfLifts_original
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.AlikeData.resultComparison
