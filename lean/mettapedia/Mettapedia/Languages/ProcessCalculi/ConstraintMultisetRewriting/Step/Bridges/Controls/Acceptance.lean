import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Readouts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Controls.PositiveBlocks
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Hosting.Answers.Bags
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationReplayControls

/-!
# Separate certificates exclude three misleading bridge claims

A constant state map satisfies weak operational correspondence while erasing
two distinguishable readings. Real hosted programs with equal answer support
can differ in multiplicity. Finally, convertible code is not a licence to
replay an instruction whose literal source is a later intermediate state.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Acceptance

open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)

abbrev collapsed := equalityGSLT Unit (fun _ _ => False)

/-- Deliberately invalid as an answer-preserving implementation: its relation
is the graph of the constant map, though the weak operational laws hold. -/
def erasing : OperationalCorrespondence PositiveBlocks.source collapsed where
  related _ target := target = ()
  readStep := by
    intro _ _ _ _ impossible
    exact False.elim impossible
  forward := by
    intro _ _ target _ _
    cases target
    exact ⟨(), ⟨.refl ()⟩, rfl⟩

theorem constant_map_cannot_deliver_distinguishable_answers :
    ¬ ∃ observe : Bool → Unit → Prop,
      Readouts.Delivery erasing (fun expected actual => actual = expected) observe := by
  rintro ⟨observe, delivered⟩
  obtain ⟨after, _, falseSeen⟩ := delivered.realizes (s := false) (t := ()) rfl false rfl
  cases after
  have impossible : (true : Bool) = false := delivered.reflects (s := true) (t := ()) rfl false falseSeen
  cases impossible

section Multiplicity

open Hosting.Answers.Bags

theorem same_support_different_answer_bags :
    (∀ answer, answer ∈ SourceLanguage.Config.answers (D := D) final1 ↔
      answer ∈ SourceLanguage.Config.answers (D := D) final2) ∧
    SourceLanguage.Config.answers (D := D) final1 ≠
      SourceLanguage.Config.answers (D := D) final2 := by
  constructor
  · intro answer
    rw [p1_answers, p2_answers]
    simp
  · exact bags_differ

end Multiplicity

noncomputable section LiteralSource

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization
open NativeTypesOnTheStep.Computing
open TowerVectorsModel (zeroC addC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (pkg)
open ComputationProfile.Controls (setting start middle first middle_code)
open ComputationReplay.Controls (p doubled doubled_same wrongSource)

local instance headPolicy : DecidableRel setting.R.headEq := Classical.decRel _

/-- This code is valid at the intermediate state, but only convertible with
the current source. Treating that conversion as source alignment skips an
actual computational event. -/
theorem semantic_agreement_does_not_license_this_instruction :
    Conv pkg.headEq start.code middle.code pkg.computation ∧ start.code ≠ middle.code ∧
      (ComputationReplay.read? p doubled doubled_same start wrongSource).isSome = false ∧
      (ComputationReplay.read? p doubled doubled_same middle wrongSource).isSome = true := by
  refine ⟨?_, ?_, ComputationReplay.Controls.source_refused, ?_⟩
  · have reduction := first.reduction
    change StepCore pkg.computation pkg.headEq start.code (addC zeroC zeroC) at reduction
    rw [middle_code]
    exact conv_of_stepStar (.single reduction)
  · rw [middle_code]
    decide
  · decide +kernel

end LiteralSource
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Acceptance

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Acceptance.constant_map_cannot_deliver_distinguishable_answers
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Acceptance.same_support_different_answer_bags
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.Acceptance.semantic_agreement_does_not_license_this_instruction
