import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientMotiveCoverage
import Mettapedia.TypeTheory.ContextualBasedIdentityScope
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentityInputCoherence

/-!
# Exact native J and abstraction of submitted motives

A based semantic family and its reflexivity method are sufficient inputs
for the existing total eliminator interface. Exact interpretation of a
submitted native expression is an additional requirement. These interfaces
are compared without changing the required native input domain or the
conversion relation of the candidate presentation.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientMotiveAbstraction

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation FormationSensitive SharedJudgmentFragment FormationSensitiveContextual
open SharedJudgmentTypeInterpretation SharedJudgmentQuotientInterpretation
open SharedJudgmentQuotientMotiveCoverage
open Mettapedia.TypeTheory

universe u v w w'

variable {assembly : Assembly} {C : Cwf.{u, v, w, w'}}

/-- The family-only observation does not retain the unapplied native
motive function. The latter still occurs in the source term named by the
independent meaning requirement below. -/
def frameInput {interpretation : SharedJudgmentInterpretation.Data assembly C}
    {operations : FrameOperations C} {n : Nat}
    {source : SharedJudgmentInterpretation.Context assembly n}
    {type left motive method : Tower.Tm n}
    (frame : JFrame interpretation operations source type left motive method) :
    ContextualBasedIdentityScope.Input operations.identity operations.reflSection where
  context := interpretation.ctx source
  type := frame.semanticType
  left := frame.semanticLeft
  motive := frame.motive
  base := frame.base

/-- All independently admitted native tuples and all their qualified
frames are retained. This predicate is not a reduced-motive workload. -/
def RunMeaning (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : FrameOperations C)
    (run : (input : ContextualBasedIdentityScope.Input
      operations.identity operations.reflSection) → input.Output) : Prop :=
  ∀ (n : Nat) (source : SharedJudgmentInterpretation.Context assembly n)
    (type left motive method : Tower.Tm n)
    (frame : JFrame interpretation operations source type left motive method),
    FormationSensitiveBasedIdentity.Parameters assembly.declarations source.raw type left motive method →
    JFrameMeaning interpretation operations frame →
      interpretation.term frame.context
        (FormationSensitiveBasedIdentity.genericTerm type left motive method)
        (FormationSensitiveBasedIdentity.motiveBody motive)
        (C.tySub frame.motive frame.comparison.forward)
        (C.tmSub (run (frameInput frame)) frame.comparison.forward)

/-- Restricting the operation to an admitted image is a genuine weaker
interface. Every required request must still be in that image, and its
returned value must satisfy the same exact source-meaning clause. -/
def ScopedRunMeaning (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : FrameOperations C)
    (scope : ContextualBasedIdentityScope.Input operations.identity operations.reflSection → Prop)
    (run : (input : {input // scope input}) → input.val.Output) : Prop :=
  ∀ (n : Nat) (source : SharedJudgmentInterpretation.Context assembly n)
    (type left motive method : Tower.Tm n)
    (frame : JFrame interpretation operations source type left motive method),
    FormationSensitiveBasedIdentity.Parameters assembly.declarations source.raw type left motive method →
    JFrameMeaning interpretation operations frame →
      ∃ admitted : scope (frameInput frame),
        interpretation.term frame.context
          (FormationSensitiveBasedIdentity.genericTerm type left motive method)
          (FormationSensitiveBasedIdentity.motiveBody motive)
          (C.tySub frame.motive frame.comparison.forward)
          (C.tmSub (run ⟨frameInput frame, admitted⟩) frame.comparison.forward)

/-- The old total constructor interface supplies this family-only run
without any new operation assumption. Its native exactness is precisely
the old constructor-meaning clause, not a consequence of totality. -/
theorem full_supplies_run
    (interpretation : SharedJudgmentInterpretation.Data assembly C)
    (operations : Operations C)
    (meaning : BasedJMeaning interpretation operations) :
    ∃ run : (input : ContextualBasedIdentityScope.Input
        operations.frames.identity operations.frames.reflSection) → input.Output,
      RunMeaning interpretation operations.frames run := by
  refine ⟨fun input => operations.based.elimination.j input.left input.motive input.base, ?_⟩
  exact meaning

private theorem totalSub_inverse {Head : Type} {rules : Rules Head}
    {source target : QuotientCwf.QContext rules}
    (comparison : source ≅ target) (value : QTerm source.as) :
    QuotientCwf.totalSub (QuotientCwf.totalSub value comparison.inv) comparison.hom = value :=
  (QuotientCwf.totalSub_comp value comparison.hom comparison.inv).symm.trans
    ((congrArg (QuotientCwf.totalSub value) comparison.hom_inv_id).trans
      (QuotientCwf.totalSub_id value))

/-- On the exact quotient, any operation agreeing with the submitted
generic J must return its actual quotient class. Pullback along the
independently qualified comparison cannot hide a different result. -/
theorem native_value_unique {n : Nat} (source : SharedJudgmentInterpretation.Context assembly n)
    {type left motive method : Tower.Tm n}
    (parameters : FormationSensitiveBasedIdentity.Parameters assembly.declarations
      source.raw type left motive method)
    (value : (frameInput (nativeFrame source parameters)).Output)
    (meaning : (data assembly).term (nativeFrame source parameters).context
      (FormationSensitiveBasedIdentity.genericTerm type left motive method)
      (FormationSensitiveBasedIdentity.motiveBody motive)
      (QuotientCwf.tySub (nativeFrame source parameters).motive
        (nativeFrame source parameters).comparison.forward)
      (QuotientCwf.tmSub value (nativeFrame source parameters).comparison.forward)) :
    value = nativeJ source parameters := by
  have same := term_meaning_unique
    meaning (native_j_meaning source parameters)
  have values := congrArg Subtype.val same
  have pulled := congrArg
    (fun value => QuotientCwf.totalSub value (nativeInput source parameters).presentation.hom) values
  change QuotientCwf.totalSub
      (QuotientCwf.totalSub value.val
        (nativeInput source parameters).presentation.inv)
      (nativeInput source parameters).presentation.hom =
    QuotientCwf.totalSub
      (QuotientCwf.totalSub (nativeJ source parameters).val
        (nativeInput source parameters).presentation.inv)
      (nativeInput source parameters).presentation.hom at pulled
  apply Subtype.ext
  exact (totalSub_inverse (nativeInput source parameters).presentation value.val).symm.trans
      (pulled.trans (totalSub_inverse (nativeInput source parameters).presentation
        (nativeJ source parameters).val))

theorem native_run_unique
    (run : (input : ContextualBasedIdentityScope.Input
      (frames assembly).identity (frames assembly).reflSection) → input.Output)
    (meaning : RunMeaning (data assembly) (frames assembly) run)
    {n : Nat} (source : SharedJudgmentInterpretation.Context assembly n)
    {type left motive method : Tower.Tm n}
    (parameters : FormationSensitiveBasedIdentity.Parameters assembly.declarations
      source.raw type left motive method) :
    run (frameInput (nativeFrame source parameters)) = nativeJ source parameters :=
  native_value_unique source parameters _
    (meaning n source type left motive method (nativeFrame source parameters)
      parameters (native_frame_meaning source parameters))

namespace Controls

private def source : SharedJudgmentInterpretation.Context common 4 :=
  ⟨QuotientIdentityInputCoherence.Controls.parameterContext.raw,
    QuotientIdentityInputCoherence.Controls.parameterContext.formed⟩

/-- The two independently formed requests have identical family-only
inputs but distinguishable native J outputs. Therefore no total function
of this observation satisfies the unchanged exact meaning requirement.
This refutes this combination of interface and interpretation, not J. -/
theorem no_body_only_exact_run :
    ¬ ∃ run : (input : ContextualBasedIdentityScope.Input
        (frames common).identity (frames common).reflSection) → input.Output,
      RunMeaning (data common) (frames common) run := by
  rintro ⟨run, meaning⟩
  let first := QuotientIdentityInputCoherence.Controls.variableInput
  let second := QuotientIdentityInputCoherence.abstractedInput first
  have firstResult := native_run_unique run meaning source first.parameters
  have secondResult := native_run_unique run meaning source second.parameters
  change run (QuotientIdentityInputCoherence.semanticInput first) = first.chosenJ at firstResult
  change run (QuotientIdentityInputCoherence.semanticInput second) = second.chosenJ at secondResult
  have sameInput := QuotientIdentityInputCoherence.abstracted_semantic_input first
  have sameResult : HEq (run (QuotientIdentityInputCoherence.semanticInput first))
      (run (QuotientIdentityInputCoherence.semanticInput second)) := by
    have dependentCongruence {firstInput secondInput : ContextualBasedIdentityScope.Input
        (frames common).identity (frames common).reflSection} (same : firstInput = secondInput) :
        HEq (run firstInput) (run secondInput) := by
      cases same
      rfl
    exact dependentCongruence sameInput.symm
  exact QuotientIdentityInputCoherence.Controls.eta_collision_chosen_j_heq
    ((heq_of_eq firstResult).symm.trans (sameResult.trans (heq_of_eq secondResult)))

/-- Even the stronger total profile cannot satisfy its original J meaning
clause while retaining these canonical frames and exact source quotient.
No beta, substitution or off-scope assumption is needed for the conflict. -/
theorem no_total_exact_constructor
    (operations : Operations (QuotientCwf.cwf common.rules))
    (sameFrames : operations.frames = frames common) :
    ¬ BasedJMeaning (data common) operations := by
  intro meaning
  have supplied := full_supplies_run (data common) operations meaning
  rw [sameFrames] at supplied
  exact no_body_only_exact_run supplied

/-- Merely narrowing a family-only function's domain does not repair
this collision: both independently admitted native requests are required.
An admission proof cannot secretly restore the discarded motive value. -/
theorem no_scoped_body_only_exact_run
    (scope : ContextualBasedIdentityScope.Input
      (frames common).identity (frames common).reflSection → Prop) :
    ¬ ∃ run : (input : {input // scope input}) → input.val.Output,
      ScopedRunMeaning (data common) (frames common) scope run := by
  rintro ⟨run, meaning⟩
  let first := QuotientIdentityInputCoherence.Controls.variableInput
  let second := QuotientIdentityInputCoherence.abstractedInput first
  obtain ⟨firstAdmitted, firstMeaning⟩ := meaning 4 source first.type first.left first.motive
    first.method (nativeFrame source first.parameters) first.parameters
    (native_frame_meaning source first.parameters)
  obtain ⟨secondAdmitted, secondMeaning⟩ := meaning 4 source second.type second.left second.motive
    second.method (nativeFrame source second.parameters) second.parameters
    (native_frame_meaning source second.parameters)
  have firstResult := native_value_unique source first.parameters _ firstMeaning
  have secondResult := native_value_unique source second.parameters _ secondMeaning
  have sameInput : (⟨frameInput (nativeFrame source first.parameters), firstAdmitted⟩ :
      {input // scope input}) = ⟨frameInput (nativeFrame source second.parameters), secondAdmitted⟩ :=
    Subtype.ext (QuotientIdentityInputCoherence.abstracted_semantic_input first).symm
  have sameResult : HEq (run ⟨frameInput (nativeFrame source first.parameters), firstAdmitted⟩)
      (run ⟨frameInput (nativeFrame source second.parameters), secondAdmitted⟩) := by
    have dependentCongruence {firstInput secondInput : {input // scope input}}
        (same : firstInput = secondInput) : HEq (run firstInput) (run secondInput) := by
      cases same
      rfl
    exact dependentCongruence sameInput
  exact QuotientIdentityInputCoherence.Controls.eta_collision_chosen_j_heq
    ((heq_of_eq firstResult).symm.trans (sameResult.trans (heq_of_eq secondResult)))

end Controls

#print axioms full_supplies_run
#print axioms native_value_unique
#print axioms native_run_unique
#print axioms Controls.no_body_only_exact_run
#print axioms Controls.no_total_exact_constructor
#print axioms Controls.no_scoped_body_only_exact_run

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentQuotientMotiveAbstraction
