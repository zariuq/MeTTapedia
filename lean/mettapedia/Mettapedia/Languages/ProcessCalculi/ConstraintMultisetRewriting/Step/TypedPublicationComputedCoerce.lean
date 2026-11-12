import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationFamilies
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationCoerce
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.OlderUnknownControls

/-!
# The computed older-unknown certificate publishes the actual coerce result

The source adapter consumes the existing kernel-checked older-unknown family.
The chosen family and its budget remain explicit in this control. The result
uses the family-returned context and substitution, not the separately known
semantic answer and not an ideal settler.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.ComputedCoerce

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull DependentFull.Controls
open NativeTypesOnTheStep.OlderUnknown
open ProgrammingOnTheStep.Refinement (coerceFiring)

def computed : Resolution (state := baseState) Coerce.schema Coerce.pick :=
  Coerce.schema.resolveFamily Coerce.pick (olderFamily olderFuel)

theorem computed_certificate_publishes :
    ∃ (application : Application setting.levels Nat baseState)
      (admitted : (realizationStep setting.levels Nat).Admits application),
      computed.application? = some application ∧ application.schema = Coerce.schema ∧
        (((realizationStep setting.levels Nat).result application admitted).label 8).1.code = ground := by
  have settles := NativeTypesOnTheStep.OlderUnknown.Controls.coerce_older_settled
  cases chosen : olderFamily olderFuel coerceFiring.information with
  | settled target answer initial =>
      let application : Application setting.levels Nat baseState :=
        ⟨Coerce.schema, Coerce.pick, target, answer,
          .principal (NativeTypesOnTheStep.principal_of_initial setting.levels initial)⟩
      let admitted := (realization_admits_iff application).mpr Coerce.source_admitted
      refine ⟨application, admitted, ?_, rfl, rfl⟩
      exact congrArg (fun decision : NativeTypesOnTheStep.Decision setting.levels coerceFiring.information =>
        (Coerce.schema.resolveFamilyDecision (state := baseState) Coerce.pick decision).application?) chosen
  | refuted absent => rw [chosen] at settles; cases settles
  | undecided => rw [chosen] at settles; cases settles

open ContextualDependentSweep.Witnesses in
/-- Even this successful family cannot turn the nonprincipal cross store
into a decision; the source adapter keeps the problem when it is declined. -/
theorem cross_family_declines : olderFamily olderFuel crossStore = .undecided := by
  have declines := NativeTypesOnTheStep.OlderUnknown.Controls.cross_undecided (olderFamily olderFuel)
  cases chosen : olderFamily olderFuel crossStore with
  | settled target answer initial =>
      rw [chosen] at declines
      exact False.elim (declines True.intro)
  | refuted absent =>
      rw [chosen] at declines
      exact False.elim (declines True.intro)
  | undecided => rfl

open ContextualDependentSweep.Witnesses in
theorem declined_is_still_solvable :
    olderFamily olderFuel crossStore = .undecided ∧ (frames setting.levels).Solvable crossStore :=
  ⟨cross_family_declines, fragment_without_principal_answer.2.1⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.ComputedCoerce

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.ComputedCoerce.computed_certificate_publishes
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.ComputedCoerce.cross_family_declines
