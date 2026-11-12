import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.ConversionSettling
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.AgreementCounterexample
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.CoerceSettled

/-!
# The converting step on the coerce firing and on the η firing

**The coerce firing** (`ProgrammingOnTheStep.Refinement.coerceFiring`: helpers `x : X` and `g : Ground`
over `X : U0`, told `(x : X) ≐ (g : Ground)`, made row `x` at `Ground`) is admitted by conversion
(`coerce_admitsByConversion`): its code `x` is typed in its frame at `X`, and at every solution `X` is
equal to `Ground`. So the converting step with the semantic settler admits it
(`coerce_converted`), where the present step refuses it (`coerce_converted_separation`), and the made row
of the result has its declared type `Ground` (`coerce_converted_result_type`). The coerce row is in the
class where typing is closed under agreement (`coerce_closed`).

**The η firing** (`Eta.etaFiring`: helper `h : Π (x : U₁). U₁`, made row `h` at `Π (x : U₀). U₁`) is
refused by the converting step **for every settler** (`eta_converting_refused`), including the settler
along the η-expansion with which the settling step admits it (`settling_vs_converting`). The row is typed
along the η-expansion, and does not convert along it (`eta_typed_not_converts`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.ConversionControls

open _root_.CategoryTheory Opposite Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull Interface.DependentFull.Controls
open ProgrammingOnTheStep.Refinement
open NativeTypesOnTheStep.Coerce NativeTypesOnTheStep.Eta

/-! ## The coerce firing is admitted by conversion -/

/-- **The coerce code `x` is typed in its frame at `X`.** -/
theorem coerce_frameTyped : FrameTypedAt coerceRow xRow.1 := xRow.2.typed

/-- **At every solution of the coerce information, `X` is usable at `Ground`.** -/
theorem coerce_conversion_everywhere :
    solutions setting.levels coerceFiring.information ≤ conversion coerceRow xRow.1 := by
  intro Θ τ solved
  obtain ⟨⟨u, hu, e⟩, -⟩ := tell_heterogeneous setting.levels coerceFiring solved (List.mem_singleton_self _)
  exact .subEqual e hu

/-- **The coerce firing is admitted by conversion.** -/
theorem coerce_admitsByConversion : AdmitsByConversion setting.levels coerceFiring := by
  refine ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (DependentFull.enabled_iff coerceFiring).mpr ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
      fun o _ inside => Finset.notMem_empty o inside⟩, coerce_solvable, ?_⟩
  · obtain rfl := List.mem_singleton.mp member
    exact ⟨xRow.1, coerce_frameTyped, coerce_conversion_everywhere⟩
  · intro _ _ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-- **F1, soundly**: the converting step with the semantic settler admits the coerce firing. -/
theorem coerce_converted :
    (convertingStep setting.levels Nat (Settler.ideal setting.levels)).Admits coerceFiring :=
  ideal_converting_admits setting.levels coerce_admitsByConversion toGround_initial

/-- **The separation**: the converting step admits the coerce firing, the present step refuses it. -/
theorem coerce_converted_separation :
    (convertingStep setting.levels Nat (Settler.ideal setting.levels)).Admits coerceFiring ∧
      ¬ (step setting.levels Nat).Admits coerceFiring :=
  ⟨coerce_converted, coerce_refused⟩

/-- **The made row of the result has its declared type `Ground`.** -/
theorem coerce_converted_result_type :
    (((convertingStep setting.levels Nat (Settler.ideal setting.levels)).result coerceFiring
      coerce_converted).label 8).1.code = ground := rfl

/-- **The coerce row is in the class where typing is closed under agreement**: its typings at solutions
are conversions of its frame typing at `X`. -/
theorem coerce_closed : ClosedUnderAgreement setting.levels coerceFiring.information coerceRow :=
  closedUnderAgreement_of_conversion setting.levels coerce_frameTyped
    (fun Θ _ solved _ => coerce_conversion_everywhere (op Θ) solved)

/-! ## The η firing is refused by conversion, whatever the settler -/

/-- **The η row is typed along the η-expansion, and does not convert along it**: converting along an
initial solution of the empty store would type it in its frame. -/
theorem eta_typed_not_converts :
    (etaRow.reindex etaHom).WellTyped ∧ ¬ ConvertsAlong etaRow etaHom :=
  ⟨etaRow_typed_at_eta, fun converts => eta_gap.2
    (typedAfterMatch_of_convertsAlong setting.levels (principal_of_initial setting.levels eta_initial)
      converts)⟩

/-- **The converting step refuses the η firing for every settler.** -/
theorem eta_converting_refused (settler : Settler setting.levels) :
    ¬ (convertingStep setting.levels Nat settler).Admits etaFiring :=
  fun admitted => eta_gap.2
    (converting_typedAfterMatch setting.levels settler admitted (1, etaRow) (List.mem_singleton_self _))

/-- **Settling the raw row and settling by conversion separate on the η firing**, with the same
settler. -/
theorem settling_vs_converting :
    (settlingStep setting.levels Nat etaSettler).Admits etaFiring ∧
      ¬ (convertingStep setting.levels Nat etaSettler).Admits etaFiring :=
  ⟨eta_settled_admitted, eta_converting_refused etaSettler⟩

end NativeTypesOnTheStep.ConversionControls

#print axioms NativeTypesOnTheStep.ConversionControls.coerce_frameTyped
#print axioms NativeTypesOnTheStep.ConversionControls.coerce_conversion_everywhere
#print axioms NativeTypesOnTheStep.ConversionControls.coerce_admitsByConversion
#print axioms NativeTypesOnTheStep.ConversionControls.coerce_converted
#print axioms NativeTypesOnTheStep.ConversionControls.coerce_converted_separation
#print axioms NativeTypesOnTheStep.ConversionControls.coerce_converted_result_type
#print axioms NativeTypesOnTheStep.ConversionControls.coerce_closed
#print axioms NativeTypesOnTheStep.ConversionControls.eta_typed_not_converts
#print axioms NativeTypesOnTheStep.ConversionControls.eta_converting_refused
#print axioms NativeTypesOnTheStep.ConversionControls.settling_vs_converting

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
