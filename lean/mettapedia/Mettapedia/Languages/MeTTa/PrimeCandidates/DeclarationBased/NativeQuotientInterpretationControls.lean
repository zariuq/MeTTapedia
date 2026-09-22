import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveQuotientInterpretation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveQuotientCwf
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeQuotientCwfControls

/-! # Concrete controls for interpretation in the formed conversion quotient -/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual.QuotientInterpretation
open _root_.CategoryTheory FormationSensitive
namespace Controls

open FormationSensitiveCompletedConversion.Controls

def missingContext : Tower.Ctx 1 := .snoc .nil (.const missingName)

theorem missing_context_unformed :
    ¬ ContextFormation HOLNativeRelatorCompatibility.rules missingContext := by
  intro formed
  cases formed with
  | snoc base entry universeWitness => exact missing_not_admitted _ ⟨base, entry⟩

theorem common_has_no_total_context_section :
    ¬ ∃ attach : ((n : Nat) × Tower.Ctx n) → QuotientCwf.QContext HOLNativeRelatorCompatibility.rules,
      ∀ source, underlyingContext (attach source) = source :=
  no_total_context_section missing_context_unformed

/-- Two convertible but syntactically different annotations cannot both
have their retained native extension literally equal to one model extension.
The comparison isomorphisms above remain available for both. -/
theorem converted_comprehensions_not_both_strict :
    ¬ ((quotientProjection HOLNativeRelatorCompatibility.rules).obj
          (extend Common.context ComparisonControls.expandedWireType) =
        QuotientCwf.ext ((quotientProjection HOLNativeRelatorCompatibility.rules).obj Common.context)
          (QType.mk ComparisonControls.expandedWireType) ∧
      (quotientProjection HOLNativeRelatorCompatibility.rules).obj
          (extend Common.context Common.wireType) =
        QuotientCwf.ext ((quotientProjection HOLNativeRelatorCompatibility.rules).obj Common.context)
          (QType.mk Common.wireType)) := by
  rintro ⟨expanded, wire⟩
  have sameExtension := congrArg
    (QuotientCwf.ext ((quotientProjection HOLNativeRelatorCompatibility.rules).obj Common.context))
    FibreControls.expanded_annotation_same_class.2
  exact ComparisonControls.isomorphic_contexts_are_not_equal
    (congrArg (fun context => context.as) (expanded.trans (sameExtension.trans wire.symm)))

theorem mixed_projection_meaning (wire : NativeWireData.Wire) :
    TermMeaning Common.context (Common.projected wire).code Common.wireType.code
      (QType.mk Common.wireType) (TermFibre.mk (Common.result wire)) :=
  ⟨Common.wireType, rfl, Common.projected wire, rfl, rfl,
    (QTerm.mk_eq_iff _ _).mpr ⟨.refl _, Common.projected_converts_result wire⟩⟩

theorem seven_not_eight_meaning :
    ¬ TermMeaning Common.context (Common.result (.natural 7)).code Common.wireType.code
      (QType.mk Common.wireType) (TermFibre.mk (Common.result (.natural 8))) := by
  rintro ⟨actualType, sameType, actual, sameTerm, _, sameValue⟩
  have converted := ((QTerm.mk_eq_iff actual (Common.result (.natural 8))).mp sameValue).2
  rw [sameTerm] at converted
  have impossible := (QuotientControls.natural_conversion_iff 7 8).mp converted
  cases impossible

end Controls

end FormationSensitiveContextual.QuotientInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
