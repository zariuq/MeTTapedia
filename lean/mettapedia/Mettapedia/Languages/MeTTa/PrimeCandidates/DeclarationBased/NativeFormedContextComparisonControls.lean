import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextualComparison
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextualCategory
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeFormedContextControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextConversion
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveCompletedRelatorPreservation

/-! # Concrete controls for comparison of convertible formed context extensions -/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual
open _root_.CategoryTheory FormationSensitive
/-! ## A real converted annotation and a dependent fibre -/

namespace ComparisonControls

variable {Head : Type}

open NativeIndexedFamilies

def expandedWireType : TypeOver Common.context where
  code := FormationSensitiveCompletedRelatorPreservation.Examples.betaCopy NativeWireData.dataType
  level := .sort Tower.zero
  universeWitness := .sort _
  formed := by
    have sortFormed : Typing HOLNativeRelatorCompatibility.rules Common.context.raw
        (.head (.sort Tower.zero)) (.head (.sort (.succ Tower.zero))) := .headType (.sort _)
    have function : Typing HOLNativeRelatorCompatibility.rules Common.context.raw (.lam (.var 0))
        (.pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))) := by
      apply Typing.lamIntro (u := .sort (.max (.succ Tower.zero) (.succ Tower.zero)))
      · exact .piForm sortFormed (.sort _) (.headType (.sort Tower.zero))
          (.sort _) (.sorts _ _)
      · exact .sort _
      · exact .var 0
    simpa only [FormationSensitiveCompletedRelatorPreservation.Examples.betaCopy, inst0, subst,
      Common.wireType] using
      Typing.appElim function Common.wireType.formed

theorem expanded_converts_wire :
    Conv HOLNativeRelatorCompatibility.rules.headEq expandedWireType.code Common.wireType.code
      HOLNativeRelatorCompatibility.rules.computation :=
  Declaration.Conv.includeSignature IntrinsicRelator.rules HOLNativeRelatorCompatibility.signature
    (FormationSensitiveCompletedRelatorPreservation.Examples.betaCopy_converts NativeWireData.dataType)

theorem expanded_annotation_distinct : expandedWireType.code ≠ Common.wireType.code := by
  intro same
  cases same

def wireComparison : extend Common.context expandedWireType ≅ extend Common.context Common.wireType :=
  extensionComparison expandedWireType Common.wireType expanded_converts_wire

/-- A native family depending on the newest value, not a renamed constant
motive. Its endpoints remain the variable under comparison. -/
def variableIdentity : TypeOver (extend Common.context Common.wireType) where
  code := .id (Common.wireType.reindex (projectionHom Common.context Common.wireType)).code
    (.var 0) (.var 0)
  level := .sort Tower.zero
  universeWitness := .sort _
  formed := .idForm (Common.wireType.reindex (projectionHom Common.context Common.wireType)).formed
    (.sort _) (newest Common.context Common.wireType).typed
    (newest Common.context Common.wireType).typed

def variableReflexivity : Term (extend Common.context Common.wireType) variableIdentity :=
  ⟨.refl (.var 0), .reflIntro (newest Common.context Common.wireType).typed⟩

/-- Actual refined admission in the beta-annotated context follows by
reindexing the dependent identity family and its reflexivity term. -/
theorem dependent_fibre_transport :
    Judgment HOLNativeRelatorCompatibility.rules (extend Common.context expandedWireType).raw
      (variableReflexivity.reindex wireComparison.hom).code
      (variableIdentity.reindex wireComparison.hom).code ∧
      (variableIdentity.reindex wireComparison.hom).code = variableIdentity.code ∧
      (variableReflexivity.reindex wireComparison.hom).code = .refl (.var 0) := by
  refine ⟨(variableReflexivity.reindex wireComparison.hom).judgment, ?_, ?_⟩
  · exact extensionComparison_reindex_type_code _ _ expanded_converts_wire variableIdentity
  · exact extensionComparison_reindex_term_code _ _ expanded_converts_wire variableReflexivity

/-- This retained raw inspection is not required to descend to conversion
classes. It observes the actual newest annotation's syntax. -/
def newestIsApplication {R : Rules Head} (context : Context R) : Bool :=
  match context.arity, context.raw with
  | _, .nil => false
  | _, .snoc _ (.app _ _) => true
  | _, .snoc _ _ => false

theorem annotation_inspection_distinguishes :
    newestIsApplication (extend Common.context expandedWireType) = true ∧
      newestIsApplication (extend Common.context Common.wireType) = false := by
  exact ⟨rfl, rfl⟩

theorem isomorphic_contexts_are_not_equal :
    extend Common.context expandedWireType ≠ extend Common.context Common.wireType := by
  intro same
  have inspected := congrArg newestIsApplication same
  have impossible : true = false := inspected
  cases impossible

end ComparisonControls
end FormationSensitiveContextual
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
