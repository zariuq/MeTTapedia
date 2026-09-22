import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLGenericProofFamily
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveProofAttachment
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLUniformList
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLProofFamily
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveHOLInvariant
import Mettapedia.Logic.HOL.TransitionInvariantProofSyntax

/-!
# Two independent instances of the generic HOL proof-family extension

The same layered construction is instantiated for the uniform List theory and
for the call-guard invariant theory.  These sources have different base types,
constant families, declaration vocabularies, and represented theorems.  In
both cases the source proposition remains formed after extension and its proof
family is formed without copying the source declaration table or its
computation field.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace FormationSensitiveHOLGenericProofInstances

open Presentation Presentation.FormationSensitive
open FormationSensitiveHOLInterface
open FormationSensitiveHOLGenericProofFamily

namespace UniformList

def proofName : DeclName := FormationSensitiveHOLProofFamily.proofName

def rules : Rules Tower.Head :=
  FormationSensitiveHOLGenericProofFamily.rules
    FormationSensitiveHOLUniformList.signature proofName

theorem proofName_fresh :
    FormationSensitiveHOLUniformList.signature.rules.constantType proofName = none := by
  decide

/-- The represented map-length theorem is retained from the actual List
interface, then admitted as the index of the generic native proof family. -/
theorem mapLength_proof_family_formed :
    Typing rules .nil
      (proof proofName (FormationSensitiveHOLUniformList.rawMapLength : Tower.Tm 0))
      (sortTm Tower.zero) := by
  have proposition :
      Typing rules .nil
        (FormationSensitiveHOLUniformList.rawMapLength : Tower.Tm 0)
        (typeAt FormationSensitiveHOLUniformList.types 0 .prop) := by
    exact include_typed FormationSensitiveHOLUniformList.signature proofName
      (FormationSensitiveHOLUniformList.mapLength_formed []).2
  exact proof_formed FormationSensitiveHOLUniformList.signature proofName
    proofName_fresh proposition

/-- The extension table contains only its new proof declaration; source List
symbols remain owned by the inherited presentation. -/
theorem proof_layer_does_not_redeclare_map :
    (declarations FormationSensitiveHOLUniformList.signature proofName).entries
      `HOLUniformList.map = none := by
  decide

end UniformList

namespace CallGuard

open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHOLInvariant
open Mettapedia.Logic.HOL.TransitionInvariantProofSyntax

/-- The call-guard refinement theorem as retained proof data.  This is the
explicit generic proof tree, instantiated at the three symbols interpreted by
the compiler micro-machine. -/
def preservationSyntax : Mettapedia.Logic.HOL.ProofSyntax
    Constant assumptions conclusion :=
  Mettapedia.Logic.HOL.TransitionInvariantProofSyntax.preservationOfRefinement
    Constant.step Constant.sameResult Constant.property

/-- Forgetting the retained tree yields the same extensional judgment as the
proposition-valued theorem already consumed by the operational soundness
proof. -/
theorem preservationSyntax_erases :
    preservationSyntax.erase =
      Mettapedia.Logic.HOL.ExtDerivation.ofBase preservation_derived := by
  exact preservationOfRefinement_erases (Γ := []) Constant.step
    Constant.sameResult Constant.property

/-- The retained call-guard proof begins by introducing a quantified state;
it is not a leaf that treats the requested invariant as an assumption. -/
theorem preservationSyntax_root : preservationSyntax.rootObservation =
    ⟨Mettapedia.Logic.HOL.ProofSyntax.RuleTag.allI, none⟩ := by
  exact preservationOfRefinement_root Constant.step Constant.sameResult Constant.property

theorem preservationSyntax_root_not_hyp : preservationSyntax.rootObservation ≠
    ⟨Mettapedia.Logic.HOL.ProofSyntax.RuleTag.hyp, none⟩ := by
  exact preservationOfRefinement_root_not_hyp Constant.step Constant.sameResult Constant.property

def proofName : DeclName := `HOLInterface.LayeredPrf

def rules : Rules Tower.Head :=
  FormationSensitiveHOLGenericProofFamily.rules
    FormationSensitiveHOLInvariant.signature proofName

theorem proofName_fresh :
    FormationSensitiveHOLInvariant.signature.rules.constantType proofName = none := by
  decide

/-- The independently derived call-guard theorem uses the same proof-family
construction despite having a different HOL signature from the List theory. -/
theorem conclusion_proof_family_formed :
    Typing rules .nil
      (proof proofName FormationSensitiveHOLInvariant.rawConclusion)
      (sortTm Tower.zero) := by
  have proposition :
      Typing rules .nil FormationSensitiveHOLInvariant.rawConclusion
        (typeAt FormationSensitiveHOLInvariant.types 0 .prop) := by
    exact include_typed FormationSensitiveHOLInvariant.signature proofName
      FormationSensitiveHOLInvariant.conclusion_formed
  exact proof_formed FormationSensitiveHOLInvariant.signature proofName
    proofName_fresh proposition

/-- The actual source derivation and its representation survive beside the
new native proof-family formation; no List-specific theorem is used. -/
theorem source_derivation_representation_and_native_family :
    Mettapedia.Logic.HOL.Derivation
        Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHOLInvariant.Constant
        Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHOLInvariant.assumptions
        Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHOLInvariant.conclusion ∧
      represent FormationSensitiveHOLInvariant.signature
          Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHOLInvariant.conclusion =
        some FormationSensitiveHOLInvariant.rawConclusion ∧
      Typing rules .nil
        (proof proofName FormationSensitiveHOLInvariant.rawConclusion)
        (sortTm Tower.zero) :=
  ⟨Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHOLInvariant.preservation_derived,
    FormationSensitiveHOLInvariant.conclusion_represented,
    conclusion_proof_family_formed⟩

/-- The existing higher-order call-guard specialization is an actual
attachment through the generic proof extension.  Its substitution replaces a
predicate-valued variable beneath a state quantifier, so this is not an
identity-only instance of the attachment interface. -/
def higherOrderAttachment : FormationSensitiveProofAttachment.Attachment
    (sourceMorphism FormationSensitiveHOLInvariant.signature proofName)
    (FormationSensitiveHOLInterface.context FormationSensitiveHOLInvariant.types
      [FormationSensitiveHOLInvariant.predicateType])
    .nil FormationSensitiveHOLInvariant.rawPredicateBody
    (typeAt FormationSensitiveHOLInvariant.types 1 .prop) where
  sourceJudgment :=
    represent_judgment FormationSensitiveHOLInvariant.signature
      FormationSensitiveHOLInvariant.predicateBody
      FormationSensitiveHOLInvariant.predicate_body_represented
  targetContextFormed := .nil
  substitution := subst0 FormationSensitiveHOLInvariant.rawFunctionArgument
  substitutionTyped := by
    have argumentTypedSource :=
      represent_typed FormationSensitiveHOLInvariant.signature
        FormationSensitiveHOLInvariant.functionArgument
        FormationSensitiveHOLInvariant.function_argument_represented
    have argumentTypedTarget :=
      include_typed FormationSensitiveHOLInvariant.signature proofName
        argumentTypedSource
    change Typing rules
      (FormationSensitiveHOLInterface.context FormationSensitiveHOLInvariant.types [])
      FormationSensitiveHOLInvariant.rawFunctionArgument
      (typeAt FormationSensitiveHOLInvariant.types 0
        FormationSensitiveHOLInvariant.predicateType) at argumentTypedTarget
    have argumentTypedTarget' : Typing rules .nil
        FormationSensitiveHOLInvariant.rawFunctionArgument
        (subst ids (typeAt FormationSensitiveHOLInvariant.types 0
          FormationSensitiveHOLInvariant.predicateType)) := by
      simpa only [FormationSensitiveHOLInterface.context, subst_ids] using argumentTypedTarget
    have identity := FormationSensitiveProofAttachment.identityCtxMor
      (FormationSensitiveHOLGenericProofFamily.rules
        FormationSensitiveHOLInvariant.signature proofName) (.nil)
    have extended := identity.extend argumentTypedTarget'
    have pairedIdentityIsOpening :
        consSub FormationSensitiveHOLInvariant.rawFunctionArgument ids =
          subst0 FormationSensitiveHOLInvariant.rawFunctionArgument := by
      funext index
      refine Fin.cases ?_ ?_ index
      · rfl
      · intro prior
        rfl
    rw [pairedIdentityIsOpening] at extended
    simpa only [FormationSensitiveHOLInterface.context, Ctx.mapHead_id, subst0,
      List.length_cons, List.length_nil, Nat.zero_add] using extended

/-- The target judgment computed by the retained attachment is exactly the
native higher-order specialization already used by the call-guard theory. -/
theorem higherOrderAttachment_target :
    Judgment rules .nil
      (inst0 FormationSensitiveHOLInvariant.rawFunctionArgument
        FormationSensitiveHOLInvariant.rawPredicateBody)
      (typeAt FormationSensitiveHOLInvariant.types 0 .prop) := by
  have attached :=
    FormationSensitiveProofAttachment.Attachment.targetJudgment higherOrderAttachment
  change Judgment rules .nil
    (subst (subst0 FormationSensitiveHOLInvariant.rawFunctionArgument)
      FormationSensitiveHOLInvariant.rawPredicateBody)
    (subst (subst0 FormationSensitiveHOLInvariant.rawFunctionArgument)
      (typeAt FormationSensitiveHOLInvariant.types 1 .prop)) at attached
  simpa only [inst0, typeAt_subst] using attached

/-- The higher-order attachment performs real work: its closed result is not
the predicate function that was substituted into the open formula. -/
theorem higherOrderAttachment_not_projection :
    inst0 FormationSensitiveHOLInvariant.rawFunctionArgument
        FormationSensitiveHOLInvariant.rawPredicateBody ≠
      FormationSensitiveHOLInvariant.rawFunctionArgument := by
  decide

/-- The proof layer does not take ownership of the source's operational
predicate symbol. -/
theorem proof_layer_does_not_redeclare_step :
    (declarations FormationSensitiveHOLInvariant.signature proofName).entries
      `HOLInterface.step = none := by
  decide

end CallGuard

#print axioms UniformList.mapLength_proof_family_formed
#print axioms CallGuard.conclusion_proof_family_formed
#print axioms CallGuard.source_derivation_representation_and_native_family
#print axioms CallGuard.higherOrderAttachment_target
#print axioms CallGuard.higherOrderAttachment_not_projection
#print axioms CallGuard.preservationSyntax
#print axioms CallGuard.preservationSyntax_erases
#print axioms CallGuard.preservationSyntax_root
#print axioms CallGuard.preservationSyntax_root_not_hyp
#print axioms UniformList.proof_layer_does_not_redeclare_map
#print axioms CallGuard.proof_layer_does_not_redeclare_step

end FormationSensitiveHOLGenericProofInstances
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
