import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeConstructorFunctions
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeSourceReading
import Mettapedia.Logic.HOL.PredicateContextInstantiation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.GuardedEnvironmentInterpretation

/-!
# Original source guards with constructor functions installed

The original seven-variable context retains its source telescope. Its two
type parameters and two constructor variables are assigned actual target
programs. The arbitrary motive satisfies the selected full codomain guard;
both case methods retain their original guards.
The resulting realizer transports retained source-context proofs, without
claiming a source-term substitution or a model of the source universes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeConstructorInstallation
open Mettapedia.Logic Mettapedia.Logic.HOL Mettapedia.TypeTheory
namespace Source
export IndexedVectorTreeNativeSourceReading
  (ambient ambientContext familyPredicate answerPredicate solvedCaseCarrier branchCaseCarrier motiveCarrier)
end Source
namespace Native
export IndexedContainerNativeVectorMethodReading (Base Const N E V W original selection)
end Native
abbrev Base := Native.Base
abbrev Const := Native.Const
abbrev P := Native.E ⇒ .prop

def rawImages {Ω : Ctx Base} (answer family : Term Const Ω P)
    (motive : Term Const Ω Source.motiveCarrier)
    (solved : Term Const Ω (Native.E ⇒ Native.E))
    (branch : Term Const Ω (Native.N ⇒ Native.V ⇒ Native.E))
    (solvedCase : Term Const Ω Source.solvedCaseCarrier)
    (branchCase : Term Const Ω Source.branchCaseCarrier) : Subst Const Source.ambient Ω :=
  (Subst.Table.cons branchCase (.cons solvedCase (.cons branch (.cons solved (.cons motive
    (.cons family (.cons answer .nil))))))).lookup

def solvedGuardFor {Ω : Ctx Base} (answer family : Term Const Ω P) :=
  PredicateProducts.pi answer (weaken family)

def branchGuardFor {Ω : Ctx Base} (family : Term Const Ω P) :=
  PredicateProducts.pi (PredicateProducts.full Native.N)
    (PredicateProducts.pi
      (Calculi.CumulativePiSigmaId.NativeVectorAll.Reading.vectorCode Native.original Native.selection
        (weaken family) (.var .vz)) (weaken (weaken family)))

private def solvedVariable : Var Source.ambient (Native.E ⇒ Native.E) := .vs (.vs (.vs .vz))
private def branchVariable : Var Source.ambient (Native.N ⇒ Native.V ⇒ Native.E) := .vs (.vs .vz)
private def motiveVariable : Var Source.ambient Source.motiveCarrier := .vs (.vs (.vs (.vs .vz)))
private def familyVariable : Var Source.ambient P := .vs (.vs (.vs (.vs (.vs .vz))))
private def answerVariable : Var Source.ambient P := .vs (.vs (.vs (.vs (.vs (.vs .vz)))))

private theorem sourceSolvedDomain : Source.ambientContext.telescope.domain solvedVariable =
    solvedGuardFor Source.answerPredicate Source.familyPredicate := by
  with_unfolding_all rfl

private theorem sourceBranchDomain : Source.ambientContext.telescope.domain branchVariable =
    branchGuardFor Source.familyPredicate := by
  with_unfolding_all rfl

private theorem sourceMotiveDomain : Source.ambientContext.telescope.domain motiveVariable =
    PredicateProducts.pi Source.familyPredicate (PredicateProducts.full (Native.W ⇒ .prop)) := by
  with_unfolding_all rfl

theorem solvedGuardFor_subst {Ω Ξ : Ctx Base} (images : Subst Const Ω Ξ) (answer family : Term Const Ω P) :
    HOL.subst images (solvedGuardFor answer family) = solvedGuardFor (HOL.subst images answer) (HOL.subst images family) := by
  simp only [solvedGuardFor,PredicateProducts.subst_pi,subst_weaken]

theorem branchGuardFor_subst {Ω Ξ : Ctx Base} (images : Subst Const Ω Ξ) (family : Term Const Ω P) :
    HOL.subst images (branchGuardFor family) = branchGuardFor (HOL.subst images family) := by
  simp only [branchGuardFor,PredicateProducts.subst_pi,PredicateProducts.subst_full,
    Calculi.CumulativePiSigmaId.NativeVectorAll.Reading.vectorCode,HOL.subst,subst_weaken,
    subst_weakenCtx,Subst.lift]
  rfl

theorem solvedGuardFor_rename {Ω Ξ : Ctx Base} (rho : Rename Base Ω Ξ) (answer family : Term Const Ω P) :
    HOL.rename rho (solvedGuardFor answer family) = solvedGuardFor (HOL.rename rho answer) (HOL.rename rho family) := by
  simpa only [subst_ofRename] using solvedGuardFor_subst (Subst.ofRename rho) answer family

theorem branchGuardFor_rename {Ω Ξ : Ctx Base} (rho : Rename Base Ω Ξ) (family : Term Const Ω P) :
    HOL.rename rho (branchGuardFor family) = branchGuardFor (HOL.rename rho family) := by
  simpa only [subst_ofRename] using branchGuardFor_subst (Subst.ofRename rho) family

variable {Ω : Ctx Base} (answer family : Term Const Ω P)
  (motive : Term Const Ω Source.motiveCarrier)
  (solved : Term Const Ω (Native.E ⇒ Native.E))
  (branch : Term Const Ω (Native.N ⇒ Native.V ⇒ Native.E))
  (solvedCase : Term Const Ω Source.solvedCaseCarrier)
  (branchCase : Term Const Ω Source.branchCaseCarrier)

theorem rawSolvedGuard :
    HOL.subst (rawImages answer family motive solved branch solvedCase branchCase)
      (Source.ambientContext.telescope.guard solvedVariable) = .app (solvedGuardFor answer family) solved := by
  change Term.app (HOL.subst (rawImages answer family motive solved branch solvedCase branchCase)
    (Source.ambientContext.telescope.domain solvedVariable))
    (HOL.subst (rawImages answer family motive solved branch solvedCase branchCase) (.var solvedVariable)) = _
  rw [sourceSolvedDomain,solvedGuardFor_subst]
  rfl

theorem rawBranchGuard :
    HOL.subst (rawImages answer family motive solved branch solvedCase branchCase)
      (Source.ambientContext.telescope.guard branchVariable) = .app (branchGuardFor family) branch := by
  change Term.app (HOL.subst (rawImages answer family motive solved branch solvedCase branchCase)
    (Source.ambientContext.telescope.domain branchVariable))
    (HOL.subst (rawImages answer family motive solved branch solvedCase branchCase) (.var branchVariable)) = _
  rw [sourceBranchDomain,branchGuardFor_subst]
  rfl

private theorem rawFamilyGuard :
    HOL.subst (rawImages answer family motive solved branch solvedCase branchCase)
      (Source.ambientContext.telescope.guard familyVariable) = .app (PredicateProducts.full P) family := by
  with_unfolding_all rfl

private theorem rawAnswerGuard :
    HOL.subst (rawImages answer family motive solved branch solvedCase branchCase)
      (Source.ambientContext.telescope.guard answerVariable) = .app (PredicateProducts.full P) answer := by
  with_unfolding_all rfl

private theorem rawMotiveGuard :
    HOL.subst (rawImages answer family motive solved branch solvedCase branchCase)
      (Source.ambientContext.telescope.guard motiveVariable) =
      .app (PredicateProducts.pi family (PredicateProducts.full (Native.W ⇒ .prop))) motive := by
  change Term.app (HOL.subst (rawImages answer family motive solved branch solvedCase branchCase)
    (Source.ambientContext.telescope.domain motiveVariable))
    (HOL.subst (rawImages answer family motive solved branch solvedCase branchCase) (.var motiveVariable)) = _
  rw [sourceMotiveDomain,PredicateProducts.subst_pi,PredicateProducts.subst_full]
  rfl

@[irreducible] private def fullCodomainProof {Ξ : Ctx Base} {hypotheses : List (Formula Const Ξ)}
    (family : Term Const Ξ P) (motive : Term Const Ξ Source.motiveCarrier) :
    ProofSyntax Const hypotheses
      (.app (PredicateProducts.pi family (PredicateProducts.full (Native.W ⇒ .prop))) motive) :=
  PredicateProducts.introduce family (PredicateProducts.full (Native.W ⇒ .prop)) motive
    (.impE (.eqPropER (.beta (.app (weaken motive) (.var .vz)) .top)) .topI)

private theorem fullCodomainProof_free {Ξ : Ctx Base} {hypotheses : List (Formula Const Ξ)}
    (family : Term Const Ξ P) (motive : Term Const Ξ Source.motiveCarrier) :
    (fullCodomainProof (hypotheses := hypotheses) family motive).FunctionExtensionalityFree := by
  unfold fullCodomainProof
  apply PredicateProducts.introduce_free
  trivial

private def fullTypeProof {Ξ : Ctx Base} {hypotheses : List (Formula Const Ξ)} (value : Term Const Ξ P) :
    ProofSyntax Const hypotheses (.app (PredicateProducts.full P) value) :=
  .impE (.eqPropER (.beta value .top)) .topI

private def rawMapped {type : Ty Base} (index : Var Source.ambient type) : Formula Const Ω :=
  HOL.subst (rawImages answer family motive solved branch solvedCase branchCase)
    (Source.ambientContext.telescope.guard index)

variable {H : List (Formula Const Ω)}
  (solvedPresent : ProofSyntax Const H (rawMapped answer family motive solved branch solvedCase branchCase solvedVariable))
  (branchPresent : ProofSyntax Const H (rawMapped answer family motive solved branch solvedCase branchCase branchVariable))
  (solvedCasePresent : ProofSyntax Const H (rawMapped answer family motive solved branch solvedCase branchCase (.vs .vz)))
  (branchCasePresent : ProofSyntax Const H (rawMapped answer family motive solved branch solvedCase branchCase .vz))

private def rawFamilyProof : ProofSyntax Const H
    (rawMapped answer family motive solved branch solvedCase branchCase familyVariable) :=
  .castIndices rfl (rawFamilyGuard answer family motive solved branch solvedCase branchCase).symm (fullTypeProof family)

private def rawAnswerProof : ProofSyntax Const H
    (rawMapped answer family motive solved branch solvedCase branchCase answerVariable) :=
  .castIndices rfl (rawAnswerGuard answer family motive solved branch solvedCase branchCase).symm (fullTypeProof answer)

private def rawMotiveProof : ProofSyntax Const H
    (rawMapped answer family motive solved branch solvedCase branchCase motiveVariable) :=
  .castIndices rfl (rawMotiveGuard answer family motive solved branch solvedCase branchCase).symm (fullCodomainProof family motive)

private theorem rawFamilyProof_free :
    (rawFamilyProof answer family motive solved branch solvedCase branchCase (H := H)).FunctionExtensionalityFree := by
  unfold rawFamilyProof
  simp only [ProofSyntax.functionExtensionalityFree_castIndices]
  trivial

private theorem rawAnswerProof_free :
    (rawAnswerProof answer family motive solved branch solvedCase branchCase (H := H)).FunctionExtensionalityFree := by
  unfold rawAnswerProof
  simp only [ProofSyntax.functionExtensionalityFree_castIndices]
  trivial

private theorem rawMotiveProof_free :
    (rawMotiveProof answer family motive solved branch solvedCase branchCase (H := H)).FunctionExtensionalityFree := by
  unfold rawMotiveProof
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact fullCodomainProof_free family motive

@[irreducible] def rawRealizes : Source.ambientContext.telescope.Realizes
    (rawImages answer family motive solved branch solvedCase branchCase) H := by
  intro type index
  cases index with
  | vz => exact branchCasePresent
  | vs index => cases index with
    | vz => exact solvedCasePresent
    | vs index => cases index with
      | vz => exact branchPresent
      | vs index => cases index with
        | vz => exact solvedPresent
        | vs index => cases index with
          | vz => exact rawMotiveProof answer family motive solved branch solvedCase branchCase
          | vs index => cases index with
            | vz => exact rawFamilyProof answer family motive solved branch solvedCase branchCase
            | vs index => cases index with
              | vz => exact rawAnswerProof answer family motive solved branch solvedCase branchCase
              | vs index => cases index

theorem rawRealizes_free (solvedFree : solvedPresent.FunctionExtensionalityFree)
    (branchFree : branchPresent.FunctionExtensionalityFree)
    (solvedCaseFree : solvedCasePresent.FunctionExtensionalityFree)
    (branchCaseFree : branchCasePresent.FunctionExtensionalityFree) :
    ∀ {type} (index : Var Source.ambient type),
      (rawRealizes answer family motive solved branch solvedCase branchCase
        solvedPresent branchPresent solvedCasePresent branchCasePresent index).FunctionExtensionalityFree := by
  intro type index
  unfold rawRealizes
  cases index with
  | vz => exact branchCaseFree
  | vs index => cases index with
    | vz => exact solvedCaseFree
    | vs index => cases index with
      | vz => exact branchFree
      | vs index => cases index with
        | vz => exact solvedFree
        | vs index => cases index with
          | vz => with_unfolding_all exact rawMotiveProof_free answer family motive solved branch solvedCase branchCase (H := H)
          | vs index => cases index with
            | vz => with_unfolding_all exact rawFamilyProof_free answer family motive solved branch solvedCase branchCase (H := H)
            | vs index => cases index with
              | vz => with_unfolding_all exact rawAnswerProof_free answer family motive solved branch solvedCase branchCase (H := H)
              | vs index => cases index

section Actual
variable {Γ : Ctx Base} {A : Ty Base}
  (elementSelection : ClosedTerm Const (SelectionProofs.Selection (Native.N ⇒ Native.E)))
  (arraySelection : ClosedTerm Const (SelectionProofs.Selection (Native.N ⇒ Native.V ⇒ Native.N ⇒ Native.E)))
  (input : VectorTreeFieldEmbedding.Inputs Const Γ Native.N A Native.E)
  (parameter : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (Native.N ⇒ .prop))
  (one : ClosedTerm Const Native.N) (ordinals : Nat → Term Const Γ Native.N) (bottom : Term Const Γ Native.E)
  {Δ : List (Formula Const Γ)}

abbrev target (Γ : Ctx Base) : Ctx Base :=
  Source.branchCaseCarrier :: Source.solvedCaseCarrier :: Source.motiveCarrier :: Γ

private def raiseThree : Rename Base Γ (target Γ) := fun {_type} index => .vs (.vs (.vs index))

def familyProgram : Term Const Γ P :=
  IndexedVectorTreeConstructorFunctions.Native.branchFamily Native.original input parameter numbers one ordinals bottom

def solvedProgram : Term Const Γ (Native.E ⇒ Native.E) :=
  IndexedVectorTreeConstructorFunctions.solved input parameter numbers Native.original.zero one ordinals bottom

def branchProgram : Term Const Γ (Native.N ⇒ Native.V ⇒ Native.E) :=
  IndexedVectorTreeConstructorFunctions.Native.branch Native.original elementSelection arraySelection
    input parameter numbers one ordinals bottom

def images : Subst Const Source.ambient (target Γ) :=
  rawImages (HOL.rename raiseThree (input.predicate parameter))
    (HOL.rename raiseThree (familyProgram input parameter numbers one ordinals bottom)) (.var (.vs (.vs .vz)))
    (HOL.rename raiseThree (solvedProgram input parameter numbers one ordinals bottom))
    (HOL.rename raiseThree (branchProgram elementSelection arraySelection input parameter numbers one ordinals bottom))
    (.var (.vs .vz)) (.var .vz)

def mappedGuard {type : Ty Base} (index : Var Source.ambient type) : Formula Const (target Γ) :=
  HOL.subst (images elementSelection arraySelection input parameter numbers one ordinals bottom)
    (Source.ambientContext.telescope.guard index)

def remainingGuards : List (Formula Const (target Γ)) :=
  [mappedGuard elementSelection arraySelection input parameter numbers one ordinals bottom .vz,
   mappedGuard elementSelection arraySelection input parameter numbers one ordinals bottom (.vs .vz)]

def assumptions : List (Formula Const (target Γ)) :=
  remainingGuards elementSelection arraySelection input parameter numbers one ordinals bottom ++ Δ.map (HOL.rename raiseThree)

theorem remainingGuards_length :
    (remainingGuards elementSelection arraySelection input parameter numbers one ordinals bottom).length = 2 := rfl

theorem assumptions_length :
    (assumptions elementSelection arraySelection input parameter numbers one ordinals bottom (Δ := Δ)).length = Δ.length + 2 := by
  simp only [assumptions,List.length_append,remainingGuards_length,List.length_map]
  omega

private def liftProof {claim : Formula Const Γ} (proof : ProofSyntax Const Δ claim) :
    ProofSyntax Const (assumptions elementSelection arraySelection input parameter numbers one ordinals bottom (Δ := Δ))
      (HOL.rename raiseThree claim) :=
  (proof.renameShared raiseThree).mono (ProofSyntax.OccurrenceMap.appendLeft
    (remainingGuards elementSelection arraySelection input parameter numbers one ordinals bottom) (Δ.map (HOL.rename raiseThree)))

private theorem liftProof_free {claim : Formula Const Γ} (proof : ProofSyntax Const Δ claim)
    (free : proof.FunctionExtensionalityFree) :
    (liftProof elementSelection arraySelection input parameter numbers one ordinals bottom proof).FunctionExtensionalityFree := by
  simpa only [liftProof,ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.renameShared_eq,
    ProofSyntax.functionExtensionalityFree_rename] using free

private theorem solvedGuard_equation :
    mappedGuard elementSelection arraySelection input parameter numbers one ordinals bottom solvedVariable =
      HOL.rename raiseThree (.app (solvedGuardFor (input.predicate parameter)
        (familyProgram input parameter numbers one ordinals bottom))
        (solvedProgram input parameter numbers one ordinals bottom)) := by
  unfold mappedGuard images
  rw [rawSolvedGuard,← solvedGuardFor_rename]
  rfl

private theorem branchGuard_equation :
    mappedGuard elementSelection arraySelection input parameter numbers one ordinals bottom branchVariable =
      HOL.rename raiseThree (.app (branchGuardFor (familyProgram input parameter numbers one ordinals bottom))
        (branchProgram elementSelection arraySelection input parameter numbers one ordinals bottom)) := by
  unfold mappedGuard images
  rw [rawBranchGuard,← branchGuardFor_rename]
  rfl

@[irreducible] private def solvedProof : ProofSyntax Const
    (assumptions elementSelection arraySelection input parameter numbers one ordinals bottom (Δ := Δ))
    (mappedGuard elementSelection arraySelection input parameter numbers one ordinals bottom solvedVariable) :=
  .castIndices rfl (solvedGuard_equation elementSelection arraySelection input parameter numbers one ordinals bottom).symm
    (liftProof elementSelection arraySelection input parameter numbers one ordinals bottom
      (IndexedVectorTreeConstructorFunctions.solvedMember
        input parameter numbers Native.original.zero one Native.original.successor ordinals bottom))

private theorem solvedProof_free :
    (solvedProof elementSelection arraySelection input parameter numbers one ordinals bottom (Δ := Δ)).FunctionExtensionalityFree := by
  unfold solvedProof
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact liftProof_free _ _ _ _ _ _ _ _ _ (IndexedVectorTreeConstructorFunctions.solvedMember_free _ _ _ _ _ _ _ _)

variable (recognition : ProofSyntax Const Δ (IndexedVectorTreeConstructorFunctions.Native.numberRecognition numbers))
  (premises : (IndexedVectorTreeConstructorFunctions.Native.arrays Native.original elementSelection arraySelection).ComputationPremises Δ)
  (arithmetic : SuccessorOrder.PeanoEvidence Native.original.successor Native.original.zero Δ)

@[irreducible] private def branchProof : ProofSyntax Const
    (assumptions elementSelection arraySelection input parameter numbers one ordinals bottom (Δ := Δ))
    (mappedGuard elementSelection arraySelection input parameter numbers one ordinals bottom branchVariable) :=
  .castIndices rfl (branchGuard_equation elementSelection arraySelection input parameter numbers one ordinals bottom).symm
    (liftProof elementSelection arraySelection input parameter numbers one ordinals bottom
      (IndexedVectorTreeConstructorFunctions.Native.branchMember Native.original Native.selection
        elementSelection arraySelection input parameter numbers one ordinals bottom recognition premises arithmetic))

private theorem branchProof_free (recognitionFree : recognition.FunctionExtensionalityFree)
    (premisesFree : premises.FunctionExtensionalityFree) (arithmeticFree : arithmetic.Free) :
    (branchProof elementSelection arraySelection input parameter numbers one ordinals bottom
      recognition premises arithmetic).FunctionExtensionalityFree := by
  unfold branchProof
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact liftProof_free _ _ _ _ _ _ _ _ _ (IndexedVectorTreeConstructorFunctions.Native.branchMember_free
    Native.original Native.selection elementSelection arraySelection input parameter numbers one ordinals bottom
    recognition premises arithmetic recognitionFree premisesFree arithmeticFree)

private def branchCaseProof : ProofSyntax Const
    (assumptions elementSelection arraySelection input parameter numbers one ordinals bottom (Δ := Δ))
    (mappedGuard elementSelection arraySelection input parameter numbers one ordinals bottom .vz) := by
  simp only [assumptions,remainingGuards,List.cons_append,List.nil_append]
  exact .hyp 0

private def solvedCaseProof : ProofSyntax Const
    (assumptions elementSelection arraySelection input parameter numbers one ordinals bottom (Δ := Δ))
    (mappedGuard elementSelection arraySelection input parameter numbers one ordinals bottom (.vs .vz)) := by
  simp only [assumptions,remainingGuards,List.cons_append,List.nil_append]
  exact .hyp 1

@[irreducible] def realizes : Source.ambientContext.telescope.Realizes
    (images elementSelection arraySelection input parameter numbers one ordinals bottom)
    (assumptions elementSelection arraySelection input parameter numbers one ordinals bottom (Δ := Δ)) :=
  rawRealizes (HOL.rename raiseThree (input.predicate parameter))
    (HOL.rename raiseThree (familyProgram input parameter numbers one ordinals bottom)) (.var (.vs (.vs .vz)))
    (HOL.rename raiseThree (solvedProgram input parameter numbers one ordinals bottom))
    (HOL.rename raiseThree (branchProgram elementSelection arraySelection input parameter numbers one ordinals bottom))
    (.var (.vs .vz)) (.var .vz)
    (solvedProof elementSelection arraySelection input parameter numbers one ordinals bottom)
    (branchProof elementSelection arraySelection input parameter numbers one ordinals bottom recognition premises arithmetic)
    (solvedCaseProof elementSelection arraySelection input parameter numbers one ordinals bottom)
    (branchCaseProof elementSelection arraySelection input parameter numbers one ordinals bottom)

theorem realizes_free (recognitionFree : recognition.FunctionExtensionalityFree)
    (premisesFree : premises.FunctionExtensionalityFree) (arithmeticFree : arithmetic.Free) :
    ∀ {type} (index : Var Source.ambient type),
      (realizes elementSelection arraySelection input parameter numbers one ordinals bottom recognition premises arithmetic index).FunctionExtensionalityFree := by
  unfold realizes
  apply rawRealizes_free
  · exact solvedProof_free elementSelection arraySelection input parameter numbers one ordinals bottom
  · exact branchProof_free elementSelection arraySelection input parameter numbers one ordinals bottom
      recognition premises arithmetic recognitionFree premisesFree arithmeticFree
  · trivial
  · trivial

def transport {claim : Formula Const Source.ambient}
    (proof : ProofSyntax Const Source.ambientContext.telescope.hypotheses claim) :
    ProofSyntax Const (assumptions elementSelection arraySelection input parameter numbers one ordinals bottom (Δ := Δ))
      (HOL.subst (images elementSelection arraySelection input parameter numbers one ordinals bottom) claim) :=
  PredicateContexts.Telescope.Realizes.transport
    (realizes elementSelection arraySelection input parameter numbers one ordinals bottom recognition premises arithmetic) proof

theorem transport_free {claim : Formula Const Source.ambient}
    (proof : ProofSyntax Const Source.ambientContext.telescope.hypotheses claim)
    (recognitionFree : recognition.FunctionExtensionalityFree)
    (premisesFree : premises.FunctionExtensionalityFree) (arithmeticFree : arithmetic.Free)
    (proofFree : proof.FunctionExtensionalityFree) :
    (transport elementSelection arraySelection input parameter numbers one ordinals bottom recognition premises arithmetic proof).FunctionExtensionalityFree :=
  PredicateContexts.Telescope.Realizes.transport_free _ proof
    (realizes_free elementSelection arraySelection input parameter numbers one ordinals bottom
      recognition premises arithmetic recognitionFree premisesFree arithmeticFree) proofFree

namespace Reading
export Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading (assumptions)
end Reading

private def rootTargets (roots : List (ClosedFormula Const))
    (rootProofs : ProofSyntax.HypothesisSubstitution (Reading.assumptions roots Γ) Δ) :
    ProofSyntax.HypothesisSubstitution (Reading.assumptions roots (target Γ))
      (assumptions elementSelection arraySelection input parameter numbers one ordinals bottom (Δ := Δ)) :=
  fun occurrence => by
    let original : Fin (Reading.assumptions roots Γ).length := occurrence.cast (by simp [Reading.assumptions])
    apply ProofSyntax.castIndices rfl ?_
      (liftProof elementSelection arraySelection input parameter numbers one ordinals bottom (rootProofs original))
    simp only [Reading.assumptions,List.get_eq_getElem,List.getElem_map,original,Fin.val_cast,rename_weakenCtx]

private theorem rootTargets_free (roots : List (ClosedFormula Const))
    (rootProofs : ProofSyntax.HypothesisSubstitution (Reading.assumptions roots Γ) Δ)
    (free : ∀ occurrence, (rootProofs occurrence).FunctionExtensionalityFree) :
    ∀ occurrence, (rootTargets elementSelection arraySelection input parameter numbers one ordinals bottom
      roots rootProofs occurrence).FunctionExtensionalityFree := by
  intro occurrence
  unfold rootTargets
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact liftProof_free _ _ _ _ _ _ _ _ _ (free _)

/-- Closed source-root occurrences are supplied independently of the
remaining motive/case guards and retain their original order. -/
def transportWithRoots (roots : List (ClosedFormula Const))
    (rootProofs : ProofSyntax.HypothesisSubstitution (Reading.assumptions roots Γ) Δ)
    {claim : Formula Const Source.ambient}
    (proof : ProofSyntax Const (Source.ambientContext.hypotheses roots) claim) :
    ProofSyntax Const (assumptions elementSelection arraySelection input parameter numbers one ordinals bottom (Δ := Δ))
      (HOL.subst (images elementSelection arraySelection input parameter numbers one ordinals bottom) claim) :=
  Source.ambientContext.realizeProof (images elementSelection arraySelection input parameter numbers one ordinals bottom)
    (realizes elementSelection arraySelection input parameter numbers one ordinals bottom recognition premises arithmetic)
    (rootTargets elementSelection arraySelection input parameter numbers one ordinals bottom roots rootProofs) proof

theorem transportWithRoots_free (roots : List (ClosedFormula Const))
    (rootProofs : ProofSyntax.HypothesisSubstitution (Reading.assumptions roots Γ) Δ)
    {claim : Formula Const Source.ambient}
    (proof : ProofSyntax Const (Source.ambientContext.hypotheses roots) claim)
    (recognitionFree : recognition.FunctionExtensionalityFree)
    (premisesFree : premises.FunctionExtensionalityFree) (arithmeticFree : arithmetic.Free)
    (rootsFree : ∀ occurrence, (rootProofs occurrence).FunctionExtensionalityFree)
    (proofFree : proof.FunctionExtensionalityFree) :
    (transportWithRoots elementSelection arraySelection input parameter numbers one ordinals bottom recognition premises arithmetic
      roots rootProofs proof).FunctionExtensionalityFree := by
  unfold transportWithRoots
  apply Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading.GuardedContext.realizeProof_free
  · exact realizes_free elementSelection arraySelection input parameter numbers one ordinals bottom recognition premises arithmetic
      recognitionFree premisesFree arithmeticFree
  · exact rootTargets_free elementSelection arraySelection input parameter numbers one ordinals bottom roots rootProofs rootsFree
  · exact proofFree

#print axioms realizes
#print axioms realizes_free
#print axioms transport_free
#print axioms transportWithRoots_free
end Actual

#print axioms rawSolvedGuard
#print axioms rawBranchGuard
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeConstructorInstallation
