import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeChildConditions
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamilyConstructors

/-!
# The original guarded Vector branch introduces the derived family

The branch retains its source length, a separate canonical shape field and
the ordered child array generated from the original Vector. Its complete
child contract follows from guarded Vector membership and the declared
recursor/arithmetic laws. No branch-membership or complete child-contract
premise is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamilyBranch
open Mettapedia.Logic Mettapedia.Logic.HOL
open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
  (ops : VectorChildArrays.Operations Const) {A : Ty Base}
  (given : VectorTreeFieldEmbedding.Inputs Const Γ ops.number A ops.element)
  (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (ops.number ⇒ .prop))
  (one : ClosedTerm Const ops.number) (tags : Nat → Term Const Γ ops.number)
  (bottom : Term Const Γ ops.element) {Δ : List (Formula Const Γ)}

def occurrence : Fin (VectorTreeFieldEmbedding.storedSignature ops.number ops.element).length :=
  ⟨1,by change 1 < 2; decide⟩

def arguments (n : Term Const Γ ops.number) : Arguments Const Γ
    ((IndexedVectorTreeStoredFieldGuards.reading (Γ := Γ) (E := ops.element) one).fields
      (IndexedVectorTreeStoredFamilyConstructors.originalCode (occurrence ops))) :=
  (n,weakenCtx Γ ops.zero,PUnit.unit)

def value (n : Term Const Γ ops.number) (vector : Term Const Γ ops.vector) : Term Const Γ ops.element :=
  IndexedVectorTreeStoredFamilyConstructors.value given source numbers ops.zero one tags
    (ops.single n vector bottom) (occurrence ops) (arguments ops one n)

private def evidence (n : Term Const Γ ops.number) (numeric : ProofSyntax Const Δ (.app numbers n)) :
    (IndexedVectorTreeStoredFieldGuards.guards given source numbers ops.zero one).Evidence Δ
      (IndexedVectorTreeStoredFamilyConstructors.originalCode (occurrence ops)) Subst.id (arguments ops one n) :=
  (IndexedVectorTreeStoredFieldGuards.guards given source numbers ops.zero one).readEvidence
    (IndexedVectorTreeStoredFamilyConstructors.originalCode (occurrence ops)) Subst.id (arguments ops one n)
    (IndexedVectorTreeStoredFieldGuards.branchIntroduce given source numbers ops.zero one n (weakenCtx Γ ops.zero)
      (.andI numeric (.andI (.eqRefl _) .topI)))

private theorem evidence_free (n : Term Const Γ ops.number) (numeric : ProofSyntax Const Δ (.app numbers n))
    (free : numeric.FunctionExtensionalityFree) :
    (IndexedVectorTreeStoredFieldGuards.guards given source numbers ops.zero one).EvidenceFree Δ
      (IndexedVectorTreeStoredFamilyConstructors.originalCode (occurrence ops)) Subst.id
      (arguments ops one n) (evidence ops given source numbers one n numeric) :=
  (IndexedVectorTreeStoredFieldGuards.guards given source numbers ops.zero one).readEvidence_free
    _ _ _ _ (IndexedVectorTreeStoredFieldGuards.branchIntroduce_free _ _ _ _ _ _ _ _
      ⟨free,True.intro,True.intro⟩)

@[irreducible] def member (n : Term Const Γ ops.number) (vector : Term Const Γ ops.vector)
    (numeric : ProofSyntax Const Δ (.app numbers n))
    (premises : ops.ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence ops.successor ops.zero Δ)
    (elements : ProofSyntax Const Δ (ops.toSignature.member
      (IndexedVectorTreeStoredFamily.family given source numbers ops.zero one ops.successor tags bottom) n vector)) :
    ProofSyntax Const Δ (.app (IndexedVectorTreeStoredFamily.family
      given source numbers ops.zero one ops.successor tags bottom)
      (value ops given source numbers one tags bottom n vector)) :=
  IndexedVectorTreeStoredFamilyConstructors.constructorMember
    given source numbers ops.zero one ops.successor tags bottom
    (ops.single n vector bottom) (occurrence ops) (arguments ops one n)
    (evidence ops given source numbers one n numeric)
    (IndexedVectorTreeNativeChildConditions.sourceChildConditions ops given source numbers one tags bottom
      n (weakenCtx Γ ops.zero) vector
      (IndexedVectorTreeNativeChildConditions.numericAllowed ops given source numbers one tags n numeric)
      premises arithmetic elements)

theorem member_free (n : Term Const Γ ops.number) (vector : Term Const Γ ops.vector)
    (numeric : ProofSyntax Const Δ (.app numbers n))
    (premises : ops.ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence ops.successor ops.zero Δ)
    (elements : ProofSyntax Const Δ (ops.toSignature.member
      (IndexedVectorTreeStoredFamily.family given source numbers ops.zero one ops.successor tags bottom) n vector))
    (numericFree : numeric.FunctionExtensionalityFree) (premisesFree : premises.FunctionExtensionalityFree)
    (arithmeticFree : arithmetic.Free) (elementsFree : elements.FunctionExtensionalityFree) :
    (member ops given source numbers one tags bottom n vector numeric premises arithmetic elements).FunctionExtensionalityFree := by
  unfold member
  apply IndexedVectorTreeStoredFamilyConstructors.constructorMember_free
  · exact evidence_free ops given source numbers one n numeric numericFree
  · exact IndexedVectorTreeNativeChildConditions.sourceChildConditions_free _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (IndexedVectorTreeNativeChildConditions.numericAllowed_free _ _ _ _ _ _ _ _ numericFree)
      premisesFree arithmeticFree elementsFree

namespace ReaderGuard
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
variable (original : NativeVectorComputationRows.Operations Base Const) {W : Ty Base}
  (selection : ClosedTerm Const (SelectionProofs.Selection (original.number ⇒ original.vector ⇒ W ⇒ .prop)))
  (elementSelection : ClosedTerm Const (SelectionProofs.Selection (original.number ⇒ original.element)))
  (arraySelection : ClosedTerm Const (SelectionProofs.Selection
    (original.number ⇒ original.vector ⇒ original.number ⇒ original.element)))
  (input : VectorTreeFieldEmbedding.Inputs Const Γ original.number A original.element)
  (answer : Term Const Γ (A ⇒ .prop)) (natural : Term Const Γ (original.number ⇒ .prop))
  (unitCode : ClosedTerm Const original.number) (ordinals : Nat → Term Const Γ original.number)
  (padding : Term Const Γ original.element)

abbrev arrays := IndexedVectorTreeNativeChildConditions.ReaderGuard.arrays original elementSelection arraySelection

def value (n : Term Const Γ original.number) (vector : Term Const Γ original.vector) :=
  IndexedVectorTreeStoredFamilyBranch.value (arrays original elementSelection arraySelection)
    input answer natural unitCode ordinals padding n vector

def member (n : Term Const Γ original.number) (vector : Term Const Γ original.vector)
    (numeric : ProofSyntax Const Δ (.app natural n))
    (premises : (arrays original elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (elements : ProofSyntax Const Δ (.app (NativeVectorAll.Reading.vectorCode original selection
      (IndexedVectorTreeStoredFamily.family input answer natural original.zero unitCode original.successor ordinals padding) n) vector)) :
    ProofSyntax Const Δ (.app (IndexedVectorTreeStoredFamily.family
      input answer natural original.zero unitCode original.successor ordinals padding)
      (value original elementSelection arraySelection input answer natural unitCode ordinals padding n vector)) :=
  IndexedVectorTreeStoredFamilyBranch.member (arrays original elementSelection arraySelection)
    input answer natural unitCode ordinals padding n vector numeric premises arithmetic
    (IndexedVectorTreeNativeChildConditions.ReaderGuard.memberOfGuard original selection _ n vector elements)

theorem member_free (n : Term Const Γ original.number) (vector : Term Const Γ original.vector)
    (numeric : ProofSyntax Const Δ (.app natural n))
    (premises : (arrays original elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (elements : ProofSyntax Const Δ (.app (NativeVectorAll.Reading.vectorCode original selection
      (IndexedVectorTreeStoredFamily.family input answer natural original.zero unitCode original.successor ordinals padding) n) vector))
    (numericFree : numeric.FunctionExtensionalityFree) (premisesFree : premises.FunctionExtensionalityFree)
    (arithmeticFree : arithmetic.Free) (elementsFree : elements.FunctionExtensionalityFree) :
    (member original selection elementSelection arraySelection input answer natural unitCode ordinals padding
      n vector numeric premises arithmetic elements).FunctionExtensionalityFree :=
  IndexedVectorTreeStoredFamilyBranch.member_free _ _ _ _ _ _ _ _ _ _ _ _ _
    numericFree premisesFree arithmeticFree
    (IndexedVectorTreeNativeChildConditions.ReaderGuard.memberOfGuard_free original selection _ n vector elements elementsFree)

end ReaderGuard

#print axioms member
#print axioms member_free
#print axioms ReaderGuard.member_free
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamilyBranch
