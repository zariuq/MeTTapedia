import Mettapedia.Logic.HOL.VectorChildMembershipLaws

/-!
# Producing the lookup interface of the actual mixed array

The quantified law follows from the existing exact lookup proof at every
typed position and element. Combining the four implementation laws through
the membership assembly retains the original arithmetic, array and field
premises. No interface law becomes a new axiom.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.VectorChildArrays.Operations
open FiniteConstructorEncoding VectorChildMembershipLaws SuccessorOrder OrderedPositionPrograms
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} (ops : Operations Const)
    {Γ Ξ : Ctx Base} {Δ : List (Formula Const Γ)}

def lookupLawPoint (length : Term Const Γ ops.number) (before : Term Const Γ ops.element)
    (vector : Term Const Γ ops.vector) (after bottom : Term Const Γ ops.element)
    (premises : ops.ComputationPremises Δ) :
    ArgumentProof Δ [ops.number,ops.element]
      (VectorChildMembershipLaws.lookupBody ops.toSignature (ops.mixed length before vector after bottom) length vector) := by
  intro Ω images fields
  let found := IndexedVectorPositions.lookup ops.toSignature (HOL.subst images length) (HOL.subst images vector) fields.1 fields.2.1
  refine .impI ?_
  apply ProofSyntax.castIndices rfl ?_
    (ops.mixedAtLookup (HOL.subst images length) (HOL.subst images before) (HOL.subst images vector)
      (HOL.subst images after) (HOL.subst images bottom) fields.1 fields.2.1 ((premises.subst images).prepend found) (.hyp 0))
  simp only [mixed_subst]

theorem lookupLawPoint_free (length : Term Const Γ ops.number) (before : Term Const Γ ops.element)
    (vector : Term Const Γ ops.vector) (after bottom : Term Const Γ ops.element)
    (premises : ops.ComputationPremises Δ) (free : premises.FunctionExtensionalityFree)
    (images : Subst Const Γ Ξ) (fields : Arguments Const Ξ [ops.number,ops.element]) :
    (ops.lookupLawPoint length before vector after bottom premises images fields).FunctionExtensionalityFree := by
  unfold lookupLawPoint
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact ops.mixedAtLookup_free _ _ _ _ _ _ _ _ _
    ((premises.subst images).prepend_free _ (premises.subst_free images free)) True.intro

def mixedLookupLaw (length : Term Const Γ ops.number) (before : Term Const Γ ops.element)
    (vector : Term Const Γ ops.vector) (after bottom : Term Const Γ ops.element)
    (premises : ops.ComputationPremises Δ) :
    ProofSyntax Const Δ (lookupLaw ops.toSignature (ops.mixed length before vector after bottom) length vector) :=
  forallArguments_intro _ _ (ops.lookupLawPoint length before vector after bottom premises)

theorem mixedLookupLaw_free (length : Term Const Γ ops.number) (before : Term Const Γ ops.element)
    (vector : Term Const Γ ops.vector) (after bottom : Term Const Γ ops.element)
    (premises : ops.ComputationPremises Δ) (free : premises.FunctionExtensionalityFree) :
    (ops.mixedLookupLaw length before vector after bottom premises).FunctionExtensionalityFree :=
  forallArguments_intro_free _ _ _ (ops.lookupLawPoint_free length before vector after bottom premises free)

def assembleMembership {indexType : Ty Base} (predicate : Term Const Γ (ops.element ⇒ .prop))
    (length slot : Term Const Γ ops.number) (before : Term Const Γ ops.element)
    (vector : Term Const Γ ops.vector) (after bottom : Term Const Γ ops.element)
    (firstIndex vectorIndex lastIndex target : Term Const Γ indexType)
    (premises : ops.ComputationPremises Δ) (arithmetic : PeanoEvidence ops.successor ops.zero Δ)
    (beforeMember : ProofSyntax Const Δ (.app predicate before))
    (vectorMember : ProofSyntax Const Δ (ops.toSignature.member predicate length vector))
    (afterMember : ProofSyntax Const Δ (.app predicate after))
    (cases : ProofSyntax Const Δ (mixedCases ops.zero ops.successor length slot firstIndex vectorIndex lastIndex target)) :
    ProofSyntax Const Δ (.app predicate (.app (ops.mixed length before vector after bottom) slot)) :=
  VectorChildMembershipLaws.fromCases ops.toSignature predicate (ops.mixed length before vector after bottom)
    length slot vector before after firstIndex vectorIndex lastIndex target
    (ops.mixedLeading length before vector after bottom premises)
    (ops.mixedTrailing predicate length before vector after bottom premises vectorMember)
    (ops.mixedLookupLaw length before vector after bottom premises)
    (IndexedVectorLookupCoverage.fromMembership ops.toSignature predicate length vector arithmetic vectorMember)
    beforeMember afterMember cases

theorem assembleMembership_free {indexType : Ty Base} (predicate : Term Const Γ (ops.element ⇒ .prop))
    (length slot : Term Const Γ ops.number) (before : Term Const Γ ops.element)
    (vector : Term Const Γ ops.vector) (after bottom : Term Const Γ ops.element)
    (firstIndex vectorIndex lastIndex target : Term Const Γ indexType)
    (premises : ops.ComputationPremises Δ) (arithmetic : PeanoEvidence ops.successor ops.zero Δ)
    (beforeMember : ProofSyntax Const Δ (.app predicate before))
    (vectorMember : ProofSyntax Const Δ (ops.toSignature.member predicate length vector))
    (afterMember : ProofSyntax Const Δ (.app predicate after))
    (cases : ProofSyntax Const Δ (mixedCases ops.zero ops.successor length slot firstIndex vectorIndex lastIndex target))
    (premisesFree : premises.FunctionExtensionalityFree) (arithmeticFree : arithmetic.Free)
    (beforeFree : beforeMember.FunctionExtensionalityFree) (vectorFree : vectorMember.FunctionExtensionalityFree)
    (afterFree : afterMember.FunctionExtensionalityFree) (casesFree : cases.FunctionExtensionalityFree) :
    (ops.assembleMembership predicate length slot before vector after bottom firstIndex vectorIndex lastIndex target
      premises arithmetic beforeMember vectorMember afterMember cases).FunctionExtensionalityFree :=
  VectorChildMembershipLaws.fromCases_free _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (ops.mixedLeading_free _ _ _ _ _ premises premisesFree)
    (ops.mixedTrailing_free _ _ _ _ _ _ premises vectorMember premisesFree vectorFree)
    (ops.mixedLookupLaw_free _ _ _ _ _ premises premisesFree)
    (IndexedVectorLookupCoverage.fromMembership_free _ _ _ _ arithmetic vectorMember arithmeticFree vectorFree)
    beforeFree afterFree casesFree

#print axioms mixedLookupLaw_free
#print axioms assembleMembership_free
end Mettapedia.Logic.HOL.VectorChildArrays.Operations
