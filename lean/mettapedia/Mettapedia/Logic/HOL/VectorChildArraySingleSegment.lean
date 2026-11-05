import Mettapedia.Logic.HOL.VectorChildArrayBoundary
import Mettapedia.Logic.HOL.IndexedVectorLookupCoverage
import Mettapedia.Logic.HOL.SuccessorOrderOffsetWitnesses

/-!
# One open vector as a complete child array

The actual selected vector recursor copies the original ordered vector and
then returns constant bottom. Bounded-position membership follows from the
proved vector lookup coverage theorem, retaining the lookup and its element
predicate under one existential. Outside the vector, natural comparison and
the original suffix equations establish padding. No supplied array law or
global choice of lookup witnesses replaces these proofs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.VectorChildArrays.Operations
open FiniteConstructorEncoding SuccessorOrder
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} (ops : Operations Const)
  {Γ Ξ : Ctx Base} {Δ : List (Formula Const Γ)}

def single (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector)
    (bottom : Term Const Γ ops.element) : Term Const Γ ops.ArrayType :=
  ops.suffix index vector (ops.padding bottom)

@[simp] theorem single_subst (images : Subst Const Γ Ξ) (index : Term Const Γ ops.number)
    (vector : Term Const Γ ops.vector) (bottom : Term Const Γ ops.element) :
    HOL.subst images (ops.single index vector bottom) =
      ops.single (HOL.subst images index) (HOL.subst images vector) (HOL.subst images bottom) := by
  simp only [single, suffix_subst, padding_subst]

@[simp] theorem single_rename (rho : Rename Base Γ Ξ) (index : Term Const Γ ops.number)
    (vector : Term Const Γ ops.vector) (bottom : Term Const Γ ops.element) :
    HOL.rename rho (ops.single index vector bottom) =
      ops.single (HOL.rename rho index) (HOL.rename rho vector) (HOL.rename rho bottom) := by
  simpa only [subst_ofRename] using ops.single_subst (Subst.ofRename rho) index vector bottom

def singleAtLookup (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector)
    (bottom : Term Const Γ ops.element) (position : Term Const Γ ops.number) (element : Term Const Γ ops.element)
    (premises : ops.ComputationPremises Δ)
    (present : ProofSyntax Const Δ (IndexedVectorPositions.lookup ops.toSignature index vector position element)) :
    ProofSyntax Const Δ (.eq (.app (ops.single index vector bottom) position) element) :=
  ops.valueAtLookup (ops.padding bottom) index vector position element premises present

theorem singleAtLookup_free (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector)
    (bottom : Term Const Γ ops.element) (position : Term Const Γ ops.number) (element : Term Const Γ ops.element)
    (premises : ops.ComputationPremises Δ)
    (present : ProofSyntax Const Δ (IndexedVectorPositions.lookup ops.toSignature index vector position element))
    (premisesFree : premises.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (ops.singleAtLookup index vector bottom position element premises present).FunctionExtensionalityFree :=
  ops.valueAtLookup_free _ _ _ _ _ premises present premisesFree presentFree

def singleMemberAtWitness (predicate : Term Const Γ (ops.element ⇒ .prop))
    (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector) (bottom : Term Const Γ ops.element)
    (position : Term Const Γ ops.number) (premises : ops.ComputationPremises Δ)
    (present : ProofSyntax Const Δ (IndexedVectorLookupWitnesses.evidence ops.toSignature predicate index vector position)) :
    ProofSyntax Const Δ (.app predicate (.app (ops.single index vector bottom) position)) := by
  apply ProofSyntax.exE present
  let body : Formula Const (ops.element :: Γ) :=
    .and (IndexedVectorPositions.lookup ops.toSignature (weaken index) (weaken vector) (weaken position) (.var .vz))
      (.app (weaken predicate) (.var .vz))
  have same := ops.singleAtLookup (weaken index) (weaken vector) (weaken bottom) (weaken position) (.var .vz)
    ((premises.weaken ops.element).prepend body) (.andEL (.hyp 0))
  apply ProofSyntax.castIndices rfl ?_ (.impE (.eqPropER (.eqAppArg (weaken predicate) same)) (.andER (.hyp 0)))
  simp only [weaken, HOL.rename, single_rename]

theorem singleMemberAtWitness_free (predicate : Term Const Γ (ops.element ⇒ .prop))
    (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector) (bottom : Term Const Γ ops.element)
    (position : Term Const Γ ops.number) (premises : ops.ComputationPremises Δ)
    (present : ProofSyntax Const Δ (IndexedVectorLookupWitnesses.evidence ops.toSignature predicate index vector position))
    (premisesFree : premises.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (ops.singleMemberAtWitness predicate index vector bottom position premises present).FunctionExtensionalityFree := by
  unfold singleMemberAtWitness
  refine ⟨presentFree, ?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  refine ⟨?_, True.intro⟩
  apply ops.singleAtLookup_free
  · exact (premises.weaken ops.element).prepend_free _ (premises.weaken_free ops.element premisesFree)
  · trivial

def singleMemberAtBound (predicate : Term Const Γ (ops.element ⇒ .prop))
    (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector) (bottom : Term Const Γ ops.element)
    (position : Term Const Γ ops.number) (premises : ops.ComputationPremises Δ)
    (arithmetic : PeanoEvidence ops.successor ops.zero Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member predicate index vector))
    (bounded : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less ops.successor)) position) index)) :
    ProofSyntax Const Δ (.app predicate (.app (ops.single index vector bottom) position)) :=
  ops.singleMemberAtWitness predicate index vector bottom position premises
    (IndexedVectorLookupCoverage.witnessFromBound ops.toSignature predicate index vector position arithmetic member bounded)

theorem singleMemberAtBound_free (predicate : Term Const Γ (ops.element ⇒ .prop))
    (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector) (bottom : Term Const Γ ops.element)
    (position : Term Const Γ ops.number) (premises : ops.ComputationPremises Δ)
    (arithmetic : PeanoEvidence ops.successor ops.zero Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member predicate index vector))
    (bounded : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less ops.successor)) position) index))
    (premisesFree : premises.FunctionExtensionalityFree) (arithmeticFree : arithmetic.Free)
    (memberFree : member.FunctionExtensionalityFree) (boundedFree : bounded.FunctionExtensionalityFree) :
    (ops.singleMemberAtBound predicate index vector bottom position premises arithmetic member bounded).FunctionExtensionalityFree :=
  ops.singleMemberAtWitness_free _ _ _ _ _ premises _ premisesFree
    (IndexedVectorLookupCoverage.witnessFromBound_free _ _ _ _ _ _ member bounded arithmeticFree memberFree boundedFree)

def singleAtEnd (predicate : Term Const Γ (ops.element ⇒ .prop))
    (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector) (bottom : Term Const Γ ops.element)
    (premises : ops.ComputationPremises Δ) (member : ProofSyntax Const Δ (ops.toSignature.member predicate index vector)) :
    ProofSyntax Const Δ (.eq (.app (ops.single index vector bottom) index) bottom) :=
  .eqTrans (ops.valueAtEnd predicate (ops.padding bottom) index vector premises member)
    (ops.padding_apply bottom (weakenCtx Γ ops.zero))

theorem singleAtEnd_free (predicate : Term Const Γ (ops.element ⇒ .prop))
    (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector) (bottom : Term Const Γ ops.element)
    (premises : ops.ComputationPremises Δ) (member : ProofSyntax Const Δ (ops.toSignature.member predicate index vector))
    (premisesFree : premises.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree) :
    (ops.singleAtEnd predicate index vector bottom premises member).FunctionExtensionalityFree :=
  ⟨ops.valueAtEnd_free _ _ _ _ premises member premisesFree memberFree, ops.padding_apply_free _ _⟩

def singleAfterSum (predicate : Term Const Γ (ops.element ⇒ .prop))
    (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector) (bottom : Term Const Γ ops.element)
    (offset position : Term Const Γ ops.number) (premises : ops.ComputationPremises Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member predicate index vector))
    (sum : ProofSyntax Const Δ (ops.sumAt index offset position)) :
    ProofSyntax Const Δ (.eq (.app (ops.single index vector bottom) position) bottom) :=
  .eqTrans (ops.valueAfterVector predicate (ops.padding bottom) index vector offset position premises member sum)
    (ops.padding_apply bottom offset)

theorem singleAfterSum_free (predicate : Term Const Γ (ops.element ⇒ .prop))
    (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector) (bottom : Term Const Γ ops.element)
    (offset position : Term Const Γ ops.number) (premises : ops.ComputationPremises Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member predicate index vector))
    (sum : ProofSyntax Const Δ (ops.sumAt index offset position))
    (premisesFree : premises.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree)
    (sumFree : sum.FunctionExtensionalityFree) :
    (ops.singleAfterSum predicate index vector bottom offset position premises member sum).FunctionExtensionalityFree :=
  ⟨ops.valueAfterVector_free _ _ _ _ _ _ premises member sum premisesFree memberFree sumFree, ops.padding_apply_free _ _⟩

def singleAfter (predicate : Term Const Γ (ops.element ⇒ .prop))
    (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector) (bottom : Term Const Γ ops.element)
    (position : Term Const Γ ops.number) (premises : ops.ComputationPremises Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member predicate index vector))
    (later : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less ops.successor)) index) position)) :
    ProofSyntax Const Δ (.eq (.app (ops.single index vector bottom) position) bottom) := by
  have witness := less_has_successorOffset ops.successor ops.zero index position later
  apply ProofSyntax.exE witness
  let body : Formula Const (ops.number :: Γ) :=
    .app (.app (.app (weakenCtx _ (sum ops.zero ops.successor)) (weaken index))
      (.app (weakenCtx _ ops.successor) (.var .vz))) (weaken position)
  have currentMember : ProofSyntax Const (body :: weakenHyps Δ)
      (ops.toSignature.member (weaken predicate) (weaken index) (weaken vector)) :=
    ProofSyntax.castIndices rfl (ops.toSignature.rename_member Rename.weaken predicate index vector)
      ((member.rename Rename.weaken).prepend body)
  apply ProofSyntax.castIndices rfl ?_
    (ops.singleAfterSum (weaken predicate) (weaken index) (weaken vector) (weaken bottom)
      (.app (weakenCtx _ ops.successor) (.var .vz)) (weaken position)
      ((premises.weaken ops.number).prepend body) currentMember (.hyp 0))
  simp only [weaken, HOL.rename, single_rename]

theorem singleAfter_free (predicate : Term Const Γ (ops.element ⇒ .prop))
    (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector) (bottom : Term Const Γ ops.element)
    (position : Term Const Γ ops.number) (premises : ops.ComputationPremises Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member predicate index vector))
    (later : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less ops.successor)) index) position))
    (premisesFree : premises.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree)
    (laterFree : later.FunctionExtensionalityFree) :
    (ops.singleAfter predicate index vector bottom position premises member later).FunctionExtensionalityFree := by
  unfold singleAfter
  refine ⟨less_has_successorOffset_free _ _ _ _ later laterFree, ?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply ops.singleAfterSum_free
  · exact (premises.weaken ops.number).prepend_free _ (premises.weaken_free ops.number premisesFree)
  · simpa only [ProofSyntax.functionExtensionalityFree_castIndices, ProofSyntax.prepend,
      ProofSyntax.functionExtensionalityFree_mono, ProofSyntax.functionExtensionalityFree_rename] using memberFree
  · trivial

def singlePadding (predicate : Term Const Γ (ops.element ⇒ .prop))
    (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector) (bottom : Term Const Γ ops.element)
    (position : Term Const Γ ops.number) (premises : ops.ComputationPremises Δ)
    (induction : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx Γ ops.zero) (weakenCtx Γ ops.successor)))
    (member : ProofSyntax Const Δ (ops.toSignature.member predicate index vector))
    (inactive : ProofSyntax Const Δ (.not (.app (.app (weakenCtx Γ (less ops.successor)) position) index))) :
    ProofSyntax Const Δ (.eq (.app (ops.single index vector bottom) position) bottom) :=
  .orE (comparisonCoverage ops.successor ops.zero index position induction)
    (ops.singleAfter predicate index vector bottom position (premises.prepend _) (member.prepend _) (.hyp 0))
    (.orE (.hyp 0)
      (.eqTrans (.eqAppArg (ops.single index vector bottom) (.eqSymm (.hyp 0)))
        (ops.singleAtEnd predicate index vector bottom ((premises.prepend _).prepend _) ((member.prepend _).prepend _)))
      (.botE (.notE ((inactive.prepend _).prepend _) (.hyp 0))))

theorem singlePadding_free (predicate : Term Const Γ (ops.element ⇒ .prop))
    (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector) (bottom : Term Const Γ ops.element)
    (position : Term Const Γ ops.number) (premises : ops.ComputationPremises Δ)
    (induction : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx Γ ops.zero) (weakenCtx Γ ops.successor)))
    (member : ProofSyntax Const Δ (ops.toSignature.member predicate index vector))
    (inactive : ProofSyntax Const Δ (.not (.app (.app (weakenCtx Γ (less ops.successor)) position) index)))
    (premisesFree : premises.FunctionExtensionalityFree) (inductionFree : induction.FunctionExtensionalityFree)
    (memberFree : member.FunctionExtensionalityFree) (inactiveFree : inactive.FunctionExtensionalityFree) :
    (ops.singlePadding predicate index vector bottom position premises induction member inactive).FunctionExtensionalityFree := by
  unfold singlePadding
  refine ⟨comparisonCoverage_free _ _ _ _ induction inductionFree, ?_, ?_⟩
  · exact ops.singleAfter_free _ _ _ _ _ (premises.prepend _) (member.prepend _) (.hyp 0)
      (premises.prepend_free _ premisesFree) ((ProofSyntax.functionExtensionalityFree_mono _ _).mpr memberFree) trivial
  · refine ⟨True.intro, ?_, ?_⟩
    · refine ⟨True.intro, ?_⟩
      exact ops.singleAtEnd_free _ _ _ _ ((premises.prepend _).prepend _) ((member.prepend _).prepend _)
        ((premises.prepend _).prepend_free _ (premises.prepend_free _ premisesFree))
        ((ProofSyntax.functionExtensionalityFree_mono _ _).mpr ((ProofSyntax.functionExtensionalityFree_mono _ _).mpr memberFree))
    · exact ⟨(ProofSyntax.functionExtensionalityFree_mono _ _).mpr
        ((ProofSyntax.functionExtensionalityFree_mono _ _).mpr inactiveFree), True.intro⟩

#print axioms singleMemberAtBound
#print axioms singlePadding
#print axioms singlePadding_free

end Mettapedia.Logic.HOL.VectorChildArrays.Operations
