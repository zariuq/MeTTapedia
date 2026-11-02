import Mettapedia.Logic.HOL.ActiveArrayMembership
import Mettapedia.Logic.HOL.VectorChildArrayBoundary
import Mettapedia.Logic.HOL.IndexedVectorPredicateLifting
import Mettapedia.Logic.HOL.IndexedVectorPositionBounds
import Mettapedia.Logic.HOL.MixedPositionCoverage

/-!
# Recovering field predicates from the actual mixed child array

A local vector lookup reaches absolute position successor(local). Its bound
proves source activity, and the actual array equation transports the active
membership proof back to that same element. Relational vector induction then
recovers the vector field predicate. Leading and trailing fields use their
own array equations. No child identity is inferred from equality of indices.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.SuccessorOrder.MixedCoverage
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base} {number : Ty Base}
    {successor : ClosedTerm Const (number ⇒ number)} {zero : ClosedTerm Const number}
    {active : Term Const Γ (number ⇒ .prop)} {length : Term Const Γ number} {Δ : List (Formula Const Γ)}

theorem firstFree (coverage : MixedCoverage successor zero active length Δ) (free : coverage.Free) :
    coverage.first.FunctionExtensionalityFree := free.1
theorem interiorFree (coverage : MixedCoverage successor zero active length Δ) (free : coverage.Free) :
    coverage.interior.FunctionExtensionalityFree := free.2.1
theorem lastFree (coverage : MixedCoverage successor zero active length Δ) (free : coverage.Free) :
    coverage.last.FunctionExtensionalityFree := free.2.2
end Mettapedia.Logic.HOL.SuccessorOrder.MixedCoverage

namespace Mettapedia.Logic.HOL.VectorChildArrays.Operations
open FiniteConstructorEncoding SuccessorOrder
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} (ops : Operations Const)
    {Γ Ξ : Ctx Base} {Δ : List (Formula Const Γ)}

def mixedLookupMember (predicate : Term Const Γ (ops.element ⇒ .prop))
    (active : Term Const Γ (ops.number ⇒ .prop)) (length : Term Const Γ ops.number)
    (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector)
    (after bottom : Term Const Γ ops.element) (offset : Term Const Γ ops.number) (element : Term Const Γ ops.element)
    (premises : ops.ComputationPremises Δ)
    (induction : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx Γ ops.zero) (weakenCtx Γ ops.successor)))
    (covered : ProofSyntax Const Δ (interiorCoverage ops.successor active length))
    (given : ProofSyntax Const Δ (ActiveArrayMembership.condition predicate active (ops.mixed length before vector after bottom)))
    (lookup : ProofSyntax Const Δ (IndexedVectorPositions.lookup ops.toSignature length vector offset element)) :
    ProofSyntax Const Δ (.app predicate element) :=
  .impE (.eqPropEL (.eqAppArg predicate (ops.mixedAtLookup length before vector after bottom offset element premises lookup)))
    (ActiveArrayMembership.atSlot predicate active _ (.app (weakenCtx Γ ops.successor) offset) given
      (.impE (interiorAt ops.successor active length offset covered)
        (IndexedVectorPositionBounds.lessOfLookup ops.toSignature length vector offset element induction lookup)))

theorem mixedLookupMember_free (predicate : Term Const Γ (ops.element ⇒ .prop))
    (active : Term Const Γ (ops.number ⇒ .prop)) (length : Term Const Γ ops.number)
    (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector)
    (after bottom : Term Const Γ ops.element) (offset : Term Const Γ ops.number) (element : Term Const Γ ops.element)
    (premises : ops.ComputationPremises Δ)
    (induction : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx Γ ops.zero) (weakenCtx Γ ops.successor)))
    (covered : ProofSyntax Const Δ (interiorCoverage ops.successor active length))
    (given : ProofSyntax Const Δ (ActiveArrayMembership.condition predicate active (ops.mixed length before vector after bottom)))
    (lookup : ProofSyntax Const Δ (IndexedVectorPositions.lookup ops.toSignature length vector offset element))
    (premisesFree : premises.FunctionExtensionalityFree) (inductionFree : induction.FunctionExtensionalityFree)
    (coveredFree : covered.FunctionExtensionalityFree) (givenFree : given.FunctionExtensionalityFree)
    (lookupFree : lookup.FunctionExtensionalityFree) :
    (ops.mixedLookupMember predicate active length before vector after bottom offset element premises induction covered given lookup).FunctionExtensionalityFree :=
  ⟨ops.mixedAtLookup_free _ _ _ _ _ _ _ premises lookup premisesFree lookupFree,
   ActiveArrayMembership.atSlot_free _ _ _ _ given _ givenFree
     ⟨interiorAt_free _ _ _ _ covered coveredFree,
      IndexedVectorPositionBounds.lessOfLookup_free _ _ _ _ _ induction lookup inductionFree lookupFree⟩⟩

def mixedLiftingPoint (source target : Term Const Γ (ops.element ⇒ .prop))
    (active : Term Const Γ (ops.number ⇒ .prop)) (length : Term Const Γ ops.number)
    (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector) (after bottom : Term Const Γ ops.element)
    (premises : ops.ComputationPremises Δ)
    (induction : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx Γ ops.zero) (weakenCtx Γ ops.successor)))
    (covered : ProofSyntax Const Δ (interiorCoverage ops.successor active length))
    (given : ProofSyntax Const Δ (ActiveArrayMembership.condition target active (ops.mixed length before vector after bottom))) :
    ArgumentProof Δ (IndexedVectorPredicateLifting.PointFields ops.toSignature)
      (IndexedVectorPredicateLifting.pointBody ops.toSignature source target length vector) := by
  intro Ω images fields
  let found := IndexedVectorPositions.lookup ops.toSignature (HOL.subst images length) (HOL.subst images vector) fields.1 fields.2.1
  let sourceMember := Term.app (HOL.subst images source) fields.2.1
  have movedInduction : ProofSyntax Const (Δ.map (HOL.subst images)) (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx Ω ops.zero) (weakenCtx Ω ops.successor)) :=
    ProofSyntax.castIndices rfl (SuccessorOrder.inductionPrinciple_subst ops.successor ops.zero images) (induction.subst images)
  have movedCoverage := ProofSyntax.castIndices rfl (interiorCoverage_subst ops.successor images active length) (covered.subst images)
  have movedGiven : ProofSyntax Const (Δ.map (HOL.subst images))
      (ActiveArrayMembership.condition (HOL.subst images target) (HOL.subst images active)
        (ops.mixed (HOL.subst images length) (HOL.subst images before) (HOL.subst images vector)
          (HOL.subst images after) (HOL.subst images bottom))) :=
    ProofSyntax.castIndices rfl (by simp only [ActiveArrayMembership.condition_subst, mixed_subst]) (given.subst images)
  refine .impI (.impI ?_)
  exact ops.mixedLookupMember (HOL.subst images target) (HOL.subst images active)
    (HOL.subst images length) (HOL.subst images before) (HOL.subst images vector) (HOL.subst images after) (HOL.subst images bottom)
    fields.1 fields.2.1 (((premises.subst images).prepend found).prepend sourceMember)
    ((movedInduction.prepend found).prepend sourceMember) ((movedCoverage.prepend found).prepend sourceMember)
    ((movedGiven.prepend found).prepend sourceMember) (.hyp 1)

theorem mixedLiftingPoint_free (source target : Term Const Γ (ops.element ⇒ .prop))
    (active : Term Const Γ (ops.number ⇒ .prop)) (length : Term Const Γ ops.number)
    (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector) (after bottom : Term Const Γ ops.element)
    (premises : ops.ComputationPremises Δ)
    (induction : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx Γ ops.zero) (weakenCtx Γ ops.successor)))
    (covered : ProofSyntax Const Δ (interiorCoverage ops.successor active length))
    (given : ProofSyntax Const Δ (ActiveArrayMembership.condition target active (ops.mixed length before vector after bottom)))
    (premisesFree : premises.FunctionExtensionalityFree) (inductionFree : induction.FunctionExtensionalityFree)
    (coveredFree : covered.FunctionExtensionalityFree) (givenFree : given.FunctionExtensionalityFree)
    (images : Subst Const Γ Ξ) (fields : Arguments Const Ξ (IndexedVectorPredicateLifting.PointFields ops.toSignature)) :
    (ops.mixedLiftingPoint source target active length before vector after bottom premises induction covered given images fields).FunctionExtensionalityFree := by
  unfold mixedLiftingPoint
  apply mixedLookupMember_free
  · exact ((premises.subst images).prepend _).prepend_free _
      ((premises.subst images).prepend_free _ (premises.subst_free images premisesFree))
  · simpa only [ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono,
      ProofSyntax.functionExtensionalityFree_castIndices, ProofSyntax.functionExtensionalityFree_subst] using inductionFree
  · simpa only [ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono,
      ProofSyntax.functionExtensionalityFree_castIndices, ProofSyntax.functionExtensionalityFree_subst] using coveredFree
  · simpa only [ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono,
      ProofSyntax.functionExtensionalityFree_castIndices, ProofSyntax.functionExtensionalityFree_subst] using givenFree
  · trivial

def mixedReflectVector (source target : Term Const Γ (ops.element ⇒ .prop))
    (active : Term Const Γ (ops.number ⇒ .prop)) (length : Term Const Γ ops.number)
    (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector) (after bottom : Term Const Γ ops.element)
    (premises : ops.ComputationPremises Δ)
    (induction : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx Γ ops.zero) (weakenCtx Γ ops.successor)))
    (covered : ProofSyntax Const Δ (interiorCoverage ops.successor active length))
    (given : ProofSyntax Const Δ (ActiveArrayMembership.condition target active (ops.mixed length before vector after bottom)))
    (member : ProofSyntax Const Δ (ops.toSignature.member source length vector)) :
    ProofSyntax Const Δ (ops.toSignature.member target length vector) :=
  IndexedVectorPredicateLifting.relationalLift ops.toSignature source target length vector member
    (forallArguments_intro _ _ (ops.mixedLiftingPoint source target active length before vector after bottom
      premises induction covered given))

theorem mixedReflectVector_free (source target : Term Const Γ (ops.element ⇒ .prop))
    (active : Term Const Γ (ops.number ⇒ .prop)) (length : Term Const Γ ops.number)
    (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector) (after bottom : Term Const Γ ops.element)
    (premises : ops.ComputationPremises Δ)
    (induction : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx Γ ops.zero) (weakenCtx Γ ops.successor)))
    (covered : ProofSyntax Const Δ (interiorCoverage ops.successor active length))
    (given : ProofSyntax Const Δ (ActiveArrayMembership.condition target active (ops.mixed length before vector after bottom)))
    (member : ProofSyntax Const Δ (ops.toSignature.member source length vector))
    (premisesFree : premises.FunctionExtensionalityFree) (inductionFree : induction.FunctionExtensionalityFree)
    (coveredFree : covered.FunctionExtensionalityFree) (givenFree : given.FunctionExtensionalityFree)
    (memberFree : member.FunctionExtensionalityFree) :
    (ops.mixedReflectVector source target active length before vector after bottom premises induction covered given member).FunctionExtensionalityFree :=
  IndexedVectorPredicateLifting.relationalLift_free _ _ _ _ _ _ _ memberFree
    (forallArguments_intro_free _ _ _ (ops.mixedLiftingPoint_free source target active length before vector after bottom
      premises induction covered given premisesFree inductionFree coveredFree givenFree))

@[irreducible] def mixedReflectVectorProgram (source target : Term Const Γ (ops.element ⇒ .prop))
    (active : Term Const Γ (ops.number ⇒ .prop)) (length : Term Const Γ ops.number)
    (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector) (after bottom : Term Const Γ ops.element)
    (premises : ops.ComputationPremises Δ)
    (induction : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx Γ ops.zero) (weakenCtx Γ ops.successor)))
    (covered : ProofSyntax Const Δ (interiorCoverage ops.successor active length))
    (given : ProofSyntax Const Δ (ActiveArrayMembership.condition target active (ops.mixed length before vector after bottom)))
    (member : ProofSyntax Const Δ (ops.toSignature.member source length vector)) :
    { proof : ProofSyntax Const Δ (ops.toSignature.member target length vector) //
      premises.FunctionExtensionalityFree → induction.FunctionExtensionalityFree → covered.FunctionExtensionalityFree →
      given.FunctionExtensionalityFree → member.FunctionExtensionalityFree → proof.FunctionExtensionalityFree } :=
  ⟨ops.mixedReflectVector source target active length before vector after bottom premises induction covered given member,
   ops.mixedReflectVector_free source target active length before vector after bottom premises induction covered given member⟩

def mixedReflectLeading (predicate : Term Const Γ (ops.element ⇒ .prop))
    (active : Term Const Γ (ops.number ⇒ .prop)) (length : Term Const Γ ops.number)
    (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector) (after bottom : Term Const Γ ops.element)
    (premises : ops.ComputationPremises Δ)
    (given : ProofSyntax Const Δ (ActiveArrayMembership.condition predicate active (ops.mixed length before vector after bottom)))
    (covered : ProofSyntax Const Δ (.app active (weakenCtx Γ ops.zero))) : ProofSyntax Const Δ (.app predicate before) :=
  .impE (.eqPropEL (.eqAppArg predicate (ops.mixedLeading length before vector after bottom premises)))
    (ActiveArrayMembership.atSlot predicate active _ _ given covered)

theorem mixedReflectLeading_free (predicate : Term Const Γ (ops.element ⇒ .prop))
    (active : Term Const Γ (ops.number ⇒ .prop)) (length : Term Const Γ ops.number)
    (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector) (after bottom : Term Const Γ ops.element)
    (premises : ops.ComputationPremises Δ)
    (given : ProofSyntax Const Δ (ActiveArrayMembership.condition predicate active (ops.mixed length before vector after bottom)))
    (covered : ProofSyntax Const Δ (.app active (weakenCtx Γ ops.zero)))
    (premisesFree : premises.FunctionExtensionalityFree) (givenFree : given.FunctionExtensionalityFree)
    (coveredFree : covered.FunctionExtensionalityFree) :
    (ops.mixedReflectLeading predicate active length before vector after bottom premises given covered).FunctionExtensionalityFree :=
  ⟨ops.mixedLeading_free _ _ _ _ _ premises premisesFree, ActiveArrayMembership.atSlot_free _ _ _ _ given covered givenFree coveredFree⟩

def mixedReflectTrailing (source target : Term Const Γ (ops.element ⇒ .prop))
    (active : Term Const Γ (ops.number ⇒ .prop)) (length : Term Const Γ ops.number)
    (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector) (after bottom : Term Const Γ ops.element)
    (premises : ops.ComputationPremises Δ) (member : ProofSyntax Const Δ (ops.toSignature.member source length vector))
    (given : ProofSyntax Const Δ (ActiveArrayMembership.condition target active (ops.mixed length before vector after bottom)))
    (covered : ProofSyntax Const Δ (.app active (.app (weakenCtx Γ ops.successor) length))) :
    ProofSyntax Const Δ (.app target after) :=
  .impE (.eqPropEL (.eqAppArg target (ops.mixedTrailing source length before vector after bottom premises member)))
    (ActiveArrayMembership.atSlot target active _ _ given covered)

theorem mixedReflectTrailing_free (source target : Term Const Γ (ops.element ⇒ .prop))
    (active : Term Const Γ (ops.number ⇒ .prop)) (length : Term Const Γ ops.number)
    (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector) (after bottom : Term Const Γ ops.element)
    (premises : ops.ComputationPremises Δ) (member : ProofSyntax Const Δ (ops.toSignature.member source length vector))
    (given : ProofSyntax Const Δ (ActiveArrayMembership.condition target active (ops.mixed length before vector after bottom)))
    (covered : ProofSyntax Const Δ (.app active (.app (weakenCtx Γ ops.successor) length)))
    (premisesFree : premises.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree)
    (givenFree : given.FunctionExtensionalityFree) (coveredFree : covered.FunctionExtensionalityFree) :
    (ops.mixedReflectTrailing source target active length before vector after bottom premises member given covered).FunctionExtensionalityFree :=
  ⟨ops.mixedTrailing_free _ _ _ _ _ _ premises member premisesFree memberFree,
    ActiveArrayMembership.atSlot_free _ _ _ _ given covered givenFree coveredFree⟩

#print axioms mixedReflectVector_free
end Mettapedia.Logic.HOL.VectorChildArrays.Operations
