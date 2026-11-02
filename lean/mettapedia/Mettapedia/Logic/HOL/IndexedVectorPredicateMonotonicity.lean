import Mettapedia.Logic.HOL.IndexedVectorPredicateLifting
import Mettapedia.Logic.HOL.PredicateFixedPointInduction

/-!
# Lifting element inclusion through the original vector predicate

An elementwise inclusion supplies the existing position-dependent lifting
condition. Index and vector are unchanged. Intersection projections let one
source vector supply both ordinary membership and root-index evidence without
duplicating or strengthening its source membership assumption.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedVectorPredicateMonotonicity
open FiniteConstructorEncoding PredicateFixedPoint
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} (signature : IndexedVectorPredicate.Signature Const)
    {Γ Ξ : Ctx Base} {Δ : List (Formula Const Γ)}

def inclusionPoint (source target : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (inclusion : ProofSyntax Const Δ (included source target)) :
    ArgumentProof Δ (IndexedVectorPredicateLifting.PointFields signature)
      (IndexedVectorPredicateLifting.pointBody signature source target index vector) := by
  intro Ω images fields
  let source' := HOL.subst images source
  let target' := HOL.subst images target
  let lookup := IndexedVectorPositions.lookup signature (HOL.subst images index) (HOL.subst images vector) fields.1 fields.2.1
  let sourceMember := Term.app source' fields.2.1
  let moved : ProofSyntax Const (Δ.map (HOL.subst images)) (included source' target') :=
    ProofSyntax.castIndices rfl (subst_included images source target) (inclusion.subst images)
  refine .impI (.impI ?_)
  have implication : ProofSyntax Const (sourceMember :: lookup :: Δ.map (HOL.subst images))
      (.imp (.app source' fields.2.1) (.app target' fields.2.1)) :=
    ProofSyntax.castIndices rfl (instantiate_included fields.2.1 source' target')
      (.allE fields.2.1 ((moved.prepend lookup).prepend sourceMember))
  exact .impE implication (.hyp 0)

theorem inclusionPoint_free (source target : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (inclusion : ProofSyntax Const Δ (included source target)) (free : inclusion.FunctionExtensionalityFree)
    (images : Subst Const Γ Ξ) (fields : Arguments Const Ξ (IndexedVectorPredicateLifting.PointFields signature)) :
    (inclusionPoint signature source target index vector inclusion images fields).FunctionExtensionalityFree := by
  unfold inclusionPoint
  refine ⟨?_,True.intro⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  simpa only [ProofSyntax.FunctionExtensionalityFree, ProofSyntax.prepend,
    ProofSyntax.functionExtensionalityFree_mono,
    ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.functionExtensionalityFree_subst] using free

def conditionFromInclusion (source target : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (inclusion : ProofSyntax Const Δ (included source target)) :
    ProofSyntax Const Δ (IndexedVectorPredicateLifting.condition signature source target index vector) :=
  forallArguments_intro _ _ (inclusionPoint signature source target index vector inclusion)

theorem conditionFromInclusion_free (source target : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (inclusion : ProofSyntax Const Δ (included source target)) (free : inclusion.FunctionExtensionalityFree) :
    (conditionFromInclusion signature source target index vector inclusion).FunctionExtensionalityFree :=
  forallArguments_intro_free _ _ _ (inclusionPoint_free signature source target index vector inclusion free)

def lift (source target : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (inclusion : ProofSyntax Const Δ (included source target))
    (member : ProofSyntax Const Δ (signature.member source index vector)) :
    ProofSyntax Const Δ (signature.member target index vector) :=
  IndexedVectorPredicateLifting.relationalLift signature source target index vector member
    (conditionFromInclusion signature source target index vector inclusion)

theorem lift_free (source target : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (inclusion : ProofSyntax Const Δ (included source target))
    (member : ProofSyntax Const Δ (signature.member source index vector))
    (inclusionFree : inclusion.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree) :
    (lift signature source target index vector inclusion member).FunctionExtensionalityFree :=
  IndexedVectorPredicateLifting.relationalLift_free _ _ _ _ _ _ _ memberFree
    (conditionFromInclusion_free _ _ _ _ _ inclusion inclusionFree)

def intersectionRight (first second : Term Const Γ (signature.element ⇒ .prop)) :
    ProofSyntax Const Δ (included (intersection first second) second) := by
  refine .allI (.impI ?_)
  have present : ProofSyntax Const
      (.app (weaken (intersection first second)) (.var .vz) :: weakenHyps Δ)
      (.app (intersection (weaken first) (weaken second)) (.var .vz)) := by
    apply ProofSyntax.castIndices rfl ?_ (.hyp 0)
    simp [weaken,rename_intersection]
  exact .andER (.impE (.eqPropEL (intersection_beta (weaken first) (weaken second) (.var .vz))) present)

theorem intersectionRight_free (first second : Term Const Γ (signature.element ⇒ .prop)) :
    (intersectionRight (Δ := Δ) signature first second).FunctionExtensionalityFree := by
  simp [intersectionRight, intersection_beta_free, ProofSyntax.FunctionExtensionalityFree]

def projectLeft (first second : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (member : ProofSyntax Const Δ (signature.member (intersection first second) index vector)) :
    ProofSyntax Const Δ (signature.member first index vector) :=
  lift signature _ _ index vector (intersection_left first second) member

def projectRight (first second : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (member : ProofSyntax Const Δ (signature.member (intersection first second) index vector)) :
    ProofSyntax Const Δ (signature.member second index vector) :=
  lift signature _ _ index vector (intersectionRight signature first second) member

theorem projectLeft_free (first second : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (member : ProofSyntax Const Δ (signature.member (intersection first second) index vector))
    (free : member.FunctionExtensionalityFree) :
    (projectLeft signature first second index vector member).FunctionExtensionalityFree :=
  lift_free _ _ _ _ _ _ member (intersection_left_free _ _) free

theorem projectRight_free (first second : Term Const Γ (signature.element ⇒ .prop))
    (index : Term Const Γ signature.number) (vector : Term Const Γ signature.vector)
    (member : ProofSyntax Const Δ (signature.member (intersection first second) index vector))
    (free : member.FunctionExtensionalityFree) :
    (projectRight signature first second index vector member).FunctionExtensionalityFree :=
  lift_free _ _ _ _ _ _ member (intersectionRight_free _ _ _) free

#print axioms projectLeft_free
#print axioms projectRight_free
end Mettapedia.Logic.HOL.IndexedVectorPredicateMonotonicity
