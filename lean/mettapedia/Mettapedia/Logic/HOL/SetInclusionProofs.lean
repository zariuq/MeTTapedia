import Mettapedia.Logic.HOL.SetMembershipProofs

/-!
# Retained set inclusion and extensional equality

Inclusion is the existing universally quantified membership implication.
Its substitution, weakening, composition and equality laws construct ordinary
HOL proof syntax. Antisymmetry consumes the supplied set-extensionality law.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.SetInclusionProofs
open SetComprehensionProofs SetMembershipProofs
open Embedding.ZFSetHenkinInterpretation (set)
universe v
variable {Const : Ty Unit → Type v} (core : Core Const)
variable {Γ Ξ : Ctx Unit} {Δ : List (Formula Const Γ)}

theorem subst_included (theta : Subst Const Γ Ξ) (left right : Term Const Γ set) :
    HOL.subst theta (included core left right) = included core (HOL.subst theta left) (HOL.subst theta right) := by
  simp only [included,member,HOL.subst,HOL.subst_weaken,Subst.lift]

theorem rename_included (rho : Rename Unit Γ Ξ) (left right : Term Const Γ set) :
    HOL.rename rho (included core left right) = included core (HOL.rename rho left) (HOL.rename rho right) := by
  simpa only [HOL.subst_ofRename] using subst_included core (Subst.ofRename rho) left right

def weakenInclusion {added : Ty Unit} (left right : Term Const Γ set)
    (proof : ProofSyntax Const Δ (included core left right)) :
    ProofSyntax Const (weakenHyps (σ := added) Δ) (included core (HOL.weaken left) (HOL.weaken right)) :=
  .castIndices rfl (rename_included core Rename.weaken left right) (PredicateFixedPoint.weakenProof proof)

theorem weakenInclusion_free {added : Ty Unit} (left right : Term Const Γ set)
    (proof : ProofSyntax Const Δ (included core left right)) (free : proof.FunctionExtensionalityFree) :
    (weakenInclusion (added := added) core left right proof).FunctionExtensionalityFree := by
  unfold weakenInclusion
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  simpa [PredicateFixedPoint.weakenProof] using free

theorem eliminate_free (left right point : Term Const Γ set)
    (inclusion : ProofSyntax Const Δ (included core left right))
    (present : ProofSyntax Const Δ (member core point left))
    (inclusionFree : inclusion.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (subsetElim core left right point inclusion present).FunctionExtensionalityFree := by
  simp only [subsetElim,ProofSyntax.FunctionExtensionalityFree,ProofSyntax.functionExtensionalityFree_castIndices]
  exact ⟨inclusionFree,presentFree⟩

def reflexive (point : Term Const Γ set) : ProofSyntax Const Δ (included core point point) := .allI (.impI (.hyp 0))

def transitive (first middle last : Term Const Γ set)
    (before : ProofSyntax Const Δ (included core first middle))
    (after : ProofSyntax Const Δ (included core middle last)) : ProofSyntax Const Δ (included core first last) :=
  .allI (.impI (subsetElim core (HOL.weaken middle) (HOL.weaken last) (.var .vz)
    ((weakenInclusion core middle last after).prepend _)
    (subsetElim core (HOL.weaken first) (HOL.weaken middle) (.var .vz)
      ((weakenInclusion core first middle before).prepend _) (.hyp 0))))

def fromEquality (left right : Term Const Γ set) (equal : ProofSyntax Const Δ (.eq left right)) :
    ProofSyntax Const Δ (included core left right) :=
  .allI (.impI (transportBound core (.var .vz) ((PredicateFixedPoint.weakenProof equal).prepend _) (.hyp 0)))

def transportEndpoints {left right left' right' : Term Const Γ set}
    (leftEqual : ProofSyntax Const Δ (.eq left left')) (rightEqual : ProofSyntax Const Δ (.eq right right'))
    (proof : ProofSyntax Const Δ (included core left right)) : ProofSyntax Const Δ (included core left' right') :=
  .allI (.impI (transportBound core (.var .vz) ((PredicateFixedPoint.weakenProof rightEqual).prepend _)
    (subsetElim core (HOL.weaken left) (HOL.weaken right) (.var .vz)
      ((weakenInclusion core left right proof).prepend _)
      (transportBound core (.var .vz) (.eqSymm ((PredicateFixedPoint.weakenProof leftEqual).prepend _)) (.hyp 0)))))

def antisymmetric (left right : Term Const Γ set)
    (law : ProofSyntax Const Δ (lawAt core Embedding.ZFSetHenkinInterpretation.extensionality))
    (forward : ProofSyntax Const Δ (included core left right))
    (backward : ProofSyntax Const Δ (included core right left)) : ProofSyntax Const Δ (.eq left right) :=
  .impE (SetComprehensionProofs.extensionality core left right law)
    (.allI (.andI
      (.impI (subsetElim core (HOL.weaken left) (HOL.weaken right) (.var .vz)
        ((weakenInclusion core left right forward).prepend _) (.hyp 0)))
      (.impI (subsetElim core (HOL.weaken right) (HOL.weaken left) (.var .vz)
        ((weakenInclusion core right left backward).prepend _) (.hyp 0)))))

theorem reflexive_free (point : Term Const Γ set) : (reflexive (Δ := Δ) core point).FunctionExtensionalityFree := trivial

theorem transitive_free (first middle last : Term Const Γ set)
    (before : ProofSyntax Const Δ (included core first middle))
    (after : ProofSyntax Const Δ (included core middle last))
    (beforeFree : before.FunctionExtensionalityFree) (afterFree : after.FunctionExtensionalityFree) :
    (transitive core first middle last before after).FunctionExtensionalityFree := by
  unfold transitive
  apply eliminate_free
  · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (weakenInclusion_free core middle last after afterFree)
  · apply eliminate_free
    · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (weakenInclusion_free core first middle before beforeFree)
    · trivial

theorem fromEquality_free (left right : Term Const Γ set) (equal : ProofSyntax Const Δ (.eq left right))
    (free : equal.FunctionExtensionalityFree) : (fromEquality core left right equal).FunctionExtensionalityFree := by
  unfold fromEquality
  apply transportBound_free
  · apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
    simpa [PredicateFixedPoint.weakenProof] using free
  · trivial

theorem antisymmetric_free (left right : Term Const Γ set)
    (law : ProofSyntax Const Δ (lawAt core Embedding.ZFSetHenkinInterpretation.extensionality))
    (forward : ProofSyntax Const Δ (included core left right))
    (backward : ProofSyntax Const Δ (included core right left))
    (lawFree : law.FunctionExtensionalityFree) (forwardFree : forward.FunctionExtensionalityFree)
    (backwardFree : backward.FunctionExtensionalityFree) :
    (antisymmetric core left right law forward backward).FunctionExtensionalityFree := by
  unfold antisymmetric
  constructor
  · simpa only [SetComprehensionProofs.extensionality,ProofSyntax.functionExtensionalityFree_castIndices,
      ProofSyntax.FunctionExtensionalityFree] using lawFree
  · constructor
    · apply eliminate_free
      · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (weakenInclusion_free core left right forward forwardFree)
      · trivial
    · apply eliminate_free
      · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (weakenInclusion_free core right left backward backwardFree)
      · trivial

theorem transportEndpoints_free {left right left' right' : Term Const Γ set}
    (leftEqual : ProofSyntax Const Δ (.eq left left')) (rightEqual : ProofSyntax Const Δ (.eq right right'))
    (proof : ProofSyntax Const Δ (included core left right))
    (leftFree : leftEqual.FunctionExtensionalityFree) (rightFree : rightEqual.FunctionExtensionalityFree)
    (free : proof.FunctionExtensionalityFree) : (transportEndpoints core leftEqual rightEqual proof).FunctionExtensionalityFree := by
  unfold transportEndpoints
  apply transportBound_free
  · simpa [ProofSyntax.prepend,PredicateFixedPoint.weakenProof] using rightFree
  · apply eliminate_free
    · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr (weakenInclusion_free core _ _ proof free)
    · apply transportBound_free
      · change ((PredicateFixedPoint.weakenProof leftEqual).prepend _).FunctionExtensionalityFree
        simpa [ProofSyntax.prepend,PredicateFixedPoint.weakenProof] using leftFree
      · trivial

end Mettapedia.Logic.HOL.SetInclusionProofs
