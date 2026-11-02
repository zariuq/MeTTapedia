import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateStructuralProfile

/-!
# Retained evidence operations for the selected structural profile

Identity introduction retains both endpoint-domain proofs. Elimination exposes
those guards and the designated witness equation. These are operations for the
explicit HOL equality profile, without an intensional Id/J reflection claim.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading.StructuralProfile

open Mettapedia.Logic
local infixr:60 " ⇒ " => HOL.Ty.arr
universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}
    {endpoint evidence : HOL.Ty Base} {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)}

def identityProperty (witness : HOL.ClosedTerm Const evidence)
    (domain : HOL.Term Const Γ (endpoint ⇒ .prop)) (left right : HOL.Term Const Γ endpoint)
    (value : HOL.Term Const Γ evidence) : HOL.Formula Const Γ :=
  .and (.app domain left) (.and (.app domain right) (HOL.EqualityWitness.property witness left right value))

def identity_beta (witness : HOL.ClosedTerm Const evidence)
    (domain : HOL.Term Const Γ (endpoint ⇒ .prop)) (left right : HOL.Term Const Γ endpoint)
    (value : HOL.Term Const Γ evidence) : HOL.ProofSyntax Const Δ
      (.eq (.app (identityPredicate witness domain left right) value)
        (identityProperty witness domain left right value)) := by
  apply HOL.ProofSyntax.castIndices rfl ?_ (.beta value
    (.and (.app (HOL.weaken domain) (HOL.weaken left))
      (.and (.app (HOL.weaken domain) (HOL.weaken right))
        (HOL.EqualityWitness.property witness (HOL.weaken left) (HOL.weaken right) (.var .vz)))))
  have domainCancel : HOL.subst (HOL.Subst.single value) (HOL.weaken domain) = domain :=
    HOL.instantiate_weaken value domain
  have leftCancel : HOL.subst (HOL.Subst.single value) (HOL.weaken left) = left :=
    HOL.instantiate_weaken value left
  have rightCancel : HOL.subst (HOL.Subst.single value) (HOL.weaken right) = right :=
    HOL.instantiate_weaken value right
  simp only [identityPredicate, identityProperty, HOL.instantiate, HOL.subst,
    HOL.EqualityWitness.subst_property, domainCancel, leftCancel, rightCancel, HOL.Subst.single]

theorem identity_beta_free (witness : HOL.ClosedTerm Const evidence)
    (domain : HOL.Term Const Γ (endpoint ⇒ .prop)) (left right : HOL.Term Const Γ endpoint)
    (value : HOL.Term Const Γ evidence) :
    (identity_beta (Δ := Δ) witness domain left right value).FunctionExtensionalityFree := by
  simp [identity_beta, HOL.ProofSyntax.FunctionExtensionalityFree]

def identity_introduce (witness : HOL.ClosedTerm Const evidence)
    (domain : HOL.Term Const Γ (endpoint ⇒ .prop)) (left right : HOL.Term Const Γ endpoint)
    (leftMember : HOL.ProofSyntax Const Δ (.app domain left))
    (rightMember : HOL.ProofSyntax Const Δ (.app domain right))
    (equal : HOL.ProofSyntax Const Δ (.eq left right)) :
    HOL.ProofSyntax Const Δ (.app (identityPredicate witness domain left right) (HOL.weakenCtx Γ witness)) :=
  .impE (.eqPropER (identity_beta witness domain left right _))
    (.andI leftMember (.andI rightMember (.andI (.eqRefl _) equal)))

theorem identity_introduce_free (witness : HOL.ClosedTerm Const evidence)
    (domain : HOL.Term Const Γ (endpoint ⇒ .prop)) (left right : HOL.Term Const Γ endpoint)
    (leftMember : HOL.ProofSyntax Const Δ (.app domain left))
    (rightMember : HOL.ProofSyntax Const Δ (.app domain right))
    (equal : HOL.ProofSyntax Const Δ (.eq left right))
    (leftFree : leftMember.FunctionExtensionalityFree) (rightFree : rightMember.FunctionExtensionalityFree)
    (equalFree : equal.FunctionExtensionalityFree) :
    (identity_introduce witness domain left right leftMember rightMember equal).FunctionExtensionalityFree := by
  simp [identity_introduce, HOL.ProofSyntax.FunctionExtensionalityFree, identity_beta_free,
    leftFree, rightFree, equalFree]

def identity_eliminate (witness : HOL.ClosedTerm Const evidence)
    (domain : HOL.Term Const Γ (endpoint ⇒ .prop)) (left right : HOL.Term Const Γ endpoint)
    (value : HOL.Term Const Γ evidence)
    (member : HOL.ProofSyntax Const Δ (.app (identityPredicate witness domain left right) value)) :
    HOL.ProofSyntax Const Δ (identityProperty witness domain left right value) :=
  .impE (.eqPropEL (identity_beta witness domain left right value)) member

theorem identity_eliminate_free (witness : HOL.ClosedTerm Const evidence)
    (domain : HOL.Term Const Γ (endpoint ⇒ .prop)) (left right : HOL.Term Const Γ endpoint)
    (value : HOL.Term Const Γ evidence)
    (member : HOL.ProofSyntax Const Δ (.app (identityPredicate witness domain left right) value))
    (memberFree : member.FunctionExtensionalityFree) :
    (identity_eliminate witness domain left right value member).FunctionExtensionalityFree := by
  simp [identity_eliminate, HOL.ProofSyntax.FunctionExtensionalityFree, identity_beta_free, memberFree]

def reflexivityAt (witness : HOL.ClosedTerm Const evidence) : HOL.Term Const Γ (endpoint ⇒ evidence) :=
  .lam (HOL.weakenCtx (endpoint :: Γ) witness)

theorem subst_reflexivityAt {Ξ : HOL.Ctx Base} (witness : HOL.ClosedTerm Const evidence)
    (images : HOL.Subst Const Γ Ξ) :
    HOL.subst images (reflexivityAt (endpoint := endpoint) witness) =
      reflexivityAt (Γ := Ξ) (endpoint := endpoint) witness := by
  simp only [reflexivityAt, HOL.subst, HOL.subst_weakenCtx]

theorem weaken_reflexivityCode (witness : HOL.ClosedTerm Const evidence) :
    HOL.weakenCtx Γ (reflexivityCode witness endpoint) = reflexivityAt (Γ := Γ) witness := by
  let images : HOL.Subst Const [] Γ := fun index => nomatch index
  exact (HOL.subst_weakenCtx images (reflexivityCode witness endpoint)).symm.trans
    (subst_reflexivityAt witness images)

def reflexivity_apply (witness : HOL.ClosedTerm Const evidence) (argument : HOL.Term Const Γ endpoint) :
    HOL.ProofSyntax Const Δ (.eq
      (.app (HOL.weakenCtx Γ (reflexivityCode witness endpoint)) argument) (HOL.weakenCtx Γ witness)) := by
  apply HOL.ProofSyntax.castIndices rfl ?_ (.beta argument (HOL.weakenCtx (endpoint :: Γ) witness))
  rw [weaken_reflexivityCode]
  simp only [reflexivityAt, HOL.instantiate, HOL.subst_weakenCtx]

theorem reflexivity_apply_free (witness : HOL.ClosedTerm Const evidence) (argument : HOL.Term Const Γ endpoint) :
    (reflexivity_apply (Δ := Δ) witness argument).FunctionExtensionalityFree := by
  simp [reflexivity_apply, HOL.ProofSyntax.FunctionExtensionalityFree]

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading.StructuralProfile
