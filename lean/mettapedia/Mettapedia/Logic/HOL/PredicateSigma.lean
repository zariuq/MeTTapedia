import Mettapedia.Logic.HOL.PredicateProducts

/-!
# Dependent-pair predicates in a fixed evidence carrier

Membership retains an actual pair-image equation and both component guards.
The family is curried in the ambient context; an open source family is supplied
by abstraction over its first component. Packing/projection operations are
syntax, and their laws remain explicit proof inputs when used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.PredicateSigma

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base} {space : Ty Base}

structure Operations (Const : Ty Base → Type v) (space : Ty Base) where
  pair : ClosedTerm Const (space ⇒ space ⇒ space)
  first : ClosedTerm Const (space ⇒ space)
  second : ClosedTerm Const (space ⇒ space)

def pair (ops : Operations Const space) (first second : Term Const Γ space) : Term Const Γ space :=
  .app (.app (weakenCtx Γ ops.pair) first) second

def first (ops : Operations Const space) (point : Term Const Γ space) : Term Const Γ space :=
  .app (weakenCtx Γ ops.first) point

def second (ops : Operations Const space) (point : Term Const Γ space) : Term Const Γ space :=
  .app (weakenCtx Γ ops.second) point

def familyAt (family : Term Const Γ (space ⇒ space ⇒ .prop))
    (first second : Term Const Γ space) : Formula Const Γ := .app (.app family first) second

@[simp] theorem subst_pair (ops : Operations Const space) (images : Subst Const Γ Ξ)
    (first second : Term Const Γ space) :
    HOL.subst images (pair ops first second) = pair ops (HOL.subst images first) (HOL.subst images second) := by
  simp only [pair, HOL.subst, subst_weakenCtx]

@[simp] theorem subst_first (ops : Operations Const space) (images : Subst Const Γ Ξ)
    (point : Term Const Γ space) : HOL.subst images (first ops point) = first ops (HOL.subst images point) := by
  simp only [first, HOL.subst, subst_weakenCtx]

@[simp] theorem subst_second (ops : Operations Const space) (images : Subst Const Γ Ξ)
    (point : Term Const Γ space) : HOL.subst images (second ops point) = second ops (HOL.subst images point) := by
  simp only [second, HOL.subst, subst_weakenCtx]

def membership (ops : Operations Const space) (domain : Term Const Γ (space ⇒ .prop))
    (family : Term Const Γ (space ⇒ space ⇒ .prop)) (point : Term Const Γ space) : Formula Const Γ :=
  .ex (.ex (.and
    (.eq (pair ops (.var (.vs .vz)) (.var .vz)) (weaken (weaken point)))
    (.and (.app (weaken (weaken domain)) (.var (.vs .vz)))
      (familyAt (weaken (weaken family)) (.var (.vs .vz)) (.var .vz)))))

def sigma (ops : Operations Const space) (domain : Term Const Γ (space ⇒ .prop))
    (family : Term Const Γ (space ⇒ space ⇒ .prop)) : Term Const Γ (space ⇒ .prop) :=
  .lam (membership ops (weaken domain) (weaken family) (.var .vz))

@[simp] theorem subst_membership (ops : Operations Const space) (images : Subst Const Γ Ξ)
    (domain : Term Const Γ (space ⇒ .prop)) (family : Term Const Γ (space ⇒ space ⇒ .prop))
    (point : Term Const Γ space) :
    HOL.subst images (membership ops domain family point) =
      membership ops (HOL.subst images domain) (HOL.subst images family) (HOL.subst images point) := by
  simp only [membership, familyAt, HOL.subst, subst_pair, subst_weaken, Subst.lift,
    HOL.rename, Rename.weaken]

@[simp] theorem subst_sigma (ops : Operations Const space) (images : Subst Const Γ Ξ)
    (domain : Term Const Γ (space ⇒ .prop)) (family : Term Const Γ (space ⇒ space ⇒ .prop)) :
    HOL.subst images (sigma ops domain family) =
      sigma ops (HOL.subst images domain) (HOL.subst images family) := by
  simp only [sigma, HOL.subst, subst_membership, subst_weaken, Subst.lift]

@[simp] theorem rename_sigma (ops : Operations Const space) (rho : Rename Base Γ Ξ)
    (domain : Term Const Γ (space ⇒ .prop)) (family : Term Const Γ (space ⇒ space ⇒ .prop)) :
    HOL.rename rho (sigma ops domain family) = sigma ops (HOL.rename rho domain) (HOL.rename rho family) := by
  simpa only [subst_ofRename] using subst_sigma ops (Subst.ofRename rho) domain family

variable {Δ : List (Formula Const Γ)}

def beta (ops : Operations Const space) (domain : Term Const Γ (space ⇒ .prop))
    (family : Term Const Γ (space ⇒ space ⇒ .prop)) (point : Term Const Γ space) :
    ProofSyntax Const Δ (.eq (.app (sigma ops domain family) point) (membership ops domain family point)) := by
  have domainCancel : HOL.subst (Subst.single point) (weaken domain) = domain := instantiate_weaken point domain
  have familyCancel : HOL.subst (Subst.single point) (weaken family) = family := instantiate_weaken point family
  apply ProofSyntax.castIndices rfl ?_
    (.beta point (membership ops (weaken domain) (weaken family) (.var .vz)))
  simp only [sigma, instantiate, subst_membership, domainCancel, familyCancel, HOL.subst, Subst.single]

theorem beta_free (ops : Operations Const space) (domain : Term Const Γ (space ⇒ .prop))
    (family : Term Const Γ (space ⇒ space ⇒ .prop)) (point : Term Const Γ space) :
    (beta (Δ := Δ) ops domain family point).FunctionExtensionalityFree := by
  simp [beta, ProofSyntax.FunctionExtensionalityFree]

def introduce (ops : Operations Const space) (domain : Term Const Γ (space ⇒ .prop))
    (family : Term Const Γ (space ⇒ space ⇒ .prop)) (head tail : Term Const Γ space)
    (headMember : ProofSyntax Const Δ (.app domain head))
    (tailMember : ProofSyntax Const Δ (familyAt family head tail)) :
    ProofSyntax Const Δ (.app (sigma ops domain family) (pair ops head tail)) := by
  apply ProofSyntax.impE (.eqPropER (beta ops domain family (pair ops head tail)))
  refine .exI head (.exI tail ?_)
  apply ProofSyntax.castIndices rfl ?_ (.andI (.eqRefl (pair ops head tail)) (.andI headMember tailMember))
  simp [familyAt, instantiate, HOL.subst, subst_pair, subst_weaken,
    Subst.single, Subst.lift, subst_rename, Rename.weaken]
  exact ⟨congrArg (fun value => pair ops value tail) (HOL.subst_id head).symm, HOL.subst_id head |>.symm⟩

theorem introduce_free (ops : Operations Const space) (domain : Term Const Γ (space ⇒ .prop))
    (family : Term Const Γ (space ⇒ space ⇒ .prop)) (head tail : Term Const Γ space)
    (headMember : ProofSyntax Const Δ (.app domain head))
    (tailMember : ProofSyntax Const Δ (familyAt family head tail))
    (headFree : headMember.FunctionExtensionalityFree) (tailFree : tailMember.FunctionExtensionalityFree) :
    (introduce ops domain family head tail headMember tailMember).FunctionExtensionalityFree := by
  simp [introduce, ProofSyntax.FunctionExtensionalityFree, beta_free, headFree, tailFree]

#print axioms subst_sigma
#print axioms introduce_free

end Mettapedia.Logic.HOL.PredicateSigma
