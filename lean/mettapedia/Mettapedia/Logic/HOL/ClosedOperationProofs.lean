import Mettapedia.Logic.HOL.ProofSyntaxStructural
import Mettapedia.Logic.HOL.Syntax.Closed

/-!
# Closing substitution-natural operations with retained beta receipts

The operation supplies its actual syntax and its substitution law. Closing
its arguments produces a lambda term; application has a constructed retained
beta proof, uniformly in the surrounding context and hypotheses.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

structure UnaryOperation (Const : Ty Base → Type v) (input output : Ty Base) where
  term : {Γ : Ctx Base} → Term Const Γ input → Term Const Γ output
  subst : ∀ {Γ Ξ : Ctx Base} (theta : Subst Const Γ Ξ) (value : Term Const Γ input),
    HOL.subst theta (term value) = term (HOL.subst theta value)

namespace UnaryOperation
variable {input output : Ty Base} (operation : UnaryOperation Const input output)
variable {Γ Ξ : Ctx Base} {Δ : List (Formula Const Γ)}

theorem rename (rho : Rename Base Γ Ξ) (value : Term Const Γ input) :
    HOL.rename rho (operation.term value) = operation.term (HOL.rename rho value) := by
  simpa only [HOL.subst_ofRename] using operation.subst (Subst.ofRename rho) value

def bodyAt (context : Ctx Base) : Term Const context (.arr input output) := .lam (operation.term (.var .vz))
def body : ClosedTerm Const (.arr input output) := operation.bodyAt []

theorem rename_bodyAt (rho : Rename Base Γ Ξ) : HOL.rename rho (operation.bodyAt Γ) = operation.bodyAt Ξ := by
  simp only [bodyAt,HOL.rename,rename,Rename.lift]

theorem weakenCtx_body (context : Ctx Base) : weakenCtx context operation.body = operation.bodyAt context := by
  induction context with
  | nil => rfl
  | cons added context previous =>
    rw [weakenCtx_cons,previous]
    exact operation.rename_bodyAt (Rename.weaken (σ := added))

def beta (value : Term Const Γ input) :
    ProofSyntax Const Δ (.eq (.app (weakenCtx Γ operation.body) value) (operation.term value)) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta value (operation.term (.var .vz)))
  simp only [weakenCtx_body,bodyAt,instantiate,subst,HOL.subst,Subst.single]

theorem beta_free (value : Term Const Γ input) : (operation.beta (Δ := Δ) value).FunctionExtensionalityFree := by
  simp [beta,ProofSyntax.FunctionExtensionalityFree]
end UnaryOperation

structure BinaryOperation (Const : Ty Base → Type v) (first second output : Ty Base) where
  term : {Γ : Ctx Base} → Term Const Γ first → Term Const Γ second → Term Const Γ output
  subst : ∀ {Γ Ξ : Ctx Base} (theta : Subst Const Γ Ξ) (left : Term Const Γ first) (right : Term Const Γ second),
    HOL.subst theta (term left right) = term (HOL.subst theta left) (HOL.subst theta right)

namespace BinaryOperation
variable {first second output : Ty Base} (operation : BinaryOperation Const first second output)
variable {Γ Ξ : Ctx Base} {Δ : List (Formula Const Γ)}

theorem rename (rho : Rename Base Γ Ξ) (left : Term Const Γ first) (right : Term Const Γ second) :
    HOL.rename rho (operation.term left right) = operation.term (HOL.rename rho left) (HOL.rename rho right) := by
  simpa only [HOL.subst_ofRename] using operation.subst (Subst.ofRename rho) left right

def bodyAt (context : Ctx Base) : Term Const context (.arr first (.arr second output)) :=
  .lam (.lam (operation.term (.var (.vs .vz)) (.var .vz)))
def body : ClosedTerm Const (.arr first (.arr second output)) := operation.bodyAt []

theorem rename_bodyAt (rho : Rename Base Γ Ξ) : HOL.rename rho (operation.bodyAt Γ) = operation.bodyAt Ξ := by
  simp only [bodyAt,HOL.rename,rename,Rename.lift]

theorem weakenCtx_body (context : Ctx Base) : weakenCtx context operation.body = operation.bodyAt context := by
  induction context with
  | nil => rfl
  | cons added context previous =>
    rw [weakenCtx_cons,previous]
    exact operation.rename_bodyAt (Rename.weaken (σ := added))

private theorem substituteWeak {type : Ty Base} (value : Term Const Γ second) (term : Term Const Γ type) :
    HOL.subst (Subst.single value) (HOL.weaken term) = term := instantiate_weaken value term

def beta (left : Term Const Γ first) (right : Term Const Γ second) :
    ProofSyntax Const Δ (.eq (.app (.app (weakenCtx Γ operation.body) left) right) (operation.term left right)) := by
  have firstStep : ProofSyntax Const Δ (.eq (.app (.app (weakenCtx Γ operation.body) left) right)
      (.app (.lam (operation.term (HOL.weaken left) (.var .vz))) right)) := by
    apply ProofSyntax.castIndices rfl ?_
      (.eqApp right (.beta left (.lam (operation.term (.var (.vs .vz)) (.var .vz)))))
    simp only [weakenCtx_body,bodyAt,instantiate,HOL.subst,subst,Subst.lift,Subst.single,HOL.weaken]
  have secondStep : ProofSyntax Const Δ (.eq (.app (.lam (operation.term (HOL.weaken left) (.var .vz))) right)
      (operation.term left right)) := by
    apply ProofSyntax.castIndices rfl ?_ (.beta right (operation.term (HOL.weaken left) (.var .vz)))
    simp only [instantiate,subst,HOL.subst,Subst.single,substituteWeak]
  exact .eqTrans firstStep secondStep

theorem beta_free (left : Term Const Γ first) (right : Term Const Γ second) :
    (operation.beta (Δ := Δ) left right).FunctionExtensionalityFree := by
  simp [beta,ProofSyntax.FunctionExtensionalityFree]
end BinaryOperation

end Mettapedia.Logic.HOL
