import Mettapedia.Logic.HOL.PredicateProducts
import Mettapedia.Logic.HOL.ConstantSubstitutionSemantics

/-!
# A designated witness for an explicit HOL equality guard

Endpoint values and witness values have independent carriers. This code
admits the designated witness precisely when the endpoints are HOL-equal.
It supplies guard syntax and retained HOL proofs, not an interpretation of
all intensional identity proofs, J, or an equality-reflection principle.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.EqualityWitness

universe u v w
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
    {endpoint evidence : Ty Base}

def property (witness : ClosedTerm Const evidence) (left right : Term Const Γ endpoint)
    (value : Term Const Γ evidence) : Formula Const Γ :=
  .and (.eq value (weakenCtx Γ witness)) (.eq left right)

def predicate (witness : ClosedTerm Const evidence) (left right : Term Const Γ endpoint) :
    Term Const Γ (evidence ⇒ .prop) :=
  .lam (.and (.eq (.var .vz) (weakenCtx (evidence :: Γ) witness)) (.eq (weaken left) (weaken right)))

@[simp] theorem subst_property (witness : ClosedTerm Const evidence) (images : Subst Const Γ Ξ)
    (left right : Term Const Γ endpoint) (value : Term Const Γ evidence) :
    HOL.subst images (property witness left right value) =
      property witness (HOL.subst images left) (HOL.subst images right) (HOL.subst images value) := by
  simp only [property, HOL.subst, subst_weakenCtx]

@[simp] theorem subst_predicate (witness : ClosedTerm Const evidence) (images : Subst Const Γ Ξ)
    (left right : Term Const Γ endpoint) :
    HOL.subst images (predicate witness left right) =
      predicate witness (HOL.subst images left) (HOL.subst images right) := by
  simp only [predicate, HOL.subst, subst_weakenCtx, subst_weaken, Subst.lift]

@[simp] theorem rename_predicate (witness : ClosedTerm Const evidence) (rho : Rename Base Γ Ξ)
    (left right : Term Const Γ endpoint) :
    HOL.rename rho (predicate witness left right) = predicate witness (HOL.rename rho left) (HOL.rename rho right) := by
  simpa only [subst_ofRename] using subst_predicate witness (Subst.ofRename rho) left right

variable {Δ : List (Formula Const Γ)}

def beta (witness : ClosedTerm Const evidence) (left right : Term Const Γ endpoint) (value : Term Const Γ evidence) :
    ProofSyntax Const Δ (.eq (.app (predicate witness left right) value) (property witness left right value)) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta value
    (.and (.eq (.var .vz) (weakenCtx (evidence :: Γ) witness)) (.eq (weaken left) (weaken right))))
  have leftCancel : HOL.subst (Subst.single value) (weaken left) = left := instantiate_weaken value left
  have rightCancel : HOL.subst (Subst.single value) (weaken right) = right := instantiate_weaken value right
  simp only [predicate, property, instantiate, HOL.subst, subst_weakenCtx, Subst.single, leftCancel, rightCancel]

theorem beta_free (witness : ClosedTerm Const evidence) (left right : Term Const Γ endpoint) (value : Term Const Γ evidence) :
    (beta (Δ := Δ) witness left right value).FunctionExtensionalityFree := by
  simp [beta, ProofSyntax.FunctionExtensionalityFree]

def introduce (witness : ClosedTerm Const evidence) (left right : Term Const Γ endpoint)
    (equal : ProofSyntax Const Δ (.eq left right)) :
    ProofSyntax Const Δ (.app (predicate witness left right) (weakenCtx Γ witness)) :=
  .impE (.eqPropER (beta witness left right _)) (.andI (.eqRefl _) equal)

def eliminate (witness : ClosedTerm Const evidence) (left right : Term Const Γ endpoint) (value : Term Const Γ evidence)
    (member : ProofSyntax Const Δ (.app (predicate witness left right) value)) :
    ProofSyntax Const Δ (property witness left right value) :=
  .impE (.eqPropEL (beta witness left right value)) member

theorem introduce_free (witness : ClosedTerm Const evidence) (left right : Term Const Γ endpoint)
    (equal : ProofSyntax Const Δ (.eq left right)) (free : equal.FunctionExtensionalityFree) :
    (introduce witness left right equal).FunctionExtensionalityFree := by
  simp [introduce, ProofSyntax.FunctionExtensionalityFree, beta_free, free]

theorem eliminate_free (witness : ClosedTerm Const evidence) (left right : Term Const Γ endpoint) (value : Term Const Γ evidence)
    (member : ProofSyntax Const Δ (.app (predicate witness left right) value)) (free : member.FunctionExtensionalityFree) :
    (eliminate witness left right value member).FunctionExtensionalityFree := by
  simp [eliminate, ProofSyntax.FunctionExtensionalityFree, beta_free, free]

theorem denote (model : HenkinModel.{u,v,w} Base Const) (witness : ClosedTerm Const evidence)
    (left right : Term Const Γ endpoint) (value : Term Const Γ evidence) (values : model.Valuation Γ) :
    (model.denote (.app (predicate witness left right) value) values).down ↔
      model.Eqv evidence (model.denote value values) (model.denote witness (fun index => nomatch index)) ∧
      model.Eqv endpoint (model.denote left values) (model.denote right values) := by
  have closed : model.denote (weakenCtx (evidence :: Γ) witness) (model.extend values (model.denote value values)) =
      model.denote witness (fun index => nomatch index) := model.denote_weakenCtx _ witness _
  simp only [predicate, HenkinModel.denote, PreModel.denote, Soundness.denote_weaken, closed, PreModel.extend]

#print axioms introduce_free
#print axioms denote

end Mettapedia.Logic.HOL.EqualityWitness
