import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading
import Mettapedia.Logic.HOL.PredicateSigmaInterpretation
import Mettapedia.Logic.HOL.EqualityWitness

/-!
# A pair-image and guarded equality profile for structural readings

The shared reader accepts arbitrary carrier-indexed closed structural codes.
This selected instance uses the existing homogeneous pair operations, while
identity endpoints may have any carrier. Identity membership retains both
endpoint guards. No interpretation of arbitrary intensional Id or J follows.
Pair projection laws remain explicit inputs to the existing Sigma theorems.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading.StructuralProfile

open Mettapedia.Logic
local infixr:60 " ⇒ " => HOL.Ty.arr
universe u v w
variable {Base : Type u} {Const : HOL.Ty Base → Type v} {evidence endpoint : HOL.Ty Base}
    {Γ Ξ : HOL.Ctx Base}

def sigmaCodeAt (operations : HOL.PredicateSigma.Operations Const evidence) :
    HOL.Term Const Γ ((StructuralOperator.sigma evidence evidence).codeType evidence) :=
  .lam (.lam (HOL.PredicateSigma.sigma operations (.var (.vs .vz)) (.var .vz)))

def sigmaCode (operations : HOL.PredicateSigma.Operations Const evidence) :
    HOL.ClosedTerm Const ((StructuralOperator.sigma evidence evidence).codeType evidence) :=
  sigmaCodeAt operations

@[simp] theorem subst_sigmaCodeAt (operations : HOL.PredicateSigma.Operations Const evidence)
    (images : HOL.Subst Const Γ Ξ) :
    HOL.subst images (sigmaCodeAt operations (Γ := Γ)) = sigmaCodeAt operations (Γ := Ξ) := by
  simp only [sigmaCodeAt, HOL.subst, HOL.PredicateSigma.subst_sigma, HOL.Subst.lift,
    HOL.rename, HOL.Rename.weaken]

theorem weaken_sigmaCode (operations : HOL.PredicateSigma.Operations Const evidence) :
    HOL.weakenCtx Γ (sigmaCode operations) = sigmaCodeAt operations (Γ := Γ) := by
  let images : HOL.Subst Const [] Γ := fun index => nomatch index
  exact (HOL.subst_weakenCtx images (sigmaCode operations)).symm.trans
    (subst_sigmaCodeAt operations images)

def identityPredicate (witness : HOL.ClosedTerm Const evidence)
    (domain : HOL.Term Const Γ (endpoint ⇒ .prop)) (left right : HOL.Term Const Γ endpoint) :
    HOL.Term Const Γ (evidence ⇒ .prop) :=
  .lam (.and (.app (HOL.weaken domain) (HOL.weaken left))
    (.and (.app (HOL.weaken domain) (HOL.weaken right))
      (HOL.EqualityWitness.property witness (HOL.weaken left) (HOL.weaken right) (.var .vz))))

@[simp] theorem subst_identityPredicate (witness : HOL.ClosedTerm Const evidence)
    (images : HOL.Subst Const Γ Ξ) (domain : HOL.Term Const Γ (endpoint ⇒ .prop))
    (left right : HOL.Term Const Γ endpoint) :
    HOL.subst images (identityPredicate witness domain left right) =
      identityPredicate witness (HOL.subst images domain) (HOL.subst images left) (HOL.subst images right) := by
  simp only [identityPredicate, HOL.subst, HOL.EqualityWitness.subst_property,
    HOL.subst_weaken, HOL.Subst.lift]

def identityCodeAt (witness : HOL.ClosedTerm Const evidence) (endpoint : HOL.Ty Base) :
    HOL.Term Const Γ ((StructuralOperator.identity endpoint).codeType evidence) :=
  .lam (.lam (.lam (identityPredicate witness (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))))

def identityCode (witness : HOL.ClosedTerm Const evidence) (endpoint : HOL.Ty Base) :
    HOL.ClosedTerm Const ((StructuralOperator.identity endpoint).codeType evidence) :=
  identityCodeAt witness endpoint

@[simp] theorem subst_identityCodeAt (witness : HOL.ClosedTerm Const evidence) (endpoint : HOL.Ty Base)
    (images : HOL.Subst Const Γ Ξ) :
    HOL.subst images (identityCodeAt witness endpoint (Γ := Γ)) = identityCodeAt witness endpoint (Γ := Ξ) := by
  simp only [identityCodeAt, HOL.subst, subst_identityPredicate, HOL.Subst.lift,
    HOL.rename, HOL.Rename.weaken]

theorem weaken_identityCode (witness : HOL.ClosedTerm Const evidence) (endpoint : HOL.Ty Base) :
    HOL.weakenCtx Γ (identityCode witness endpoint) = identityCodeAt witness endpoint (Γ := Γ) := by
  let images : HOL.Subst Const [] Γ := fun index => nomatch index
  exact (HOL.subst_weakenCtx images (identityCode witness endpoint)).symm.trans
    (subst_identityCodeAt witness endpoint images)

def reflexivityCode (witness : HOL.ClosedTerm Const evidence) (endpoint : HOL.Ty Base) :
    HOL.ClosedTerm Const ((StructuralOperator.reflexivity endpoint).codeType evidence) :=
  .lam (HOL.weaken witness)

section Selection
variable [DecidableEq Base]

def code? (operations : HOL.PredicateSigma.Operations Const evidence)
    (witness : HOL.ClosedTerm Const evidence) : (operator : StructuralOperator Base) →
    Option (Σ result : HOL.Ty Base, HOL.ClosedTerm Const (operator.codeType result))
  | .sigma domain codomain =>
      if first : domain = evidence then
        if second : codomain = evidence then by
          subst domain; subst codomain
          exact some ⟨evidence, sigmaCode operations⟩
        else none
      else none
  | .identity endpoint => some ⟨evidence, identityCode witness endpoint⟩
  | .pair firstType secondType =>
      if first : firstType = evidence then
        if second : secondType = evidence then by
          subst firstType; subst secondType
          exact some ⟨evidence, operations.pair⟩
        else none
      else none
  | .first pairType =>
      if same : pairType = evidence then by subst pairType; exact some ⟨evidence, operations.first⟩
      else none
  | .second pairType =>
      if same : pairType = evidence then by subst pairType; exact some ⟨evidence, operations.second⟩
      else none
  | .reflexivity endpoint => some ⟨evidence, reflexivityCode witness endpoint⟩

@[simp] theorem code_sigma (operations : HOL.PredicateSigma.Operations Const evidence)
    (witness : HOL.ClosedTerm Const evidence) :
    code? operations witness (.sigma evidence evidence) = some ⟨evidence, sigmaCode operations⟩ := by
  simp only [code?, ↓reduceDIte]

@[simp] theorem code_pair (operations : HOL.PredicateSigma.Operations Const evidence)
    (witness : HOL.ClosedTerm Const evidence) :
    code? operations witness (.pair evidence evidence) = some ⟨evidence, operations.pair⟩ := by
  simp only [code?, ↓reduceDIte]

end Selection

variable {Δ : List (HOL.Formula Const Γ)}

/-- The two lexical applications really reduce to the previously specified
pair-image predicate; no equality of semantic operations is assumed. -/
def sigma_apply (operations : HOL.PredicateSigma.Operations Const evidence)
    (domain : HOL.Term Const Γ (evidence ⇒ .prop))
    (family : HOL.Term Const Γ (evidence ⇒ evidence ⇒ .prop)) :
    HOL.ProofSyntax Const Δ (.eq (.app (.app (HOL.weakenCtx Γ (sigmaCode operations)) domain) family)
      (HOL.PredicateSigma.sigma operations domain family)) := by
  have first : HOL.ProofSyntax Const Δ
      (.eq (.app (HOL.weakenCtx Γ (sigmaCode operations)) domain)
        (.lam (HOL.PredicateSigma.sigma operations (HOL.weaken domain) (.var .vz)))) := by
    apply HOL.ProofSyntax.castIndices rfl ?_ (.beta domain
      (.lam (HOL.PredicateSigma.sigma operations (.var (.vs .vz)) (.var .vz))))
    rw [weaken_sigmaCode]
    simp only [sigmaCodeAt, HOL.instantiate, HOL.subst, HOL.PredicateSigma.subst_sigma,
      HOL.Subst.lift, HOL.Subst.single]
    rfl
  have second : HOL.ProofSyntax Const Δ
      (.eq (.app (.lam (HOL.PredicateSigma.sigma operations (HOL.weaken domain) (.var .vz))) family)
        (HOL.PredicateSigma.sigma operations domain family)) := by
    apply HOL.ProofSyntax.castIndices rfl ?_ (.beta family
      (HOL.PredicateSigma.sigma operations (HOL.weaken domain) (.var .vz)))
    simp only [HOL.instantiate, HOL.PredicateSigma.subst_sigma, HOL.subst, HOL.Subst.single]
    have cancel : HOL.subst (HOL.Subst.single family) (HOL.weaken domain) = domain :=
      HOL.instantiate_weaken family domain
    rw [cancel]
  exact .eqTrans (.eqApp family first) second

theorem sigma_apply_free (operations : HOL.PredicateSigma.Operations Const evidence)
    (domain : HOL.Term Const Γ (evidence ⇒ .prop))
    (family : HOL.Term Const Γ (evidence ⇒ evidence ⇒ .prop)) :
    (sigma_apply (Δ := Δ) operations domain family).FunctionExtensionalityFree := by
  simp [sigma_apply, HOL.ProofSyntax.FunctionExtensionalityFree]

def identity_apply (witness : HOL.ClosedTerm Const evidence)
    (domain : HOL.Term Const Γ (endpoint ⇒ .prop)) (left right : HOL.Term Const Γ endpoint) :
    HOL.ProofSyntax Const Δ (.eq
      (.app (.app (.app (HOL.weakenCtx Γ (identityCode witness endpoint)) domain) left) right)
      (identityPredicate witness domain left right)) := by
  have first : HOL.ProofSyntax Const Δ (.eq
      (.app (HOL.weakenCtx Γ (identityCode witness endpoint)) domain)
      (.lam (.lam (identityPredicate witness (HOL.weaken (HOL.weaken domain)) (.var (.vs .vz)) (.var .vz))))) := by
    apply HOL.ProofSyntax.castIndices rfl ?_ (.beta domain
      (.lam (.lam (identityPredicate witness (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz)))))
    rw [weaken_identityCode]
    simp only [identityCodeAt, HOL.instantiate, HOL.subst, subst_identityPredicate,
      HOL.Subst.lift, HOL.Subst.single]
    rfl
  have second : HOL.ProofSyntax Const Δ (.eq
      (.app (.lam (.lam (identityPredicate witness (HOL.weaken (HOL.weaken domain))
        (.var (.vs .vz)) (.var .vz)))) left)
      (.lam (identityPredicate witness (HOL.weaken domain) (HOL.weaken left) (.var .vz)))) := by
    apply HOL.ProofSyntax.castIndices rfl ?_ (.beta left
      (.lam (identityPredicate witness (HOL.weaken (HOL.weaken domain)) (.var (.vs .vz)) (.var .vz))))
    simp only [HOL.instantiate, HOL.subst, subst_identityPredicate, HOL.subst_weaken,
      HOL.Subst.lift, HOL.Subst.single]
    have cancel : HOL.subst (HOL.Subst.single left) (HOL.weaken domain) = domain :=
      HOL.instantiate_weaken left domain
    rw [cancel]
    rfl
  have third : HOL.ProofSyntax Const Δ (.eq
      (.app (.lam (identityPredicate witness (HOL.weaken domain) (HOL.weaken left) (.var .vz))) right)
      (identityPredicate witness domain left right)) := by
    apply HOL.ProofSyntax.castIndices rfl ?_ (.beta right
      (identityPredicate witness (HOL.weaken domain) (HOL.weaken left) (.var .vz)))
    have cancelDomain : HOL.subst (HOL.Subst.single right) (HOL.weaken domain) = domain :=
      HOL.instantiate_weaken right domain
    have cancelLeft : HOL.subst (HOL.Subst.single right) (HOL.weaken left) = left :=
      HOL.instantiate_weaken right left
    simp only [HOL.instantiate, subst_identityPredicate, cancelDomain, cancelLeft, HOL.subst, HOL.Subst.single]
  exact .eqTrans (.eqApp right (.eqApp left first)) (.eqTrans (.eqApp right second) third)

theorem identity_apply_free (witness : HOL.ClosedTerm Const evidence)
    (domain : HOL.Term Const Γ (endpoint ⇒ .prop)) (left right : HOL.Term Const Γ endpoint) :
    (identity_apply (Δ := Δ) witness domain left right).FunctionExtensionalityFree := by
  simp [identity_apply, HOL.ProofSyntax.FunctionExtensionalityFree]

/-- The selected identity guard admits only endpoints in the declared domain.
It uses HOL equality and carries no intensional identity reflection claim. -/
theorem identity_denote (model : HOL.HenkinModel.{u,v,w} Base Const)
    (witness : HOL.ClosedTerm Const evidence) (domain : HOL.Term Const Γ (endpoint ⇒ .prop))
    (left right : HOL.Term Const Γ endpoint) (value : HOL.Term Const Γ evidence)
    (values : model.Valuation Γ) :
    (model.denote (.app (identityPredicate witness domain left right) value) values).down ↔
      (model.denote (.app domain left) values).down ∧ (model.denote (.app domain right) values).down ∧
      model.Eqv evidence (model.denote value values) (model.denote witness (fun index => nomatch index)) ∧
      model.Eqv endpoint (model.denote left values) (model.denote right values) := by
  have closed : model.denote (HOL.weakenCtx (evidence :: Γ) witness)
      (model.extend values (model.denote value values)) =
      model.denote witness (fun index => nomatch index) := model.denote_weakenCtx _ witness _
  simp only [identityPredicate, HOL.EqualityWitness.property, HOL.HenkinModel.denote,
    HOL.PreModel.denote, HOL.Soundness.denote_weaken, closed, HOL.PreModel.extend]

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading.StructuralProfile
