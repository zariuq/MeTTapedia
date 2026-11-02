import Mettapedia.Logic.HOL.PredicateSigma
import Mettapedia.Logic.HOL.CurriedExistentialElimination

/-!
# Retained existence of a pair of independent witnesses

Each existential is opened only inside the pair construction. The resulting
predicate keeps the actual pair image and both guards. No projection equation
or choice principle is needed to introduce the pair.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.PredicateSigma
open CurriedPredicates
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {space : Ty Base}
    (ops : Operations Const space) {Γ Ξ : Ctx Base}

def independent (first second : Term Const Γ (space ⇒ .prop)) : Term Const Γ (space ⇒ .prop) :=
  sigma ops first (.lam (weaken second))

@[simp] theorem subst_independent (images : Subst Const Γ Ξ)
    (first second : Term Const Γ (space ⇒ .prop)) :
    HOL.subst images (independent ops first second) =
      independent ops (HOL.subst images first) (HOL.subst images second) := by
  simp only [independent, subst_sigma, HOL.subst, subst_weaken]

@[simp] theorem rename_independent (rho : Rename Base Γ Ξ)
    (first second : Term Const Γ (space ⇒ .prop)) :
    HOL.rename rho (independent ops first second) =
      independent ops (HOL.rename rho first) (HOL.rename rho second) := by
  simpa only [subst_ofRename] using subst_independent ops (Subst.ofRename rho) first second

def independent_family {Δ : List (Formula Const Γ)}
    (second : Term Const Γ (space ⇒ .prop)) (head tail : Term Const Γ space) :
    ProofSyntax Const Δ (.eq (familyAt (.lam (weaken second)) head tail) (.app second tail)) := by
  apply ProofSyntax.castIndices rfl ?_ (.eqApp tail (.beta head (weaken second)))
  simp only [familyAt, instantiate_weaken]

theorem independent_family_free {Δ : List (Formula Const Γ)}
    (second : Term Const Γ (space ⇒ .prop)) (head tail : Term Const Γ space) :
    (independent_family (Δ := Δ) second head tail).FunctionExtensionalityFree := by
  simp [independent_family, ProofSyntax.FunctionExtensionalityFree]

def independent_exists {Δ : List (Formula Const Γ)}
    (first second : Term Const Γ (space ⇒ .prop))
    (firstExists : ProofSyntax Const Δ (existsValue [] first))
    (secondExists : ProofSyntax Const Δ (existsValue [] second)) :
    ProofSyntax Const Δ (existsValue [] (independent ops first second)) := by
  let goal := existsValue [] (independent ops first second)
  refine existsValue_elim [] first PUnit.unit goal firstExists ?_
  have later : ProofSyntax Const
      (.app (weaken first) (.var .vz) :: weakenHyps Δ)
      (existsValue [] (weaken second)) := by
    apply ProofSyntax.castIndices rfl ?_
      ((PredicateFixedPoint.weakenProof secondExists).prepend (.app (weaken first) (.var .vz)))
    exact rename_existsValue Rename.weaken [] second
  refine existsValue_elim [] (weaken second) PUnit.unit (weaken goal) later ?_
  let a := weaken (σ := space) (weaken (σ := space) first)
  let b := weaken (σ := space) (weaken (σ := space) second)
  let h : Term Const (space :: space :: Γ) space := .var (.vs .vz)
  let t : Term Const (space :: space :: Γ) space := .var .vz
  have headMember : ProofSyntax Const
      (.app b t :: weakenHyps (.app (weaken first) (.var .vz) :: weakenHyps Δ)) (.app a h) := .hyp 1
  have tailMember : ProofSyntax Const
      (.app b t :: weakenHyps (.app (weaken first) (.var .vz) :: weakenHyps Δ)) (.app b t) := .hyp 0
  have packed := introduce ops a (.lam (weaken b)) h t headMember
    (.impE (.eqPropER (independent_family b h t)) tailMember)
  have output := existsValue_intro [] (independent ops a b) PUnit.unit (pair ops h t) packed
  apply ProofSyntax.castIndices rfl ?_ output
  simp only [goal, weaken, rename_existsValue, rename_independent, a, b,
    FiniteConstructorEncoding.applyArguments]

theorem independent_exists_free {Δ : List (Formula Const Γ)}
    (first second : Term Const Γ (space ⇒ .prop))
    (firstExists : ProofSyntax Const Δ (existsValue [] first))
    (secondExists : ProofSyntax Const Δ (existsValue [] second))
    (firstFree : firstExists.FunctionExtensionalityFree) (secondFree : secondExists.FunctionExtensionalityFree) :
    (independent_exists ops first second firstExists secondExists).FunctionExtensionalityFree := by
  simp only [independent_exists, existsValue_elim, existsValue_intro_free,
    ProofSyntax.functionExtensionalityFree_castIndices, ProofSyntax.FunctionExtensionalityFree,
    introduce_free, independent_family_free, existsValue_beta_free, PredicateFixedPoint.weakenProof,
    ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono, ProofSyntax.functionExtensionalityFree_rename,
    firstFree, secondFree, and_self]

#print axioms independent_exists
#print axioms independent_exists_free
end Mettapedia.Logic.HOL.PredicateSigma
