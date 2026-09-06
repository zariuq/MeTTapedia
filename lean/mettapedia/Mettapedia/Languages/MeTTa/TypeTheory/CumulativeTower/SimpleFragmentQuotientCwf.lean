import Mettapedia.TypeTheory.ScwfQuotient
import Mettapedia.TypeTheory.ContextualProductComparison
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SimpleFragmentConversionDecision

/-!
# The beta-quotient category with families of the simple fragment

Terms and substitutions are quotiented together. The generic congruence
construction supplies terminal context, comprehension, and the strict
projection from raw syntax. Lambda abstraction and application descend and
satisfy beta, without adding eta. Substitutions have unique pointwise normal
representatives; the tower conversion comparison reflects their components.

This construction is on the simple side. It does not provide a reduct of all
tower inhabitants or a quotient of the tower's dependent type families.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace SimpleFragmentQuotientCwf

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualProductComparison
open FourFaceBetaExperiment FourFaceBetaExperiment.IntrinsicSTT
open SimpleFragmentNormalization SimpleFragmentConversionDecision

variable {Γ Δ Θ : List Ty} {A B : Ty}

def substitutionSetoid (Γ Δ : List Ty) : Setoid (Substitution Γ Δ) where
  r := Substitution.BetaConv
  iseqv :=
    ⟨fun _ _ _ => .refl _,
     fun h A v => .symm _ _ (h A v),
     fun h k A v => .trans _ _ _ (h A v) (k A v)⟩

/-- Beta conversion respects every operation of the raw simple CwF. -/
def congruence : syntacticScwf.Congruence where
  sub Γ Δ := substitutionSetoid Δ Γ
  tm := betaSetoid
  comp_rel := by
    intro Γ Δ Θ σ σ' τ τ' hσ hτ A v
    exact BetaConv.substitute_congr (hσ A v) hτ
  tmSub_rel := by
    intro Γ Δ A t t' σ σ' ht hσ
    exact BetaConv.substitute_congr ht hσ
  pair_rel := by
    intro Γ Δ A σ σ' t t' hσ ht B v
    cases v with
    | zero => exact ht
    | succ v => exact hσ B v

def scwf : Scwf := congruence.quotient

def withTerminal : ScwfWithTerminal :=
  syntacticScwfWithTerminal.quotient congruence

def projection : StrictCwfMorphism syntacticCwfWithTerminal
    withTerminal.toCwfWithTerminal :=
  syntacticScwfWithTerminal.quotientMorphism congruence

def lam : BetaClass (A :: Γ) B → BetaClass Γ (.arr A B) :=
  Quotient.map Term.lam (fun {_ _} h => h.lam)

def app : BetaClass Γ (.arr A B) → BetaClass Γ A → BetaClass Γ B :=
  Quotient.map₂ Term.app (fun {_ _} hf {_ _} ha => hf.app ha)

/-- The beta equation is actual equality in the contextual quotient. -/
def functions : SimpleFunctionBeta scwf where
  arrow := Ty.arr
  lam := lam
  app := app
  beta := by
    intro Γ A B body argument
    induction body, argument using Quotient.inductionOn₂ with
    | _ body argument => exact Quotient.sound (.rel _ _ (.beta body argument))

/-- Quotient substitutions lift under binders without choosing representatives. -/
def lift (σ : scwf.Sub Γ Δ) : scwf.Sub (A :: Γ) (A :: Δ) :=
  Quotient.map (liftSubstitution (B := A))
    (fun {_ _} h => Substitution.BetaConv.lift h) σ

theorem lam_substitute (body : BetaClass (A :: Δ) B) (σ : scwf.Sub Γ Δ) :
    scwf.tmSub (lam body) σ = lam (scwf.tmSub body (lift σ)) := by
  induction body, σ using Quotient.inductionOn₂ with
  | _ body σ => rfl

theorem app_substitute (f : BetaClass Δ (.arr A B)) (a : BetaClass Δ A)
    (σ : scwf.Sub Γ Δ) :
    scwf.tmSub (app f a) σ = app (scwf.tmSub f σ) (scwf.tmSub a σ) := by
  induction f, a, σ using Quotient.inductionOn₃ with
  | _ f a σ => rfl

def normalizeSubstitution (σ : Substitution Γ Δ) : Substitution Γ Δ :=
  fun v => (normalize (σ v)).normalForm

theorem normalizeSubstitution_convert (σ : Substitution Γ Δ) :
    Substitution.BetaConv σ (normalizeSubstitution σ) :=
  fun _ v => normalize_convert (σ v)

theorem normalizeSubstitution_eq_iff (σ τ : Substitution Γ Δ) :
    @normalizeSubstitution Γ Δ σ = @normalizeSubstitution Γ Δ τ ↔
      Substitution.BetaConv σ τ := by
  constructor
  · intro equal A v
    exact (normalize_eq_iff_betaConv (σ v) (τ v)).1
      (congrFun (congrFun equal A) v)
  · intro h
    funext A v
    exact (normalize_eq_iff_betaConv (σ v) (τ v)).2 (h A v)

theorem normalizeSubstitution_comp (σ : Substitution Γ Δ) (τ : Substitution Δ Θ) :
    @normalizeSubstitution Γ Θ
        (Substitution.comp (normalizeSubstitution σ) (normalizeSubstitution τ)) =
      @normalizeSubstitution Γ Θ (Substitution.comp σ τ) := by
  apply (normalizeSubstitution_eq_iff _ _).2
  intro A v
  exact BetaConv.substitute_congr
    (.symm _ _ (normalize_convert (σ v)))
    (fun B w => .symm _ _ (normalize_convert (τ w)))

/-- Each substitution class has a unique pointwise beta-normal representative. -/
def substitutionClassEquivNormal :
    Quotient (substitutionSetoid Γ Δ) ≃
      {σ : Substitution Γ Δ // ∀ A (v : Var Γ A), Normal (σ v)} where
  toFun := Quotient.lift
    (fun σ => ⟨normalizeSubstitution σ, fun _ v => normalize_normal (σ v)⟩)
    (fun σ τ h => Subtype.ext ((normalizeSubstitution_eq_iff σ τ).2 h))
  invFun := fun σ => Quotient.mk _ σ.1
  left_inv := by
    intro σ
    induction σ using Quotient.inductionOn with
    | _ σ => exact Quotient.sound (fun A v => .symm _ _ (normalize_convert (σ v)))
  right_inv := by
    intro σ
    apply Subtype.ext
    funext A v
    exact normalize_of_irreducible (σ.1 v) (σ.2 A v).no_betaStep

/-- Full tower conversion reflects each component of a simple substitution. -/
theorem substitution_conversion_iff_tower (σ τ : Substitution Γ Δ) :
    Substitution.BetaConv σ τ ↔
      ∀ A (v : Var Γ A), Presentation.Conv Presentation.Tower.HeadEq
        (TowerDTT.eraseTerm (σ v)) (TowerDTT.eraseTerm (τ v)) := by
  constructor
  · intro h A v
    exact (h A v).erase
  · intro h A v
    exact (towerConv_iff_betaConv (σ v) (τ v)).1 (h A v)

/-- Comprehension remains a genuine pairing universal property after quotienting. -/
theorem comprehension_unique (σ : scwf.Sub Γ Δ) (t : scwf.Tm Γ A)
    (ρ : scwf.Sub Γ (scwf.ext Δ A))
    (first : scwf.compS (scwf.wk A) ρ = σ)
    (second : scwf.tmSub (scwf.vz A) ρ = t) :
    ρ = scwf.pair σ A t := by
  rw [← first, ← second]
  exact (scwf.pair_eta A ρ).symm

/-- The quotient identifies a real beta redex with its contractum. -/
theorem beta_identifies_redex :
    (Quotient.mk (betaSetoid [.atom] .atom)
      (.app (.lam (.var .zero)) (.var .zero))) =
        Quotient.mk (betaSetoid [.atom] .atom) (.var .zero) :=
  Quotient.sound (.rel _ _ (.beta _ _))

/-- The projection forgets genuine raw substitution distinctions. It is
surjective on arrows, but not faithful. -/
theorem projection_not_faithful : ¬ congruence.projection.Faithful := by
  intro faithful
  let Γ : syntacticScwf.toCwf.base.Context := ⟨[.atom]⟩
  let σ : Γ ⟶ Γ := Substitution.id [.atom]
  let τ : Γ ⟶ Γ := fun v => Term.app (Term.lam (Term.var .zero)) (Term.var v)
  have equal : congruence.projection.map σ = congruence.projection.map τ := by
    apply Quotient.sound
    intro A v
    exact .symm _ _ (.rel _ _ (.beta _ _))
  have rawEqual := faithful.map_injective equal
  have variableEqual := congrFun (congrFun rawEqual Ty.atom) Var.zero
  cases variableEqual

/-- The selected quotient does not collapse distinct context projections. -/
theorem projections_distinct :
    (Quotient.mk (betaSetoid [.atom, .atom] .atom) (.var .zero)) ≠
      Quotient.mk (betaSetoid [.atom, .atom] .atom) (.var (.succ .zero)) := by
  intro equal
  exact distinct_variables_not_convertible (Quotient.exact equal)

/-- Extensional eta is still not an equation of the quotient function structure. -/
theorem eta_distinct :
    Quotient.mk (betaSetoid [.arr .atom .atom] (.arr .atom .atom)) etaVariable ≠
      Quotient.mk (betaSetoid [.arr .atom .atom] (.arr .atom .atom)) etaExpansion := by
  intro equal
  exact eta_not_betaConvertible (Quotient.exact equal)

#print axioms congruence
#print axioms projection
#print axioms functions
#print axioms substitutionClassEquivNormal
#print axioms normalizeSubstitution_comp
#print axioms substitution_conversion_iff_tower
#print axioms comprehension_unique
#print axioms projection_not_faithful
#print axioms projections_distinct
#print axioms eta_distinct

end SimpleFragmentQuotientCwf
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
