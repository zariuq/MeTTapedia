import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SimpleFragmentCwf
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SimpleFragmentErasureBoundary

/-!
# Beta conversion of the intrinsic simple fragment

Contextual beta reduction and its equivalence closure use the existing typed
syntax. Renaming and substitution preserve conversion, including substitution
of pointwise-convertible terms. Erasure transports conversion to the tower,
and every extensional function interpretation respects it.

This constructs a conversion quotient without changing either raw calculus.
No eta equation or reflection theorem is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace FourFaceBetaExperiment.IntrinsicSTT

universe u

/-- Contextual, intrinsically typed beta reduction. -/
inductive BetaStep : {Γ : List Ty} → {A : Ty} → Term Γ A → Term Γ A → Prop where
  | beta {Γ : List Ty} {A B : Ty} (body : Term (A :: Γ) B) (argument : Term Γ A) :
      BetaStep (.app (.lam body) argument) (body.instantiateNewest argument)
  | lam {Γ : List Ty} {A B : Ty} {body body' : Term (A :: Γ) B} :
      BetaStep body body' → BetaStep (.lam body) (.lam body')
  | appLeft {Γ : List Ty} {A B : Ty} {f f' : Term Γ (.arr A B)} {a : Term Γ A} :
      BetaStep f f' → BetaStep (.app f a) (.app f' a)
  | appRight {Γ : List Ty} {A B : Ty} {f : Term Γ (.arr A B)} {a a' : Term Γ A} :
      BetaStep a a' → BetaStep (.app f a) (.app f a')

variable {Γ Δ Θ : List Ty} {A B C : Ty}

abbrev BetaConv (left right : Term Γ A) : Prop :=
  Relation.EqvGen BetaStep left right

theorem Term.rename_instantiateNewest (body : Term (A :: Γ) B)
    (argument : Term Γ A) (ρ : Renaming Γ Δ) :
    (body.instantiateNewest argument).rename ρ =
      (body.rename (liftRenaming ρ)).instantiateNewest (argument.rename ρ) := by
  simp only [Term.instantiateNewest, Term.rename_substitute, Term.substitute_rename]
  congr 1
  funext C v
  cases v <;> rfl

theorem Term.substitute_instantiateNewest (body : Term (A :: Γ) B)
    (argument : Term Γ A) (σ : Substitution Γ Δ) :
    (body.instantiateNewest argument).substitute σ =
      (body.substitute (liftSubstitution σ)).instantiateNewest (argument.substitute σ) := by
  simp only [Term.instantiateNewest, Term.substitute_comp]
  congr 1
  funext C v
  cases v with
  | zero => rfl
  | succ v =>
      change σ v = ((σ v).rename weakening).substitute _
      rw [Term.substitute_rename]
      exact (Term.substitute_id (σ v)).symm

theorem BetaStep.rename {left right : Term Γ A} (step : BetaStep left right)
    (ρ : Renaming Γ Δ) : BetaStep (left.rename ρ) (right.rename ρ) := by
  induction step generalizing Δ with
  | beta body argument =>
      rw [Term.rename_instantiateNewest]
      exact .beta _ _
  | lam _ ih => exact .lam (ih (liftRenaming ρ))
  | appLeft _ ih => exact .appLeft (ih ρ)
  | appRight _ ih => exact .appRight (ih ρ)

theorem BetaStep.substitute {left right : Term Γ A} (step : BetaStep left right)
    (σ : Substitution Γ Δ) : BetaStep (left.substitute σ) (right.substitute σ) := by
  induction step generalizing Δ with
  | beta body argument =>
      rw [Term.substitute_instantiateNewest]
      exact .beta _ _
  | lam _ ih => exact .lam (ih (liftSubstitution σ))
  | appLeft _ ih => exact .appLeft (ih σ)
  | appRight _ ih => exact .appRight (ih σ)

namespace BetaConv

theorem map {Γ Δ : List Ty} {A B : Ty} (f : Term Γ A → Term Δ B)
    (preserves : ∀ {x y}, BetaStep x y → BetaStep (f x) (f y))
    {left right : Term Γ A} (h : BetaConv left right) : BetaConv (f left) (f right) := by
  induction h with
  | rel _ _ h => exact .rel _ _ (preserves h)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

theorem rename {left right : Term Γ A} (h : BetaConv left right) (ρ : Renaming Γ Δ) :
    BetaConv (left.rename ρ) (right.rename ρ) :=
  map (fun t => t.rename ρ) (fun step => step.rename ρ) h

theorem substitute {left right : Term Γ A} (h : BetaConv left right)
    (σ : Substitution Γ Δ) : BetaConv (left.substitute σ) (right.substitute σ) :=
  map (fun t => t.substitute σ) (fun step => step.substitute σ) h

theorem lam {left right : Term (A :: Γ) B} (h : BetaConv left right) :
    BetaConv (.lam left) (.lam right) := map Term.lam BetaStep.lam h

theorem app {f f' : Term Γ (.arr A B)} {a a' : Term Γ A}
    (hf : BetaConv f f') (ha : BetaConv a a') :
    BetaConv (.app f a) (.app f' a') :=
  .trans _ _ _ (map (fun g => .app g a) BetaStep.appLeft hf)
    (map (fun b => .app f' b) BetaStep.appRight ha)

end BetaConv

/-- Pointwise beta conversion of simultaneous substitutions. -/
def Substitution.BetaConv (σ τ : Substitution Γ Δ) : Prop :=
  ∀ (A : Ty) (v : Var Γ A), IntrinsicSTT.BetaConv (σ v) (τ v)

theorem Substitution.BetaConv.lift {σ τ : Substitution Γ Δ}
    (h : Substitution.BetaConv σ τ) :
    Substitution.BetaConv (liftSubstitution (B := B) σ) (liftSubstitution τ) := by
  intro A v
  cases v with
  | zero => exact .refl _
  | succ v => exact (h _ v).rename weakening

theorem Term.substitute_congr (t : Term Γ A) {σ τ : Substitution Γ Δ}
    (h : Substitution.BetaConv σ τ) : BetaConv (t.substitute σ) (t.substitute τ) := by
  induction t generalizing Δ with
  | var v => exact h _ v
  | lam body ih => exact (ih h.lift).lam
  | app f a ihf iha => exact (ihf h).app (iha h)

theorem BetaConv.substitute_congr {left right : Term Γ A}
    (h : BetaConv left right) {σ τ : Substitution Γ Δ}
    (hs : Substitution.BetaConv σ τ) :
    BetaConv (left.substitute σ) (right.substitute τ) :=
  .trans _ _ _ (h.substitute σ) (right.substitute_congr hs)

theorem BetaStep.denote {left right : Term Γ A} (h : BetaStep left right)
    {Ground : Type u} (environment : Environment Ground Γ) :
    left.denote environment = right.denote environment := by
  induction h with
  | beta body argument => exact (BetaClaim.shallowValid ⟨body, argument⟩ environment)
  | lam _ ih => exact funext (fun value => ih (environment.extend value))
  | appLeft _ ih => exact congrFun (ih environment) _
  | appRight _ ih => exact congrArg _ (ih environment)

theorem BetaConv.denote {left right : Term Γ A} (h : BetaConv left right)
    {Ground : Type u} (environment : Environment Ground Γ) :
    left.denote environment = right.denote environment := by
  induction h with
  | rel _ _ h => exact h.denote environment
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem BetaStep.erase {left right : Term Γ A} (h : BetaStep left right) :
    Presentation.StepCore Presentation.Tower.rules.computation Presentation.Tower.rules.headEq
      (TowerDTT.eraseTerm left) (TowerDTT.eraseTerm right) := by
  induction h with
  | beta body argument => exact (SimpleFragmentSubstitutionTranslation.betaClaim_typed
      ⟨body, argument⟩).1
  | lam _ ih => exact .congLam ih
  | appLeft _ ih => exact .congAppFun ih
  | appRight _ ih => exact .congAppArg ih

theorem BetaConv.erase {left right : Term Γ A} (h : BetaConv left right) :
    Presentation.Conv Presentation.Tower.rules.headEq
      (TowerDTT.eraseTerm left) (TowerDTT.eraseTerm right)
      Presentation.Tower.rules.computation := by
  induction h with
  | rel _ _ h => exact .rel _ _ h.erase
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

/-- Conversion, rather than equality of raw syntax, defines these term classes. -/
def betaSetoid (Γ : List Ty) (A : Ty) : Setoid (Term Γ A) :=
  ⟨BetaConv, Relation.EqvGen.is_equivalence BetaStep⟩

abbrev BetaClass (Γ : List Ty) (A : Ty) := Quotient (betaSetoid Γ A)

def BetaClass.denote {Ground : Type u} (t : BetaClass Γ A)
    (environment : Environment Ground Γ) : A.denote Ground :=
  Quotient.lift (s := betaSetoid Γ A) (fun t => t.denote environment)
    (fun _ _ h => BetaConv.denote h environment) t

def BetaClass.substitute (σ : Substitution Γ Δ) : BetaClass Γ A → BetaClass Δ A :=
  Quotient.map (fun t => t.substitute σ) (fun _ _ h => h.substitute σ)

theorem BetaClass.substitute_congr {σ τ : Substitution Γ Δ}
    (h : Substitution.BetaConv σ τ) (t : BetaClass Γ A) :
    t.substitute σ = t.substitute τ := by
  induction t using Quotient.inductionOn with
  | _ t => exact Quotient.sound (t.substitute_congr h)

@[simp] theorem BetaClass.substitute_id (t : BetaClass Γ A) :
    t.substitute (Substitution.id Γ) = t := by
  induction t using Quotient.inductionOn with
  | _ t => exact congrArg (Quotient.mk (betaSetoid Γ A)) t.substitute_id

theorem BetaClass.substitute_comp (t : BetaClass Γ A)
    (σ : Substitution Γ Δ) (τ : Substitution Δ Θ) :
    (t.substitute σ).substitute τ = t.substitute (Substitution.comp σ τ) := by
  induction t using Quotient.inductionOn with
  | _ t => exact congrArg (Quotient.mk (betaSetoid Θ A)) (t.substitute_comp σ τ)

/-- The existing tower conversion relation regarded as a setoid. -/
def towerConversionSetoid (n : Nat) : Setoid (Presentation.Tower.Tm n) :=
  ⟨Presentation.Conv Presentation.Tower.HeadEq,
    Relation.EqvGen.is_equivalence _⟩

/-- The simple conversion classes map into the tower's conversion classes. -/
def BetaClass.toTower : BetaClass Γ A → Quotient (towerConversionSetoid Γ.length) :=
  Quotient.map TowerDTT.eraseTerm (fun _ _ h => BetaConv.erase h)

open SimpleFragmentErasureBoundary in
/-- The raw erasure collision disappears under actual beta conversion. -/
theorem discarded_identities_convert : BetaConv discardAtomicIdentity discardFunctionIdentity :=
  .trans _ _ _ (.rel _ _ (.lam (.beta _ _)))
    (.symm _ _ (.rel _ _ (.lam (.beta _ _))))

/-- Conversion does not identify the two projections of an open context. -/
theorem distinct_variables_not_convertible :
    ¬ BetaConv (.var .zero : Term [.atom, .atom] .atom) (.var (.succ .zero)) := by
  intro h
  let environment : Environment Bool [.atom, .atom] :=
    Environment.extend false (Environment.extend true ⟨fun v => nomatch v⟩)
  have impossible := h.denote environment
  exact Bool.noConfusion impossible

#print axioms BetaConv.substitute_congr
#print axioms BetaConv.erase
#print axioms BetaClass.substitute_congr
#print axioms discarded_identities_convert
#print axioms distinct_variables_not_convertible

end FourFaceBetaExperiment.IntrinsicSTT
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
