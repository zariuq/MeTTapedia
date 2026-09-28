import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.QuotientCwf
import Mettapedia.OSLF.Syntax.ContextualExponentialStructure

/-!
# Extensional conversion in the intrinsic lambda context theory

The beta-only quotient of intrinsically typed terms is not cartesian closed:
eta expansion of an open function remains distinct there. This module adds
eta to the *equational* conversion, proves stability under renaming and
capture-avoiding substitution, and constructs the resulting contextual
quotient. The operational beta-step relation is left unchanged.

This is the single-ground-sort function fragment. The relative classifying
theory for an arbitrary authored binding signature requires further structure.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaBetaEtaContextQuotient

open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT
open Mettapedia.GSLT.Core.ContextualLadder

variable {Γ Δ Θ : List Ty} {A B : Ty}

/-- Elementary beta and eta equations, closed under term constructors. Eta
has the intrinsic freshness condition: the function is weakened from the
outer context before it is applied to the new variable. -/
inductive Equation : {Γ : List Ty} → {A : Ty} → Term Γ A → Term Γ A → Prop where
  | beta {Γ : List Ty} {A B : Ty} (body : Term (A :: Γ) B)
      (argument : Term Γ A) :
      Equation (.app (.lam body) argument) (body.instantiateNewest argument)
  | eta {Γ : List Ty} {A B : Ty} (f : Term Γ (.arr A B)) :
      Equation (.lam (.app (f.rename weakening) (.var .zero))) f
  | lam {Γ : List Ty} {A B : Ty} {body body' : Term (A :: Γ) B} :
      Equation body body' → Equation (.lam body) (.lam body')
  | appLeft {Γ : List Ty} {A B : Ty}
      {f f' : Term Γ (.arr A B)} {a : Term Γ A} :
      Equation f f' → Equation (.app f a) (.app f' a)
  | appRight {Γ : List Ty} {A B : Ty}
      {f : Term Γ (.arr A B)} {a a' : Term Γ A} :
      Equation a a' → Equation (.app f a) (.app f a')

abbrev Conv (left right : Term Γ A) : Prop :=
  Relation.EqvGen Equation left right

theorem Equation.ofBetaStep {left right : Term Γ A}
    (step : BetaStep left right) : Equation left right := by
  induction step with
  | beta body argument => exact .beta body argument
  | lam _ ih => exact .lam ih
  | appLeft _ ih => exact .appLeft ih
  | appRight _ ih => exact .appRight ih

theorem Conv.ofBetaConv {left right : Term Γ A}
    (h : BetaConv left right) : Conv left right := by
  induction h with
  | rel _ _ h => exact .rel _ _ (Equation.ofBetaStep h)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

theorem Term.substitute_weakened (f : Term Γ (.arr A B))
    (σ : Substitution Γ Δ) :
    (f.rename (weakening (B := A))).substitute (liftSubstitution (B := A) σ) =
      (f.substitute σ).rename (weakening (B := A)) := by
  rw [Term.substitute_rename, Term.rename_substitute]
  congr 1

theorem Term.rename_weakened (f : Term Γ (.arr A B))
    (ρ : Renaming Γ Δ) :
    (f.rename (weakening (B := A))).rename (liftRenaming (B := A) ρ) =
      (f.rename ρ).rename (weakening (B := A)) := by
  rw [Term.rename_comp, Term.rename_comp]
  congr 1

theorem Term.weaken_as_substitute (t : Term Γ B) :
    t.substitute (syntacticScwf.wk (Γ := Γ) A) =
      t.rename (weakening (B := A)) := by
  change t.substitute (fun v => .var (.succ v)) = _
  simpa [Substitution.id, weakening] using
    (Term.substitute_rename t (weakening (B := A))
      (Substitution.id (A :: Γ))).symm

theorem Equation.rename {left right : Term Γ A}
    (h : Equation left right) (ρ : Renaming Γ Δ) :
    Equation (left.rename ρ) (right.rename ρ) := by
  induction h generalizing Δ with
  | beta body argument =>
      rw [Term.rename_instantiateNewest]
      exact .beta _ _
  | eta f =>
      simp only [Term.rename]
      rw [Term.rename_weakened]
      exact .eta (f.rename ρ)
  | lam _ ih => exact .lam (ih (liftRenaming ρ))
  | appLeft _ ih => exact .appLeft (ih ρ)
  | appRight _ ih => exact .appRight (ih ρ)

theorem Equation.substitute {left right : Term Γ A}
    (h : Equation left right) (σ : Substitution Γ Δ) :
    Equation (left.substitute σ) (right.substitute σ) := by
  induction h generalizing Δ with
  | beta body argument =>
      rw [Term.substitute_instantiateNewest]
      exact .beta _ _
  | eta f =>
      simp only [Term.substitute]
      rw [Term.substitute_weakened]
      exact .eta (f.substitute σ)
  | lam _ ih => exact .lam (ih (liftSubstitution σ))
  | appLeft _ ih => exact .appLeft (ih σ)
  | appRight _ ih => exact .appRight (ih σ)

namespace Conv

theorem map {Γ Δ : List Ty} {A B : Ty} (f : Term Γ A → Term Δ B)
    (preserves : ∀ {x y}, Equation x y → Equation (f x) (f y))
    {left right : Term Γ A} (h : Conv left right) : Conv (f left) (f right) := by
  induction h with
  | rel _ _ h => exact .rel _ _ (preserves h)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

theorem rename {left right : Term Γ A} (h : Conv left right)
    (ρ : Renaming Γ Δ) : Conv (left.rename ρ) (right.rename ρ) :=
  map (fun t => t.rename ρ) (fun step => step.rename ρ) h

theorem substitute {left right : Term Γ A} (h : Conv left right)
    (σ : Substitution Γ Δ) : Conv (left.substitute σ) (right.substitute σ) :=
  map (fun t => t.substitute σ) (fun step => step.substitute σ) h

theorem lam {left right : Term (A :: Γ) B} (h : Conv left right) :
    Conv (.lam left) (.lam right) := map Term.lam Equation.lam h

theorem app {f f' : Term Γ (.arr A B)} {a a' : Term Γ A}
    (hf : Conv f f') (ha : Conv a a') :
    Conv (.app f a) (.app f' a') :=
  .trans _ _ _ (map (fun g => .app g a) Equation.appLeft hf)
    (map (fun b => .app f' b) Equation.appRight ha)

end Conv

/-- Pointwise extensional conversion of simultaneous substitutions. -/
def SubstitutionConv (σ τ : Substitution Γ Δ) : Prop :=
  ∀ (A : Ty) (v : Var Γ A), Conv (σ v) (τ v)

theorem SubstitutionConv.lift {σ τ : Substitution Γ Δ}
    (h : SubstitutionConv σ τ) :
    SubstitutionConv (liftSubstitution (B := B) σ) (liftSubstitution τ) := by
  intro A v
  cases v with
  | zero => exact .refl _
  | succ v => exact (h _ v).rename weakening

theorem term_substitute_congr (t : Term Γ A) {σ τ : Substitution Γ Δ}
    (h : SubstitutionConv σ τ) : Conv (t.substitute σ) (t.substitute τ) := by
  induction t generalizing Δ with
  | var v => exact h _ v
  | lam body ih => exact (ih h.lift).lam
  | app f a ihf iha => exact (ihf h).app (iha h)

theorem Conv.substitute_congr {left right : Term Γ A}
    (h : Conv left right) {σ τ : Substitution Γ Δ}
    (hs : SubstitutionConv σ τ) :
    Conv (left.substitute σ) (right.substitute τ) :=
  .trans _ _ _ (h.substitute σ) (term_substitute_congr right hs)

def termSetoid (Γ : List Ty) (A : Ty) : Setoid (Term Γ A) :=
  ⟨Conv, Relation.EqvGen.is_equivalence Equation⟩

def substitutionSetoid (Γ Δ : List Ty) : Setoid (Substitution Γ Δ) where
  r := SubstitutionConv
  iseqv :=
    ⟨fun _ _ _ => .refl _,
     fun h A v => .symm _ _ (h A v),
     fun h k A v => .trans _ _ _ (h A v) (k A v)⟩

/-- The generic CwF quotient construction applied to the actual beta-eta
congruence on intrinsic lambda syntax. -/
def congruence : syntacticScwf.Congruence where
  sub Γ Δ := substitutionSetoid Δ Γ
  tm := termSetoid
  comp_rel := by
    intro Γ Δ Θ σ σ' τ τ' hσ hτ A v
    exact Conv.substitute_congr (hσ A v) hτ
  tmSub_rel := by
    intro Γ Δ A t t' σ σ' ht hσ
    exact Conv.substitute_congr ht hσ
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

abbrev TermClass (Γ : List Ty) (A : Ty) := Quotient (termSetoid Γ A)

def lam : TermClass (A :: Γ) B → TermClass Γ (.arr A B) :=
  Quotient.map Term.lam (fun {_ _} h => h.lam)

def app : TermClass Γ (.arr A B) → TermClass Γ A → TermClass Γ B :=
  Quotient.map₂ Term.app (fun {_ _} hf {_ _} ha => hf.app ha)

theorem beta (body : TermClass (A :: Γ) B) (argument : TermClass Γ A) :
    app (lam body) argument =
      scwf.tmSub body (scwf.pair (scwf.idS Γ) A argument) := by
  induction body, argument using Quotient.inductionOn₂ with
  | _ body argument => exact Quotient.sound (.rel _ _ (.beta body argument))

/-- Eta gives an actual equation on classes, not only equality in a
particular set interpretation. -/
theorem eta (f : TermClass Γ (.arr A B)) :
    lam (app (scwf.tmSub f (scwf.wk A)) (scwf.vz A)) = f := by
  induction f using Quotient.inductionOn with
  | _ f =>
      change Quotient.mk _ (.lam (.app
        (f.substitute (syntacticScwf.wk (Γ := Γ) A)) (.var .zero))) =
        Quotient.mk _ f
      rw [Term.weaken_as_substitute]
      exact Quotient.sound (.rel _ _ (.eta f))

theorem Term.lift_weaken_instantiateNewest (body : Term (A :: Γ) B) :
    (body.rename (liftRenaming (weakening (B := A)))).instantiateNewest
        (Term.var Var.zero : Term (A :: Γ) A) = body := by
  simp only [Term.instantiateNewest, Term.substitute_rename]
  have pointwise :
      (fun {C : Ty} (v : Var (A :: Γ) C) =>
        newestSubstitution (Term.var Var.zero : Term (A :: Γ) A)
          (liftRenaming (weakening (B := A)) v)) =
        (fun {C : Ty} (v : Var (A :: Γ) C) =>
          Substitution.id (A :: Γ) v) := by
    funext C v
    cases v with
    | zero => rfl
    | succ v => rfl
  rw [pointwise, Term.substitute_id]

/-- Reindex a function one context extension deeper. -/
def weaken (f : TermClass Γ (.arr A B)) :
    TermClass (A :: Γ) (.arr A B) :=
  Quotient.map (fun t => t.rename (weakening (B := A)))
    (fun {_ _} h => Conv.rename h (weakening (B := A))) f

/-- Apply a function to the fresh variable in the extended context. -/
def uncurry (f : TermClass Γ (.arr A B)) : TermClass (A :: Γ) B :=
  app (weaken f) (Quotient.mk (termSetoid (A :: Γ) A) (.var .zero))

theorem uncurry_lam (body : TermClass (A :: Γ) B) :
    uncurry (lam body) = body := by
  induction body using Quotient.inductionOn with
  | _ body =>
      apply Quotient.sound
      change Conv
        (.app (.lam (body.rename
          (liftRenaming (weakening (B := A))))) (.var .zero)) body
      have step : Conv
          (.app (.lam (body.rename
            (liftRenaming (weakening (B := A))))) (.var .zero))
          ((body.rename (liftRenaming (weakening (B := A)))).instantiateNewest
            (Term.var Var.zero : Term (A :: Γ) A)) :=
        .rel _ _ (.beta _ _)
      simpa only [Term.lift_weaken_instantiateNewest] using step

theorem lam_uncurry (f : TermClass Γ (.arr A B)) :
    lam (uncurry f) = f := by
  induction f using Quotient.inductionOn with
  | _ f =>
      apply Quotient.sound
      exact .rel _ _ (.eta f)

/-- The context extension by one type is represented by the function type
in the beta-eta quotient. This is the exponential hom-set law for one typed
variable; its inverse is application to that fresh variable. -/
def functionHomEquiv :
    TermClass (A :: Γ) B ≃ TermClass Γ (.arr A B) where
  toFun := lam
  invFun := uncurry
  left_inv := uncurry_lam
  right_inv := lam_uncurry

/-- Lifting a quotient substitution preserves the fresh bound variable and
substitutes under its binder. -/
def lift (σ : scwf.Sub Γ Δ) : scwf.Sub (A :: Γ) (A :: Δ) :=
  Quotient.map (liftSubstitution (B := A))
    (fun {_ _} h => SubstitutionConv.lift h) σ

theorem lam_substitute (body : TermClass (A :: Δ) B)
    (σ : scwf.Sub Γ Δ) :
    scwf.tmSub (lam body) σ = lam (scwf.tmSub body (lift σ)) := by
  induction body, σ using Quotient.inductionOn₂ with
  | _ body σ => rfl

/-- Currying commutes with every substitution of the ambient context. -/
theorem functionHomEquiv_natural (body : TermClass (A :: Δ) B)
    (σ : scwf.Sub Γ Δ) :
    functionHomEquiv (Γ := Γ) (A := A) (B := B)
        (scwf.tmSub body (lift σ)) =
      scwf.tmSub (functionHomEquiv (Γ := Δ) (A := A) (B := B) body) σ := by
  exact (lam_substitute body σ).symm

/-- The inverse of currying is natural as well; it follows from eta and the
proved naturality of currying, without a second substitution induction. -/
theorem uncurry_natural (f : TermClass Δ (.arr A B))
    (σ : scwf.Sub Γ Δ) :
    uncurry (scwf.tmSub f σ) = scwf.tmSub (uncurry f) (lift σ) := by
  apply (functionHomEquiv (Γ := Γ) (A := A) (B := B)).injective
  change lam (uncurry (scwf.tmSub f σ)) =
    lam (scwf.tmSub (uncurry f) (lift σ))
  have h₁ : lam (uncurry (scwf.tmSub f σ)) = scwf.tmSub f σ :=
    lam_uncurry _
  have h₂ : scwf.tmSub (lam (uncurry f)) σ = scwf.tmSub f σ :=
    congrArg (fun t : TermClass Δ (.arr A B) => scwf.tmSub t σ)
      (lam_uncurry f)
  have h₃ : scwf.tmSub (lam (uncurry f)) σ =
      lam (scwf.tmSub (uncurry f) (lift σ)) :=
    lam_substitute (uncurry f) σ
  exact h₁.trans (h₂.symm.trans h₃)

/-- The intrinsic lift is exactly the lift supplied by contextual pairing,
after quotienting. This connects the syntax proof to the general interface. -/
theorem lift_eq_contextual (σ : scwf.Sub Γ Δ) :
    lift (A := A) σ =
      ContextualExponentialStructure.lift σ A := by
  induction σ using Quotient.inductionOn with
  | _ σ =>
      apply congrArg (Quotient.mk (substitutionSetoid (A :: Δ) (A :: Γ)))
      funext C v
      cases v with
      | zero => rfl
      | succ v =>
          exact (Term.weaken_as_substitute (A := A) (σ v)).symm

/-- The beta-eta quotient is a model of the reusable contextual exponential
interface. Its naturality is the actual substitution theorem above. -/
def contextualExponential :
    ContextualExponentialStructure.ContextualExponential scwf where
  arrow := Ty.arr
  curry := functionHomEquiv
  curry_natural := by
    intro Γ Δ A B σ body
    rw [← lift_eq_contextual (A := A) σ]
    exact functionHomEquiv_natural body σ

theorem Equation.denote {left right : Term Γ A} (h : Equation left right)
    {Ground : Type*} (environment : Environment Ground Γ) :
    left.denote environment = right.denote environment := by
  induction h with
  | beta body argument => exact (BetaClaim.shallowValid ⟨body, argument⟩ environment)
  | eta f =>
      apply funext
      intro value
      change (f.rename weakening).denote
        (Environment.extend value environment) value =
        (f.denote environment) value
      rw [Term.denote_rename]
      rfl
  | lam _ ih => exact funext (fun value => ih (environment.extend value))
  | appLeft _ ih => exact congrFun (ih environment) _
  | appRight _ ih => exact congrArg _ (ih environment)

theorem Conv.denote {left right : Term Γ A} (h : Conv left right)
    {Ground : Type*} (environment : Environment Ground Γ) :
    left.denote environment = right.denote environment := by
  induction h with
  | rel _ _ h => exact h.denote environment
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Extensional conversion does not identify distinct open projections. -/
theorem distinct_open_variables :
    ¬ Conv (.var .zero : Term [.atom, .atom] .atom) (.var (.succ .zero)) := by
  intro h
  let environment : Environment Bool [.atom, .atom] :=
    Environment.extend false (Environment.extend true ⟨fun v => nomatch v⟩)
  have impossible := h.denote environment
  exact Bool.noConfusion impossible

theorem distinct_open_classes :
    (Quotient.mk (termSetoid [.atom, .atom] .atom) (.var .zero)) ≠
      Quotient.mk (termSetoid [.atom, .atom] .atom) (.var (.succ .zero)) := by
  intro equal
  exact distinct_open_variables (Quotient.exact equal)

/-- The previously constructed beta quotient factors through the new
equational quotient; its eta-distinction shows this factor is nontrivial. -/
def fromBetaClass : BetaClass Γ A → TermClass Γ A :=
  Quotient.map id (fun {_ _} h => Conv.ofBetaConv h)

/-- Map a beta substitution class to its beta-eta class componentwise. -/
def fromBetaSub
    (σ : Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.QuotientCwf.scwf.Sub Γ Δ) :
    scwf.Sub Γ Δ :=
  Quotient.map id
    (fun {_ _} h => by
      change Substitution.BetaConv _ _ at h
      exact fun A v => Conv.ofBetaConv (h A v)) σ

theorem fromBetaSub_id :
    fromBetaSub
        (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.QuotientCwf.scwf.idS Γ) =
      scwf.idS Γ := rfl

theorem fromBetaSub_comp
    (σ : Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.QuotientCwf.scwf.Sub Δ Θ)
    (τ : Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.QuotientCwf.scwf.Sub Γ Δ) :
    fromBetaSub
        (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.QuotientCwf.scwf.compS σ τ) =
      scwf.compS (fromBetaSub σ) (fromBetaSub τ) := by
  induction σ, τ using Quotient.inductionOn₂ with
  | _ σ τ => rfl

theorem fromBetaClass_substitute
    (t : BetaClass Δ A)
    (σ : Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.QuotientCwf.scwf.Sub Γ Δ) :
    fromBetaClass
        (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.QuotientCwf.scwf.tmSub t σ) =
      scwf.tmSub (fromBetaClass t) (fromBetaSub σ) := by
  induction t, σ using Quotient.inductionOn₂ with
  | _ t σ => rfl

theorem fromBetaSub_weakening :
    fromBetaSub
        (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.QuotientCwf.scwf.wk
          (Γ := Γ) A) =
      scwf.wk A := rfl

theorem fromBetaClass_newest :
    fromBetaClass
        (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.QuotientCwf.scwf.vz
          (Γ := Γ) A) =
      scwf.vz A := rfl

theorem fromBetaSub_pair
    (σ : Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.QuotientCwf.scwf.Sub Γ Δ)
    (t : BetaClass Γ A) :
    fromBetaSub
        (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.QuotientCwf.scwf.pair σ A t) =
      scwf.pair (fromBetaSub σ) A (fromBetaClass t) := by
  induction σ, t using Quotient.inductionOn₂ with
  | _ σ t => rfl

theorem fromBetaClass_lam (body : BetaClass (A :: Γ) B) :
    fromBetaClass
        (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.QuotientCwf.lam body) =
      lam (fromBetaClass body) := by
  induction body using Quotient.inductionOn with
  | _ body => rfl

theorem fromBetaClass_app (f : BetaClass Γ (.arr A B))
    (a : BetaClass Γ A) :
    fromBetaClass
        (Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.QuotientCwf.app f a) =
      app (fromBetaClass f) (fromBetaClass a) := by
  induction f, a using Quotient.inductionOn₂ with
  | _ f a => rfl

theorem fromBetaClass_identifies_eta :
    fromBetaClass (Quotient.mk (betaSetoid [.arr .atom .atom] (.arr .atom .atom))
      Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ConversionDecision.etaExpansion) =
    fromBetaClass (Quotient.mk (betaSetoid [.arr .atom .atom] (.arr .atom .atom))
      Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ConversionDecision.etaVariable) := by
  change (Quotient.mk _
      Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ConversionDecision.etaExpansion) =
    Quotient.mk _
      Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ConversionDecision.etaVariable
  apply Quotient.sound
  change Conv (.lam (.app (.var (.succ .zero)) (.var .zero))) (.var .zero)
  apply Relation.EqvGen.rel
  simpa [Term.rename, weakening] using
    (Equation.eta
      (Term.var (Var.zero : Var [.arr .atom .atom] (.arr .atom .atom))))

/-- The beta-to-beta-eta comparison is a proper quotient: the older
conversion distinguishes these two open functions. -/
theorem fromBetaClass_not_injective :
    ¬ Function.Injective
      (@fromBetaClass [.arr .atom .atom] (.arr .atom .atom)) := by
  intro injective
  exact Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.QuotientCwf.eta_distinct
    (injective fromBetaClass_identifies_eta).symm

#print axioms Equation.substitute
#print axioms Conv.substitute_congr
#print axioms congruence
#print axioms beta
#print axioms eta
#print axioms fromBetaClass_identifies_eta
#print axioms functionHomEquiv
#print axioms functionHomEquiv_natural
#print axioms contextualExponential
#print axioms fromBetaClass_not_injective
#print axioms fromBetaClass_substitute
#print axioms fromBetaSub_comp
#print axioms fromBetaSub_pair
#print axioms fromBetaClass_lam
#print axioms fromBetaClass_app
#print axioms distinct_open_classes

end Mettapedia.OSLF.Binding.LambdaBetaEtaContextQuotient
