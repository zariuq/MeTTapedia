import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.WeakHead

/-!
# Strong normalization and Girard's candidates

The directed reduction of a rule package is β for functions, the projections
of pairs, and the package's root computations, under every term former.
Universe-head equalities belong to conversion and take no step here.

A term is strongly normalizing when every reduction sequence from it is finite.
A term is inert when it is neither an introduction (an abstraction, a pair,
reflexivity, a constructor applied to arguments) nor a partial application of
a computing constant. Applying or projecting an inert term creates no redex at
the root, so its reducts are the reducts of its parts.

A candidate is a set of strongly normalizing terms, closed under reduction,
that contains every inert term all of whose reducts it contains (Girard's
CR1–CR3). The strongly normalizing terms form a candidate; candidates are
closed under the dependent function and pair constructions over any indexed
family, and under arbitrary intersections, which interpret impredicative
quantification.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace StrongNormalization

open Normalization

variable {Head : Type}

/-! ## Directed reduction -/

/-- No universe-head step: head equality is conversion, not computation. -/
def noHeadSteps : Head → Head → Prop := fun _ _ => False

/-- One step of the directed reduction of a rule package. -/
abbrev Reduces (R : Rules Head) {n : Nat} (t u : Tm Head n) : Prop :=
  StepCore R.computation noHeadSteps t u

/-- Finitely many steps of the directed reduction. -/
abbrev ReducesStar (R : Rules Head) {n : Nat} (t u : Tm Head n) : Prop :=
  Relation.ReflTransGen (Reduces R) t u

/-- A strongly normalizing term: every reduction sequence from it is finite. -/
def SN (R : Rules Head) {n : Nat} (t : Tm Head n) : Prop :=
  Acc (fun u t => Reduces R t u) t

/-- The root steps of a rule package occur at applications of constants. -/
def SpineHeaded (R : Rules Head) : Prop :=
  ∀ ⦃n : Nat⦄ ⦃t u : Tm Head n⦄, R.computation.step t u →
    ∃ c args, t = appSpine (.const c) args

theorem RootShape.spineHeaded {R : Rules Head} {roles : Roles Head}
    (shape : RootShape R roles) : SpineHeaded R := by
  intro n t u step
  obtain ⟨c, _, _, args, _, rfl, _, _⟩ := shape.spine step
  exact ⟨c, args, rfl⟩

variable {R : Rules Head}

namespace SN

theorem intro {n : Nat} {t : Tm Head n} (h : ∀ u, Reduces R t u → SN R u) : SN R t :=
  Acc.intro t h

theorem reduct {n : Nat} {t u : Tm Head n} (sn : SN R t) (step : Reduces R t u) : SN R u :=
  sn.inv step

theorem reducts {n : Nat} {t u : Tm Head n} (sn : SN R t) (steps : ReducesStar R t u) :
    SN R u := by
  induction steps with
  | refl => exact sn
  | tail _ step ih => exact ih.reduct step

/-- Strong normalization pulls back along a map that preserves steps. -/
theorem of_map {n m : Nat} (f : Tm Head n → Tm Head m)
    (preserves : ∀ {t u : Tm Head n}, Reduces R t u → Reduces R (f t) (f u))
    {t : Tm Head n} (sn : SN R (f t)) : SN R t := by
  have key : ∀ s, SN R s → ∀ t, f t = s → SN R t := by
    intro s hs
    induction hs with
    | intro s _ ih =>
        intro t ht
        exact SN.intro fun u step => ih (f u) (ht ▸ preserves step) u rfl
  exact key _ sn t rfl

theorem of_subst {n m : Nat} (σ : Sub Head n m) {t : Tm Head n}
    (sn : SN R (Presentation.subst σ t)) : SN R t :=
  of_map (Presentation.subst σ) (fun step => StepCore.substitute step σ) sn

theorem of_rename {n m : Nat} (ρ : Ren n m) {t : Tm Head n}
    (sn : SN R (Presentation.rename ρ t)) : SN R t :=
  of_map (Presentation.rename ρ) (fun step => StepCore.renameTerms step ρ) sn

theorem app_left {n : Nat} {f a : Tm Head n} (sn : SN R (.app f a)) : SN R f :=
  of_map (fun g => .app g a) (fun step => .congAppFun step) sn

theorem app_right {n : Nat} {f a : Tm Head n} (sn : SN R (.app f a)) : SN R a :=
  of_map (fun b => .app f b) (fun step => .congAppArg step) sn

theorem fst_arg {n : Nat} {p : Tm Head n} (sn : SN R (.fst p)) : SN R p :=
  of_map (fun q => .fst q) (fun step => .congFst step) sn

theorem snd_arg {n : Nat} {p : Tm Head n} (sn : SN R (.snd p)) : SN R p :=
  of_map (fun q => .snd q) (fun step => .congSnd step) sn

theorem lam_body {n : Nat} {b : Tm Head (n + 1)} (sn : SN R (.lam b)) : SN R b :=
  of_map (fun c => .lam c) (fun step => .congLam step) sn

theorem pair_left {n : Nat} {a b : Tm Head n} (sn : SN R (.pair a b)) : SN R a :=
  of_map (fun c => .pair c b) (fun step => .congPairFst step) sn

theorem pair_right {n : Nat} {a b : Tm Head n} (sn : SN R (.pair a b)) : SN R b :=
  of_map (fun c => .pair a c) (fun step => .congPairSnd step) sn

theorem refl_arg {n : Nat} {a : Tm Head n} (sn : SN R (.refl a)) : SN R a :=
  of_map (fun c => .refl c) (fun step => .congRefl step) sn

theorem pi_dom {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)} (sn : SN R (.pi A B)) :
    SN R A :=
  of_map (fun C => .pi C B) (fun step => .congPiDom step) sn

theorem pi_cod {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)} (sn : SN R (.pi A B)) :
    SN R B :=
  of_map (fun C => .pi A C) (fun step => .congPiCod step) sn

theorem sigma_dom {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)} (sn : SN R (.sigma A B)) :
    SN R A :=
  of_map (fun C => .sigma C B) (fun step => .congSigmaDom step) sn

theorem sigma_cod {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)} (sn : SN R (.sigma A B)) :
    SN R B :=
  of_map (fun C => .sigma A C) (fun step => .congSigmaCod step) sn

theorem id_ty {n : Nat} {A a b : Tm Head n} (sn : SN R (.id A a b)) : SN R A :=
  of_map (fun C => .id C a b) (fun step => .congIdTy step) sn

theorem id_left {n : Nat} {A a b : Tm Head n} (sn : SN R (.id A a b)) : SN R a :=
  of_map (fun c => .id A c b) (fun step => .congIdLeft step) sn

theorem id_right {n : Nat} {A a b : Tm Head n} (sn : SN R (.id A a b)) : SN R b :=
  of_map (fun c => .id A a c) (fun step => .congIdRight step) sn

end SN

/-! ## Terms that are not constant spines take only congruence steps -/

/-- A constant spine is the constant itself or an application. -/
theorem appSpine_const_cases {n : Nat} (c : DeclName) (as : List (Tm Head n)) :
    appSpine (.const c) as = .const c ∨ ∃ f a, appSpine (.const c) as = .app f a := by
  cases as using List.reverseRecOn with
  | nil => exact .inl rfl
  | append_singleton init last _ => exact .inr ⟨_, _, appSpine_concat _ _ _⟩

/-- A term that is neither a constant nor an application is not a constant
spine. -/
theorem not_spine_of {n : Nat} {t : Tm Head n} (notConst : ∀ c, t ≠ .const c)
    (notApp : ∀ f a, t ≠ .app f a) : ∀ c args, t ≠ appSpine (.const c) args := by
  intro c args equal
  rcases appSpine_const_cases c args with h | ⟨f, a, h⟩
  · exact notConst c (equal.trans h)
  · exact notApp f a (equal.trans h)

section Congruence

variable (spine : SpineHeaded R)
include spine

theorem not_root_of_not_spine {n : Nat} {t u : Tm Head n}
    (notSpine : ∀ c args, t ≠ appSpine (.const c) args) : ¬ R.computation.step t u := by
  intro step
  obtain ⟨c, args, rfl⟩ := spine step
  exact notSpine c args rfl

theorem SN.var {n : Nat} (i : Fin n) : SN R (.var i : Tm Head n) :=
  SN.intro fun u step => by
    cases step with
    | root r =>
        exact absurd r (not_root_of_not_spine spine (not_spine_of (by simp) (by simp)))

theorem SN.head {n : Nat} (h : Head) : SN R (.head h : Tm Head n) :=
  SN.intro fun u step => by
    cases step with
    | head e => exact e.elim
    | root r =>
        exact absurd r (not_root_of_not_spine spine (not_spine_of (by simp) (by simp)))

theorem SN.lam {n : Nat} {b : Tm Head (n + 1)} (sn : SN R b) : SN R (.lam b) := by
  induction sn with
  | intro b _ ih =>
      refine SN.intro fun u step => ?_
      cases step with
      | root r =>
          exact absurd r (not_root_of_not_spine spine (not_spine_of (by simp) (by simp)))
      | congLam s => exact ih _ s

theorem SN.refl {n : Nat} {a : Tm Head n} (sn : SN R a) : SN R (.refl a) := by
  induction sn with
  | intro a _ ih =>
      refine SN.intro fun u step => ?_
      cases step with
      | root r =>
          exact absurd r (not_root_of_not_spine spine (not_spine_of (by simp) (by simp)))
      | congRefl s => exact ih _ s

theorem SN.pair {n : Nat} {a b : Tm Head n} (sa : SN R a) (sb : SN R b) :
    SN R (.pair a b) := by
  induction sa generalizing b with
  | intro a _ iha =>
      induction sb with
      | intro b hb ihb =>
          refine SN.intro fun u step => ?_
          cases step with
          | root r =>
              exact absurd r (not_root_of_not_spine spine (not_spine_of (by simp) (by simp)))
          | congPairFst s => exact iha _ s (SN.intro hb)
          | congPairSnd s => exact ihb _ s

theorem SN.pi {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)} (sA : SN R A) (sB : SN R B) :
    SN R (.pi A B) := by
  induction sA generalizing B with
  | intro A _ ihA =>
      induction sB with
      | intro B hB ihB =>
          refine SN.intro fun u step => ?_
          cases step with
          | root r =>
              exact absurd r (not_root_of_not_spine spine (not_spine_of (by simp) (by simp)))
          | congPiDom s => exact ihA _ s (SN.intro hB)
          | congPiCod s => exact ihB _ s

theorem SN.sigma {n : Nat} {A : Tm Head n} {B : Tm Head (n + 1)} (sA : SN R A)
    (sB : SN R B) : SN R (.sigma A B) := by
  induction sA generalizing B with
  | intro A _ ihA =>
      induction sB with
      | intro B hB ihB =>
          refine SN.intro fun u step => ?_
          cases step with
          | root r =>
              exact absurd r (not_root_of_not_spine spine (not_spine_of (by simp) (by simp)))
          | congSigmaDom s => exact ihA _ s (SN.intro hB)
          | congSigmaCod s => exact ihB _ s

theorem SN.id {n : Nat} {A a b : Tm Head n} (sA : SN R A) (sa : SN R a) (sb : SN R b) :
    SN R (.id A a b) := by
  induction sA generalizing a b with
  | intro A hA ihA =>
      induction sa generalizing b with
      | intro a ha iha =>
          induction sb with
          | intro b hb ihb =>
              refine SN.intro fun u step => ?_
              cases step with
              | root r =>
                  exact absurd r (not_root_of_not_spine spine (not_spine_of (by simp) (by simp)))
              | congIdTy s => exact ihA _ s (SN.intro ha) (SN.intro hb)
              | congIdLeft s => exact iha _ s (SN.intro hb)
              | congIdRight s => exact ihb _ s

end Congruence

/-! ## Inert terms -/

/-- A term that is neither an introduction nor a partial application of a
computing constant. Its applications and projections have no root redex. -/
def Inert (roles : Roles Head) {n : Nat} (t : Tm Head n) : Prop :=
  (∀ b, t ≠ .lam b) ∧ (∀ a b, t ≠ .pair a b) ∧ (∀ a, t ≠ .refl a) ∧
  (∀ k arity args, roles k = .constructor arity → t ≠ appSpine (.const k) args) ∧
  (∀ c arity scrutinee args, roles c = .computes arity scrutinee → args.length < arity →
    t ≠ appSpine (.const c) args)

variable {roles : Roles Head}

theorem Inert.app {n : Nat} {f a : Tm Head n} (inert : Inert roles f) :
    Inert roles (.app f a) := by
  obtain ⟨_, _, _, notCtor, notPartial⟩ := inert
  refine ⟨by simp, by simp, by simp, ?_, ?_⟩
  · intro k arity args role equal
    obtain ⟨init, rfl, hf⟩ := appSpine_const_eq_app equal.symm
    exact notCtor k arity init role hf
  · intro c arity scrutinee args role short equal
    obtain ⟨init, rfl, hf⟩ := appSpine_const_eq_app equal.symm
    simp only [List.length_append, List.length_singleton] at short
    exact notPartial c arity scrutinee init role (by omega) hf

theorem Inert.fst {n : Nat} {p : Tm Head n} : Inert roles (.fst p : Tm Head n) := by
  refine ⟨by simp, by simp, by simp, ?_, ?_⟩
  · intro k arity args _ equal
    exact appSpine_const_ne_fst equal.symm
  · intro c arity scrutinee args _ _ equal
    exact appSpine_const_ne_fst equal.symm

theorem Inert.snd {n : Nat} {p : Tm Head n} : Inert roles (.snd p : Tm Head n) := by
  refine ⟨by simp, by simp, by simp, ?_, ?_⟩
  · intro k arity args _ equal
    exact appSpine_const_ne_snd equal.symm
  · intro c arity scrutinee args _ _ equal
    exact appSpine_const_ne_snd equal.symm

theorem Inert.head {n : Nat} (h : Head) : Inert roles (.head h : Tm Head n) := by
  refine ⟨by simp, by simp, by simp, ?_, ?_⟩
  · intro k arity args _ equal
    exact not_spine_of (by simp) (by simp) k args equal
  · intro c arity scrutinee args _ _ equal
    exact not_spine_of (by simp) (by simp) c args equal

theorem Inert.var {n : Nat} (i : Fin n) : Inert roles (.var i : Tm Head n) := by
  refine ⟨by simp, by simp, by simp, ?_, ?_⟩
  · intro k arity args _ equal
    exact not_spine_of (by simp) (by simp) k args equal
  · intro c arity scrutinee args _ _ equal
    exact not_spine_of (by simp) (by simp) c args equal

section Reducts

variable (shape : RootShape R roles)
include shape

/-- The reducts of an application of an inert term are reducts of its parts. -/
theorem Inert.app_reduct {n : Nat} {f a v : Tm Head n} (inert : Inert roles f)
    (step : Reduces R (.app f a) v) :
    (∃ f', Reduces R f f' ∧ v = .app f' a) ∨ (∃ a', Reduces R a a' ∧ v = .app f a') := by
  cases step with
  | betaPi => exact (inert.1 _ rfl).elim
  | root r =>
      obtain ⟨c, arity, scrutinee, args, role, equal, length, _⟩ := shape.spine r
      obtain ⟨init, rfl, hf⟩ := appSpine_const_eq_app equal.symm
      simp only [List.length_append, List.length_singleton] at length
      exact absurd hf (inert.2.2.2.2 c arity scrutinee init role (by omega))
  | congAppFun s => exact .inl ⟨_, s, rfl⟩
  | congAppArg s => exact .inr ⟨_, s, rfl⟩

/-- The reducts of the first projection of an inert term are projections of
its reducts. -/
theorem Inert.fst_reduct {n : Nat} {p v : Tm Head n} (inert : Inert roles p)
    (step : Reduces R (.fst p) v) : ∃ p', Reduces R p p' ∧ v = .fst p' := by
  cases step with
  | betaSigmaFst => exact (inert.2.1 _ _ rfl).elim
  | root r =>
      obtain ⟨c, _, _, args, _, equal, _, _⟩ := shape.spine r
      exact absurd equal.symm appSpine_const_ne_fst
  | congFst s => exact ⟨_, s, rfl⟩

theorem Inert.snd_reduct {n : Nat} {p v : Tm Head n} (inert : Inert roles p)
    (step : Reduces R (.snd p) v) : ∃ p', Reduces R p p' ∧ v = .snd p' := by
  cases step with
  | betaSigmaSnd => exact (inert.2.1 _ _ rfl).elim
  | root r =>
      obtain ⟨c, _, _, args, _, equal, _, _⟩ := shape.spine r
      exact absurd equal.symm appSpine_const_ne_snd
  | congSnd s => exact ⟨_, s, rfl⟩

/-- An inert term that is normal: a head, for instance. -/
theorem head_normal {n : Nat} (h : Head) (u : Tm Head n) : ¬ Reduces R (.head h) u := by
  intro step
  cases step with
  | head e => exact e.elim
  | root r =>
      exact absurd r (not_root_of_not_spine (RootShape.spineHeaded shape)
        (not_spine_of (by simp) (by simp)))

end Reducts

/-! ## Reducing the terms a substitution puts in place -/

theorem ReducesStar.rename {n m : Nat} (ρ : Ren n m) {t u : Tm Head n}
    (steps : ReducesStar R t u) :
    ReducesStar R (Presentation.rename ρ t) (Presentation.rename ρ u) :=
  steps.lift (Presentation.rename ρ) fun _ _ step => StepCore.renameTerms step ρ

theorem ReducesStar.substitute {n m : Nat} (σ : Sub Head n m) {t u : Tm Head n}
    (steps : ReducesStar R t u) :
    ReducesStar R (Presentation.subst σ t) (Presentation.subst σ u) :=
  steps.lift (Presentation.subst σ) fun _ _ step => StepCore.substitute step σ

namespace ReducesStar

variable {n : Nat}

theorem pi {A A' : Tm Head n} {B B' : Tm Head (n + 1)} (hA : ReducesStar R A A')
    (hB : ReducesStar R B B') : ReducesStar R (.pi A B) (.pi A' B') :=
  (hA.lift (fun X : Tm Head n => (Tm.pi X B : Tm Head n))
      fun _ _ s => StepCore.congPiDom s).trans
    (hB.lift (fun Y : Tm Head (n + 1) => (Tm.pi A' Y : Tm Head n))
      fun _ _ s => StepCore.congPiCod s)

theorem sigma {A A' : Tm Head n} {B B' : Tm Head (n + 1)} (hA : ReducesStar R A A')
    (hB : ReducesStar R B B') : ReducesStar R (.sigma A B) (.sigma A' B') :=
  (hA.lift (fun X : Tm Head n => (Tm.sigma X B : Tm Head n))
      fun _ _ s => StepCore.congSigmaDom s).trans
    (hB.lift (fun Y : Tm Head (n + 1) => (Tm.sigma A' Y : Tm Head n))
      fun _ _ s => StepCore.congSigmaCod s)

theorem id {A A' a a' b b' : Tm Head n} (hA : ReducesStar R A A') (ha : ReducesStar R a a')
    (hb : ReducesStar R b b') : ReducesStar R (.id A a b) (.id A' a' b') :=
  ((hA.lift (fun X : Tm Head n => (Tm.id X a b : Tm Head n))
      fun _ _ s => StepCore.congIdTy s).trans
    (ha.lift (fun X : Tm Head n => (Tm.id A' X b : Tm Head n))
      fun _ _ s => StepCore.congIdLeft s)).trans
    (hb.lift (fun X : Tm Head n => (Tm.id A' a' X : Tm Head n))
      fun _ _ s => StepCore.congIdRight s)

theorem lam {b b' : Tm Head (n + 1)} (hb : ReducesStar R b b') :
    ReducesStar R (.lam b : Tm Head n) (.lam b') :=
  hb.lift (fun X : Tm Head (n + 1) => (Tm.lam X : Tm Head n)) fun _ _ s => StepCore.congLam s

theorem app {f f' a a' : Tm Head n} (hf : ReducesStar R f f') (ha : ReducesStar R a a') :
    ReducesStar R (.app f a) (.app f' a') :=
  (hf.lift (fun X : Tm Head n => (Tm.app X a : Tm Head n))
      fun _ _ s => StepCore.congAppFun s).trans
    (ha.lift (fun X : Tm Head n => (Tm.app f' X : Tm Head n))
      fun _ _ s => StepCore.congAppArg s)

theorem pair {a a' b b' : Tm Head n} (ha : ReducesStar R a a') (hb : ReducesStar R b b') :
    ReducesStar R (.pair a b) (.pair a' b') :=
  (ha.lift (fun X : Tm Head n => (Tm.pair X b : Tm Head n))
      fun _ _ s => StepCore.congPairFst s).trans
    (hb.lift (fun X : Tm Head n => (Tm.pair a' X : Tm Head n))
      fun _ _ s => StepCore.congPairSnd s)

theorem fst {p p' : Tm Head n} (hp : ReducesStar R p p') :
    ReducesStar R (.fst p) (.fst p') :=
  hp.lift (fun X : Tm Head n => (Tm.fst X : Tm Head n)) fun _ _ s => StepCore.congFst s

theorem snd {p p' : Tm Head n} (hp : ReducesStar R p p') :
    ReducesStar R (.snd p) (.snd p') :=
  hp.lift (fun X : Tm Head n => (Tm.snd X : Tm Head n)) fun _ _ s => StepCore.congSnd s

theorem refl' {a a' : Tm Head n} (ha : ReducesStar R a a') :
    ReducesStar R (.refl a) (.refl a') :=
  ha.lift (fun X : Tm Head n => (Tm.refl X : Tm Head n)) fun _ _ s => StepCore.congRefl s

end ReducesStar

/-- Reducing the terms a substitution puts in place reduces the result. -/
theorem reducesStar_subst_args : ∀ {n m : Nat} (t : Tm Head n) {σ σ' : Sub Head n m},
    (∀ i, ReducesStar R (σ i) (σ' i)) →
    ReducesStar R (Presentation.subst σ t) (Presentation.subst σ' t)
  | _, _, .var i, _, _, h => h i
  | _, _, .const _, _, _, _ => .refl
  | _, _, .head _, _, _, _ => .refl
  | _, _, .pi A B, _, _, h =>
      .pi (reducesStar_subst_args A h) (reducesStar_subst_args B (lift_args h))
  | _, _, .sigma A B, _, _, h =>
      .sigma (reducesStar_subst_args A h) (reducesStar_subst_args B (lift_args h))
  | _, _, .id A a b, _, _, h =>
      .id (reducesStar_subst_args A h) (reducesStar_subst_args a h) (reducesStar_subst_args b h)
  | _, _, .lam body, _, _, h => .lam (reducesStar_subst_args body (lift_args h))
  | _, _, .app f a, _, _, h => .app (reducesStar_subst_args f h) (reducesStar_subst_args a h)
  | _, _, .pair a b, _, _, h =>
      .pair (reducesStar_subst_args a h) (reducesStar_subst_args b h)
  | _, _, .fst p, _, _, h => .fst (reducesStar_subst_args p h)
  | _, _, .snd p, _, _, h => .snd (reducesStar_subst_args p h)
  | _, _, .refl a, _, _, h => .refl' (reducesStar_subst_args a h)
where
  lift_args {n m : Nat} {σ σ' : Sub Head n m} (h : ∀ i, ReducesStar R (σ i) (σ' i)) :
      ∀ i, ReducesStar R (liftSub σ i) (liftSub σ' i) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact .refl
    · exact (h j).rename wk

theorem reducesStar_inst0 {n : Nat} (body : Tm Head (n + 1)) {a a' : Tm Head n}
    (step : Reduces R a a') : ReducesStar R (inst0 a body) (inst0 a' body) := by
  apply reducesStar_subst_args
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact .single step
  · exact .refl

/-! ## Candidates -/

/-- A reducibility candidate: strongly normalizing terms, closed under
reduction, containing every inert term whose reducts it contains. -/
structure Candidate (R : Rules Head) (roles : Roles Head) (n : Nat) where
  mem : Tm Head n → Prop
  sn : ∀ {t}, mem t → SN R t
  reduct : ∀ {t u}, mem t → Reduces R t u → mem u
  inert : ∀ {t}, Inert roles t → (∀ u, Reduces R t u → mem u) → mem t

namespace Candidate

variable {n : Nat}

theorem reducts (C : Candidate R roles n) {t u : Tm Head n} (h : C.mem t)
    (steps : ReducesStar R t u) : C.mem u := by
  induction steps with
  | refl => exact h
  | tail _ step ih => exact C.reduct ih step

/-- Every candidate contains the normal inert terms. -/
theorem normal (C : Candidate R roles n) {t : Tm Head n} (inert : Inert roles t)
    (normal : ∀ u, ¬ Reduces R t u) : C.mem t :=
  C.inert inert fun u step => (normal u step).elim

/-- The strongly normalizing terms. -/
def sn' : Candidate R roles n where
  mem := SN R
  sn := id
  reduct := fun h step => h.reduct step
  inert := fun _ h => SN.intro h

/-- The terms in every candidate of a family, over any index: impredicative
quantification. -/
def inter {I : Sort _} (F : I → Candidate R roles n) : Candidate R roles n where
  mem t := SN R t ∧ ∀ i, (F i).mem t
  sn h := h.1
  reduct h step := ⟨h.1.reduct step, fun i => (F i).reduct (h.2 i) step⟩
  inert hi h :=
    ⟨SN.intro fun u step => (h u step).1, fun i => (F i).inert hi fun u step => (h u step).2 i⟩

section Constructions

variable (shape : RootShape R roles)
include shape

/-- A head is in every candidate. -/
theorem head_mem (C : Candidate R roles n) (h : Head) : C.mem (.head h) :=
  C.normal (Inert.head h) (head_normal shape h)

/-- Terms whose application to every realizer of each domain element lands in
the codomain at that element. -/
def pi {I : Sort _} (point : I) (h : Head) (dom : I → Candidate R roles n)
    (cod : I → Candidate R roles n) : Candidate R roles n where
  mem t := ∀ i a, (dom i).mem a → (cod i).mem (.app t a)
  sn hm := SN.app_left ((cod point).sn (hm point _ (head_mem shape (dom point) h)))
  reduct hm step := fun i a ha => (cod i).reduct (hm i a ha) (.congAppFun step)
  inert := by
    intro t hi hreducts i a ha
    have key : ∀ a, SN R a → (dom i).mem a → (cod i).mem (.app t a) := by
      intro a sa
      induction sa with
      | intro a _ ih =>
          intro ha
          refine (cod i).inert hi.app fun v step => ?_
          rcases Inert.app_reduct shape hi step with ⟨t', s, rfl⟩ | ⟨a', s, rfl⟩
          · exact hreducts t' s i a ha
          · exact ih a' s ((dom i).reduct ha s)
    exact key a ((dom i).sn ha) ha

/-- Terms whose projections are realizers of the two components. -/
def sigma (first second : Candidate R roles n) : Candidate R roles n where
  mem t := first.mem (.fst t) ∧ second.mem (.snd t)
  sn hm := SN.fst_arg (first.sn hm.1)
  reduct hm step := ⟨first.reduct hm.1 (.congFst step), second.reduct hm.2 (.congSnd step)⟩
  inert hi hreducts :=
    ⟨first.inert Inert.fst fun v step => by
        obtain ⟨p', s, rfl⟩ := Inert.fst_reduct shape hi step
        exact (hreducts p' s).1,
      second.inert Inert.snd fun v step => by
        obtain ⟨p', s, rfl⟩ := Inert.snd_reduct shape hi step
        exact (hreducts p' s).2⟩

/-- β-expansion: an applied abstraction is in a candidate when its contractum
is, its argument is strongly normalizing, and so is its body. -/
theorem beta (C : Candidate R roles n) {body : Tm Head (n + 1)} {a : Tm Head n}
    (sb : SN R body) (sa : SN R a) (contractum : C.mem (inst0 a body)) :
    C.mem (.app (.lam body) a) := by
  induction sb generalizing a with
  | intro body _ ihb =>
      induction sa with
      | intro a _ iha =>
          refine C.inert ?_ fun v step => ?_
          · refine ⟨by simp, by simp, by simp, ?_, ?_⟩
            · intro k arity args _ equal
              obtain ⟨init, _, hf⟩ := appSpine_const_eq_app equal.symm
              exact not_spine_of (by simp) (by simp) k init hf
            · intro c arity scrutinee args _ _ equal
              obtain ⟨init, _, hf⟩ := appSpine_const_eq_app equal.symm
              exact not_spine_of (by simp) (by simp) c init hf
          cases step with
          | betaPi => exact contractum
          | root r =>
              obtain ⟨c, _, _, args, _, equal, _, _⟩ := shape.spine r
              obtain ⟨init, _, hf⟩ := appSpine_const_eq_app equal.symm
              exact absurd hf (not_spine_of (by simp) (by simp) c init)
          | congAppFun s =>
              cases s with
              | root r =>
                  obtain ⟨c, _, _, args, _, equal, _, _⟩ := shape.spine r
                  exact absurd equal (not_spine_of (by simp) (by simp) c args)
              | congLam s' =>
                  exact ihb _ s' (SN.intro ‹_›) (C.reduct contractum
                    (StepCore.substitute s' (subst0 a)))
          | congAppArg s =>
              exact iha _ s (C.reducts contractum (reducesStar_inst0 body s))

/-- A first projection of a pair is in a candidate when the first component
is and the second component is strongly normalizing. -/
theorem fst_pair (C : Candidate R roles n) {a b : Tm Head n} (sb : SN R b) (ha : C.mem a) :
    C.mem (.fst (.pair a b)) := by
  have sa := C.sn ha
  induction sa generalizing b with
  | intro a _ iha =>
      induction sb with
      | intro b hb ihb =>
          refine C.inert Inert.fst fun v step => ?_
          cases step with
          | betaSigmaFst => exact ha
          | root r =>
              obtain ⟨c, _, _, args, _, equal, _, _⟩ := shape.spine r
              exact absurd equal.symm appSpine_const_ne_fst
          | congFst s =>
              cases s with
              | root r =>
                  obtain ⟨c, _, _, args, _, equal, _, _⟩ := shape.spine r
                  exact absurd equal (not_spine_of (by simp) (by simp) c args)
              | congPairFst s' => exact iha _ s' (SN.intro hb) (C.reduct ha s')
              | congPairSnd s' => exact ihb _ s'

theorem snd_pair (C : Candidate R roles n) {a b : Tm Head n} (sa : SN R a) (hb : C.mem b) :
    C.mem (.snd (.pair a b)) := by
  have sb := C.sn hb
  induction sa generalizing b with
  | intro a ha iha =>
      induction sb with
      | intro b _ ihb =>
          refine C.inert Inert.snd fun v step => ?_
          cases step with
          | betaSigmaSnd => exact hb
          | root r =>
              obtain ⟨c, _, _, args, _, equal, _, _⟩ := shape.spine r
              exact absurd equal.symm appSpine_const_ne_snd
          | congSnd s =>
              cases s with
              | root r =>
                  obtain ⟨c, _, _, args, _, equal, _, _⟩ := shape.spine r
                  exact absurd equal (not_spine_of (by simp) (by simp) c args)
              | congPairFst s' => exact iha _ s' hb (C.sn hb)
              | congPairSnd s' => exact ihb _ s' (C.reduct hb s')

end Constructions

end Candidate

end StrongNormalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
