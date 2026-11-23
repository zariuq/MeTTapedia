import Mettapedia.OSLF.Framework.GSLTTypeSynthesis
import Mathlib.Logic.Relation

/-! Computational steps may be promoted to conversion while visible transitions
retain their labels. Exactness of finite observable traces needs a lifting
property: a visible transition of another representative has to be realizable
from the present representative. Neither termination nor determinism is part
of the construction. -/

set_option autoImplicit false
namespace Mettapedia.GSLT.ComputationQuotient

open _root_.Relation (EqvGen ReflTransGen)
universe u v w

structure Split (S : GSLT.{u}) (Label : Type v) where
  compute : S.Term → S.Term → Prop
  effect : Label → S.Term → S.Term → Prop
  accounts : ∀ x y, S.Step x y ↔ compute x y ∨ ∃ l, effect l x y

namespace Split

variable {S : GSLT.{u}} {L : Type v} (P : Split S L)

/-- Keep the original equation theory, then freely equate endpoints of the
designated computations. Distinct visible labels can share endpoints. -/
def conversion : Setoid S.Term where
  r := EqvGen (fun x y => S.Equiv x y ∨ P.compute x y)
  iseqv := Relation.EqvGen.is_equivalence _

abbrev Class := Quotient P.conversion
def project (x : S.Term) : P.Class := Quotient.mk P.conversion x

def visible (l : L) (fromState toState : P.Class) : Prop :=
  ∃ x y, P.project x = fromState ∧ P.project y = toState ∧ P.effect l x y

def promoted : GSLT := Mettapedia.OSLF.Framework.GSLTTypeSynthesis.equalityGSLT P.Class
  (fun x y => ∃ l, P.visible l x y)

theorem compute_equal {x y : S.Term} (h : P.compute x y) : P.project x = P.project y :=
  Quotient.sound (EqvGen.rel _ _ (Or.inr h) : P.conversion.r x y)

theorem reductions_equal {x y : S.Term} (h : ReflTransGen P.compute x y) : P.project x = P.project y := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact ih.trans (P.compute_equal h)

theorem step_projects {x y : S.Term} (h : S.Step x y) :
    P.project x = P.project y ∨ P.promoted.Step (P.project x) (P.project y) := by
  rcases (P.accounts x y).mp h with c | ⟨l,e⟩
  · exact Or.inl (P.compute_equal c)
  · exact Or.inr ⟨l, x, y, rfl, rfl, e⟩

/-- A guard, count or returned value descends exactly when it is invariant
on the original equations and on every computation being erased. -/
theorem observer_iff {A : Type w} (observe : S.Term → A) :
    (∃ read : P.Class → A, ∀ x, read (P.project x) = observe x) ↔
      (∀ x y, S.Equiv x y → observe x = observe y) ∧
      (∀ x y, P.compute x y → observe x = observe y) := by
  constructor
  · rintro ⟨read, h⟩
    constructor
    · intro x y eqn
      exact (h x).symm.trans ((congrArg read (Quotient.sound
        (EqvGen.rel _ _ (Or.inl eqn) : P.conversion.r x y))).trans (h y))
    · intro x y c; exact (h x).symm.trans ((congrArg read (P.compute_equal c)).trans (h y))
  · rintro ⟨eqn, comp⟩
    refine ⟨Quotient.lift observe ?_, fun _ => rfl⟩
    intro x y relation
    induction relation with
    | rel x y h => exact h.elim (eqn x y) (comp x y)
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih jh => exact ih.trans jh

section Transport

variable {T U : GSLT.{u}} {M N : Type v} (Q : Split T M)

/-- A context substitution or term translation can act on the promoted
classes precisely by respecting the old equations and erased computations.
A generator may map to any finite target conversion. -/
def Respects (f : S.Term → T.Term) : Prop :=
  (∀ x y, S.Equiv x y → Q.project (f x) = Q.project (f y)) ∧
  (∀ x y, P.compute x y → Q.project (f x) = Q.project (f y))

theorem map_exists_iff (f : S.Term → T.Term) :
    (∃ F : P.Class → Q.Class, ∀ x, F (P.project x) = Q.project (f x)) ↔ P.Respects Q f :=
  P.observer_iff (fun x => Q.project (f x))

theorem map_unique {f : S.Term → T.Term} {F G : P.Class → Q.Class}
    (first : ∀ x, F (P.project x) = Q.project (f x))
    (second : ∀ x, G (P.project x) = Q.project (f x)) : F = G := by
  funext q
  exact Quotient.inductionOn q (fun x => (first x).trans (second x).symm)

theorem respects_comp (R : Split U N) {f : S.Term → T.Term} {g : T.Term → U.Term}
    (first : P.Respects Q f) (second : Q.Respects R g) : P.Respects R (g ∘ f) := by
  obtain ⟨F, hf⟩ := (P.map_exists_iff Q f).2 first
  obtain ⟨G, hg⟩ := (Q.map_exists_iff R g).2 second
  apply (P.map_exists_iff R _).1
  exact ⟨G ∘ F, fun x => (congrArg G (hf x)).trans (hg _)⟩

end Transport

/-- A source can perform silent work before issuing one visible event. -/
def weak (l : L) (x y : S.Term) : Prop :=
  ∃ prepared, ReflTransGen P.compute x prepared ∧ P.effect l prepared y

/-- Local sufficient simulation test. Starting at an equivalent
representative, one can realize the event and land in its output class. -/
def Lifts : Prop := ∀ {x u v : S.Term} {l}, P.project x = P.project u → P.effect l u v →
  ∃ y, P.weak l x y ∧ P.project y = P.project v

/-- Computations from equivalent representatives can meet, and a pending
event can be postponed across one computation without changing its output
class. These two local obligations suffice for finite traces. -/
theorem lifts_of_join_postponement
    (join : ∀ {x u}, P.project x = P.project u →
      ∃ z, ReflTransGen P.compute x z ∧ ReflTransGen P.compute u z)
    (postpone : ∀ {l u v z}, P.effect l u v → P.compute u z →
      ∃ v', P.effect l z v' ∧ P.project v' = P.project v) : P.Lifts := by
  intro x u v l same event
  obtain ⟨z, fromX, fromU⟩ := join same
  suffices ∃ y, P.effect l z y ∧ P.project y = P.project v by
    obtain ⟨y, e, result⟩ := this
    exact ⟨y, ⟨z, fromX, e⟩, result⟩
  clear fromX
  induction fromU with
  | refl => exact ⟨v, event, rfl⟩
  | tail _ step ih =>
    obtain ⟨y, e, sameY⟩ := ih
    obtain ⟨y', e', next⟩ := postpone e step
    exact ⟨y', e', next.trans sameY⟩

inductive Trace {A : Type u} (edge : L → A → A → Prop) : A → List L → A → Prop where
  | nil (x) : Trace edge x [] x
  | cons {x y z l ls} : edge l x y → Trace edge y ls z → Trace edge x (l :: ls) z

theorem trace_iff (lift : P.Lifts) (x : S.Term) (labels : List L) (final : P.Class) :
    Trace P.visible (P.project x) labels final ↔
      ∃ y, Trace P.weak x labels y ∧ P.project y = final := by
  constructor
  · intro tr
    generalize start : P.project x = q at tr
    induction tr generalizing x with
    | nil => exact ⟨x, .nil x, start⟩
    | cons first _ ih =>
      obtain ⟨u, v, hu, hv, event⟩ := first
      obtain ⟨y, native, hy⟩ := lift (start.trans hu.symm) event
      obtain ⟨z, rest, hz⟩ := ih y (hy.trans hv)
      exact ⟨z, .cons native rest, hz⟩
  · rintro ⟨y, tr, rfl⟩
    induction tr with
    | nil => exact .nil _
    | cons first _ rest =>
      obtain ⟨u, cu, e⟩ := first
      exact .cons ⟨u, _, (P.reductions_equal cu).symm, rfl, e⟩ rest

/-- Conversely, a single observable event tests the lifting condition. Thus
the local test is exact for this observation of finite traces. -/
theorem trace_exact_iff_lifts :
    (∀ x labels final, Trace P.visible (P.project x) labels final ↔
      ∃ y, Trace P.weak x labels y ∧ P.project y = final) ↔ P.Lifts := by
  constructor
  · intro exactTrace x u v l same event
    have one : Trace P.visible (P.project x) [l] (P.project v) :=
      .cons ⟨u,v,same.symm,rfl,event⟩ (.nil _)
    obtain ⟨y, run, out⟩ := (exactTrace x [l] _).mp one
    cases run with
    | cons first rest => cases rest; exact ⟨_, first, out⟩
  · exact trace_iff P

end Split

end Mettapedia.GSLT.ComputationQuotient
