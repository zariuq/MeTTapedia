import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub

/-!
# Parallel composition as the union of a store

Terms built from atoms, an empty term and a binary composition, taken modulo
associativity, unit and symmetry, are exactly the finite multisets of atoms
(`Term.congruent_iff_heat`, `Term.quotientEquiv`). The composition's equations
are the multiset laws of a store: a process presentation and a store present
one commutative monoid in two ways, by generators and equations and as the
free commutative monoid. Heating (a term to its multiset of atoms) and cooling
(a list of atoms back to a term) are the two directions of the chemical
abstract machine's correspondence between a parallel term and a solution.

Operationally, a reaction relation on multisets fires in any context of the
store (`StoreStep`). Reduction of terms modulo the congruence is that same
relation read through heating (`reduces_bisimulation`). Context rules alone,
which only lift a step of one component and never use the congruence
(`LocalStep`), are sound for the store (`localStep_heat`) but miss a reaction
whose reactants sit in different components (`local_misses_joint`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StoreComposition

universe u

/-- Terms of a composition: one atom, the empty term, or two terms side by side. -/
inductive Term (A : Type u) where
  | atom (a : A)
  | unit
  | join (left right : Term A)

namespace Term

variable {A : Type u}

/-- Associativity, unit and symmetry of `join`, closed under `join`, as an equivalence. -/
inductive Congruent : Term A → Term A → Prop
  | refl (t : Term A) : Congruent t t
  | symm {t u : Term A} : Congruent t u → Congruent u t
  | trans {t u v : Term A} : Congruent t u → Congruent u v → Congruent t v
  | assoc (t u v : Term A) : Congruent (join (join t u) v) (join t (join u v))
  | unit_join (t : Term A) : Congruent (join unit t) t
  | comm (t u : Term A) : Congruent (join t u) (join u t)
  | join_congr {t t' u u' : Term A} : Congruent t t' → Congruent u u' →
      Congruent (join t u) (join t' u')

/-- Heating: the multiset of atoms of a term. -/
def heat : Term A → Multiset A
  | atom a => {a}
  | unit => 0
  | join left right => heat left + heat right

@[simp] theorem heat_atom (a : A) : heat (atom a) = {a} := rfl
@[simp] theorem heat_unit : heat (unit : Term A) = 0 := rfl
@[simp] theorem heat_join (left right : Term A) : heat (join left right) = heat left + heat right := rfl

/-- The atoms of a term, in order. -/
def leaves : Term A → List A
  | atom a => [a]
  | unit => []
  | join left right => leaves left ++ leaves right

/-- Cooling: a list of atoms as a right-nested term. -/
def cool : List A → Term A
  | [] => unit
  | a :: rest => join (atom a) (cool rest)

theorem heat_eq_leaves : ∀ t : Term A, heat t = (leaves t : Multiset A)
  | atom _ => rfl
  | unit => rfl
  | join left right => by
      change heat left + heat right = ((leaves left ++ leaves right : List A) : Multiset A)
      rw [heat_eq_leaves left, heat_eq_leaves right, Multiset.coe_add]

theorem heat_cool : ∀ l : List A, heat (cool l) = (l : Multiset A)
  | [] => rfl
  | a :: rest => by
      change ({a} : Multiset A) + heat (cool rest) = ((a :: rest : List A) : Multiset A)
      rw [heat_cool rest, Multiset.singleton_add, Multiset.cons_coe]

/-- Heating respects the congruence. -/
theorem heat_congruent {t u : Term A} (same : Congruent t u) : heat t = heat u := by
  induction same with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ first second => exact first.trans second
  | assoc t u v => exact Multiset.add_assoc (heat t) (heat u) (heat v)
  | unit_join t => exact Multiset.zero_add (heat t)
  | comm t u => exact Multiset.add_comm (heat t) (heat u)
  | join_congr _ _ first second =>
      simp only [heat_join]
      rw [first, second]

theorem cool_append : ∀ l m : List A, Congruent (cool (l ++ m)) (join (cool l) (cool m))
  | [], m => (Congruent.unit_join (cool m)).symm
  | a :: rest, m =>
      (Congruent.join_congr (Congruent.refl (atom a)) (cool_append rest m)).trans
        (Congruent.assoc (atom a) (cool rest) (cool m)).symm

/-- Every term is congruent to the cooling of its atoms. -/
theorem congruent_cool_leaves : ∀ t : Term A, Congruent t (cool (leaves t))
  | atom a => ((Congruent.comm (atom a) unit).trans (Congruent.unit_join (atom a))).symm
  | unit => Congruent.refl unit
  | join left right =>
      (Congruent.join_congr (congruent_cool_leaves left) (congruent_cool_leaves right)).trans
        (cool_append (leaves left) (leaves right)).symm

/-- Permuting atoms is a congruence. -/
theorem cool_perm {l m : List A} (perm : l.Perm m) : Congruent (cool l) (cool m) := by
  induction perm with
  | nil => exact Congruent.refl unit
  | cons a _ ih => exact Congruent.join_congr (Congruent.refl (atom a)) ih
  | swap x y l =>
      exact ((Congruent.assoc (atom y) (atom x) (cool l)).symm.trans
        (Congruent.join_congr (Congruent.comm (atom y) (atom x)) (Congruent.refl (cool l)))).trans
        (Congruent.assoc (atom x) (atom y) (cool l))
  | trans _ _ first second => exact first.trans second

/-- **Terms modulo the congruence are exactly multisets of atoms.** -/
theorem congruent_iff_heat {t u : Term A} : Congruent t u ↔ heat t = heat u := by
  constructor
  · exact heat_congruent
  · intro same
    rw [heat_eq_leaves, heat_eq_leaves, Multiset.coe_eq_coe] at same
    exact (congruent_cool_leaves t).trans ((cool_perm same).trans (congruent_cool_leaves u).symm)

theorem heat_cool_toList (m : Multiset A) : heat (cool m.toList) = m := by
  rw [heat_cool, Multiset.coe_toList]

theorem heat_surjective : Function.Surjective (heat : Term A → Multiset A) :=
  fun m => ⟨cool m.toList, heat_cool_toList m⟩

/-- The congruence as a setoid. -/
def congruence (A : Type u) : Setoid (Term A) where
  r := Congruent
  iseqv := ⟨Congruent.refl, Congruent.symm, Congruent.trans⟩

/-- The quotient of terms by the congruence is the type of finite multisets of atoms;
`join` becomes `+` and `unit` becomes `0` (`heat_join`, `heat_unit`). -/
noncomputable def quotientEquiv : Quotient (congruence A) ≃ Multiset A where
  toFun := Quotient.lift heat (fun _ _ same => heat_congruent same)
  invFun m := Quotient.mk _ (cool m.toList)
  left_inv := Quotient.ind fun t =>
    Quotient.sound (congruent_iff_heat.mpr (heat_cool_toList (heat t)))
  right_inv m := heat_cool_toList m

end Term

open Term

variable {A : Type u}

/-- A reaction consumes one multiset of atoms and produces another. -/
abbrev Reaction (A : Type u) := Multiset A → Multiset A → Prop

/-- **The store step**: a reaction fires in any context of the store. -/
def StoreStep (react : Reaction A) (before after : Multiset A) : Prop :=
  ∃ consumed produced frame : Multiset A, react consumed produced ∧
    before = consumed + frame ∧ after = produced + frame

/-- **Context rules only**: a reaction fires on a whole component, and a step of one
component lifts through `join`. The congruence is never applied. -/
inductive LocalStep (react : Reaction A) : Term A → Term A → Prop
  | fire {t t' : Term A} : react (heat t) (heat t') → LocalStep react t t'
  | left {t t' : Term A} (u : Term A) : LocalStep react t t' →
      LocalStep react (join t u) (join t' u)
  | right {t t' : Term A} (u : Term A) : LocalStep react t t' →
      LocalStep react (join u t) (join u t')

/-- **Reduction modulo the congruence**, as process calculi define it. -/
def Reduces (react : Reaction A) (t t' : Term A) : Prop :=
  ∃ s s' : Term A, Congruent t s ∧ LocalStep react s s' ∧ Congruent s' t'

/-- Context rules are sound for the store. -/
theorem localStep_heat {react : Reaction A} {t t' : Term A} (step : LocalStep react t t') :
    StoreStep react (heat t) (heat t') := by
  induction step with
  | fire reacts =>
      exact ⟨_, _, 0, reacts, (Multiset.add_zero _).symm, (Multiset.add_zero _).symm⟩
  | left u _ ih =>
      obtain ⟨consumed, produced, frame, reacts, before, after⟩ := ih
      refine ⟨consumed, produced, frame + heat u, reacts, ?_, ?_⟩
      · rw [heat_join, before, Multiset.add_assoc]
      · rw [heat_join, after, Multiset.add_assoc]
  | right u _ ih =>
      obtain ⟨consumed, produced, frame, reacts, before, after⟩ := ih
      refine ⟨consumed, produced, heat u + frame, reacts, ?_, ?_⟩
      · rw [heat_join, before, ← Multiset.add_assoc, Multiset.add_comm (heat u) consumed,
          Multiset.add_assoc]
      · rw [heat_join, after, ← Multiset.add_assoc, Multiset.add_comm (heat u) produced,
          Multiset.add_assoc]

theorem reduces_heat {react : Reaction A} {t t' : Term A} (step : Reduces react t t') :
    StoreStep react (heat t) (heat t') := by
  obtain ⟨s, s', first, inner, last⟩ := step
  rw [heat_congruent first, ← heat_congruent last]
  exact localStep_heat inner

/-- Every store step from the heating of a term is a reduction of that term. -/
theorem storeStep_reduces {react : Reaction A} {t : Term A} {after : Multiset A}
    (step : StoreStep react (heat t) after) : ∃ t' : Term A, Reduces react t t' ∧ heat t' = after := by
  obtain ⟨consumed, produced, frame, reacts, before, rfl⟩ := step
  refine ⟨join (cool produced.toList) (cool frame.toList),
    ⟨join (cool consumed.toList) (cool frame.toList), join (cool produced.toList) (cool frame.toList),
      ?_, ?_, Congruent.refl _⟩, ?_⟩
  · apply congruent_iff_heat.mpr
    rw [before, heat_join, heat_cool_toList, heat_cool_toList]
  · apply LocalStep.left (cool frame.toList)
    apply LocalStep.fire
    rw [heat_cool_toList, heat_cool_toList]
    exact reacts
  · rw [heat_join, heat_cool_toList, heat_cool_toList]

/-- **Heating is a strong bisimulation** between reduction modulo the congruence and the
store step. -/
theorem reduces_bisimulation (react : Reaction A) :
    (∀ {t t' : Term A}, Reduces react t t' → StoreStep react (heat t) (heat t')) ∧
    (∀ {t : Term A} {after : Multiset A}, StoreStep react (heat t) after →
      ∃ t' : Term A, Reduces react t t' ∧ heat t' = after) :=
  ⟨reduces_heat, storeStep_reduces⟩

/-! ## Context rules alone miss joint reactions -/

namespace Controls

/-- One reaction: atoms `0` and `1` together become `3`. -/
def joint : Reaction (Fin 4) := fun consumed produced =>
  consumed = {0} + {1} ∧ produced = {3}

/-- The reactants `0` and `1` sit in different components, with `2` beside `0`. -/
abbrev separated : Term (Fin 4) := join (join (atom 0) (atom 2)) (atom 1)

theorem store_reacts : StoreStep joint (heat separated) ({3} + {2}) := by
  refine ⟨{0} + {1}, {3}, {2}, ⟨rfl, rfl⟩, ?_, rfl⟩
  change ({0} + {2} + {1} : Multiset (Fin 4)) = {0} + {1} + {2}
  rw [Multiset.add_assoc, Multiset.add_comm ({2} : Multiset (Fin 4)) {1}, ← Multiset.add_assoc]

theorem reduction_reacts : ∃ t' : Term (Fin 4), Reduces joint separated t' ∧ heat t' = {3} + {2} :=
  storeStep_reduces store_reacts

theorem no_local_step (t' : Term (Fin 4)) : ¬ LocalStep joint separated t' := by
  intro step
  cases step with
  | fire reacts =>
      have sizes := congrArg Multiset.card reacts.1
      simp at sizes
  | left _ inner =>
      cases inner with
      | fire reacts =>
          have present : (2 : Fin 4) ∈ heat (join (atom (0 : Fin 4)) (atom 2)) := by simp
          rw [reacts.1] at present
          simp at present
      | left _ deeper =>
          cases deeper with
          | fire reacts =>
              have sizes := congrArg Multiset.card reacts.1
              simp at sizes
      | right _ deeper =>
          cases deeper with
          | fire reacts =>
              have sizes := congrArg Multiset.card reacts.1
              simp at sizes
  | right _ inner =>
      cases inner with
      | fire reacts =>
          have sizes := congrArg Multiset.card reacts.1
          simp at sizes

/-- **Control.** The store, and reduction modulo the congruence, perform the joint
reaction; context rules alone cannot. -/
theorem local_misses_joint :
    StoreStep joint (heat separated) ({3} + {2}) ∧
      (∃ t' : Term (Fin 4), Reduces joint separated t' ∧ heat t' = {3} + {2}) ∧
      ∀ t' : Term (Fin 4), ¬ LocalStep joint separated t' :=
  ⟨store_reacts, reduction_reacts, no_local_step⟩

end Controls

#print axioms Term.congruent_iff_heat
#print axioms Term.quotientEquiv
#print axioms reduces_bisimulation
#print axioms Controls.local_misses_joint

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StoreComposition
