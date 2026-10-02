import Mathlib.Control.Bifunctor
import Mathlib.Logic.Function.Basic

/-!
# Logical forms

Every structured account of what a sentence expresses keeps the shape of the
sentence and changes what sits at its leaves.  A sentence has words at its
leaves; a Russellian proposition has the objects and properties the words stand
for (Russell, *The Principles of Mathematics*, 1903, ch. IV); a Fregean
proposition has their senses (Frege, "Über Sinn und Bedeutung", 1892).  Chalmers
states the construction in this form: a structured intension consists of the
intensions "of all the simple expressions in a sentence ... structured
according to the sentence's logical form" ("Propositions and Attitude
Ascriptions: A Fregean Account", *Noûs* 45, 2011, §2).

This module fixes one such shape and makes the leaf type a parameter.

* `Form ν π` is a logical form with name leaves in `ν` and predicate leaves in
  `π`: predication, identity, negation and conjunction.
* `Form.map` replaces the leaves and keeps the shape.  It preserves identities
  and composition (`Form.map_id`, `Form.map_map`), so `Form` is a lawful
  bifunctor, and it is injective when both leaf maps are (`Form.map_injective`).
* `Form.Holds` reads a form as true or false, given when a predicate leaf
  applies to a name leaf and when two name leaves name the same thing.
  Replacing leaves and then reading is reading with the leaf maps composed in
  (`Form.holds_map`).
* A form over pairs of leaves is the same thing as a pair of forms of one
  shape: the two projections together are injective (`Form.unzip_injective`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Propositions

universe u v u' v' u'' v''

/-- A logical form with name leaves in `ν` and predicate leaves in `π`. -/
inductive Form (ν : Type u) (π : Type v) : Type (max u v)
  /-- Predication: the predicate applies to what the name stands for. -/
  | pred (predicate : π) (subject : ν) : Form ν π
  /-- Identity: the two names stand for the same thing. -/
  | ident (left right : ν) : Form ν π
  /-- Negation. -/
  | neg (body : Form ν π) : Form ν π
  /-- Conjunction. -/
  | conj (left right : Form ν π) : Form ν π
  deriving DecidableEq

namespace Form

variable {ν : Type u} {π : Type v} {ν' : Type u'} {π' : Type v'} {ν'' : Type u''} {π'' : Type v''}

/-- Replace the leaves of a form and keep its shape. -/
def map (onNames : ν → ν') (onPredicates : π → π') : Form ν π → Form ν' π'
  | pred predicate subject => pred (onPredicates predicate) (onNames subject)
  | ident left right => ident (onNames left) (onNames right)
  | neg body => neg (map onNames onPredicates body)
  | conj left right => conj (map onNames onPredicates left) (map onNames onPredicates right)

@[simp]
theorem map_id (form : Form ν π) : map id id form = form := by
  induction form with
  | pred => rfl
  | ident => rfl
  | neg body ih => simp only [map, ih]
  | conj left right ihLeft ihRight => simp only [map, ihLeft, ihRight]

@[simp]
theorem map_map (onNames : ν → ν') (onNames' : ν' → ν'') (onPredicates : π → π')
    (onPredicates' : π' → π'') (form : Form ν π) :
    map onNames' onPredicates' (map onNames onPredicates form) =
      map (onNames' ∘ onNames) (onPredicates' ∘ onPredicates) form := by
  induction form with
  | pred => rfl
  | ident => rfl
  | neg body ih => simp only [map, ih]
  | conj left right ihLeft ihRight => simp only [map, ihLeft, ihRight]

/-- Replacing leaves injectively loses nothing. -/
theorem map_injective {onNames : ν → ν'} {onPredicates : π → π'}
    (namesInjective : Function.Injective onNames)
    (predicatesInjective : Function.Injective onPredicates) :
    Function.Injective (map onNames onPredicates) := by
  intro first
  induction first with
  | pred predicate subject =>
    intro second same
    cases second <;> simp only [map, pred.injEq, reduceCtorEq] at same
    obtain ⟨samePredicate, sameSubject⟩ := same
    rw [predicatesInjective samePredicate, namesInjective sameSubject]
  | ident left right =>
    intro second same
    cases second <;> simp only [map, ident.injEq, reduceCtorEq] at same
    obtain ⟨sameLeft, sameRight⟩ := same
    rw [namesInjective sameLeft, namesInjective sameRight]
  | neg body ih =>
    intro second same
    cases second <;> simp only [map, neg.injEq, reduceCtorEq] at same
    rw [ih same]
  | conj left right ihLeft ihRight =>
    intro second same
    cases second <;> simp only [map, conj.injEq, reduceCtorEq] at same
    obtain ⟨sameLeft, sameRight⟩ := same
    rw [ihLeft sameLeft, ihRight sameRight]

instance : Bifunctor Form.{u, v} where
  bimap := map

instance : LawfulBifunctor Form.{u, v} where
  id_bimap := map_id
  bimap_bimap onNames onNames' onPredicates onPredicates' form :=
    map_map onNames onNames' onPredicates onPredicates' form

/-- Read a form as true or false.  `applies` says when a predicate leaf applies
to a name leaf, and `same` says when two name leaves name the same thing. -/
def Holds (applies : π → ν → Prop) (same : ν → ν → Prop) : Form ν π → Prop
  | pred predicate subject => applies predicate subject
  | ident left right => same left right
  | neg body => ¬ Holds applies same body
  | conj left right => Holds applies same left ∧ Holds applies same right

/-- Replacing leaves and then reading is reading with the replacement composed
into the reading of the leaves. -/
theorem holds_map (onNames : ν → ν') (onPredicates : π → π') (applies : π' → ν' → Prop)
    (same : ν' → ν' → Prop) (form : Form ν π) :
    Holds applies same (map onNames onPredicates form) ↔
      Holds (fun predicate subject => applies (onPredicates predicate) (onNames subject))
        (fun left right => same (onNames left) (onNames right)) form := by
  induction form with
  | pred => exact Iff.rfl
  | ident => exact Iff.rfl
  | neg body ih => exact not_congr ih
  | conj left right ihLeft ihRight => exact and_congr ihLeft ihRight

/-- Two readings that agree on the leaves agree on every form. -/
theorem holds_congr {applies applies' : π → ν → Prop} {same same' : ν → ν → Prop}
    (appliesAgree : ∀ predicate subject, applies predicate subject ↔ applies' predicate subject)
    (sameAgree : ∀ left right, same left right ↔ same' left right) (form : Form ν π) :
    Holds applies same form ↔ Holds applies' same' form := by
  induction form with
  | pred predicate subject => exact appliesAgree predicate subject
  | ident left right => exact sameAgree left right
  | neg body ih => exact not_congr ih
  | conj left right ihLeft ihRight => exact and_congr ihLeft ihRight

/-- The two component forms of a form over pairs of leaves. -/
def unzip (form : Form (ν × ν') (π × π')) : Form ν π × Form ν' π' :=
  (map Prod.fst Prod.fst form, map Prod.snd Prod.snd form)

/-- A form over pairs of leaves is determined by its two component forms. -/
theorem unzip_injective : Function.Injective (unzip (ν := ν) (π := π) (ν' := ν') (π' := π')) := by
  intro first
  induction first with
  | pred predicate subject =>
    intro second same
    cases second <;>
      simp only [unzip, map, Prod.mk.injEq, pred.injEq, reduceCtorEq, and_false]
        at same
    obtain ⟨⟨firstPredicate, firstSubject⟩, secondPredicate, secondSubject⟩ := same
    rw [Prod.ext firstPredicate secondPredicate, Prod.ext firstSubject secondSubject]
  | ident left right =>
    intro second same
    cases second <;>
      simp only [unzip, map, Prod.mk.injEq, ident.injEq, reduceCtorEq, and_false]
        at same
    obtain ⟨⟨firstLeft, firstRight⟩, secondLeft, secondRight⟩ := same
    rw [Prod.ext firstLeft secondLeft, Prod.ext firstRight secondRight]
  | neg body ih =>
    intro second same
    cases second <;>
      simp only [unzip, map, Prod.mk.injEq, neg.injEq, reduceCtorEq, and_false]
        at same
    rw [ih (Prod.ext same.1 same.2)]
  | conj left right ihLeft ihRight =>
    intro second same
    cases second <;>
      simp only [unzip, map, Prod.mk.injEq, conj.injEq, reduceCtorEq, and_false]
        at same
    obtain ⟨⟨firstLeft, firstRight⟩, secondLeft, secondRight⟩ := same
    rw [ihLeft (Prod.ext firstLeft secondLeft), ihRight (Prod.ext firstRight secondRight)]

end Form

end Mettapedia.Logic.Propositions
