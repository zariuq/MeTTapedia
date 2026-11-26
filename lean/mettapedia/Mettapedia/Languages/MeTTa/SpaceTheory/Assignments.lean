import Mettapedia.Languages.MeTTa.SpaceTheory.Atoms
import Mettapedia.Languages.MeTTa.SpaceTheory.Observation
import Mathlib.Logic.Relation

/-!
# Type assignments at a snapshot

An explicit type assignment is evidence, not a choice of a single type.
Subsumption uses the least reflexive transitive closure of the subtype
assignments and the base theory. This is the assignment-generated part
of typing; a dialect's intrinsic types, application judgments, and
undefined-type behavior remain distinct.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.Assignments

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Atoms (Content)

def TypeAssignment (atoms : Multiset Atom) (term type : Atom) : Prop :=
  (Content.assignment term type).syntax ∈ atoms

def SubtypeAssignment (atoms : Multiset Atom) (small large : Atom) : Prop :=
  (Content.subtype small large).syntax ∈ atoms

def Subtype (base : Atom → Atom → Prop) (atoms : Multiset Atom) : Atom → Atom → Prop :=
  Relation.ReflTransGen (fun s t => base s t ∨ SubtypeAssignment atoms s t)

def HasType (baseType baseSubtype : Atom → Atom → Prop) (atoms : Multiset Atom)
    (term type : Atom) : Prop :=
  ∃ first, (baseType term first ∨ TypeAssignment atoms term first) ∧
    Subtype baseSubtype atoms first type

theorem type_assignment {baseType baseSubtype : Atom → Atom → Prop}
    {atoms : Multiset Atom} {term type : Atom} (written : TypeAssignment atoms term type) :
    HasType baseType baseSubtype atoms term type :=
  ⟨type, .inr written, .refl⟩

theorem subsumes {baseType baseSubtype : Atom → Atom → Prop}
    {atoms : Multiset Atom} {term small large : Atom}
    (typed : HasType baseType baseSubtype atoms term small)
    (sub : Subtype baseSubtype atoms small large) :
    HasType baseType baseSubtype atoms term large := by
  obtain ⟨_, origin, reaches⟩ := typed
  exact ⟨_, origin, reaches.trans sub⟩

/-- The type theory freely extends these positive declarations and the
base type/subtype judgments. It generates no extra subtype axioms. -/
theorem subtype_least {base target : Atom → Atom → Prop} {atoms : Multiset Atom}
    (refl : ∀ s, target s s) (trans : ∀ s t u, target s t → target t u → target s u)
    (baseMaps : ∀ s t, base s t → target s t)
    (assignMaps : ∀ s t, SubtypeAssignment atoms s t → target s t)
    {s t : Atom} (path : Subtype base atoms s t) : target s t := by
  induction path with
  | refl => exact refl _
  | tail _ edge ih => exact trans _ _ _ ih (edge.elim (baseMaps _ _) (assignMaps _ _))

theorem type_least {baseType baseSubtype target : Atom → Atom → Prop}
    {atoms : Multiset Atom}
    (baseMaps : ∀ s t, baseType s t → target s t)
    (assignMaps : ∀ s t, TypeAssignment atoms s t → target s t)
    (underSubtype : ∀ s t u, target s t → Subtype baseSubtype atoms t u → target s u)
    {term type : Atom} (typed : HasType baseType baseSubtype atoms term type) :
    target term type := by
  obtain ⟨_, source, reaches⟩ := typed
  exact underSubtype _ _ _ (source.elim (baseMaps _ _) (assignMaps _ _)) reaches

theorem type_mono {baseType baseSubtype : Atom → Atom → Prop}
    {first second : Multiset Atom} (included : ∀ ⦃a⦄, a ∈ first → a ∈ second)
    {term type : Atom} (typed : HasType baseType baseSubtype first term type) :
    HasType baseType baseSubtype second term type := by
  apply type_least (target := HasType baseType baseSubtype second) _ _ _ typed
  · exact fun _ t h => ⟨t, .inl h, .refl⟩
  · exact fun _ _ h => type_assignment (included h)
  · intro _ _ _ known path
    exact subsumes known (subtype_least (target := Subtype baseSubtype second) (fun _ => .refl)
      (fun _ _ _ x y => x.trans y) (fun _ _ e => .single (.inl e))
      (fun _ _ e => .single (.inr (included e))) path)

/-- Losing a duplicate occurrence cannot take away any proof of assignment-
generated typing. An observer of the bag may still see the lost copy. -/
theorem duplicate_removal_type_iff (baseType baseSubtype : Atom → Atom → Prop)
    {before after : Multiset Atom} {removed : Atom}
    (erased : Observation.RemovesOne before removed after) (another : removed ∈ after)
    (term type : Atom) :
    HasType baseType baseSubtype before term type ↔ HasType baseType baseSubtype after term type := by
  change before = removed ::ₘ after at erased
  subst before
  constructor
  · apply type_mono
    intro a present
    exact (Multiset.mem_cons.mp present).elim (fun same => same ▸ another) id
  · exact type_mono (fun _ present => Multiset.mem_cons_of_mem present)

section Examples

private def noBase (_ _ : Atom) : Prop := False
private def matcha : Atom := .symbol "Matcha"
private def tea : Atom := .symbol "Tea"
private def drink : Atom := .symbol "Drink"
private def assigned : Atom := (Content.assignment matcha tea).syntax
private def sub : Atom := (Content.subtype tea drink).syntax

theorem assigned_tea_is_a_drink : HasType noBase noBase ([assigned, sub] : List Atom) matcha drink := by
  exact subsumes (type_assignment (show assigned ∈ ([assigned, sub] : Multiset Atom) by simp))
    (.single (.inr (show sub ∈ ([assigned, sub] : Multiset Atom) by simp)))

theorem a_subtype_does_not_type_a_value : ¬ HasType noBase noBase ([sub] : List Atom) matcha drink := by
  rintro ⟨first, impossible | assignedHere, _⟩
  · exact impossible
  · have same : (Content.assignment matcha first).syntax = sub := by
      simpa [TypeAssignment] using assignedHere
    simp [Content.syntax, sub] at same

end Examples

end Mettapedia.Languages.MeTTa.SpaceTheory.Assignments
