import Mettapedia.SetTheory.Profiles.Principles

/-!
# Diaconescu's theorem, in set form

Extensionality, separation, an empty set and a power set, together with a
choice operator, yield excluded middle. The argument separates two subsets of
the power set of the power set of the empty set. When the proposition holds,
those subsets have the same members, so extensionality makes them equal, and
equality substitutes into the chosen element.

A choice function that only selects from inhabited subsets of one unordered
pair yields the same conclusion. The pair is built from the empty set.

The control at the end keeps two codes with the same members and a selector
that reads the code. Agreement of members does not force the selected elements
to agree. That shows where this argument uses substitutive equality. It does
not show that excluded middle is underivable from the other principles.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles

universe u

variable {S : Type u} {mem : Mem S}

/-- Excluded middle from a picker on inhabited subsets of one carrier.
The carrier supplies two distinct members `a` and `b`. The proof uses the
picker only on the two separated subsets. -/
theorem lem_of_subsetChoice (ext : Extensional mem) (sep : HasSeparation mem)
    {carrier a b : S} (ha : mem a carrier) (hb : mem b carrier) (hne : a ≠ b)
    (pick : S → S)
    (chosen : ∀ u, (∀ z, mem z u → mem z carrier) → (∃ x, mem x u) → mem (pick u) u) :
    ∀ p : Prop, p ∨ ¬ p := by
  intro p
  obtain ⟨U, hU⟩ := sep carrier (fun z => z = a ∨ p)
  obtain ⟨V, hV⟩ := sep carrier (fun z => z = b ∨ p)
  have aU : mem a U := (hU a).2 ⟨ha, Or.inl rfl⟩
  have bV : mem b V := (hV b).2 ⟨hb, Or.inl rfl⟩
  have uMem : mem (pick U) U :=
    chosen U (fun z hz => ((hU z).1 hz).1) ⟨a, aU⟩
  have vMem : mem (pick V) V :=
    chosen V (fun z hz => ((hV z).1 hz).1) ⟨b, bV⟩
  have uOr : pick U = a ∨ p := ((hU (pick U)).1 uMem).2
  have vOr : pick V = b ∨ p := ((hV (pick V)).1 vMem).2
  have agree : p → pick U = pick V := by
    intro hp
    have hUV : U = V :=
      ext U V fun z =>
        ⟨fun hz => (hV z).2 ⟨((hU z).1 hz).1, Or.inr hp⟩,
          fun hz => (hU z).2 ⟨((hV z).1 hz).1, Or.inr hp⟩⟩
    exact congrArg pick hUV
  cases uOr with
  | inr hp =>
    exact Or.inl hp
  | inl hu =>
    cases vOr with
    | inr hp =>
      exact Or.inl hp
    | inl hv =>
      exact Or.inr fun hp => hne (hu.symm.trans ((agree hp).trans hv))

/-- Extensionality, separation, an empty set, a power set and a choice operator
give excluded middle. The power set used is the power set of the power set of
the empty set. -/
theorem lem_of_choice (ext : Extensional mem) (sep : HasSeparation mem)
    (emp : HasEmpty mem) (pow : HasPower mem) (eps : (S → Prop) → S)
    (choice : ChoiceLaw eps) : ∀ p : Prop, p ∨ ¬ p := by
  obtain ⟨e, he⟩ := emp
  obtain ⟨p1, hp1⟩ := pow e
  obtain ⟨p2, hp2⟩ := pow p1
  have hep1 : mem e p1 := empty_mem_power_empty he hp1
  have hp1p2 : mem p1 p2 := mem_power_self hp2
  have hep2 : mem e p2 := mem_power_of_empty he hp2
  have hne : e ≠ p1 := empty_ne_power_empty he hep1
  exact lem_of_subsetChoice ext sep hep2 hp1p2 hne
    (fun u => eps (fun z => mem z u))
    (fun u _ ⟨x, hx⟩ => choice (fun z => mem z u) x hx)

/-- A function that returns a member of every inhabited set whose members all
lie in a given unordered pair. -/
def PairSubsetChoice (pick : S → S) : Prop :=
  ∀ a b u, (∀ z, mem z u → z = a ∨ z = b) → (∃ x, mem x u) → mem (pick u) u

/-- The same argument, with choice used only on subsets of the unordered pair
of the empty set and its singleton. -/
theorem lem_of_pairSubsetChoice (ext : Extensional mem) (sep : HasSeparation mem)
    (emp : HasEmpty mem) (pair : HasPairing mem) (pick : S → S)
    (chosen : PairSubsetChoice (mem := mem) pick) : ∀ p : Prop, p ∨ ¬ p := by
  obtain ⟨e, he⟩ := emp
  obtain ⟨s, hs⟩ := pair e e
  obtain ⟨two, htwo⟩ := pair e s
  have hes : mem e s := (hs e).2 (Or.inl rfl)
  have hne : e ≠ s := empty_ne_power_empty he hes
  have heTwo : mem e two := (htwo e).2 (Or.inl rfl)
  have hsTwo : mem s two := (htwo s).2 (Or.inr rfl)
  exact lem_of_subsetChoice ext sep heTwo hsTwo hne pick fun u sub hinhab =>
    chosen e s u (fun z hz => (htwo z).1 (sub z hz)) hinhab

/-- Substitutive equality sends a chosen element to the chosen element. -/
theorem choice_substitutes (pick : S → S) {U V : S} (h : U = V) : pick U = pick V :=
  congrArg pick h

/-- Two codes. Membership ignores the code, so the two codes have the same
members. The selector returns the code itself. -/
inductive ChoiceCode
  | left
  | right

/-- Neither code has a member. -/
def controlMem : ChoiceCode → ChoiceCode → Prop := fun _ _ => False

/-- The selector reads the code. -/
def controlChoose : ChoiceCode → ChoiceCode
  | .left => .left
  | .right => .right

/-- The two codes have the same members. -/
theorem control_same_members :
    ∀ z, controlMem z ChoiceCode.left ↔ controlMem z ChoiceCode.right := by
  intro z
  refine ⟨?_, ?_⟩
  · intro h
    nomatch h
  · intro h
    nomatch h

/-- The selector returns different elements on the two codes. -/
theorem control_chosen_differ :
    controlChoose ChoiceCode.left ≠ controlChoose ChoiceCode.right := by
  intro h
  nomatch h

/-- Agreement of members does not force the selected elements to agree.
The step `U = V → pick U = pick V` of `lem_of_subsetChoice` is agreement of
the sets under substitutive equality. Here the sets only agree in their
members, and the selector reads a code that membership forgets. -/
theorem extensional_agreement_does_not_substitute :
    (∀ z, controlMem z ChoiceCode.left ↔ controlMem z ChoiceCode.right) ∧
      controlChoose ChoiceCode.left ≠ controlChoose ChoiceCode.right :=
  ⟨control_same_members, control_chosen_differ⟩

end Mettapedia.SetTheory.Profiles
