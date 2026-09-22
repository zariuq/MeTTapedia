/-
# The worked encoding clauses are linear

`Encoding.lean` exhibits traces: supplied with a message at the subject, each
encoded input clause reaches the term the source clause would have produced.
A trace is an existence statement, and on its own it does not say the encoding
is right — an encoded term that also admitted an unintended reduction would
still have the intended one.

This file supplies the other half for the two full derivations: their soups are
*linear*.  Every name occupies at most one listening position and at most one
speaking position, so there is no name at which the reduction has a choice
between two partners.  Linearity is the hypothesis the paper's correctness
argument rests on, and `Inertness.lean` supplies the tool — inversion by
components — that a reduction-level uniqueness result would use.

The side conditions are stated first with the names abstract, then discharged by
allocating them at distinct slots.  The slot form is the one a compiler meets: it
needs a counter, not an occurrence check.

Still open, and not claimed here: that a linear soup has at most one reduction
up to congruence, and hence that each encoding's trace is unique.  Linearity
rules out a name with two partners; carrying that to a uniqueness statement about
`Step` is a further argument.
-/
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Inertness
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Encoding

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb

/-! ## The output-subject clause -/

/-- The encoding of an input whose body sends on the received name is linear
when its four listening names are distinct.  The store name is the only speaking
position, so that half holds unconditionally. -/
theorem encodeOutputSubjectInput_linear {subject p₀ p₁ store run proxy : Comb}
    (h : ([subject, p₀, run, p₁] : List Comb).Nodup) :
    Linear (encodeOutputSubjectInput subject p₀ p₁ store run proxy) where
  listening := by
    have hm : listeningSubjects (encodeOutputSubjectInput subject p₀ p₁ store run proxy)
        = (↑[subject, p₀, run, p₁] : Multiset Comb) := rfl
    rw [hm]; exact Multiset.coe_nodup.mpr h
  speaking := by
    have hm : speakingSubjects (encodeOutputSubjectInput subject p₀ p₁ store run proxy)
        = (↑[store] : Multiset Comb) := rfl
    rw [hm]; simp

/-! ## The quoted-occurrence clause -/

/-- The encoding of an input whose body places the received name inside a
quotation is linear when its seven listening names are distinct.  This is the
clause that runs a constructor, so the names it must keep apart include the two
child names the constructor reads and the name it assembles at. -/
theorem encodeQuotedOccurrenceInput_linear
    {subject p₀ p₁ r₁ r₂ built store run proxy : Comb}
    (h : ([subject, p₁, r₁, r₂, built, p₀, run] : List Comb).Nodup) :
    Linear (encodeQuotedOccurrenceInput subject p₀ p₁ r₁ r₂ built store run proxy) where
  listening := by
    have hm : listeningSubjects
        (encodeQuotedOccurrenceInput subject p₀ p₁ r₁ r₂ built store run proxy)
        = (↑[subject, p₁, r₁, r₂, built, p₀, run] : Multiset Comb) := rfl
    rw [hm]; exact Multiset.coe_nodup.mpr h
  speaking := by
    have hm : speakingSubjects
        (encodeQuotedOccurrenceInput subject p₀ p₁ r₁ r₂ built store run proxy)
        = (↑[store] : Multiset Comb) := rfl
    rw [hm]; simp

/-! ## Discharging the conditions by allocation -/

/-- A list of slots at distinct indices is a list of distinct names. -/
theorem nodup_slot_map (s : Comb) {indices : List ℕ} (h : indices.Nodup) :
    (indices.map (slot s)).Nodup :=
  h.map (slot_injective s)

/-- With its names allocated at distinct slots, the output-subject clause is
linear outright: no side condition survives. -/
theorem encodeOutputSubjectInput_linear_of_slots (s : Comb) :
    Linear (encodeOutputSubjectInput (slot s 0) (slot s 1) (slot s 3)
      (slot s 4) (slot s 2) (slot s 5)) :=
  encodeOutputSubjectInput_linear
    (nodup_slot_map s (by decide : ([0, 1, 2, 3] : List ℕ).Nodup))

/-- With its names allocated at distinct slots, the quoted-occurrence clause is
linear outright. -/
theorem encodeQuotedOccurrenceInput_linear_of_slots (s : Comb) :
    Linear (encodeQuotedOccurrenceInput (slot s 0) (slot s 5) (slot s 1)
      (slot s 2) (slot s 3) (slot s 4) (slot s 7) (slot s 6) (slot s 8)) :=
  encodeQuotedOccurrenceInput_linear
    (nodup_slot_map s (by decide : ([0, 1, 2, 3, 4, 5, 6] : List ℕ).Nodup))

/-! ## The two halves together -/

/-- **The quoted-occurrence clause, both halves.**  Allocated at slots it
reaches the term the source clause produces, and its soup is linear, so no name
in it has two possible partners.  Written as one statement because neither half
is the correctness claim on its own. -/
theorem encodeQuotedOccurrenceInput_reaches_and_linear (s v : Comb) :
    ReachesFull
        (par (encodeQuotedOccurrenceInput (slot s 0) (slot s 5) (slot s 1)
          (slot s 2) (slot s 3) (slot s 4) (slot s 7) (slot s 6) (slot s 8))
          (mm (slot s 0) v))
        (mm (par v v) nil)
      ∧ Linear (encodeQuotedOccurrenceInput (slot s 0) (slot s 5) (slot s 1)
          (slot s 2) (slot s 3) (slot s 4) (slot s 7) (slot s 6) (slot s 8)) :=
  ⟨encodeQuotedOccurrenceInput_reaches _ _ _ _ _ _ _ _ _ v,
    encodeQuotedOccurrenceInput_linear_of_slots s⟩

/-- **The gate inside an allocated clause sits still.**  Its two side conditions
reduce to inequalities between slot indices. -/
theorem gate_inert_of_slots (s continuation : Comb) {trigger store run : ℕ}
    (htrigger : trigger ≠ store) (hrun : run ≠ store) :
    ∀ t, ¬ Step Cong (gate (slot s trigger) (slot s store) (slot s run) continuation) t :=
  gate_inert (slot_not_cong htrigger) (slot_not_cong hrun)

end Mettapedia.Languages.ProcessCalculi.RhoCombinators
