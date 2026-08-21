import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fin.Basic

/-!
# Values do not determine occurrences

Parallel canonicalization sorts and may collapse, so a proof relating two
parallel frontiers must say *which occurrence corresponds to which*.  The
tempting shortcut is to pair frontier entries by value: if the two sides
carry equal elements, zip them up.  This module shows the shortcut is
unsound in exactly the situation parallel composition creates — repeated
elements — and therefore that a correspondence must be carried as data,
not recovered from values.

The statement is elementary and that is the point: it needs no machinery,
so it can be cited wherever a value-based pairing is about to be
introduced.
-/

namespace Mettapedia.Algebra

namespace OccurrenceIdentity

/-- A two-element frontier whose entries carry the same value — the
minimal duplicate. -/
def duplicateFrontier : Fin 2 → Nat := fun _ => 7

/-- Exchange of the two positions. -/
def exchange : Fin 2 → Fin 2 := fun index => if index = 0 then 1 else 0

theorem exchange_ne_id : exchange ≠ id := by
  intro equal
  have atZero : exchange 0 = id 0 := congrFun equal 0
  simp [exchange] at atZero

/-- **Values do not determine the correspondence.**  On a frontier with a
repeated element, the identity and the exchange are *different* maps that
agree on every value.  A proof that recovers a correspondence from values
alone therefore cannot say which occurrence went where. -/
theorem occurrence_correspondence_not_determined_by_values :
    ∃ first second : Fin 2 → Fin 2,
      first ≠ second ∧
      ∀ index, duplicateFrontier (first index) =
        duplicateFrontier (second index) := by
  refine ⟨id, exchange, ?_, ?_⟩
  · intro equal
    exact exchange_ne_id equal.symm
  · intro index
    simp [duplicateFrontier]

/-- **The consequence for parallel alignment.**  Value-agreement of two
frontiers is strictly weaker than a correspondence: agreement holds for
both candidate maps above, so it cannot single one out.  Any parallel
restoration argument must therefore carry its permutation as evidence and
identify duplicates by position, never by content. -/
theorem value_agreement_does_not_yield_correspondence
    (recover : (Fin 2 → Nat) → (Fin 2 → Fin 2)) :
    ¬ ((recover duplicateFrontier = id) ∧
      (recover duplicateFrontier = exchange)) := by
  rintro ⟨isIdentity, isExchange⟩
  exact exchange_ne_id (isExchange.symm.trans isIdentity)

/-- Positive counterpart: when the frontier entries are pairwise distinct,
a value-preserving map *is* forced to be the identity, so the shortcut is
sound exactly in the duplicate-free case.  This delimits where the
shortcut may be used rather than banning it outright. -/
theorem injective_frontier_forces_identity {Value : Type}
    (frontier : Fin 2 → Value) (distinct : Function.Injective frontier)
    (relabel : Fin 2 → Fin 2)
    (preserves : ∀ index, frontier (relabel index) = frontier index) :
    relabel = id := by
  funext index
  exact distinct (preserves index)

end OccurrenceIdentity

end Mettapedia.Algebra
