import Mettapedia.Machines.ScheduledRun.Periodicity
import Mathlib.Data.List.Nodup

/-!
# Exact rotating lasso licences for distinct successors

Divisibility is sufficient without distinctness. If each successor list has
no duplicates, equal consecutive states force equal chosen indices, making
the arity divisibility necessary for an actual state period as well. Thus a
segment-local certificate is exact for live periodicity at a fixed positive
period; a global prefix LCM may still be unnecessarily restrictive.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ScheduledRun

universe u
variable {S : Type u}

theorem periodic_arity_dvd (next : S → List S) (initial : S) (start period offset : Nat)
    (infinite : Nonterminating next rotating initial)
    (periodic : PeriodicFrom next rotating initial start period) (state : S)
    (present : run next rotating initial (start + offset) = some state) (distinct : (next state).Nodup) :
    (next state).length ∣ period := by
  have positive := nonterminal_on_infinite next rotating initial infinite present
  have later : run next rotating initial (start + offset + period) = some state :=
    (periodic offset).trans present
  have earlierNext := successor_of_present next rotating initial present positive
  have laterNext := successor_of_present next rotating initial later positive
  have equalNext : run next rotating initial (start + offset + period + 1) =
      run next rotating initial (start + offset + 1) := by
    simpa only [Nat.add_assoc, Nat.add_comm period 1] using periodic (offset + 1)
  have values := Option.some.inj (earlierNext.symm.trans (equalNext.symm.trans laterNext))
  have indices := distinct.injective_get values
  have phase : Nat.ModEq (next state).length (start + offset) (start + offset + period) :=
    congrArg Fin.val indices
  simpa only [Nat.add_sub_cancel_left] using phase.dvd'

theorem rotating_lasso_exact (next : S → List S) (initial : S) (start period : Nat)
    (positive : 0 < period) (state : S) (present : run next rotating initial start = some state)
    (distinct : ∀ value, (next value).Nodup) :
    (Nonterminating next rotating initial ∧ PeriodicFrom next rotating initial start period) ↔
      run next rotating initial (start + period) = some state ∧
      ∀ offset < period, ∀ value, run next rotating initial (start + offset) = some value →
        (next value).length ∣ period := by
  constructor
  · rintro ⟨infinite, periodic⟩
    refine ⟨?_, fun offset _ value here => periodic_arity_dvd next initial start period offset
      infinite periodic value here (distinct value)⟩
    simpa only [Nat.add_zero] using (periodic 0).trans (by simpa only [Nat.add_zero] using present)
  · rintro ⟨returned, counts⟩
    exact return_periodic_of_shift_compatible next rotating initial start period positive state present returned
      (fun offset inside value here => rotating_shift_compatible _ _ _ (counts offset inside value here))

end Mettapedia.Machines.ScheduledRun
