import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Step
import Mettapedia.SetTheory.ValuesAndLocations

/-!
# Terms are values, spaces are locations

The calculus has two kinds of things, and `SetTheory.ValuesAndLocations` says what each is.

* **Terms are values.** A step reads a configuration only as a bag of terms (`Step` is a relation
  on `Multiset T`), and it compares terms by the declared theory, never by where they sit. Two bags
  with the same elements are the same configuration (`Readings.bag_swap`); a bag value such as
  `bag(a, b)` equals `bag(b, a)` when the theory says `bag` commutes
  (`Reflection.Example.one_value_two_syntaxes`).
* **Spaces are locations.** Every term lives in a space (`space : T → N`). What a space holds at a
  moment is its **snapshot**, a bag value (`snapshot`). Two spaces with equal snapshots are still two
  spaces: a step that writes one leaves the other as it was (`Example.two_spaces`), so no relation on
  spaces can be "same contents" (`Readings.Store.no_identity_by_contents`).
* **The snapshot is the bridge.** A step is the value update at each space: the snapshot after,
  plus what was taken there, is the snapshot before, plus what was made there (`Step.snapshots`). A
  step that writes nothing at a space leaves its snapshot (`Step.frame`). Read as a store of
  locations, a step that writes one space is exactly a `write` of that location
  (`Step.as_write`), which moves its revision; other spaces keep their contents and revisions
  (`Readings.Store.snap_write_of_ne`, `rev_write_of_ne`). This is the store side of revision
  validation (`Readings.Run.snap_eq_of_rev_eq`).
* **Updating in place** is a matter for the runtime: a step that takes the term holding a value may
  reuse its cell exactly when nothing else references it (`StepReuse.take_reuse_sound`), never when
  it keeps the term (`StepReuse.keep_reuse_unsound`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.SetTheory.ValuesAndLocations

universe uV uT uP uN

variable {V : Type uV} {T : Type uT} {P : Type uP} {N : Type uN} [DecidableEq N]

/-- **The snapshot of a space**: the bag of terms it holds in a configuration. -/
def snapshot (space : T → N) (n : N) (M : Multiset T) : Multiset T :=
  M.filter fun t => space t = n

theorem snapshot_add (space : T → N) (n : N) (M M' : Multiset T) :
    snapshot space n (M + M') = snapshot space n M + snapshot space n M' :=
  Multiset.filter_add _ _ _

/-- **A step is a value update at each space**: after the step, the snapshot of every space plus
what was taken there is the snapshot before plus what was made there. -/
theorem Step.snapshots {L : TermLayer V T P} {r : Rule V T P} {M M' : Multiset T}
    (step : Step L r M M') (space : T → N) :
    ∃ (σ : Subst V T) (taken : Multiset T) (made : List T),
      Matches L σ r.take taken ∧ instTemplate L σ r.produce = some made ∧ taken ≤ M ∧
        ∀ n, snapshot space n M' + snapshot space n taken =
          snapshot space n M + snapshot space n (made : Multiset T) := by
  obtain ⟨σ, S, taken, kept, made, -, takes, -, hM, -, inst, hM'⟩ := step
  refine ⟨σ, taken, made, takes, inst, ?_, fun n => ?_⟩
  · rw [hM, add_right_comm]; exact Multiset.le_add_left _ _
  · rw [hM, hM']
    simp only [snapshot_add]
    abel

/-- **The frame law of a space**: a step that takes nothing and makes nothing at a space leaves its
snapshot as it was. -/
theorem Step.frame {L : TermLayer V T P} {r : Rule V T P} {M M' : Multiset T}
    (step : Step L r M M') (space : T → N) (n : N)
    (untouched : ∀ (σ : Subst V T) (taken : Multiset T) (made : List T),
      Matches L σ r.take taken → instTemplate L σ r.produce = some made →
        snapshot space n taken = 0 ∧ snapshot space n (made : Multiset T) = 0) :
    snapshot space n M' = snapshot space n M := by
  obtain ⟨σ, taken, made, takes, inst, -, update⟩ := step.snapshots space
  obtain ⟨t0, m0⟩ := untouched σ taken made takes inst
  have := update n
  rw [t0, m0, add_zero, add_zero] at this
  exact this

/-- The location reading of a configuration: each space holds its snapshot, with revisions kept
alongside. -/
def asStore (space : T → N) (M : Multiset T) (rev : N → ℕ) : Store N (Multiset T) :=
  ⟨fun n => some (snapshot space n M), rev⟩

/-- **A step that writes one space is a `write` of that location.** When everything the step takes
and makes lives in the space `n₀`, the store after the step is the store before, written at `n₀`
with "remove what was taken, add what was made", and its revision moved. -/
theorem Step.as_write [DecidableEq T] {L : TermLayer V T P} {r : Rule V T P} {M M' : Multiset T}
    (step : Step L r M M') (space : T → N) (n₀ : N) (rev : N → ℕ)
    (inside : ∀ (σ : Subst V T) (taken : Multiset T) (made : List T),
      Matches L σ r.take taken → instTemplate L σ r.produce = some made →
        (∀ t ∈ taken, space t = n₀) ∧ ∀ t ∈ made, space t = n₀) :
    ∃ (taken made : Multiset T),
      asStore space M' (Function.update rev n₀ (rev n₀ + 1)) =
        (asStore space M rev).write n₀ (fun v => v - snapshot space n₀ taken + snapshot space n₀ made) := by
  obtain ⟨σ, taken, made, takes, inst, le, update⟩ := step.snapshots space
  obtain ⟨inTaken, inMade⟩ := inside σ taken made takes inst
  refine ⟨taken, made, ?_⟩
  unfold asStore Store.write
  congr 1
  funext n
  by_cases e : n = n₀
  · subst e
    simp only [Function.update_self, Option.map_some]
    have le' : snapshot space n taken ≤ snapshot space n M := Multiset.filter_le_filter _ le
    have h := update n
    rw [← tsub_add_cancel_of_le le', add_right_comm] at h
    rw [add_right_cancel h]
  · simp only [Function.update_of_ne e]
    have t0 : snapshot space n taken = 0 :=
      Multiset.filter_eq_nil.mpr fun t m h => e (h ▸ inTaken t m)
    have m0 : snapshot space n (made : Multiset T) = 0 :=
      Multiset.filter_eq_nil.mpr fun t m h => e (h ▸ inMade t (by simpa using m))
    have := update n
    rw [t0, m0, add_zero, add_zero] at this
    rw [this]

/-! ## Example: two spaces with equal contents -/

namespace Example

/-- A term is a space and an atom. -/
abbrev Term := ℕ × Char

def space : Term → ℕ := Prod.fst

/-- Spaces `1` and `2` both hold `a`. -/
def before : Multiset Term := {(1, 'a'), (2, 'a')}

/-- After adding `b` to space `1`. -/
def after : Multiset Term := {(1, 'b'), (1, 'a'), (2, 'a')}

/-- **Two spaces, equal contents, two locations**: both hold `a` before; writing space `1`
changes space `1` and leaves space `2`. -/
theorem two_spaces :
    (snapshot space 1 before).map Prod.snd = (snapshot space 2 before).map Prod.snd ∧
      (snapshot space 1 after).map Prod.snd ≠ (snapshot space 2 after).map Prod.snd ∧
      snapshot space 2 after = snapshot space 2 before := by
  decide

end Example

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting
