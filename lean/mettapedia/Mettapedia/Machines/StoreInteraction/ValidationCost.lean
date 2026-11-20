import Mettapedia.Machines.ReadOnlyQuery
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

/-!
# What individual liveness probes can establish

An adaptive checker observes independent Boolean coordinates. If its answer
decides whether every coordinate is live, its all-live execution must inspect
every coordinate. This is a probe-model lower bound, not a lower bound for a
store with a maintained aggregate certificate or an epoch service.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.StoreInteraction.ValidationCost

open ReadOnlyQuery

variable {Key : Type} [DecidableEq Key]

/-- The Boolean query decides all-coordinate liveness on every input. -/
def DecidesAll (query : Program Key Bool Bool) : Prop :=
  ∀ store, (run store query).answer = true ↔ ∀ key, store key = true

/-- An unobserved coordinate could be the unique dead one. Adaptivity does
not avoid the obligation on the all-live path. -/
theorem every_coordinate_is_read (query : Program Key Bool Bool)
    (correct : DecidesAll query) (key : Key) :
    ∃ read ∈ (run (fun _ => true) query).reads, read.1 = key := by
  by_contra omitted
  have different : ∀ read ∈ (run (fun _ => true) query).reads, read.1 ≠ key := by
    intro read member same
    exact omitted ⟨read, member, same⟩
  let changed : Key → Bool := Function.update (fun _ => true) key false
  have agrees : Agrees changed (run (fun _ => true) query).reads := by
    intro read member
    have old := run_agrees (fun _ : Key => true) query read member
    rw [show changed read.1 = true by
      exact Function.update_of_ne (different read member) _ _]
    exact old
  have replay := run_eq_of_agrees (fun _ : Key => true) changed query agrees
  have allLive : (run (fun _ : Key => true) query).answer = true :=
    (correct _).mpr (fun _ => rfl)
  have falseLive := (correct changed).mp (by rw [replay]; exact allLive) key
  simp [changed] at falseLive

/-- At least one primitive read per independent coordinate is necessary. -/
theorem number_of_reads_ge_card [Fintype Key] (query : Program Key Bool Bool)
    (correct : DecidesAll query) :
    Fintype.card Key ≤ (run (fun _ => true) query).reads.length := by
  let keys := (run (fun _ : Key => true) query).reads.map Prod.fst
  have covers : keys.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro key
    obtain ⟨read, member, same⟩ := every_coordinate_is_read query correct key
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨read, member, same⟩)
  have bound := List.toFinset_card_le keys
  rw [covers, Finset.card_univ] at bound
  simpa [keys] using bound

namespace Controls

def both : Program Bool Bool Bool :=
  .read false fun first => .read true fun second => .pure (first && second)

theorem both_decides : DecidesAll both := by
  intro store
  simp only [both, run, Bool.and_eq_true]
  constructor
  · rintro ⟨first, second⟩ key
    cases key <;> assumption
  · intro all
    exact ⟨all false, all true⟩

theorem two_probes_suffice :
    (run (fun _ => true) both).reads.length = 2 := rfl

/-- A single row flag cannot decide a two-row firing's readiness. -/
def onlyFirst : Program Bool Bool Bool := .read false Program.pure

theorem one_flag_is_insufficient : ¬ DecidesAll onlyFirst := by
  intro correct
  have bound := number_of_reads_ge_card onlyFirst correct
  norm_num [onlyFirst, run] at bound

end Controls

end Mettapedia.Machines.StoreInteraction.ValidationCost
