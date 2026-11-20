import Mettapedia.GSLT.Contracts.OccurrenceReadWindows

/-!
# Joint cuts from addressed reads

The exact uniform address coverage of a query is the image of its
predicate, not the addresses of the rows returned by that predicate.
This file specializes occurrence read windows to such a partition.
The replay theorem includes adaptive joins: a row can supply the
address of the next read. Bracketing that later read is a separate
obligation, so discovery cannot silently weaken validation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.Dependencies.AddressedReadCuts

open MarkedReadCuts (History)
open OccurrenceReadWindows (Covers observe epochs epoch)
open Mettapedia.GSLT.Contracts.ReadWindowCuts
open Mettapedia.Machines
open Mettapedia.Machines.ReadOnlyQuery (Program Observation run)

variable {Atom Address : Type*} (address : Atom → Address)

/-- Image of the labels that can answer a query, whether or not they are
currently present. -/
def scope (query : Atom → Bool) : Set Address :=
  {location | ∃ atom, query atom = true ∧ address atom = location}

variable [DecidableEq Address]

def watch (location : Address) (atom : Atom) : Bool :=
  decide (address atom = location)

theorem covers_iff_scope_subset (tracked : (Atom → Bool) → Set Address) :
    Covers (watch address) tracked ↔ ∀ query, scope address query ⊆ tracked query := by
  constructor
  · rintro covers query location ⟨atom, hit, assigned⟩
    obtain ⟨another, member, read⟩ := covers query atom hit
    have same : address atom = another := of_decide_eq_true read
    exact (same.symm.trans assigned) ▸ member
  · intro includes query atom hit
    exact ⟨address atom, includes query ⟨atom, hit, rfl⟩, by simp [watch]⟩

/-- Sharp uniform licence, quantified over the actual occurrence histories.
A missing address can be detected by a one-event insertion witness. -/
theorem discipline_iff_scope_subset (tracked : (Atom → Bool) → Set Address) :
    (∀ h : History Atom, Discipline (observe h) tracked (epochs h (watch address))) ↔
      ∀ query, scope address query ⊆ tracked query :=
  (OccurrenceReadWindows.covers_iff_occurrence_discipline (watch address) tracked).symm.trans
    (covers_iff_scope_subset address tracked)

theorem point_read_scope (location : Address) :
    scope address (watch address location) ⊆ {location} := by
  rintro another ⟨atom, hit, identified⟩
  exact identified.symm.trans (of_decide_eq_true hit)

def atAddress (h : History Atom) (cut : h.Cut) (location : Address) : Store Atom :=
  observe h cut (watch address location)

theorem point_discipline (h : History Atom) :
    Discipline (atAddress address h) (fun location => {location}) (epochs h (watch address)) where
  advance := (OccurrenceReadWindows.occurrence_discipline h (watch address) (scope address)
    ((covers_iff_scope_subset address _).mpr fun _ => Set.Subset.rfl)).advance
  frame := by
    intro step location unchanged
    apply (OccurrenceReadWindows.occurrence_discipline h (watch address) (scope address)
      ((covers_iff_scope_subset address _).mpr fun _ => Set.Subset.rfl)).frame
    intro candidate inside
    exact unchanged (point_read_scope address location inside)

/-- If the read brackets overlap and each address is unchanged across
its own bracket, the whole query (including addresses discovered by
earlier reads) has the same ordered transcript at one actual cut.
Unmentioned addresses require no checks. -/
theorem replay_addressed_join (h : History Atom) {Answer : Type*}
    {program : Program Address (Store Atom) Answer}
    {reads : List (Address × Window h.Cut)} {answer : Answer}
    (captured : Captured (atAddress address h) program reads answer)
    (unchanged : ∀ entry ∈ reads,
      epoch h (watch address entry.1) entry.2.start =
        epoch h (watch address entry.1) entry.2.finish)
    (overlap : Window.CrossOrdered (reads.map Prod.snd)) :
    run (atAddress address h (Window.jointStart (reads.map Prod.snd))) program =
      (⟨answer, recordedReads (atAddress address h) reads⟩ : Observation _ _ _) := by
  apply captured.replay_at_jointStart (point_discipline address h) _ overlap
  intro entry member candidate singleton
  have atEntry : candidate = entry.1 := singleton
  subst candidate
  exact unchanged entry member

/-- A write to a different address leaves the local epoch unchanged. -/
theorem epoch_unchanged_iff_outside (h : History Atom) (location : Address)
    (event : Fin h.word.length) :
    epoch h (watch address location) event.castSucc = epoch h (watch address location) event.succ ↔
      ∀ o ∈ (h.word.get event).writes, address (h.label o) ≠ location := by
  rw [OccurrenceReadWindows.epoch_step_unchanged_iff]
  simp [watch]

namespace Controls

theorem full_partition_covers (tracked : Set Bool) :
    Covers (watch (id : Bool → Bool)) (fun _ => tracked) ↔ tracked = Set.univ := by
  rw [covers_iff_scope_subset]
  refine ⟨fun covers => Set.eq_univ_of_forall fun b => ?_, fun full _ => full ▸ Set.subset_univ _⟩
  exact covers (fun _ => true) ⟨b, rfl, rfl⟩

theorem watching_other_address_does_not_cover_even_empty_read :
    ¬ ∀ h : History Bool,
      Discipline (observe h) (fun _ => ({false} : Set Bool)) (epochs h (watch id)) := by
  intro uniform
  have whole : ({false} : Set Bool) = Set.univ :=
    full_partition_covers _ |>.mp ((OccurrenceReadWindows.covers_iff_occurrence_discipline ..).mpr uniform)
  have impossible : true ∈ ({false} : Set Bool) := whole ▸ Set.mem_univ true
  cases impossible

end Controls

#print axioms discipline_iff_scope_subset
#print axioms replay_addressed_join
#print axioms epoch_unchanged_iff_outside
#print axioms Controls.full_partition_covers
#print axioms Controls.watching_other_address_does_not_cover_even_empty_read

end Mettapedia.GSLT.Contracts.Dependencies.AddressedReadCuts
