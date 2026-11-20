import Mettapedia.GSLT.Contracts.ReadWindowCuts
import Mettapedia.GSLT.Contracts.MarkedReadCuts

/-!
# Local read windows on executed occurrence histories

An epoch counts writes in a declared region along the actual commit word.
An outside commit does not advance that epoch. Regions may overlap and a
query may depend on several. If the region family covers its possible
matches, equal endpoint epochs give the exact ordered occurrence read.

The computed epochs witness the abstract stamp discipline. They are not a
prescribed implementation of counters, snapshots, or synchronization.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.Dependencies.OccurrenceReadWindows

open MarkedReadCuts (History Mark markedReads orderedRows validatingCuts)
open Mettapedia.GSLT.Contracts.ReadWindowCuts
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
  (Commit Writes fire fireList_cons fireList_nil fireList_append regionOf regionOf_fire_of_no_write)

universe u v w

variable {Atom : Type u} {Region : Type v}

/-- A query's footprint includes every label it could observe, not just
the rows present at the sample. This includes phantoms. -/
def Covers (watch : Region → Atom → Bool) (footprint : (Atom → Bool) → Set Region) : Prop :=
  ∀ query atom, query atom = true → ∃ region ∈ footprint query, watch region atom = true

def touchesWrite (label : Nat → Atom) (watch : Atom → Bool) (commit : Commit Nat Atom) : Bool :=
  decide (Writes label commit watch)

def epoch (history : History Atom) (watch : Atom → Bool) (cut : history.Cut) : Nat :=
  (history.word.take cut.val).countP (touchesWrite history.label watch)

def epochs (history : History Atom) (watch : Region → Atom → Bool) :
    history.Cut → Region → Nat :=
  fun cut region => epoch history (watch region) cut

private theorem take_step (h : History Atom) (step : Fin h.word.length) :
    h.word.take (step.val + 1) = h.word.take step.val ++ [h.word.get step] :=
  List.take_succ_eq_append_getElem step.isLt

theorem epoch_succ (h : History Atom) (watch : Atom → Bool) (step : Fin h.word.length) :
    epoch h watch step.succ = epoch h watch step.castSucc +
      (if touchesWrite h.label watch (h.word.get step) then 1 else 0) := by
  unfold epoch
  simp only [Fin.val_succ, Fin.val_castSucc]
  rw [take_step h step, List.countP_append, List.countP_singleton]

/-- The count stays fixed exactly when the event writes outside the
watched region, even if it changes the rest of the global store. -/
theorem epoch_step_unchanged_iff (h : History Atom) (watch : Atom → Bool)
    (step : Fin h.word.length) :
    epoch h watch step.castSucc = epoch h watch step.succ ↔
      ∀ identity ∈ (h.word.get step).writes, watch (h.label identity) = false := by
  constructor
  · intro same identity written
    cases observed : watch (h.label identity) with
    | false => rfl
    | true =>
        have touched : touchesWrite h.label watch (h.word.get step) = true :=
          decide_eq_true ⟨identity, written, observed⟩
        rw [epoch_succ h watch step, touched] at same
        simp at same
  · intro outside
    have untouched : touchesWrite h.label watch (h.word.get step) = false := by
      apply decide_eq_false
      rintro ⟨identity, written, observed⟩
      simp [outside identity written] at observed
    simpa only [untouched, Bool.false_eq_true, if_false, Nat.add_zero] using
      (epoch_succ h watch step).symm

theorem presentAt_succ (h : History Atom) (step : Fin h.word.length) :
    h.presentAt step.succ = fire (h.presentAt step.castSucc) (h.word.get step) := by
  unfold History.presentAt
  simp only [Fin.val_succ, Fin.val_castSucc]
  rw [take_step h step]
  simpa only [fireList_cons, fireList_nil] using
    fireList_append h.initial (h.word.take step.val) [h.word.get step]

def observe (h : History Atom) (cut : h.Cut) (q : Atom → Bool) : Store Atom :=
  matchingRows q (h.view cut)

private theorem sort_filter_nat (present : Finset Nat) (keep : Nat → Bool) :
    (present.sort (· ≤ ·)).filter keep =
      (present.filter (fun item => keep item)).sort (· ≤ ·) := by
  let kept := (present.sort (· ≤ ·)).filter keep
  have inventory : kept.toFinset = present.filter (fun item => keep item) := by
    simp [kept, List.toFinset_filter]
  have distinct : kept.Nodup := (present.sort_nodup (· ≤ ·)).sublist List.filter_sublist
  have ordered : kept.Pairwise (· ≤ ·) :=
    (present.pairwise_sort (· ≤ ·)).sublist List.filter_sublist
  have recovered := (List.toFinset_sort (· ≤ ·) distinct).mpr ordered
  rw [inventory] at recovered
  exact recovered.symm

theorem observe_eq_ordered_region (h : History Atom) (cut : h.Cut) (q : Atom → Bool) :
    observe h cut q = orderedRows h.label (regionOf h.label (h.presentAt cut) q) := by
  unfold observe matchingRows History.view orderedRows regionOf
  rw [List.filter_map]
  exact congrArg (List.map (fun occurrence => (occurrence, h.label occurrence)))
    (sort_filter_nat (h.presentAt cut) (fun occurrence => q (h.label occurrence)))

theorem occurrence_discipline (h : History Atom) (watch : Region → Atom → Bool)
    (footprint : (Atom → Bool) → Set Region) (covers : Covers watch footprint) :
    Discipline (observe h) footprint (epochs h watch) where
  advance := by
    intro step region
    simp [epochs, epoch_succ]
  frame := by
    intro step q same
    have outside : ∀ identity ∈ (h.word.get step).writes, q (h.label identity) = false := by
      intro identity written
      cases sees : q (h.label identity) with
      | false => rfl
      | true =>
          obtain ⟨region, within, hit⟩ := covers q (h.label identity) sees
          have unchanged := (epoch_step_unchanged_iff h (watch region) step).mp (same within)
          have impossible := unchanged identity written
          simp [hit] at impossible
    rw [observe_eq_ordered_region, observe_eq_ordered_region, presentAt_succ]
    exact congrArg (orderedRows h.label) (regionOf_fire_of_no_write outside).symm

/-- Coverage is also necessary for a uniform licence over occurrence
histories. A single legal insertion of an unwatched matching label changes
the observation without changing any of its declared stamps. -/
theorem covers_iff_occurrence_discipline (watch : Region → Atom → Bool)
    (footprint : (Atom → Bool) → Set Region) :
    Covers watch footprint ↔
      ∀ h : History Atom, Discipline (observe h) footprint (epochs h watch) := by
  constructor
  · exact fun covers h => occurrence_discipline h watch footprint covers
  · intro disciplined q atom selected
    by_contra uncovered
    let insertion : Commit Nat Atom := Commit.makeOne 0
    let history : History Atom :=
      { label := fun _ => atom
        initial := ∅
        word := [insertion]
        executed := .cons (by constructor <;> simp [insertion]) (.nil _) }
    let step : Fin history.word.length := ⟨0, by simp [history]⟩
    have same : Set.EqOn (epochs history watch step.castSucc) (epochs history watch step.succ)
        (footprint q) := by
      intro region member
      apply (epoch_step_unchanged_iff history (watch region) step).mpr
      intro identity _
      change watch region atom = false
      cases vote : watch region atom with
      | false => rfl
      | true => exact False.elim (uncovered ⟨region, member, vote⟩)
    have preserved := (disciplined history).frame step q same
    have before : history.presentAt step.castSucc = ∅ := rfl
    have after : history.presentAt step.succ = {0} := by
      rw [presentAt_succ, before]
      change fire ∅ insertion = {0}
      simp [fire, insertion]
    rw [observe_eq_ordered_region, observe_eq_ordered_region, before, after] at preserved
    simp [orderedRows, regionOf, history, selected] at preserved

/-- The existing marked-read observer now receives an actual validating
cut from local version evidence. The alignment is the read transcript,
not an equality of final answers. -/
theorem marked_replay_at_jointStart (h : History Atom) (watch : Region → Atom → Bool)
    (footprint : (Atom → Bool) → Set Region) (covers : Covers watch footprint)
    (marks : List (Mark.{u,0,w} Atom h.Cut))
    (reads : List ((Atom → Bool) × Window h.Cut))
    (alignment : recordedReads (observe h) reads = markedReads h.view marks)
    (checks : ∀ entry ∈ reads, Set.EqOn
      (epochs h watch entry.2.start) (epochs h watch entry.2.finish) (footprint entry.1))
    (cross : Window.CrossOrdered (reads.map Prod.snd)) :
    let cut := Window.jointStart (reads.map Prod.snd)
    cut ∈ validatingCuts h.view (readDependencies (markedReads h.view marks)) ∧
      ∀ mark ∈ marks, mark.observe h.view cut = mark.observe h.view mark.origin := by
  let cut := Window.jointStart (reads.map Prod.snd)
  have agreement := agrees_at_jointStart (occurrence_discipline h watch footprint covers)
    reads checks cross
  rw [alignment] at agreement
  have valid : cut ∈ validatingCuts h.view (readDependencies (markedReads h.view marks)) :=
    valid_readDependencies_of_agrees (h.view cut) _ agreement
  exact ⟨valid, (h.cut_replays_iff marks cut).mp valid⟩

#print axioms epoch_succ
#print axioms epoch_step_unchanged_iff
#print axioms observe_eq_ordered_region
#print axioms occurrence_discipline
#print axioms covers_iff_occurrence_discipline
#print axioms marked_replay_at_jointStart

end Mettapedia.GSLT.Contracts.Dependencies.OccurrenceReadWindows
