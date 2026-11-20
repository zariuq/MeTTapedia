import Mettapedia.Machines.ReadOnlyQuery
import Mathlib.Order.Fin.Basic

/-!
# Common cuts from locally stamped read windows

A retained read has a sample cut bracketed by two stamp observations.
Adjacent steps must account for changes to the read's declared support.
Equal stamps at the bracket ends then certify stability throughout it.
Overlapping brackets give one actual cut at which all recorded reads
replay, even when earlier reads selected the later query keys.

No timestamp mechanism, shared mutex, or live write authority is assumed.
The cut order belongs to the supplied history. A sample must already
denote a read at its reported cut; stamp equality is not a memory-safety
or pointer-lifetime argument.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.ReadWindowCuts

open Mettapedia.Machines.ReadOnlyQuery (Agrees Observation Program Reads run)

universe uCut uKey uRegion uValue uStamp uAnswer

structure Window (Cut : Type uCut) [LE Cut] where
  start : Cut
  sample : Cut
  finish : Cut
  start_le_sample : start ≤ sample
  sample_le_finish : sample ≤ finish

namespace Window

variable {Cut : Type uCut}

def Contains [LE Cut] (w : Window Cut) (cut : Cut) : Prop :=
  w.start ≤ cut ∧ cut ≤ w.finish

/-- Every lower endpoint is below every upper endpoint, not merely
each lower endpoint below its own upper endpoint. -/
def CrossOrdered [LE Cut] (windows : List (Window Cut)) : Prop :=
  ∀ first ∈ windows, ∀ second ∈ windows, first.start ≤ second.finish

variable [SemilatticeSup Cut] [OrderBot Cut]

/-- The earliest possible common cut when all the upper bounds permit it. -/
def jointStart : List (Window Cut) → Cut
  | [] => ⊥
  | w :: rest => w.start ⊔ jointStart rest

theorem jointStart_le_iff (windows : List (Window Cut)) (cut : Cut) :
    jointStart windows ≤ cut ↔ ∀ w ∈ windows, w.start ≤ cut := by
  induction windows with
  | nil => simp [jointStart]
  | cons w rest ih => simp [jointStart, sup_le_iff, ih]

theorem contains_jointStart {windows : List (Window Cut)} (cross : CrossOrdered windows) :
    ∀ w ∈ windows, w.Contains (jointStart windows) := by
  intro w member
  exact ⟨(jointStart_le_iff windows _).mp le_rfl w member,
    (jointStart_le_iff windows _).mpr (fun earlier inside => cross earlier inside w member)⟩

/-- This interval law applies when the chosen admissible cuts have finite
joins. It does not apply to arbitrary sets of cuts validating a predicate. -/
theorem exists_joint_iff (windows : List (Window Cut)) :
    (∃ cut, ∀ w ∈ windows, w.Contains cut) ↔ CrossOrdered windows := by
  constructor
  · rintro ⟨cut, liesIn⟩ first firstMem second secondMem
    exact (liesIn first firstMem).1.trans (liesIn second secondMem).2
  · intro cross
    exact ⟨jointStart windows, contains_jointStart cross⟩

end Window

/-! ## Inferring an interval from steps of a bounded history -/

/-- The cuts of a finite word, including its initial and final states. -/
abbrev Cut (steps : Nat) := Fin (steps + 1)

variable {Key : Type uKey} {Region : Type uRegion}
  {Value : Type uValue} {Stamp : Type uStamp}

/-- Stamps do not decrease, and a *single* step that preserves all stamps
in a read's declared footprint preserves the observation. A stamp may
advance conservatively even if the observation did not change. -/
structure Discipline [PartialOrder Stamp] {steps : Nat}
    (view : Cut steps → Key → Value) (footprint : Key → Set Region)
    (stamp : Cut steps → Region → Stamp) : Prop where
  advance : ∀ (i : Fin steps) region, stamp i.castSucc region ≤ stamp i.succ region
  frame : ∀ (i : Fin steps) key,
    Set.EqOn (stamp i.castSucc) (stamp i.succ) (footprint key) →
      view i.castSucc key = view i.succ key

namespace Discipline

variable [PartialOrder Stamp] {steps : Nat}
  {view : Cut steps → Key → Value} {footprint : Key → Set Region}
  {stamp : Cut steps → Region → Stamp}

theorem stamp_mono (license : Discipline view footprint stamp) (region : Region) :
    Monotone (fun cut => stamp cut region) :=
  Fin.monotone_iff_le_succ.mpr fun i => license.advance i region

/-- From the single-step frame law, unchanged support stamps give the
same observation across any intervening sequence of commits. -/
theorem same_of_stamps (license : Discipline view footprint stamp)
    (key : Key) {first last : Cut steps} (ordered : first ≤ last)
    (same : Set.EqOn (stamp first) (stamp last) (footprint key)) :
    view first key = view last key := by
  let relation : Cut steps → Cut steps → Prop := fun a b =>
    a ≤ b ∧ (Set.EqOn (stamp a) (stamp b) (footprint key) → view a key = view b key)
  let _ : IsTrans (Cut steps) relation := ⟨fun a b c ab bc => by
    refine ⟨ab.1.trans bc.1, fun unchanged => ?_⟩
    have left : Set.EqOn (stamp a) (stamp b) (footprint key) := by
      intro region member
      have mono := license.stamp_mono region
      exact le_antisymm (mono ab.1) ((mono bc.1).trans_eq (unchanged member).symm)
    have right : Set.EqOn (stamp b) (stamp c) (footprint key) :=
      fun _ member => (left member).symm.trans (unchanged member)
    exact (ab.2 left).trans (bc.2 right)⟩
  rcases ordered.eq_or_lt with sameCut | earlier
  · rw [sameCut]
  · have along := (Fin.liftFun_iff_succ relation (f := id)).mpr
      (fun i => ⟨i.castSucc_lt_succ.le, license.frame i key⟩)
    exact (along earlier).2 same

/-- Equal endpoint stamps make the sampled value valid throughout the
bracket. No comparison of values or stamps at intermediate cuts is used. -/
theorem stable_in_window (license : Discipline view footprint stamp)
    (key : Key) (w : Window (Cut steps)) {cut : Cut steps}
    (agrees : Set.EqOn (stamp w.start) (stamp w.finish) (footprint key))
    (inside : w.Contains cut) :
    view cut key = view w.sample key := by
  have atMiddle (mid : Cut steps) (bounds : w.Contains mid) :
      view w.start key = view mid key := by
    apply license.same_of_stamps key bounds.1
    intro region member
    have mono := license.stamp_mono region
    exact le_antisymm (mono bounds.1) ((mono bounds.2).trans_eq (agrees member).symm)
  exact (atMiddle cut inside).symm.trans
    (atMiddle w.sample ⟨w.start_le_sample, w.sample_le_finish⟩)

end Discipline

/-! ## Interpreting an actual adaptive transcript -/

variable {C : Type uCut} [LE C] {Answer : Type uAnswer}

def recordedReads (view : C → Key → Value) (reads : List (Key × Window C)) :
    Reads Key Value :=
  reads.map fun entry => (entry.1, view entry.2.sample entry.1)

/-- The existing query branches on sampled values, which may come from
different cuts. The list is in query order; a retained snapshot may be
consulted later. This witness does not claim the runtime can obtain
brackets for a previously untracked dependency. -/
inductive Captured (view : C → Key → Value) :
    Program Key Value Answer → List (Key × Window C) → Answer → Prop where
  | pure (answer : Answer) : Captured view (.pure answer) [] answer
  | read (key : Key) (next : Value → Program Key Value Answer) (w : Window C)
      {rest : List (Key × Window C)} {answer : Answer} :
      Captured view (next (view w.sample key)) rest answer →
      Captured view (.read key next) ((key, w) :: rest) answer

theorem Captured.replay_of_agrees {view : C → Key → Value} {program : Program Key Value Answer}
    {reads : List (Key × Window C)} {answer : Answer}
    (captured : Captured view program reads answer) (store : Key → Value)
    (agrees : Agrees store (recordedReads view reads)) :
    run store program = (⟨answer, recordedReads view reads⟩ : Observation Key Value Answer) := by
  induction captured with
  | pure answer => rfl
  | @read key next w rest answer capture ih =>
      have here : store key = view w.sample key := agrees (key, view w.sample key)
        (by simp [recordedReads])
      have tail : Agrees store (recordedReads view rest) := by
        intro entry member
        exact agrees entry (List.mem_cons_of_mem _ member)
      simp [run, recordedReads, here, ih tail]

section Joint

variable [PartialOrder Stamp] {steps : Nat}
  {view : Cut steps → Key → Value} {footprint : Key → Set Region}
  {stamp : Cut steps → Region → Stamp}

theorem agrees_at_jointStart (license : Discipline view footprint stamp)
    (reads : List (Key × Window (Cut steps)))
    (checks : ∀ entry ∈ reads,
      Set.EqOn (stamp entry.2.start) (stamp entry.2.finish) (footprint entry.1))
    (cross : Window.CrossOrdered (reads.map Prod.snd)) :
    Agrees (view (Window.jointStart (reads.map Prod.snd))) (recordedReads view reads) := by
  intro observation member
  obtain ⟨entry, inside, rfl⟩ := List.mem_map.mp member
  exact license.stable_in_window entry.1 entry.2 (checks entry inside)
    (Window.contains_jointStart cross _ (List.mem_map.mpr ⟨entry, inside, rfl⟩))

theorem Captured.replay_at_jointStart (license : Discipline view footprint stamp)
    {program : Program Key Value Answer} {reads : List (Key × Window (Cut steps))}
    {answer : Answer} (capture : Captured view program reads answer)
    (checks : ∀ entry ∈ reads,
      Set.EqOn (stamp entry.2.start) (stamp entry.2.finish) (footprint entry.1))
    (cross : Window.CrossOrdered (reads.map Prod.snd)) :
    run (view (Window.jointStart (reads.map Prod.snd))) program =
      (⟨answer, recordedReads view reads⟩ : Observation Key Value Answer) :=
  capture.replay_of_agrees _ (agrees_at_jointStart license reads checks cross)

end Joint

#print axioms Window.exists_joint_iff
#print axioms Discipline.same_of_stamps
#print axioms Discipline.stable_in_window
#print axioms Captured.replay_of_agrees
#print axioms agrees_at_jointStart
#print axioms Captured.replay_at_jointStart

end Mettapedia.GSLT.Contracts.ReadWindowCuts
