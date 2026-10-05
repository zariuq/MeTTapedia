import Mettapedia.GSLT.Logic.SeparationAlgebra
import Mettapedia.GSLT.Causality.ResourceProduct

/-!
# Separation assertions for resource-system execution

This module connects the existing bag separation algebra to the existing
consume/read/produce operational semantics. An enabled instance can be replayed
beside any unchanged frame. Its footprint includes the resources it reads,
even though those resources remain after firing.

Existential execution specifications therefore admit an unconditional frame
rule. A specification of every permitted successor needs more: the frame must
not enable a new permitted instance. `NoNewEnabled` records this operational
condition, and disjointness from every permitted complete demand implies it.
The condition is stronger than the bag separation algebra's separateness,
which permits two bags containing equal atoms.

The predicates below concern one transition. `SafeTriple` includes progress
as well as the postcondition for every permitted transition; it makes no claim
of termination, fairness, or freedom from errors absent from the given system.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.ResourceFrame

open Mettapedia.GSLT.Causality.ResourceInteraction
open Mettapedia.GSLT.SeparationAlgebra

universe u v

variable {R : Type u} [DecidableEq R] (S : System.{u, v} R)

/-- All resource occurrences needed by an instance, including shared reads. -/
def demand (entry : S.Entry) : Multiset R := S.consume entry.2 + S.read entry.2

omit [DecidableEq R] in
/-- Adding a frame preserves an already enabled instance. -/
theorem enables_add_frame {M : Multiset R} (entry : S.Entry)
    (enabled : S.Enables M entry.2) (frame : Multiset R) :
    S.Enables (M + frame) entry.2 :=
  le_trans enabled (Multiset.le_add_right _ _)

/-- The same enabled instance changes only its local bag. -/
theorem fire_add_frame {M : Multiset R} (entry : S.Entry)
    (enabled : S.Enables M entry.2) (frame : Multiset R) :
    S.fire (M + frame) entry.2 = S.fire M entry.2 + frame := by
  have consumes : S.consume entry.2 ≤ M :=
    le_trans (Multiset.le_add_right _ _) enabled
  unfold System.fire
  rw [← tsub_add_eq_add_tsub consumes]
  ac_rfl

/-- A read-bearing firing has a complete footprint and retains its reads. -/
theorem enables_fire_iff_read_frame (entry : S.Entry) (M N : Multiset R) :
    S.Enables M entry.2 ∧ N = S.fire M entry.2 ↔
      ∃ frame, M = frame + S.consume entry.2 + S.read entry.2 ∧
        N = frame + S.read entry.2 + S.produce entry.2 := by
  constructor
  · rintro ⟨enabled, rfl⟩
    let frame := M - demand S entry
    have source : M = frame + demand S entry :=
      (tsub_add_cancel_of_le enabled).symm
    refine ⟨frame, ?_, ?_⟩
    · simpa only [demand, add_assoc] using source
    · have source' : M = frame + S.read entry.2 + S.consume entry.2 := by
        calc M = frame + demand S entry := source
          _ = frame + S.read entry.2 + S.consume entry.2 := by unfold demand; ac_rfl
      calc S.fire M entry.2 = S.fire (frame + S.read entry.2 + S.consume entry.2) entry.2 :=
            congrArg (fun marking => S.fire marking entry.2) source'
        _ = frame + S.read entry.2 + S.produce entry.2 := by
            unfold System.fire
            rw [add_tsub_cancel_right]
  · rintro ⟨frame, rfl, rfl⟩
    refine ⟨?_, ?_⟩
    · change S.consume entry.2 + S.read entry.2 ≤ _
      rw [add_assoc]
      exact Multiset.le_add_left _ _
    · unfold System.fire
      rw [show frame + S.consume entry.2 + S.read entry.2 =
          frame + S.read entry.2 + S.consume entry.2 by ac_rfl, add_tsub_cancel_right]

/-- Existing resource rewrites remain possible beside a fixed frame. -/
theorem rewrites_add_frame {M N : Multiset R} (step : S.theory.rewrites M N)
    (frame : Multiset R) : S.theory.rewrites (M + frame) (N + frame) := by
  obtain ⟨site, chosen, enabled, rfl⟩ := step
  exact ⟨site, chosen, enables_add_frame S ⟨site, chosen⟩ enabled frame,
    (fire_add_frame S ⟨site, chosen⟩ enabled frame).symm⟩

/-- Replay the same finite sequence, with the same instances and multiplicity,
beside a fixed unchanged frame. -/
theorem fires_add_frame : ∀ (entries : List S.Entry) {M N : Multiset R},
    S.Fires entries M N → ∀ frame, S.Fires entries (M + frame) (N + frame)
  | [], _, _, fires, _ => by
      change _ = _ at fires ⊢
      exact congrArg (· + _) fires
  | entry :: rest, _, _, fires, frame => by
      obtain ⟨enabled, later⟩ := fires
      refine ⟨enables_add_frame S entry enabled frame, ?_⟩
      rw [fire_add_frame S entry enabled frame]
      exact fires_add_frame rest later frame

/-- A control restriction on the existing instances, with no new transitions. -/
def selectedStep (allowed : S.Entry → Prop) (M N : Multiset R) : Prop :=
  ∃ entry : S.Entry, allowed entry ∧ S.Enables M entry.2 ∧ N = S.fire M entry.2

theorem selectedStep_iff_rewrites (M N : Multiset R) :
    selectedStep S (fun _ => True) M N ↔ S.theory.rewrites M N := by
  constructor
  · rintro ⟨entry, _, enabled, target⟩
    exact ⟨entry.1, entry.2, enabled, target⟩
  · rintro ⟨site, chosen, enabled, target⟩
    exact ⟨⟨site, chosen⟩, trivial, enabled, target⟩

theorem selectedStep_add_frame {allowed : S.Entry → Prop} {M N : Multiset R}
    (step : selectedStep S allowed M N) (frame : Multiset R) :
    selectedStep S allowed (M + frame) (N + frame) := by
  obtain ⟨entry, permitted, enabled, rfl⟩ := step
  exact ⟨entry, permitted, enables_add_frame S entry enabled frame,
    (fire_add_frame S entry enabled frame).symm⟩

/-- A frame supplies no new permitted instance at this local state. -/
def NoNewEnabled (allowed : S.Entry → Prop) (M frame : Multiset R) : Prop :=
  ∀ entry : S.Entry, allowed entry → S.Enables (M + frame) entry.2 → S.Enables M entry.2

/-- Disjoint complete demands give an operationally inert frame. Shared reads
must be included in the demands, not only consumed resources. -/
theorem noNewEnabled_of_apart {allowed : S.Entry → Prop} (M frame : Multiset R)
    (apart : ∀ entry : S.Entry, allowed entry → ∀ r ∈ frame, r ∉ demand S entry) :
    NoNewEnabled S allowed M frame := by
  intro entry permitted enabled
  change demand S entry ≤ M
  change demand S entry ≤ M + frame at enabled
  rw [Multiset.le_iff_count] at enabled ⊢
  intro r
  have bound := enabled r
  rw [Multiset.count_add] at bound
  by_cases present : r ∈ frame
  · rw [Multiset.count_eq_zero.mpr (apart entry permitted r present)]
    exact Nat.zero_le _
  · rw [Multiset.count_eq_zero.mpr present] at bound
    exact bound

/-- Under no-new-enablement every permitted global successor has the actual
local successor as its endpoint, with the supplied frame unchanged. -/
theorem selectedStep_iff_frame {allowed : S.Entry → Prop} {M frame N : Multiset R}
    (inert : NoNewEnabled S allowed M frame) :
    selectedStep S allowed (M + frame) N ↔
      ∃ localTarget, selectedStep S allowed M localTarget ∧ N = localTarget + frame := by
  constructor
  · rintro ⟨entry, permitted, enabled, rfl⟩
    have localEnabled := inert entry permitted enabled
    exact ⟨S.fire M entry.2, ⟨entry, permitted, localEnabled, rfl⟩,
      fire_add_frame S entry localEnabled frame⟩
  · rintro ⟨localTarget, step, rfl⟩
    exact selectedStep_add_frame S step frame

/-- From each precondition state some permitted step reaches the postcondition. -/
def MayTriple (allowed : S.Entry → Prop) (pre post : Multiset R → Prop) : Prop :=
  ∀ M, pre M → ∃ N, selectedStep S allowed M N ∧ post N

/-- Every permitted step reaches the postcondition, and at least one is enabled. -/
def SafeTriple (allowed : S.Entry → Prop) (pre post : Multiset R → Prop) : Prop :=
  ∀ M, pre M → (∃ N, selectedStep S allowed M N) ∧
    ∀ N, selectedStep S allowed M N → post N

theorem SafeTriple.may {allowed : S.Entry → Prop} {pre post : Multiset R → Prop}
    (specification : SafeTriple S allowed pre post) : MayTriple S allowed pre post := by
  intro M holds
  obtain ⟨⟨N, step⟩, all⟩ := specification M holds
  exact ⟨N, step, all N step⟩

/-- Existential specifications frame with no interference hypothesis. -/
theorem mayTriple_frame {allowed : S.Entry → Prop} {pre post frame : Multiset R → Prop}
    (specification : MayTriple S allowed pre post) :
    MayTriple S allowed (sepConj pre frame) (sepConj post frame) := by
  rintro _ ⟨M, F, _, rfl, holds, framed⟩
  obtain ⟨N, step, result⟩ := specification M holds
  exact ⟨N + F, selectedStep_add_frame S step F, ⟨N, F, trivial, rfl, result, framed⟩⟩

/-- Demonic specifications frame when the extension enables no new permitted
firings. The conclusion covers the supplied actual global endpoint. -/
theorem safeTriple_frame {allowed : S.Entry → Prop} {pre post frame : Multiset R → Prop}
    (specification : SafeTriple S allowed pre post)
    (inert : ∀ M F, pre M → frame F → NoNewEnabled S allowed M F) :
    SafeTriple S allowed (sepConj pre frame) (sepConj post frame) := by
  rintro _ ⟨M, F, _, rfl, holds, framed⟩
  obtain ⟨⟨N, step⟩, all⟩ := specification M holds
  refine ⟨⟨N + F, selectedStep_add_frame S step F⟩, ?_⟩
  intro actual globalStep
  obtain ⟨localTarget, localStep, rfl⟩ := (selectedStep_iff_frame S (inert M F holds framed)).mp globalStep
  exact ⟨localTarget, F, trivial, rfl, all localTarget localStep, framed⟩

/-- A complete footprint provides progress, and its selected firing retains
the reads and publishes exactly the production. -/
theorem footprint_safeTriple (entry : S.Entry) :
    SafeTriple S (fun candidate => candidate = entry)
      (fun M => M = demand S entry)
      (fun N => N = S.read entry.2 + S.produce entry.2) := by
  intro M equal
  subst M
  have enabled : S.Enables (demand S entry) entry.2 := le_rfl
  have target : S.fire (demand S entry) entry.2 = S.read entry.2 + S.produce entry.2 := by
    unfold System.fire demand
    rw [add_comm (S.consume entry.2), add_tsub_cancel_right]
  refine ⟨⟨_, ⟨entry, rfl, enabled, rfl⟩⟩, ?_⟩
  rintro N ⟨candidate, rfl, _, rfl⟩
  exact target

/-- The selected complete-footprint specification frames even if other
unselected instances can race with it. -/
theorem footprint_safeTriple_frame (entry : S.Entry) (frame : Multiset R → Prop) :
    SafeTriple S (fun candidate => candidate = entry)
      (sepConj (fun M => M = demand S entry) frame)
      (sepConj (fun N => N = S.read entry.2 + S.produce entry.2) frame) := by
  apply safeTriple_frame S (footprint_safeTriple S entry)
  intro M F equal _ candidate same _
  subst M
  subst candidate
  exact le_rfl

end Mettapedia.GSLT.Logic.ResourceFrame
