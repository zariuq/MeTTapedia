import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.ChannelAddressing

/-!
# Dynamic rights and scope extrusion

Sending a name passes the right to use it. A label may carry names in its payload (`names`); a
process that takes or keeps an occurrence, or sees it in a predicate query, learns the names it
carries, and its rights grow (`learned`, `DynamicRun`). A commit builds the names its made
occurrences carry from the names it holds, the names it learns and constants (`BuildsFromHeld`), so
a process may forward any name it holds, including one it learned earlier
(`Controls.forwarding_in_class`), and cannot forge one (`Controls.forging_excluded`). This module
says which laws of `ChannelAddressing` survive.

## What survives

* **Rights only grow** (`DynamicRun.rights_mono`), and every step is scoped to the rights held at
  that step, so each step factors through the restriction to those rights
  (`ChannelAddressing.enabled_iff_restrict`). A process learns from what it takes, keeps or sees in a
  predicate query (`Commit.learnedFrom`); the facets of `InteractionTypes.Facets` are learned from the same
  occurrences, and carried names are carried facets
  (`RegionPermissions.facets_learned_eq_names`). A one-process authority run of
  `InteractionTypes.Facets` is a dynamic run (`RegionPermissions.AuthorityRun.dynamicRun`), and a
  dynamic run is an authority run exactly when no commit forwards a name in the commit that learns
  it or uses a constant (`RegionPermissions.authorityRun_iff_dynamicRun`).
* **Non-interference relative to a closed scope** (`DynamicRun.noninterference_closed`). A set of
  names is *closed* in a store when every occurrence at one of its names carries only names in
  it (`ClosedNames`). A closed set containing a process's rights bounds everything the process
  can ever learn (`DynamicRun.rights_subset_closed`). Two stores that agree on such a set run the
  process alike, with the same growth of rights, and stay in agreement on the set. The scope of
  a process is the least closed set of names containing its rights.
* **Predicate queries outside another process's closed scope stay stable**
  (`DynamicRun.read_stable_outside_closed`): an absence, or any other predicate query, at names
  outside a closed set containing the other process's rights survives every run of that process.

## What fails

Static non-interference fails. Agreement on the *initial* rights is not enough: a message on a
held channel can carry a name, and after taking it the process sees and writes a region it did
not hold (`Controls.extrusion_breaks_static_noninterference`). The predicate query of the name's
owner, answered under the closed world of its scope, is then falsified by one send
(`Controls.extruded_send_falsifies_absence`). Extrusion is
exactly the way into a scope: if no occurrence in the process's closed scope carries a name, the
process never acquires it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v w

variable {O : Type u} [DecidableEq O] {R : Type v} {N : Type w} [DecidableEq N]

variable (label : O → R) (loc : R → N) (names : R → Finset N)

/-- The names a commit learns: those carried by what it takes, keeps or sees in a predicate query
(`Commit.learnedFrom`). -/
def learned (c : Commit O R) : Finset N :=
  c.learnedFrom.biUnion fun o => names (label o)

/-- Rights as a finite set of names, read as a predicate. -/
def holds (K : Finset N) (n : N) : Bool := decide (n ∈ K)

/-- A commit builds the names its made occurrences carry from the names it holds, the names it
learns, and constants. -/
def BuildsFromHeld (constants rights : Finset N) (c : Commit O R) : Prop :=
  ∀ o ∈ c.made, names (label o) ⊆ rights ∪ learned label names c ∪ constants

/-- One process's run with rights that grow by what it learns. -/
inductive DynamicRun (constants : Finset N) :
    Finset O → Finset N → List (Commit O R) → Finset O → Finset N → Prop
  | nil (store : Finset O) (rights : Finset N) : DynamicRun constants store rights [] store rights
  | cons {store : Finset O} {rights : Finset N} {c : Commit O R} {rest : List (Commit O R)}
      {store' : Finset O} {rights' : Finset N}
      (enabled : Enabled label store c) (inScope : Scoped label loc (holds rights) c)
      (builds : BuildsFromHeld label names constants rights c)
      (after : DynamicRun constants (fire store c) (rights ∪ learned label names c) rest store' rights') :
      DynamicRun constants store rights (c :: rest) store' rights'

/-- A set of names is closed in a store: every occurrence at one of its names carries only names
in it. -/
def ClosedNames (C : Finset N) (store : Finset O) : Prop :=
  ∀ o ∈ store, loc (label o) ∈ C → names (label o) ⊆ C

variable {label loc names}

namespace DynamicRun

variable {constants : Finset N}

/-- **Rights only grow.** -/
theorem rights_mono {store store' : Finset O} {rights rights' : Finset N} {run : List (Commit O R)}
    (dynamic : DynamicRun label loc names constants store rights run store' rights') :
    rights ⊆ rights' := by
  induction dynamic with
  | nil => exact le_rfl
  | cons _ _ _ _ ih => exact Finset.subset_union_left.trans ih

/-- What a scoped commit learns lies in a closed set containing its rights. -/
theorem learned_subset_closed {C : Finset N} {store : Finset O} {rights : Finset N}
    {c : Commit O R} (closed : ClosedNames label loc names C store) (inside : rights ⊆ C)
    (enabled : Enabled label store c) (inScope : Scoped label loc (holds rights) c) :
    learned label names c ⊆ C := by
  intro n member
  obtain ⟨o, used, carried⟩ := Finset.mem_biUnion.mp member
  have heldAndPresent : loc (label o) ∈ rights ∧ o ∈ store := by
    rcases Finset.mem_union.mp used with used | seen
    · rcases Finset.mem_union.mp used with taken | kept
      · exact ⟨by simpa [holds] using inScope.taken o taken, enabled.taken_subset taken⟩
      · exact ⟨by simpa [holds] using inScope.kept o kept, enabled.kept_subset kept⟩
    · obtain ⟨read, member, inSeen⟩ := mem_seenOf.mp seen
      have holdsRead := enabled.queries_hold read member
      unfold PredicateQuery.Holds at holdsRead
      rw [← holdsRead] at inSeen
      obtain ⟨inStore, inRegion⟩ := mem_regionOf.mp inSeen
      exact ⟨by simpa [holds] using inScope.queries read member (label o) inRegion, inStore⟩
  exact closed o heldAndPresent.2 (inside heldAndPresent.1) carried

/-- A step of a process whose rights lie in a closed set keeps the set closed. -/
theorem closed_fire {C : Finset N} {store : Finset O} {rights : Finset N} {c : Commit O R}
    (closed : ClosedNames label loc names C store) (inside : rights ⊆ C) (constantsIn : constants ⊆ C)
    (enabled : Enabled label store c) (inScope : Scoped label loc (holds rights) c)
    (builds : BuildsFromHeld label names constants rights c) :
    ClosedNames label loc names C (fire store c) := by
  intro o member _
  rcases mem_fire.mp member with ⟨inStore, _⟩ | made
  · exact closed o inStore ‹_›
  · intro n carried
    rcases Finset.mem_union.mp (builds o made carried) with heldOrLearned | constant
    · rcases Finset.mem_union.mp heldOrLearned with held | fromUse
      · exact inside held
      · exact learned_subset_closed closed inside enabled inScope fromUse
    · exact constantsIn constant

/-- **A closed set containing the rights bounds every name the process can learn.** -/
theorem rights_subset_closed {C : Finset N} {store store' : Finset O} {rights rights' : Finset N}
    {run : List (Commit O R)} (dynamic : DynamicRun label loc names constants store rights run store' rights')
    (closed : ClosedNames label loc names C store) (inside : rights ⊆ C) (constantsIn : constants ⊆ C) :
    rights' ⊆ C ∧ ClosedNames label loc names C store' := by
  induction dynamic with
  | nil => exact ⟨inside, closed⟩
  | cons enabled inScope builds _ ih =>
      exact ih (closed_fire closed inside constantsIn enabled inScope builds)
        (Finset.union_subset inside (learned_subset_closed closed inside enabled inScope))

/-- **Non-interference relative to a closed scope.** Two stores that agree on a set of names that
is closed in both and contains the rights run the process alike: the same commits execute, with
the same growth of rights, and the stores stay in agreement on the set. -/
theorem noninterference_closed {C : Finset N} (constantsIn : constants ⊆ C) :
    ∀ {first second : Finset O} {rights : Finset N} {run : List (Commit O R)},
      ClosedNames label loc names C first → ClosedNames label loc names C second → rights ⊆ C →
      restrict label loc (holds C) first = restrict label loc (holds C) second →
      ∀ {first' : Finset O} {rights' : Finset N},
        DynamicRun label loc names constants first rights run first' rights' →
        ∃ second', DynamicRun label loc names constants second rights run second' rights' ∧
          restrict label loc (holds C) first' = restrict label loc (holds C) second' := by
  intro first second rights run closedFirst closedSecond inside agree first' rights' dynamic
  induction dynamic generalizing second with
  | nil => exact ⟨second, .nil _ _, agree⟩
  | @cons store rights c rest store' rights' enabled inScope builds after ih =>
      have scopedC : Scoped label loc (holds C) c :=
        ⟨fun o taken => by have := inScope.taken o taken; simp [holds] at this ⊢; exact inside this,
          fun o kept => by have := inScope.kept o kept; simp [holds] at this ⊢; exact inside this,
          fun o made => by have := inScope.made o made; simp [holds] at this ⊢; exact inside this,
          fun read member r inRegion => by
            have := inScope.queries read member r inRegion; simp [holds] at this ⊢; exact inside this⟩
      have enabledSecond : Enabled label second c := by
        rw [enabled_iff_restrict scopedC, ← agree, ← enabled_iff_restrict scopedC]
        exact enabled
      have learnedSame : learned label names c ⊆ C :=
        learned_subset_closed closedFirst inside enabled inScope
      have agreeNext : restrict label loc (holds C) (fire store c) =
          restrict label loc (holds C) (fire second c) := by
        rw [restrict_fire scopedC, restrict_fire scopedC, agree]
      obtain ⟨second', run', agree'⟩ := ih
        (closed_fire closedFirst inside constantsIn enabled inScope builds)
        (closed_fire closedSecond inside constantsIn enabledSecond inScope builds)
        (Finset.union_subset inside learnedSame) agreeNext
      exact ⟨second', .cons enabledSecond inScope builds run', agree'⟩

/-- **Predicate queries outside another process's closed scope stay stable.** -/
theorem read_stable_outside_closed {C : Finset N} {store store' : Finset O}
    {rights rights' : Finset N} {run : List (Commit O R)}
    (dynamic : DynamicRun label loc names constants store rights run store' rights')
    (closed : ClosedNames label loc names C store) (inside : rights ⊆ C) (constantsIn : constants ⊆ C)
    {read : PredicateQuery O R} (outside : ∀ r, read.region r = true → loc r ∉ C)
    (holdsRead : read.Holds label store) : read.Holds label store' := by
  induction dynamic with
  | nil => exact holdsRead
  | @cons store rights c rest store' rights' enabled inScope builds after ih =>
      apply ih (closed_fire closed inside constantsIn enabled inScope builds)
        (Finset.union_subset inside (learned_subset_closed closed inside enabled inScope))
      refine PredicateQuery.holds_fire_of_no_write (fun o written => ?_) holdsRead
      cases inRegion : read.region (label o)
      · rfl
      · have heldO : loc (label o) ∈ rights := by
          rcases Finset.mem_union.mp written with taken | made
          · simpa [holds] using inScope.taken o taken
          · simpa [holds] using inScope.made o made
        exact absurd (inside heldO) (outside _ inRegion)

end DynamicRun

/-! ## Controls -/

namespace Controls

/-- Labels: a location and, optionally, a carried name. Occurrence `300` is a message on name `1`
carrying name `0`; `301` lives at name `0`; `302` is a send on name `0`. -/
def extrusionLabel : ℕ → ℕ × Option ℕ
  | 300 => (1, some 0)
  | 301 => (0, none)
  | 302 => (0, none)
  | _ => (5, none)

/-- The names a label carries. -/
def carried : ℕ × Option ℕ → Finset ℕ
  | (_, some n) => {n}
  | (_, none) => ∅

/-- Take the message on name `1`. -/
def takeMessage : Commit ℕ (ℕ × Option ℕ) := ⟨{300}, ∅, ∅, []⟩

/-- Take the occurrence at name `0`. -/
def takeAtZero : Commit ℕ (ℕ × Option ℕ) := ⟨{301}, ∅, ∅, []⟩

/-- Send on name `0`. -/
def extrudedSend : Commit ℕ (ℕ × Option ℕ) := ⟨∅, ∅, {302}, []⟩

/-- **Static non-interference fails under extrusion.** The stores `{300}` and `{300, 301}` agree on
name `1`, the process's initial rights. After taking the message, which carries name `0`, the
process can take the occurrence at name `0` in the second store and not in the first. -/
theorem extrusion_breaks_static_noninterference :
    restrict extrusionLabel Prod.fst (holds {1}) {300} =
        restrict extrusionLabel Prod.fst (holds {1}) {300, 301} ∧
      DynamicRun extrusionLabel Prod.fst carried ∅ {300, 301} {1} [takeMessage, takeAtZero]
        ∅ {1, 0} ∧
      ¬ ∃ store' rights', DynamicRun extrusionLabel Prod.fst carried ∅ {300} {1}
        [takeMessage, takeAtZero] store' rights' := by
  refine ⟨by decide, ?_, ?_⟩
  · refine .cons ⟨by decide, by decide, by decide, by decide, by simp [takeMessage]⟩
      ⟨by decide, by simp [takeMessage], by simp [takeMessage], by simp [takeMessage]⟩
      (by simp [BuildsFromHeld, takeMessage]) ?_
    refine .cons ⟨by decide, by decide, by decide, by decide, by simp [takeAtZero]⟩
      ⟨by decide, by simp [takeAtZero], by simp [takeAtZero], by simp [takeAtZero]⟩
      (by simp [BuildsFromHeld, takeAtZero]) ?_
    convert DynamicRun.nil (label := extrusionLabel) (loc := Prod.fst) (names := carried)
      (constants := ∅) (∅ : Finset ℕ) ({1, 0} : Finset ℕ) using 2 <;> decide
  · rintro ⟨store', rights', dynamic⟩
    cases dynamic with
    | cons _ _ _ after =>
        cases after with
        | cons enabled _ _ _ =>
            have := enabled.taken_subset (show 301 ∈ takeAtZero.taken by simp [takeAtZero])
            revert this
            decide

/-- **The owner's predicate query falls once the name is extruded**: extrusion opens the closed
world of its scope. The absence at name `0` holds at `{300}`; the process that learns name `0` from
the message sends on it and falsifies the absence. A process whose closed scope excludes name `0`
could not. -/
theorem extruded_send_falsifies_absence :
    AbsenceHolds extrusionLabel (fun r => r.1 == 0) {300} ∧
      DynamicRun extrusionLabel Prod.fst carried ∅ {300} {1} [takeMessage, extrudedSend] {302} {1, 0} ∧
      ¬ AbsenceHolds extrusionLabel (fun r => r.1 == 0) {302} := by
  refine ⟨by unfold AbsenceHolds; decide, ?_, by unfold AbsenceHolds; decide⟩
  refine .cons ⟨by decide, by decide, by decide, by decide, by simp [takeMessage]⟩
    ⟨by decide, by simp [takeMessage], by simp [takeMessage], by simp [takeMessage]⟩
    (by simp [BuildsFromHeld, takeMessage]) ?_
  refine .cons ⟨by simp [extrudedSend], by simp [extrudedSend], by simp [extrudedSend], by decide,
      by simp [extrudedSend]⟩
    ⟨by simp [extrudedSend], by simp [extrudedSend], by decide, by simp [extrudedSend]⟩
    (by intro o made; simp [extrudedSend] at made; subst made; simp [extrusionLabel, carried]) ?_
  convert DynamicRun.nil (label := extrusionLabel) (loc := Prod.fst) (names := carried)
    (constants := ∅) ({302} : Finset ℕ) ({1, 0} : Finset ℕ) using 2 <;> decide

/-! ### The closed-scope theorem has instances -/

theorem closed_first : ClosedNames extrusionLabel Prod.fst carried ({0, 1} : Finset ℕ) {300} := by
  intro o member _
  rw [Finset.mem_singleton.mp member]
  decide

theorem closed_second :
    ClosedNames extrusionLabel Prod.fst carried ({0, 1} : Finset ℕ) {300, 304} := by
  intro o member atC
  rcases Finset.mem_insert.mp member with rfl | member
  · decide
  · rw [Finset.mem_singleton.mp member] at atC ⊢
    revert atC
    decide

theorem run_first :
    DynamicRun extrusionLabel Prod.fst carried ∅ {300} {1} [takeMessage] ∅ {1, 0} := by
  refine .cons ⟨by decide, by decide, by decide, by decide, by simp [takeMessage]⟩
    ⟨by decide, by simp [takeMessage], by simp [takeMessage], by simp [takeMessage]⟩
    (by simp [BuildsFromHeld, takeMessage]) ?_
  convert DynamicRun.nil (label := extrusionLabel) (loc := Prod.fst) (names := carried)
    (constants := ∅) (∅ : Finset ℕ) ({1, 0} : Finset ℕ) using 2 <;> decide

/-- **The hypotheses of `noninterference_closed` are jointly satisfiable**: `{300}` and
`{300, 304}` agree on the closed set `{0, 1}`, and the run that takes the message from the first
runs from the second too. -/
theorem noninterference_closed_instance :
    ∃ second', DynamicRun extrusionLabel Prod.fst carried ∅ {300, 304} {1} [takeMessage] second'
        {1, 0} ∧
      restrict extrusionLabel Prod.fst (holds ({0, 1} : Finset ℕ)) ∅ =
        restrict extrusionLabel Prod.fst (holds ({0, 1} : Finset ℕ)) second' :=
  DynamicRun.noninterference_closed (C := {0, 1}) (by simp) closed_first closed_second (by decide)
    (by decide) run_first

/-! ### Forwarding, forging, and learning by a predicate query -/

/-- Labels with a forwarding message: `300` and `303` are messages on name `1` carrying name `0`;
`304` is a message on name `1` carrying name `7`. -/
def fwdLabel : ℕ → ℕ × Option ℕ
  | 300 => (1, some 0)
  | 303 => (1, some 0)
  | 304 => (1, some 7)
  | _ => (5, none)

/-- Forward the learned name `0` on channel `1`. -/
def forward : Commit ℕ (ℕ × Option ℕ) := ⟨∅, ∅, {303}, []⟩

/-- **Forwarding a held name is in the class**: the process learns name `0` from the message, and
in a later commit sends a message carrying it. -/
theorem forwarding_in_class :
    DynamicRun fwdLabel Prod.fst carried ∅ {300} {1} [takeMessage, forward] {303} {1, 0} := by
  refine .cons ⟨by decide, by decide, by decide, by decide, by simp [takeMessage]⟩
    ⟨by decide, by simp [takeMessage], by simp [takeMessage], by simp [takeMessage]⟩
    (by simp [BuildsFromHeld, takeMessage]) ?_
  refine .cons ⟨by simp [forward], by simp [forward], by simp [forward], by decide,
      by simp [forward]⟩
    ⟨by simp [forward], by simp [forward], by decide, by simp [forward]⟩
    (by
      intro o made
      simp only [forward, Finset.mem_singleton] at made
      subst made
      decide) ?_
  convert DynamicRun.nil (label := fwdLabel) (loc := Prod.fst) (names := carried)
    (constants := ∅) ({303} : Finset ℕ) ({1, 0} : Finset ℕ) using 2 <;> decide

/-- Send a message carrying name `7`. -/
def forge : Commit ℕ (ℕ × Option ℕ) := ⟨∅, ∅, {304}, []⟩

/-- **A name neither held nor learned cannot be sent**: with rights `{1}` and no constants, the
message carrying name `7` is not a step. -/
theorem forging_excluded :
    ¬ ∃ store' rights', DynamicRun fwdLabel Prod.fst carried ∅ ∅ {1} [forge] store' rights' := by
  rintro ⟨store', rights', dynamic⟩
  cases dynamic with
  | cons _ _ builds _ =>
      have := builds 304 (by simp [forge])
      revert this
      decide

/-- Query the messages on name `1`, having seen `300`. -/
def readMessages : Commit ℕ (ℕ × Option ℕ) := ⟨∅, ∅, ∅, [⟨fun r => r.1 == 1, {300}⟩]⟩

/-- **A predicate query teaches names too**: the process queries the message region, learns name
`0` from what it saw, and then sends on name `0`. -/
theorem learns_by_predicate_query :
    DynamicRun extrusionLabel Prod.fst carried ∅ {300} {1} [readMessages, extrudedSend]
      {300, 302} {1, 0} := by
  refine .cons ⟨by simp [readMessages], by simp [readMessages], by simp [readMessages],
      by simp [readMessages], ?_⟩
    ⟨by simp [readMessages], by simp [readMessages], by simp [readMessages], ?_⟩
    (by simp [BuildsFromHeld, readMessages]) ?_
  · intro read member
    simp only [readMessages, List.mem_singleton] at member
    subst member
    decide
  · intro read member r inRegion
    simp only [readMessages, List.mem_singleton] at member
    subst member
    simp only [beq_iff_eq] at inRegion
    simp [holds, inRegion]
  refine .cons ⟨by simp [extrudedSend], by simp [extrudedSend], by simp [extrudedSend], by decide,
      by simp [extrudedSend]⟩
    ⟨by simp [extrudedSend], by simp [extrudedSend], by decide, by simp [extrudedSend]⟩
    (by intro o made; simp [extrudedSend] at made; subst made; simp [extrusionLabel, carried]) ?_
  convert DynamicRun.nil (label := extrusionLabel) (loc := Prod.fst) (names := carried)
    (constants := ∅) ({300, 302} : Finset ℕ) ({1, 0} : Finset ℕ) using 2 <;> decide

/-! ### Building from held names, closed name sets -/

/-- Take the message carrying name `0` and, in the same commit, send a message carrying it. -/
def learnAndForward : Commit ℕ (ℕ × Option ℕ) := ⟨{300}, ∅, {303}, []⟩

/-- **Positive control**: a commit builds name `0` from what it learns in the same step. It holds
only name `1`, takes the message carrying `0`, and sends `0` on. -/
theorem learnAndForward_builds_from_held :
    BuildsFromHeld fwdLabel carried ∅ {1} learnAndForward := by
  unfold BuildsFromHeld learned; decide

/-- **Positive control**: once name `0` is held, forwarding it builds from held names. -/
theorem forward_builds_from_held : BuildsFromHeld fwdLabel carried ∅ {1, 0} forward := by
  unfold BuildsFromHeld learned; decide

/-- **Negative control**: with rights `{1}`, nothing learned and no constants, a message carrying
name `7` is forged. -/
theorem forge_not_builds_from_held : ¬ BuildsFromHeld fwdLabel carried ∅ {1} forge := by
  unfold BuildsFromHeld learned; decide

/-- **Positive control**: names `{0, 1}` are closed in `{300, 301}`: the message at name `1`
carries only name `0`, and the occurrence at name `0` carries nothing. -/
theorem extrusion_store_closed : ClosedNames extrusionLabel Prod.fst carried {0, 1} {300, 301} := by
  unfold ClosedNames; decide

/-- **Negative control**: name `1` alone is not closed in `{300}`: the message at name `1` carries
name `0`, the way into the other scope. -/
theorem extrusion_store_open_at_one : ¬ ClosedNames extrusionLabel Prod.fst carried {1} {300} := by
  unfold ClosedNames; decide

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
