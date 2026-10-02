import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.CausalInteraction
import Mettapedia.GSLT.Causality.ResourceReads
import Mettapedia.GSLT.Causality.ResourceFrontier

/-!
# Guarded transactions as interaction on a bag of located atoms

A located network holding finitely many occurrences is a bag of located atoms.
A guarded transaction claims the atoms selected by its consume guards, checks
the atoms selected by its observe guards against the snapshot before the
transaction, and publishes what its continuation emits. As a firing on the bag
it consumes its claims, reads each observed atom that it does not also claim,
once, and produces its emissions.

A transaction fires from the network of a bag exactly when this firing is
enabled at the bag, and it reaches the network of the fired bag. The theory of
resource firings therefore applies to transactions. Two transactions that
claim one occurrence conflict; transactions that only observe it in common
are concurrent and commute. The direct communication of the MeTTa-calculus
claims both guarded parties.

For single located requests, which publish nothing, a commuting square of the
two orders is exactly concurrency. A transaction that publishes again what it
claimed has a commuting square with a second copy of itself without being
concurrent with it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.TransactionResources

open Mettapedia.GSLT
open Mettapedia.GSLT.Causality.ResourceInteraction
open Mettapedia.OSLF.MeTTaIL.Match
open SpaceChannelBoundary
open SpaceInteraction
open SpaceInteraction.GuardedTransaction
open CausalInteraction

variable {Location Atom : Type} [DecidableEq Location] [DecidableEq Atom]

/-! ## Networks of bags -/

/-- The network holding a bag of located atoms. -/
def networkOf (M : Multiset (Location × Atom)) : Network Location Atom :=
  fun location => (M.filter fun occurrence => occurrence.1 = location).map Prod.snd

theorem count_networkOf (M : Multiset (Location × Atom)) (location : Location)
    (atom : Atom) : (networkOf M location).count atom = M.count (location, atom) := by
  induction M using Multiset.induction_on with
  | empty => simp [networkOf]
  | cons occurrence M ih =>
      obtain ⟨place, value⟩ := occurrence
      unfold networkOf at ih ⊢
      rw [Multiset.filter_cons, Multiset.map_add, Multiset.count_add, ih, Multiset.count_cons]
      by_cases here : place = location
      · subst here
        by_cases same : atom = value
        · subst same
          simp [add_comm]
        · simp [same]
      · have apart : (location, atom) ≠ (place, value) := fun h => here (Prod.mk.inj h).1.symm
        simp [here, apart]

theorem mem_networkOf {M : Multiset (Location × Atom)} {location : Location} {atom : Atom} :
    atom ∈ networkOf M location ↔ (location, atom) ∈ M := by
  rw [← Multiset.count_pos, ← Multiset.count_pos, count_networkOf]

theorem networkOf_injective {M N : Multiset (Location × Atom)}
    (same : networkOf M = networkOf N) : M = N := by
  ext occurrence
  obtain ⟨location, atom⟩ := occurrence
  rw [← count_networkOf, ← count_networkOf, same]

/-- Removing a located atom removes it at its location. -/
theorem networkOf_erase (M : Multiset (Location × Atom)) (location : Location) (atom : Atom) :
    networkOf (M.erase (location, atom)) =
      Function.update (networkOf M) location ((networkOf M location).erase atom) := by
  funext place
  ext other
  rw [count_networkOf, Function.update_apply]
  split_ifs with here
  · subst here
    by_cases same : other = atom
    · subst same
      rw [Multiset.count_erase_self, Multiset.count_erase_self, count_networkOf]
    · rw [Multiset.count_erase_of_ne (fun h => same (Prod.mk.inj h).2),
        Multiset.count_erase_of_ne same, count_networkOf]
  · rw [Multiset.count_erase_of_ne (fun h => here (Prod.mk.inj h).1), count_networkOf]

/-- Publishing one occurrence adds it to the bag. -/
theorem publish_networkOf (emission : Emission Location Atom) (M : Multiset (Location × Atom)) :
    publish emission (networkOf M) = networkOf ((emission.location, emission.atom) ::ₘ M) := by
  funext place
  ext other
  rw [count_networkOf, Multiset.count_cons]
  unfold publish
  rw [Function.update_apply]
  split_ifs with here same same
  · subst here
    rw [Multiset.count_cons, count_networkOf, if_pos (Prod.mk.inj same).2]
  · subst here
    have differ : other ≠ emission.atom := fun h => same (by rw [h])
    rw [Multiset.count_cons, count_networkOf, if_neg differ]
  · exact absurd (Prod.mk.inj same).1 here
  · rw [count_networkOf, add_zero]

/-- The located atoms a list of emissions publishes. -/
def emitted (emissions : List (Emission Location Atom)) : Multiset (Location × Atom) :=
  (emissions.map fun emission => (emission.location, emission.atom) : Multiset (Location × Atom))

theorem publishAll_networkOf : ∀ (emissions : List (Emission Location Atom))
    (M : Multiset (Location × Atom)),
    publishAll emissions (networkOf M) = networkOf (M + emitted emissions)
  | [], M => by
      rw [publishAll_nil]
      simp [emitted]
  | emission :: rest, M => by
      rw [publishAll_cons, publish_networkOf, publishAll_networkOf rest]
      change networkOf ((emission.location, emission.atom) ::ₘ M + emitted rest) =
        networkOf (M + (emission.location, emission.atom) ::ₘ emitted rest)
      rw [Multiset.cons_add, Multiset.add_cons]

/-! ## What a transaction claims and observes -/

variable {Pattern : Type}

/-- The located atoms claimed by the consume guards. -/
def claims : List (Guard Location Pattern) → List Atom → Multiset (Location × Atom)
  | ⟨.consume, location, _⟩ :: guards, atom :: atoms => (location, atom) ::ₘ claims guards atoms
  | ⟨.observe, _, _⟩ :: guards, _ :: atoms => claims guards atoms
  | _, _ => 0

/-- The located atoms checked by the observe guards. -/
def sightings : List (Guard Location Pattern) → List Atom → Multiset (Location × Atom)
  | ⟨.observe, location, _⟩ :: guards, atom :: atoms =>
      (location, atom) ::ₘ sightings guards atoms
  | ⟨.consume, _, _⟩ :: guards, _ :: atoms => sightings guards atoms
  | _, _ => 0

/-- **Claiming from the network of a bag is subtraction.** -/
theorem consumes_sound {guards : List (Guard Location Pattern)} {atoms : List Atom}
    {source residual : Network Location Atom} (consumed : Consumes guards atoms source residual) :
    ∀ M : Multiset (Location × Atom), source = networkOf M →
      guards.length = atoms.length ∧ claims guards atoms ≤ M ∧
        residual = networkOf (M - claims guards atoms) := by
  induction consumed with
  | nil =>
      intro M from_
      subst from_
      refine ⟨rfl, Multiset.zero_le _, ?_⟩
      change networkOf M = networkOf (M - 0)
      rw [tsub_zero]
  | observe _ ih =>
      intro M from_
      obtain ⟨lengths, claimed, residualEq⟩ := ih M from_
      exact ⟨by simp [lengths], claimed, residualEq⟩
  | @consume location _ atom _ _ source middle _ head _ ih =>
      intro M from_
      subst from_
      obtain ⟨rest, atLocation, rfl⟩ := LocatedStep.consume_iff.mp head
      have member : (location, atom) ∈ M :=
        mem_networkOf.mp (by rw [atLocation]; exact Multiset.mem_cons_self _ _)
      have restEq : rest = (networkOf M location).erase atom := by
        rw [atLocation, Multiset.erase_cons_head]
      have middleEq : Function.update (networkOf M) location rest =
          networkOf (M.erase (location, atom)) := by
        rw [restEq, networkOf_erase]
      obtain ⟨lengths, claimed, residualEq⟩ := ih (M.erase (location, atom)) middleEq
      refine ⟨by simp [lengths], ?_, ?_⟩
      · change (location, atom) ::ₘ claims _ _ ≤ M
        rw [← Multiset.cons_erase member]
        exact Multiset.cons_le_cons _ claimed
      · change _ = networkOf (M - (location, atom) ::ₘ claims _ _)
        rw [Multiset.sub_cons]
        exact residualEq

/-- Claims present in a bag are claimed from its network. -/
theorem consumes_complete : ∀ (guards : List (Guard Location Pattern)) (atoms : List Atom)
    (M : Multiset (Location × Atom)), guards.length = atoms.length → claims guards atoms ≤ M →
      Consumes guards atoms (networkOf M) (networkOf (M - claims guards atoms))
  | [], [], M, _, _ => by
      change Consumes [] [] (networkOf M) (networkOf (M - 0))
      rw [tsub_zero]
      exact .nil
  | [], _ :: _, _, lengths, _ => by simp at lengths
  | _ :: _, [], _, lengths, _ => by simp at lengths
  | ⟨.observe, _, _⟩ :: guards, _ :: atoms, M, lengths, claimed =>
      .observe (consumes_complete guards atoms M (by simpa using lengths) claimed)
  | ⟨.consume, location, _⟩ :: guards, atom :: atoms, M, lengths, claimed => by
      change (location, atom) ::ₘ claims guards atoms ≤ M at claimed
      have member : (location, atom) ∈ M := Multiset.mem_of_le claimed (Multiset.mem_cons_self _ _)
      have restClaimed : claims guards atoms ≤ M.erase (location, atom) := by
        rw [← Multiset.cons_le_cons_iff (location, atom), Multiset.cons_erase member]
        exact claimed
      have tail := consumes_complete guards atoms (M.erase (location, atom))
        (by simpa using lengths) restClaimed
      rw [← Multiset.sub_cons] at tail
      refine .consume ?_ tail
      rw [networkOf_erase]
      exact LocatedStep.consume _ (Multiset.cons_erase (mem_networkOf.mpr member)).symm

/-- **Observing the network of a bag is membership in the bag.** -/
theorem observes_iff : ∀ (guards : List (Guard Location Pattern)) (atoms : List Atom)
    (M : Multiset (Location × Atom)), guards.length = atoms.length →
      (ObservesSnapshot guards atoms (networkOf M) ↔
        ∀ occurrence ∈ sightings guards atoms, occurrence ∈ M)
  | [], [], M, _ => by
      constructor
      · intro _ occurrence seen
        simp [sightings] at seen
      · intro _
        exact .nil
  | [], _ :: _, _, lengths => by simp at lengths
  | _ :: _, [], _, lengths => by simp at lengths
  | ⟨.observe, location, pattern⟩ :: guards, atom :: atoms, M, lengths => by
      have rest := observes_iff guards atoms M (by simpa using lengths)
      constructor
      · intro observed
        cases observed with
        | observe present tail =>
            intro occurrence seen
            change occurrence ∈ (location, atom) ::ₘ sightings guards atoms at seen
            rcases Multiset.mem_cons.mp seen with here | later
            · rw [here]
              exact mem_networkOf.mp present
            · exact rest.mp tail occurrence later
      · intro seen
        exact .observe (mem_networkOf.mpr (seen _ (Multiset.mem_cons_self _ _)))
          (rest.mpr fun occurrence later => seen occurrence (Multiset.mem_cons_of_mem later))
  | ⟨.consume, location, pattern⟩ :: guards, atom :: atoms, M, lengths => by
      have rest := observes_iff guards atoms M (by simpa using lengths)
      constructor
      · intro observed
        cases observed with
        | consume tail => exact rest.mp tail
      · intro seen
        exact .consume (rest.mpr seen)

/-! ## Transactions as a resource system -/

variable {Environment : Type}

/-- The atoms and the environment of one firing of a command. -/
abbrev Choice (selects : Selection Location Atom Pattern Environment)
    (command : Command Location Atom Pattern Environment) : Type :=
  {choice : List Atom × Environment //
    command.guards.length = choice.1.length ∧ selects command.guards choice.1 choice.2}

/-- The observed atoms a firing reads: those it does not also claim, each once.
Observation checks the snapshot before the transaction, so an atom the firing
claims needs no further copy to be observed. -/
def snapshotReads (guards : List (Guard Location Pattern)) (atoms : List Atom) :
    Multiset (Location × Atom) :=
  (sightings guards atoms).dedup.filter fun occurrence => occurrence ∉ claims guards atoms

/-- Guarded transactions as a resource system over located atoms. -/
def transactions (selects : Selection Location Atom Pattern Environment)
    (enabled : Command Location Atom Pattern Environment → Prop) :
    System (Location × Atom) where
  Site := {command // enabled command}
  Instance := fun command => Choice selects command.1
  consume := fun {command} choice => claims command.1.guards choice.1.1
  read := fun {command} choice => snapshotReads command.1.guards choice.1.1
  produce := fun {command} choice => emitted (command.1.continuation choice.1.2)

/-- A firing is enabled when its claims are present and everything it observes
is present. -/
theorem snapshot_enables_iff (guards : List (Guard Location Pattern)) (atoms : List Atom)
    (M : Multiset (Location × Atom)) :
    claims guards atoms + snapshotReads guards atoms ≤ M ↔
      claims guards atoms ≤ M ∧ ∀ occurrence ∈ sightings guards atoms, occurrence ∈ M := by
  constructor
  · intro fits
    have claimed := le_trans (Multiset.le_add_right _ _) fits
    refine ⟨claimed, ?_⟩
    intro occurrence seen
    by_cases isClaimed : occurrence ∈ claims guards atoms
    · exact Multiset.mem_of_le claimed isClaimed
    · apply Multiset.mem_of_le (le_trans (Multiset.le_add_left _ _) fits)
      simp [snapshotReads, seen, isClaimed]
  · rintro ⟨claimed, seen⟩
    rw [Multiset.le_iff_count]
    intro occurrence
    rw [Multiset.count_add]
    by_cases isClaimed : occurrence ∈ claims guards atoms
    · have unread : (snapshotReads guards atoms).count occurrence = 0 := by
        rw [Multiset.count_eq_zero]
        simp [snapshotReads, isClaimed]
      rw [unread, add_zero]
      exact Multiset.count_le_of_le _ claimed
    · rw [Multiset.count_eq_zero.mpr isClaimed, zero_add]
      unfold snapshotReads
      rw [Multiset.count_filter, if_pos isClaimed, Multiset.count_dedup]
      split_ifs with isSeen
      · exact Multiset.one_le_count_iff_mem.mpr (seen _ isSeen)
      · exact Nat.zero_le _

/-- **A transaction fires from the network of a bag exactly as its firing does
on the bag.** -/
theorem fires_networkOf_iff (selects : Selection Location Atom Pattern Environment)
    (command : Command Location Atom Pattern Environment) (M : Multiset (Location × Atom))
    (target : Network Location Atom) :
    Fires selects command (networkOf M) target ↔
      ∃ choice : Choice selects command,
        claims command.guards choice.1.1 + snapshotReads command.guards choice.1.1 ≤ M ∧
          target = networkOf (M - claims command.guards choice.1.1 +
            emitted (command.continuation choice.1.2)) := by
  constructor
  · intro fires
    obtain ⟨atoms, environment, residual, selected, observed, consumed, rfl⟩ :=
      (fires_iff selects command (networkOf M) target).mp fires
    obtain ⟨lengths, claimed, rfl⟩ := consumes_sound consumed M rfl
    have seen := (observes_iff command.guards atoms M lengths).mp observed
    exact ⟨⟨(atoms, environment), lengths, selected⟩,
      (snapshot_enables_iff command.guards atoms M).mpr ⟨claimed, seen⟩,
      publishAll_networkOf _ _⟩
  · rintro ⟨⟨⟨atoms, environment⟩, lengths, selected⟩, enabled, rfl⟩
    obtain ⟨claimed, seen⟩ := (snapshot_enables_iff command.guards atoms M).mp enabled
    rw [← publishAll_networkOf]
    exact .fire selected ((observes_iff command.guards atoms M lengths).mpr seen)
      (consumes_complete command.guards atoms M lengths claimed)

/-- **The transaction theory on networks of bags is the resource theory of
transactions.** -/
theorem step_networkOf_iff (selects : Selection Location Atom Pattern Environment)
    (enabled : Command Location Atom Pattern Environment → Prop)
    (M : Multiset (Location × Atom)) (target : Network Location Atom) :
    (theory selects enabled).Step (networkOf M) target ↔
      ∃ N, target = networkOf N ∧ (transactions selects enabled).theory.Step M N := by
  constructor
  · rintro ⟨command, commandEnabled, fires⟩
    obtain ⟨choice, fits, rfl⟩ := (fires_networkOf_iff selects command M target).mp fires
    exact ⟨_, rfl, ⟨command, commandEnabled⟩, choice, fits, rfl⟩
  · rintro ⟨N, rfl, ⟨command, commandEnabled⟩, choice, fits, rfl⟩
    exact ⟨command, commandEnabled,
      (fires_networkOf_iff selects command M _).mpr ⟨choice, fits, rfl⟩⟩

/-! ## Current-world search executes actual guarded transactions -/

/-- Every recorded resource firing is a step of the independently defined
guarded transaction theory, including work enabled by earlier continuations. -/
theorem fires_networkOf_multiStep (selects : Selection Location Atom Pattern Environment)
    (enabled : Command Location Atom Pattern Environment → Prop) :
    ∀ (path : List (transactions selects enabled).Entry) (M N : Multiset (Location × Atom)),
      (transactions selects enabled).Fires path M N →
        (theory selects enabled).MultiStep (networkOf M) (networkOf N)
  | [], M, N, fires => by
      change N = M at fires
      subst fires
      exact .refl _
  | entry :: rest, M, N, fires => by
      apply GSLT.MultiStep.step
      · apply (step_networkOf_iff selects enabled M _).mpr
        exact ⟨_, rfl, entry.1, entry.2, fires.1, rfl⟩
      · exact fires_networkOf_multiStep selects enabled rest _ N fires.2

/-- Every finite guarded execution starting from a finite bag retains a
finite bag presentation and an actual resource-firing history. The target
network is arbitrary, so this also proves closure of the presentation. -/
theorem multiStep_networkOf_iff (selects : Selection Location Atom Pattern Environment)
    (enabled : Command Location Atom Pattern Environment → Prop)
    (M : Multiset (Location × Atom)) (target : Network Location Atom) :
    (theory selects enabled).MultiStep (networkOf M) target ↔
      ∃ path N, target = networkOf N ∧ (transactions selects enabled).Fires path M N := by
  constructor
  · intro execution
    have reflect : ∀ {source target}, (theory selects enabled).MultiStep source target →
        ∀ M, source = networkOf M →
          ∃ path N, target = networkOf N ∧ (transactions selects enabled).Fires path M N := by
      intro source target execution
      induction execution with
      | refl source =>
          intro M same
          exact ⟨[], M, same, rfl⟩
      | @step source middle target first _ ih =>
          intro M same
          rw [same] at first
          obtain ⟨N, rfl, site, occurrence, fits, rfl⟩ :=
            (step_networkOf_iff selects enabled M middle).mp first
          obtain ⟨path, final, reached, fires⟩ := ih _ rfl
          exact ⟨⟨site, occurrence⟩ :: path, final, reached, fits, fires⟩
    exact reflect execution M rfl
  · rintro ⟨path, N, rfl, fires⟩
    exact fires_networkOf_multiStep selects enabled path M N fires

/-- Exhaustion on bags is exactly quiescence of the guarded transaction
network. It does not depend on the catalogue or on a scheduler budget. -/
theorem normalForm_networkOf_iff (selects : Selection Location Atom Pattern Environment)
    (enabled : Command Location Atom Pattern Environment → Prop)
    (M : Multiset (Location × Atom)) :
    (theory selects enabled).IsNormalForm (networkOf M) ↔
      ∀ entry : (transactions selects enabled).Entry,
        ¬(transactions selects enabled).Enables M entry.2 := by
  constructor
  · intro normal entry fits
    exact normal ⟨_, (step_networkOf_iff selects enabled M _).mpr
      ⟨_, rfl, entry.1, entry.2, fits, rfl⟩⟩
  · intro exhausted ⟨target, step⟩
    obtain ⟨N, _, site, choice, fits, _⟩ :=
      (step_networkOf_iff selects enabled M target).mp step
    exact exhausted ⟨site, choice⟩ fits

/-- A published current-world search result is reached through actual
transactions and is quiescent there. The catalogue must cover enabled
choices in every reached bag; an initially complete list alone is insufficient. -/
theorem state_emission_networkOf (selects : Selection Location Atom Pattern Environment)
    (enabled : Command Location Atom Pattern Environment → Prop)
    (catalogueAt : Multiset (Location × Atom) → List (transactions selects enabled).Entry)
    (complete : (transactions selects enabled).StateCatalogueComplete catalogueAt)
    (scheduler : Core.BranchingTemporal.Scheduler
      (List (transactions selects enabled).Entry × Multiset (Location × Atom)))
    (fuel : Nat) (M : Multiset (Location × Atom))
    (event : Core.BranchingTemporal.Emission
      (List (transactions selects enabled).Entry × Multiset (Location × Atom))
      (List (transactions selects enabled).Entry × Multiset (Location × Atom)))
    (member : event ∈ (Core.BranchingTemporal.run
      ((transactions selects enabled).stateSearch catalogueAt) scheduler fuel
      (Core.BranchingTemporal.initial [([], M)])).events) :
    (theory selects enabled).MultiStep (networkOf M) (networkOf event.value.2) ∧
      (theory selects enabled).IsNormalForm (networkOf event.value.2) := by
  obtain ⟨_, fires, terminal⟩ :=
    (transactions selects enabled).state_emitted_is_run catalogueAt complete
      scheduler fuel M event member
  exact ⟨fires_networkOf_multiStep selects enabled _ _ _ fires,
    (normalForm_networkOf_iff selects enabled _).mpr terminal⟩

/-- Every finite terminal execution of the original guarded theory is
represented in the weighted handler. A complete catalogue is needed at each
descendant world, and zero coefficients do not remove the returned history. -/
theorem graded_return_of_guarded_execution {V : Type*} [Monoid V]
    (selects : Selection Location Atom Pattern Environment)
    (enabled : Command Location Atom Pattern Environment → Prop)
    (catalogueAt : Multiset (Location × Atom) → List (transactions selects enabled).Entry)
    (coefficient : (List (transactions selects enabled).Entry × Multiset (Location × Atom)) →
      (transactions selects enabled).Entry → V)
    (complete : (transactions selects enabled).StateCatalogueComplete catalogueAt)
    (M : Multiset (Location × Atom)) (target : Network Location Atom)
    (execution : (theory selects enabled).MultiStep (networkOf M) target)
    (terminal : (theory selects enabled).IsNormalForm target) :
    ∃ path N fuel value, target = networkOf N ∧
      (.inl (path, N), value) ∈ Dynamics.WeightedBranchingResumption.contributions
        ((transactions selects enabled).gradedStateSource catalogueAt coefficient) fuel ([], M) := by
  obtain ⟨path, N, reached, fires⟩ :=
    (multiStep_networkOf_iff selects enabled M target).mp execution
  have exhausted := (normalForm_networkOf_iff selects enabled N).mp (reached ▸ terminal)
  obtain ⟨fuel, value, present⟩ := (transactions selects enabled).graded_return_of_fires
    catalogueAt coefficient complete fires exhausted
  exact ⟨path, N, fuel, value, reached, present⟩

/-- The shared weighted handler retains actual guarded executions in both
completed and suspended leaves. Only a completed world carries quiescence. -/
theorem graded_leaf_networkOf {V : Type*} [Monoid V]
    (selects : Selection Location Atom Pattern Environment)
    (enabled : Command Location Atom Pattern Environment → Prop)
    (catalogueAt : Multiset (Location × Atom) → List (transactions selects enabled).Entry)
    (coefficient : (List (transactions selects enabled).Entry × Multiset (Location × Atom)) →
      (transactions selects enabled).Entry → V)
    (complete : (transactions selects enabled).StateCatalogueComplete catalogueAt)
    (M : Multiset (Location × Atom)) (fuel : Nat)
    (leaf : ((List (transactions selects enabled).Entry × Multiset (Location × Atom)) ⊕
      (List (transactions selects enabled).Entry × Multiset (Location × Atom))) × V)
    (member : leaf ∈ Dynamics.WeightedBranchingResumption.contributions
      ((transactions selects enabled).gradedStateSource catalogueAt coefficient) fuel ([], M)) :
    Sum.elim
      (fun done => (theory selects enabled).MultiStep (networkOf M) (networkOf done.2) ∧
        (theory selects enabled).IsNormalForm (networkOf done.2))
      (fun pending => (theory selects enabled).MultiStep (networkOf M) (networkOf pending.2))
      leaf.1 := by
  have valid := (transactions selects enabled).graded_contributions_valid catalogueAt
    coefficient complete M fuel ([], M) rfl leaf member
  cases located : leaf.1 with
  | inl done =>
      simp only [located, Sum.elim_inl] at valid ⊢
      exact ⟨fires_networkOf_multiStep selects enabled _ _ _ valid.1,
        (normalForm_networkOf_iff selects enabled _).mpr valid.2⟩
  | inr pending =>
      simp only [located, Sum.elim_inr] at valid ⊢
      exact fires_networkOf_multiStep selects enabled _ _ _ valid

/-! ## The direct communication of the MeTTa-calculus -/

section DirectContact

open DirectCommBridge

/-- The direct contact of two guarded parties, as a firing. -/
def contact (location : Name) (left right : GuardedParty) (substitution : Bindings)
    (unifies : unifyPattern? left.term right.term = some substitution) :
    Choice directSelection (directCommand location left right) :=
  ⟨([.party left, .party right], substitution), rfl,
    ⟨location, left, right, rfl, rfl, unifies⟩⟩

/-- **Direct communication claims both parties** and observes nothing. -/
theorem contact_claims_both (location : Name) (left right : GuardedParty)
    (substitution : Bindings) (unifies : unifyPattern? left.term right.term = some substitution) :
    claims (directCommand location left right).guards
        (contact location left right substitution unifies).1.1 =
      {(some location, .party left), (some location, .party right)} ∧
    sightings (directCommand location left right).guards
        (contact location left right substitution unifies).1.1 = 0 :=
  ⟨rfl, rfl⟩

/-- **Two contacts claiming one party conflict.** When the party is present once,
the contacts are not concurrent, and after either the other is disabled. -/
theorem contacts_sharing_a_party_conflict
    (enabled : Command ContactLocation ContactOccurrence GuardedParty Bindings → Prop)
    (location : Name) (left right right' : GuardedParty) (substitution substitution' : Bindings)
    (unifies : unifyPattern? left.term right.term = some substitution)
    (unifies' : unifyPattern? left.term right'.term = some substitution')
    (commandEnabled : enabled (directCommand location left right))
    (commandEnabled' : enabled (directCommand location left right'))
    (M : Multiset (ContactLocation × ContactOccurrence))
    (once : M.count (some location, .party left) ≤ 1) :
    ¬ (transactions directSelection enabled).Concurrent M
        (site₁ := ⟨_, commandEnabled⟩) (site₂ := ⟨_, commandEnabled'⟩)
        (contact location left right substitution unifies)
        (contact location left right' substitution' unifies') :=
  (transactions directSelection enabled).not_concurrent_of_shared_consumption M
    (site₁ := ⟨_, commandEnabled⟩) (site₂ := ⟨_, commandEnabled'⟩) _ _
    (some location, .party left)
    (by simp [transactions, contact, directCommand, claims])
    (by simp [transactions, contact, directCommand, claims]) once

end DirectContact

/-! ## Single requests: commuting squares are concurrency -/

/-- A located request as a firing: it claims or reads its occurrence and
publishes nothing. -/
def requests : System (Location × Atom) where
  Site := Unit
  Instance := fun _ => Request Location Atom
  consume := fun request => match request.mode with
    | .consume => {(request.location, request.atom)}
    | .observe => 0
  read := fun request => match request.mode with
    | .consume => 0
    | .observe => {(request.location, request.atom)}
  produce := fun _ => 0

/-- A request as an instance of `requests`. -/
def asFiring (request : Request Location Atom) : (requests (Location := Location) (Atom := Atom)).Instance () :=
  request

theorem request_steps_iff (request : Request Location Atom) (M : Multiset (Location × Atom))
    (target : Network Location Atom) :
    request.Steps (networkOf M) target ↔
      requests.Enables M (asFiring request) ∧ target = networkOf (requests.fire M (asFiring request)) := by
  obtain ⟨mode, location, atom⟩ := request
  cases mode with
  | observe =>
      change LocatedStep .observe location atom (networkOf M) target ↔
        0 + {(location, atom)} ≤ M ∧ target = networkOf (M - 0 + 0)
      rw [LocatedStep.observe_iff, zero_add, Multiset.singleton_le, tsub_zero, add_zero,
        mem_networkOf]
  | consume =>
      change LocatedStep .consume location atom (networkOf M) target ↔
        {(location, atom)} + 0 ≤ M ∧ target = networkOf (M - {(location, atom)} + 0)
      rw [LocatedStep.consume_iff, add_zero, Multiset.singleton_le, add_zero,
        Multiset.sub_singleton]
      constructor
      · rintro ⟨rest, atLocation, rfl⟩
        have present : atom ∈ networkOf M location := by
          rw [atLocation]
          exact Multiset.mem_cons_self _ _
        refine ⟨mem_networkOf.mp present, ?_⟩
        rw [networkOf_erase, atLocation, Multiset.erase_cons_head]
      · rintro ⟨member, rfl⟩
        refine ⟨(networkOf M location).erase atom,
          (Multiset.cons_erase (mem_networkOf.mpr member)).symm, ?_⟩
        rw [networkOf_erase]

/-- **For single requests, a commuting square of the two orders is exactly
concurrency.** -/
theorem coexecutible_iff_concurrent (first second : Request Location Atom)
    (M : Multiset (Location × Atom)) :
    Request.Coexecutible first second (networkOf M) ↔
      requests.Concurrent M (asFiring first) (asFiring second) := by
  constructor
  · rintro ⟨square⟩
    obtain ⟨enabledFirst, afterFirstEq⟩ :=
      (request_steps_iff first M square.afterFirst).mp square.firstFromSource
    obtain ⟨enabledSecond, afterSecondEq⟩ :=
      (request_steps_iff second M square.afterSecond).mp square.secondFromSource
    have secondAfterFirst := square.secondAfterFirst
    have firstAfterSecond := square.firstAfterSecond
    rw [afterFirstEq] at secondAfterFirst
    rw [afterSecondEq] at firstAfterSecond
    obtain ⟨secondAfter, joinedFromFirst⟩ := (request_steps_iff second _ _).mp secondAfterFirst
    obtain ⟨firstAfter, joinedFromSecond⟩ := (request_steps_iff first _ _).mp firstAfterSecond
    refine requests.concurrent_of_square M _ _ (fun _ absent => absurd absent (by simp [requests]))
      (fun _ absent => absurd absent (by simp [requests])) ⟨enabledFirst, enabledSecond,
        secondAfter, firstAfter, networkOf_injective (joinedFromFirst.symm.trans joinedFromSecond)⟩
  · intro concurrent
    have square := requests.square_of_concurrent concurrent
    exact ⟨⟨networkOf (requests.fire M (asFiring first)),
      networkOf (requests.fire M (asFiring second)),
      networkOf (requests.fire (requests.fire M (asFiring first)) (asFiring second)),
      (request_steps_iff first M _).mpr ⟨square.first, rfl⟩,
      (request_steps_iff second M _).mpr ⟨square.second, rfl⟩,
      (request_steps_iff second _ _).mpr ⟨square.secondAfter, rfl⟩,
      (request_steps_iff first _ _).mpr ⟨square.firstAfter, by rw [square.meet]⟩⟩⟩

/-! ## Controls on the transaction canaries -/

namespace Controls

open Canary

/-- Exact matching fixes the complete selected atom list. -/
private theorem exact_selection_atoms {guards : List (Guard CanaryLocation CanaryAtom)}
    {atoms : List CanaryAtom} {environment : Unit}
    (selected : exactSelection guards atoms environment) :
    atoms = guards.map Guard.pattern := by
  induction selected with
  | nil => rfl
  | cons head _ ih =>
      change _ = _ at head
      simp only [List.map_cons]
      rw [head, ih]

def mixedEntry : (transactions exactSelection Canary.enabled).Entry :=
  ⟨⟨mixedCommand, Or.inl rfl⟩,
    ⟨([.exec, .fact], ()), rfl, .cons rfl (.cons rfl .nil)⟩⟩

def followupEntry : (transactions exactSelection Canary.enabled).Entry :=
  ⟨⟨followupCommand, Or.inr rfl⟩,
    ⟨([.nextExec, .answer], ()), rfl, .cons rfl (.cons rfl .nil)⟩⟩

/-- Discovery uses the current world's atoms, including newly published work. -/
def currentCandidates (M : Multiset (CanaryLocation × CanaryAtom)) :
    List (transactions exactSelection Canary.enabled).Entry :=
  (transactions exactSelection Canary.enabled).enabledAt [mixedEntry, followupEntry] M

/-- This concrete catalogue covers every enabled command and binding choice,
rather than relying on an uninhabited completeness premise. -/
theorem current_candidates_complete :
    (transactions exactSelection Canary.enabled).StateCatalogueComplete currentCandidates := by
  rintro M ⟨⟨command, commandEnabled⟩, choice⟩ fits
  apply List.mem_filter.mpr
  refine ⟨?_, ((transactions exactSelection Canary.enabled).enabledB_iff M _).mpr fits⟩
  rcases commandEnabled with rfl | rfl
  · have selectedAtoms := exact_selection_atoms choice.2.2
    have same : choice = mixedEntry.2 := by
      apply Subtype.ext
      exact Prod.ext selectedAtoms (Subsingleton.elim _ _)
    subst same
    simp [mixedEntry]
  · have selectedAtoms := exact_selection_atoms choice.2.2
    have same : choice = followupEntry.2 := by
      apply Subtype.ext
      exact Prod.ext selectedAtoms (Subsingleton.elim _ _)
    subst same
    simp [followupEntry]

def initialWorld : Multiset (CanaryLocation × CanaryAtom) :=
  {(.control, .exec), (.data, .fact)}

def finishedWorld : Multiset (CanaryLocation × CanaryAtom) :=
  {(.data, .fact), (.output, .answer), (.output, .done)}

/-- The shared scheduler discovers and executes the continuation's directive.
The fact and earlier answer persist in the completed world. -/
theorem current_world_runs_both_transactions :
    Core.BranchingTemporal.run
      ((transactions exactSelection Canary.enabled).stateSearch currentCandidates)
      Core.BranchingTemporal.Scheduler.depthFirst 3
      (Core.BranchingTemporal.initial [([], initialWorld)]) =
    ⟨[⟨([mixedEntry, followupEntry], finishedWorld),
       ([mixedEntry, followupEntry], finishedWorld)⟩], []⟩ := by
  rfl

/-- The result of the actual search is a genuine guarded-transaction run and
is quiescent in that independently defined theory. -/
theorem discovered_world_is_guarded_execution :
    (theory exactSelection Canary.enabled).MultiStep
      (networkOf initialWorld) (networkOf finishedWorld) ∧
    (theory exactSelection Canary.enabled).IsNormalForm (networkOf finishedWorld) := by
  apply state_emission_networkOf exactSelection Canary.enabled currentCandidates
    current_candidates_complete Core.BranchingTemporal.Scheduler.depthFirst 3 initialWorld
    ⟨([mixedEntry, followupEntry], finishedWorld),
      ([mixedEntry, followupEntry], finishedWorld)⟩
  rw [current_world_runs_both_transactions]
  exact List.mem_cons_self

/-- An initial-only catalogue publishes the first continuation's world,
which still has an actual enabled guarded transaction. -/
theorem frozen_catalogue_publishes_nonterminal_world :
    Core.BranchingTemporal.run
      ((transactions exactSelection Canary.enabled).search (currentCandidates initialWorld))
      Core.BranchingTemporal.Scheduler.depthFirst 2
      (Core.BranchingTemporal.initial [([], initialWorld)]) =
      ⟨[⟨([mixedEntry], (transactions exactSelection Canary.enabled).fire initialWorld mixedEntry.2),
         ([mixedEntry], (transactions exactSelection Canary.enabled).fire initialWorld mixedEntry.2)⟩], []⟩ ∧
    ¬ (theory exactSelection Canary.enabled).IsNormalForm
      (networkOf ((transactions exactSelection Canary.enabled).fire initialWorld mixedEntry.2)) := by
  constructor
  · rfl
  · intro normal
    apply ((normalForm_networkOf_iff exactSelection Canary.enabled _).mp normal) followupEntry
    unfold System.Enables
    decide

/-- Every command of the controls may fire. -/
def always (_command : Command CanaryLocation CanaryAtom CanaryAtom Unit) : Prop := True

/-- An MM2-shaped transaction on a second directive, observing the same fact. -/
def secondDirective : Command CanaryLocation CanaryAtom CanaryAtom Unit where
  guards := [⟨.consume, .control, .nextExec⟩, ⟨.observe, .data, .fact⟩]
  continuation _ := [⟨.output, .done⟩]

def firstFiring : (transactions exactSelection always).Instance ⟨mixedCommand, trivial⟩ :=
  ⟨([.exec, .fact], ()), rfl, .cons rfl (.cons rfl .nil)⟩

def secondFiring : (transactions exactSelection always).Instance ⟨secondDirective, trivial⟩ :=
  ⟨([.nextExec, .fact], ()), rfl, .cons rfl (.cons rfl .nil)⟩

/-- Two directives and one fact. -/
def twoDirectives : Multiset (CanaryLocation × CanaryAtom) :=
  {(.control, .exec), (.control, .nextExec), (.data, .fact)}

/-- **Transactions observing one fact are concurrent.** Each claims its own
directive; the fact, present once, is read by both. -/
theorem shared_fact_concurrent :
    (transactions exactSelection always).Concurrent twoDirectives firstFiring secondFiring := by
  unfold System.Concurrent
  decide

def claimAndObserve : (transactions exactSelection always).Instance
    ⟨consumeThenObserve, trivial⟩ :=
  ⟨([.fact, .fact], ()), rfl, .cons rfl (.cons rfl .nil)⟩

/-- **A firing observes what it claims without a second copy.** The observation
checks the snapshot, so the one stored fact is claimed and observed; reading it
beside the claim would need two copies. -/
theorem snapshot_observes_its_claim :
    (transactions exactSelection always).Enables (site := ⟨consumeThenObserve, trivial⟩)
        {(.data, .fact)} claimAndObserve ∧
      ¬ claims consumeThenObserve.guards claimAndObserve.1.1 +
          sightings consumeThenObserve.guards claimAndObserve.1.1 ≤
        ({(.data, .fact)} : Multiset (CanaryLocation × CanaryAtom)) := by
  constructor
  · unfold System.Enables
    decide
  · decide

/-- Claim a fact and publish it again. -/
def republishFact : Command CanaryLocation CanaryAtom CanaryAtom Unit where
  guards := [⟨.consume, .data, .fact⟩]
  continuation _ := [⟨.data, .fact⟩]

def republishing : (transactions exactSelection always).Instance ⟨republishFact, trivial⟩ :=
  ⟨([.fact], ()), rfl, .cons rfl .nil⟩

def oneFact : Multiset (CanaryLocation × CanaryAtom) := {(.data, .fact)}

/-- **A square without concurrency.** Two firings that take the one fact and
publish it again run in either order and meet, but they cannot run together. -/
theorem republishing_square_not_concurrent :
    (transactions exactSelection always).Square oneFact republishing republishing ∧
      ¬ (transactions exactSelection always).Concurrent oneFact republishing republishing := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · unfold System.Enables; decide
  · unfold System.Enables; decide
  · unfold System.Enables System.fire; decide
  · unfold System.Enables System.fire; decide
  · rfl
  · unfold System.Concurrent; decide

end Controls

#print axioms count_networkOf
#print axioms consumes_sound
#print axioms consumes_complete
#print axioms observes_iff
#print axioms snapshot_enables_iff
#print axioms fires_networkOf_iff
#print axioms step_networkOf_iff
#print axioms fires_networkOf_multiStep
#print axioms multiStep_networkOf_iff
#print axioms normalForm_networkOf_iff
#print axioms state_emission_networkOf
#print axioms graded_return_of_guarded_execution
#print axioms graded_leaf_networkOf
#print axioms Controls.current_candidates_complete
#print axioms Controls.discovered_world_is_guarded_execution
#print axioms Controls.frozen_catalogue_publishes_nonterminal_world
#print axioms contacts_sharing_a_party_conflict
#print axioms request_steps_iff
#print axioms coexecutible_iff_concurrent
#print axioms Controls.shared_fact_concurrent
#print axioms Controls.snapshot_observes_its_claim
#print axioms Controls.republishing_square_not_concurrent

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.TransactionResources
