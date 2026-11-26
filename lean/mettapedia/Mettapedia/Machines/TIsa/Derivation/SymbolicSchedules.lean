import Mettapedia.Machines.TIsa.Derivation.SnapshotMachine
import Mettapedia.Machines.TIsa.Derivation.SymbolicRound
import Mettapedia.Machines.TIsa.Derivation.SymbolicScheduleSearch

/-!
# One symbolic machine, several scheduling disciplines

Only selection changes with the discipline. All disciplines open
their members at the entry snapshot, find a principal solution, and
check it before one atomic publication. The controller does not run
any member against a partly published batch. The round checker may
inspect serial outcomes privately; none is an external publication.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.SymbolicSchedules

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RuleSyntax.OneFrame (Terms ext)
open RuleSyntax.JointFirings (Bag bagOf)
open RuleSyntax.JointFirings.SymmetricMatches (WordResultModel)
open RuleSyntax.StepWeb.Rounds (RuntimeRound admitsOwn_of_runtimeRound)
open SymbolicFiring (Rules LiveWorld act)
open SymbolicBatch (Request Prepared requestBatch prepareRequests prepared_batch publishRequests)

variable {signature : LPSignature} {rules : Rules signature}

universe uKey

inductive Discipline (rules : Rules signature) where
  | round
  | synchronous
  | joint
  | every (keying : SymbolicComplete.Keying.{uKey, _, _} rules) (region : keying.identity.Key → Bool)
  | maximal
  | unique (keying : SymbolicComplete.Keying.{uKey, _, _} rules) (region : keying.identity.Key → Bool)

def Discipline.reading : Discipline rules → SymbolicBatch.Reading
  | .round | .every .. | .unique .. => .memberOwn
  | .synchronous => .snapshot
  | .joint | .maximal => .joint

abbrev Population (rules : Rules signature) := List (Request rules.program)
abbrev ObservedBag (before : LiveWorld signature) (rules : Rules signature) :=
  Bag ℕ (ext (FirstOrder.action signature)) rules.program before.state.frame

def Allows (policy : Discipline rules) (before : LiveWorld signature)
    (batch : ObservedBag before rules) : Prop :=
  match policy with
  | .round => RuntimeRound (FirstOrder.action signature) before.state batch.members
  | .synchronous => batch.AdmitsSnapshot (act signature) before.state
  | .joint => batch.Admits (act signature) before.state
  | .every keying region => SymbolicComplete.Admits keying before region .every batch
  | .maximal => batch.AdmitsMaximal (act signature) before.state
  | .unique keying region => SymbolicComplete.Admits keying before region .unique batch

private theorem bagOf_members {before : LiveWorld signature} (batch : ObservedBag before rules) :
    bagOf (FirstOrder.action signature) batch.members = batch := by
  obtain ⟨extension, members⟩ := batch
  cases extension
  rfl

variable [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
  (slots : signature.vars ≃ ℕ) (policy : Discipline rules)
  {before : LiveWorld signature}

omit [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
theorem Allows.reading (selection : Prepared (program := rules.program) before.state)
    (allowed : Allows policy before selection.batch) : SymbolicBatch.Admits policy.reading selection := by
  cases policy with
  | round =>
    have own := admitsOwn_of_runtimeRound (FirstOrder.action signature) allowed
    change selection.batch.AdmitsOwn (act signature) before.state
    exact (bagOf_members selection.batch) ▸ own
  | synchronous => exact allowed
  | joint => exact allowed
  | every keying region =>
    change selection.batch.AdmitsEveryBy (act signature) before.state keying.identity { k | region k = true } at allowed
    exact allowed.1
  | maximal => exact allowed.1
  | unique keying region =>
    change selection.batch.AdmitsUniqueBy (act signature) before.state keying.identity { k | region k = true } at allowed
    exact allowed.1.1

def demandOK (selection : Prepared (program := rules.program) before.state)
    (entry : SymbolicBatch.Admits policy.reading selection) : Bool :=
  match policy with
  | .round =>
    SymbolicRound.roundOK before.state selection.batch.members ((bagOf_members selection.batch).symm ▸ entry)
  | .synchronous | .joint => true
  | .every keying region => SymbolicComplete.demandOK slots keying before region .every selection.batch
  | .maximal => SymbolicScheduleSearch.maximalOK before slots rules selection.batch
  | .unique keying region => SymbolicComplete.demandOK slots keying before region .unique selection.batch

theorem demandOK_exact (selection : Prepared (program := rules.program) before.state)
    (entry : SymbolicBatch.Admits policy.reading selection) :
    demandOK slots policy selection entry = true ↔ Allows policy before selection.batch := by
  cases policy with
  | round => exact SymbolicRound.roundOK_exact _ _ _
  | synchronous => exact ⟨fun _ => entry, fun _ => rfl⟩
  | joint => exact ⟨fun _ => entry, fun _ => rfl⟩
  | every keying region => exact SymbolicComplete.demandOK_exact slots keying before region .every selection entry
  | maximal => exact SymbolicScheduleSearch.maximalOK_exact before slots rules selection.batch entry
  | unique keying region => exact SymbolicComplete.demandOK_exact slots keying before region .unique selection entry

structure Reserved (rules : Rules signature) (before : LiveWorld signature) where
  selection : Prepared (program := rules.program) before.state
  allocation : selection.batch.selection.made = before.reserve 0 selection.batch.selection.made.length

private def reserve (requests : Population rules) (selection : Prepared (program := rules.program) before.state)
    (prepared : prepareRequests before slots requests = some selection) : Reserved rules before where
  selection := selection
  allocation := by
    rw [prepared_batch before slots requests prepared]
    exact SymbolicBatch.requestBatch_reserved before slots requests

structure Resolved (rules : Rules signature) (before : LiveWorld signature) where
  reservation : Reserved rules before
  answer : Subst signature
  solved : unifyTotal (reservation.selection.batch.information (act signature) before.state) = some answer

structure Accepted (policy : Discipline rules) (before : LiveWorld signature) where
  resolved : Resolved rules before
  allowed : Allows policy before resolved.reservation.selection.batch

def resolve (reservation : Reserved rules before) : Option (Resolved rules before) :=
  match solved : unifyTotal (reservation.selection.batch.information (act signature) before.state) with
  | none => none
  | some answer => some ⟨reservation, answer, solved⟩

def prepare (requests : Population rules) : Option (Resolved rules before) :=
  match prepared : prepareRequests before slots requests with
  | none => none
  | some selection => resolve (reserve slots requests selection prepared)

def verify (pending : Resolved rules before) : Option (Accepted policy before) :=
  let selection := pending.reservation.selection
  if passes : SymbolicBatch.permits policy.reading selection pending.answer = true then
    let entry := (SymbolicBatch.permits_exact policy.reading selection pending.answer pending.solved).mp passes
    if chosen : demandOK slots policy selection entry = true then
      some ⟨pending, (demandOK_exact slots policy selection entry).mp chosen⟩
    else none
  else none

theorem verify_of_allows (pending : Resolved rules before)
    (allowed : Allows policy before pending.reservation.selection.batch) :
    verify slots policy pending = some ⟨pending, allowed⟩ := by
  have entry := Allows.reading policy pending.reservation.selection allowed
  have passes := (SymbolicBatch.permits_exact _ _ _ pending.solved).mpr entry
  have chosen := (demandOK_exact slots policy _ entry).mpr allowed
  simp only [verify, dif_pos passes, dif_pos chosen]

def Accepted.publish {policy : Discipline rules} (accepted : Accepted policy before) : LiveWorld signature :=
  let ready := accepted.resolved.reservation
  before.commitDelta ready.selection.batch.selection (ready.selection.batch.result (act signature) before.state)
    rfl ready.allocation

theorem Accepted.principal {policy : Discipline rules} (accepted : Accepted policy before) :
    (FirstOrder.action signature).Principal accepted.publish.state.knowledge accepted.resolved.answer :=
  FirstOrder.accepted_principal _ _ accepted.resolved.solved

private theorem verify_keeps_solution {pending : Resolved rules before} {accepted : Accepted policy before}
    (found : verify slots policy pending = some accepted) : accepted.resolved = pending := by
  unfold verify at found
  dsimp only at found
  split at found
  · split at found
    · exact congrArg Accepted.resolved (Option.some.inj found).symm
    · cases found
  · cases found

private theorem resolve_keeps_reservation {reservation : Reserved rules before} {resolved : Resolved rules before}
    (found : resolve reservation = some resolved) : resolved.reservation = reservation := by
  unfold resolve at found
  split at found
  · cases found
  · exact congrArg Resolved.reservation (Option.some.inj found).symm

theorem prepare_geometry {requests : Population rules} {found : Resolved rules before}
    (ready : prepare slots requests = some found) :
    requests ≠ [] ∧ found.reservation.selection.batch = requestBatch before slots requests := by
  unfold prepare at ready
  split at ready
  · cases ready
  · rename_i selection prepared
    have existsReady : (prepareRequests before slots requests).isSome = true := by rw [prepared]; rfl
    refine ⟨((SymbolicBatch.prepareRequests_some_iff before slots requests).mp existsReady).1, ?_⟩
    rw [resolve_keeps_reservation ready]
    exact prepared_batch before slots requests prepared

private theorem solve_of_reserved {reservation : Reserved rules before} {answer : Subst signature}
    (solved : unifyTotal (reservation.selection.batch.information (act signature) before.state) = some answer) :
    ∃ resolved, resolve reservation = some resolved := by
  unfold resolve
  split
  · rename_i missing
    rw [solved] at missing
    cases missing
  · exact ⟨_, rfl⟩

private theorem prepare_of_allowed (requests : Population rules) (nonempty : requests ≠ [])
    (allowed : Allows policy before (requestBatch before slots requests)) :
    ∃ resolved, prepare slots requests = some resolved ∧ Allows policy before resolved.reservation.selection.batch := by
  have fits : (requestBatch before slots requests).Fits (act signature) before.state := by
    cases policy with
    | round =>
      have joint : (bagOf (FirstOrder.action signature) (requestBatch before slots requests).members).Admits
          (act signature) before.state := allowed.1
      exact bagOf_members (requestBatch before slots requests) ▸ joint.1
    | synchronous => exact allowed.1
    | joint => exact allowed.1
    | every _ _ => exact allowed.1.1
    | maximal => exact allowed.1.1
    | unique _ _ => exact allowed.1.1.1
  have existsReady := (SymbolicBatch.prepareRequests_some_iff before slots requests).mpr ⟨nonempty, fits.2.1⟩
  obtain ⟨selection, prepared⟩ := Option.isSome_iff_exists.mp existsReady
  obtain ⟨resolved, found⟩ : ∃ resolved, prepare slots requests = some resolved := by
    unfold prepare
    split
    · rename_i missing
      rw [prepared] at missing
      cases missing
    · rename_i actual lookup
      have admitted : Allows policy before actual.batch := (prepared_batch before slots requests lookup) ▸ allowed
      have base := Allows.reading policy actual admitted
      obtain ⟨answer, computed⟩ := SymbolicBatch.admitted_has_result policy.reading actual base
      have solved := ((SymbolicBatch.evaluate_exact policy.reading actual answer _).mp computed).1
      exact solve_of_reserved (reservation := reserve slots requests actual lookup) solved
  exact ⟨resolved, found, (prepare_geometry slots found).2 ▸ allowed⟩

omit [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
private theorem publish_congr {source target : ObservedBag before rules}
    (same : source = target)
    (left : source.selection.made = before.reserve 0 source.selection.made.length)
    (right : target.selection.made = before.reserve 0 target.selection.made.length) :
    before.commitDelta source.selection (source.result (act signature) before.state) rfl left =
      before.commitDelta target.selection (target.result (act signature) before.state) rfl right := by
  cases same
  rfl

theorem publish_geometry (requests : Population rules) (accepted : Accepted policy before)
    (same : accepted.resolved.reservation.selection.batch = requestBatch before slots requests) :
    accepted.publish = publishRequests before slots requests :=
  publish_congr same accepted.resolved.reservation.allocation (SymbolicBatch.requestBatch_reserved before slots requests)

/-- The finite population of proposed batches up to a declared width.
This width limits only proposals; completeness and maximality still ask
about the original snapshot, not just the narrower set of proposals. -/
def options (rules : Rules signature) (width : ℕ) (before : LiveWorld signature) : List (Population rules) :=
  (List.range width).flatMap fun size => SymbolicScheduleSearch.atWidth before rules (size + 1)

omit [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
theorem mem_options (rules : Rules signature) (width : ℕ) (before : LiveWorld signature)
    (requests : Population rules) :
    requests ∈ options rules width before ↔ requests ≠ [] ∧ requests.length ≤ width ∧
      requests ∈ SymbolicScheduleSearch.atWidth before rules requests.length := by
  constructor
  · intro offered
    obtain ⟨size, below, listed⟩ := List.mem_flatMap.mp offered
    have length := ((SymbolicFiring.mem_tuples _ _ _).mp listed).1
    refine ⟨fun empty => ?_, length ▸ Nat.succ_le_of_lt (List.mem_range.mp below), ?_⟩
    · rw [empty] at length
      cases length
    · exact length ▸ listed
  · rintro ⟨nonempty, below, listed⟩
    cases length : requests.length with
    | zero => exact (nonempty (List.eq_nil_of_length_eq_zero length)).elim
    | succ size =>
      exact List.mem_flatMap.mpr ⟨size, List.mem_range.mpr (by omega), length ▸ listed⟩

def phases (policy : Discipline rules) : SnapshotMachine.Phases (LiveWorld signature) where
  Candidate _ := Population rules
  Pending := Resolved rules
  Accepted := Accepted policy

def schedule (width : ℕ) : SnapshotMachine.Schedule (phases policy) where
  options := options rules width
  prepare := prepare slots
  verify := verify slots policy
  publish := Accepted.publish

theorem candidate_exact (width : ℕ) (requests : Population rules) :
    (SnapshotMachine.candidateResult (schedule slots policy width) (before := before) requests).isSome = true ↔
      requests ≠ [] ∧ Allows policy before (requestBatch before slots requests) := by
  constructor
  · intro result
    obtain ⟨accepted, found⟩ := Option.isSome_iff_exists.mp result
    change (prepare (before := before) slots requests).bind (verify slots policy) = some accepted at found
    obtain ⟨pending, prepared, checked⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨nonempty, source⟩ := prepare_geometry slots prepared
    have geometry : accepted.resolved.reservation.selection.batch = requestBatch before slots requests := by
      rw [verify_keeps_solution slots policy checked]
      exact source
    exact ⟨nonempty, geometry ▸ accepted.allowed⟩
  · rintro ⟨nonempty, allowed⟩
    obtain ⟨pending, resolved, licensed⟩ := prepare_of_allowed slots policy requests nonempty allowed
    apply Option.isSome_iff_exists.mpr
    refine ⟨⟨pending, licensed⟩, ?_⟩
    change (prepare (before := before) slots requests).bind (verify slots policy) = _
    rw [resolved, Option.bind_some, verify_of_allows slots policy pending licensed]
    rfl

def EnabledAt (width : ℕ) (before : LiveWorld signature) : Prop :=
  ∃ requests ∈ options rules width before, Allows policy before (requestBatch before slots requests)

def Moves (width : ℕ) (before after : LiveWorld signature) : Prop :=
  ∃ requests ∈ options rules width before,
    Allows policy before (requestBatch before slots requests) ∧ after = publishRequests before slots requests

theorem search_empty_iff (width : ℕ) (before : LiveWorld signature) :
    SnapshotMachine.search (schedule slots policy width) before = none ↔ ¬EnabledAt slots policy width before := by
  rw [SnapshotMachine.search, List.findSome?_eq_none_iff]
  constructor
  · intro empty ⟨requests, proposed, allowed⟩
    have nonempty := ((mem_options rules width before requests).mp proposed).1
    have found := (candidate_exact (before := before) slots policy width requests).mpr ⟨nonempty, allowed⟩
    have refused := empty requests proposed
    rw [refused] at found
    cases found
  · intro disabled requests proposed
    cases checked : SnapshotMachine.candidateResult (schedule slots policy width) (before := before) requests with
    | none => rfl
    | some accepted =>
      have found := (candidate_exact (before := before) slots policy width requests).mp (by rw [checked]; rfl)
      exact (disabled ⟨requests, proposed, found.2⟩).elim

theorem search_sound (width : ℕ) {accepted : Accepted policy before}
    (computed : SnapshotMachine.search (schedule slots policy width) before = some accepted) :
    EnabledAt slots policy width before ∧ Moves slots policy width before accepted.publish := by
  obtain ⟨requests, listed, onCandidate⟩ := List.exists_of_findSome?_eq_some computed
  change (prepare (before := before) slots requests).bind (verify slots policy) = some accepted at onCandidate
  obtain ⟨pending, prepared, checked⟩ := Option.bind_eq_some_iff.mp onCandidate
  have geometry : accepted.resolved.reservation.selection.batch = requestBatch before slots requests := by
    rw [verify_keeps_solution slots policy checked]
    exact (prepare_geometry slots prepared).2
  have allowed : Allows policy before (requestBatch before slots requests) := geometry ▸ accepted.allowed
  exact ⟨⟨requests, listed, allowed⟩, ⟨requests, listed, allowed, publish_geometry slots policy requests accepted geometry⟩⟩

def SourceEnabled (width : ℕ) (before : LiveWorld signature) : Prop :=
  ∃ batch : ObservedBag before rules,
    batch.members ≠ [] ∧ batch.members.length ≤ width ∧ Allows policy before batch

omit [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
theorem enabled_is_source (width : ℕ) (enabled : EnabledAt slots policy width before) :
    SourceEnabled policy width before := by
  obtain ⟨requests, listed, permitted⟩ := enabled
  have sizes := (mem_options rules width before requests).mp listed
  let batch := requestBatch before slots requests
  have length : batch.members.length = requests.length := SymbolicBatch.requestBatch_width before slots requests
  refine ⟨batch, ?_, length ▸ sizes.2.1, permitted⟩
  intro empty
  have zero : requests.length = 0 := length ▸ congrArg List.length empty
  exact sizes.1 (List.eq_nil_of_length_eq_zero zero)

omit [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
/-- Every discipline admits exact finite search up to the chosen width.
The same pair of renamings transports all serial orders of a round. -/
theorem source_models_covered (width : ℕ)
    (batch : ObservedBag before rules) (nonempty : batch.members ≠ []) (bounded : batch.members.length ≤ width)
    (allowed : Allows policy before batch) :
    ∃ requests ∈ options rules width before, Allows policy before (requestBatch before slots requests) ∧
      ∀ incoming output, WordResultModel before.state batch incoming output ↔
        WordResultModel before.state (requestBatch before slots requests) incoming output := by
  have presentation := bagOf_members batch
  have candidates : ∃ requests ∈ SymbolicScheduleSearch.atWidth before rules batch.members.length,
      Allows policy before (requestBatch before slots requests) ∧
        ∀ incoming output, WordResultModel before.state (bagOf (FirstOrder.action signature) batch.members) incoming output ↔
          WordResultModel before.state (requestBatch before slots requests) incoming output := by
    cases policy with
    | round =>
      obtain ⟨requests, found, license, model⟩ :=
        SymbolicScheduleSearch.atWidth_covers_round_models before slots rules batch.members allowed
      exact ⟨requests, found, license, model⟩
    | synchronous =>
      have original : (bagOf (FirstOrder.action signature) batch.members).AdmitsSnapshot (act signature) before.state :=
        presentation.symm ▸ (show batch.AdmitsSnapshot (act signature) before.state from allowed)
      obtain ⟨requests, found, license, _, model⟩ :=
        SymbolicScheduleSearch.atWidth_covers_snapshot_models before slots rules batch.members original
      exact ⟨requests, found, license, model⟩
    | joint =>
      have original : (bagOf (FirstOrder.action signature) batch.members).Admits (act signature) before.state :=
        presentation.symm ▸ (show batch.Admits (act signature) before.state from allowed)
      obtain ⟨requests, found, license, _, model⟩ :=
        SymbolicScheduleSearch.atWidth_covers_joint_models before slots rules batch.members original
      exact ⟨requests, found, license, model⟩
    | every keying region =>
      have original : (bagOf (FirstOrder.action signature) batch.members).AdmitsEveryBy
          (act signature) before.state keying.identity { k | region k = true } :=
        presentation.symm ▸ (show batch.AdmitsEveryBy (act signature) before.state keying.identity
          { k | region k = true } from allowed)
      exact SymbolicScheduleSearch.atWidth_covers_every_models before slots rules keying _ batch.members original
    | maximal =>
      have original : (bagOf (FirstOrder.action signature) batch.members).AdmitsMaximal (act signature) before.state :=
        presentation.symm ▸ (show batch.AdmitsMaximal (act signature) before.state from allowed)
      exact SymbolicScheduleSearch.atWidth_covers_maximal_models before slots rules batch.members original
    | unique keying region =>
      have original : (bagOf (FirstOrder.action signature) batch.members).AdmitsUniqueBy
          (act signature) before.state keying.identity { k | region k = true } :=
        presentation.symm ▸ (show batch.AdmitsUniqueBy (act signature) before.state keying.identity
          { k | region k = true } from allowed)
      exact SymbolicScheduleSearch.atWidth_covers_unique_models before slots rules keying _ batch.members original
  obtain ⟨requests, listed, permitted, output⟩ := candidates
  have length : requests.length = batch.members.length := ((SymbolicFiring.mem_tuples _ _ _).mp listed).1
  have ready : requests ∈ options rules width before := by
    apply (mem_options rules width before requests).mpr
    refine ⟨?_, length ▸ bounded, length ▸ listed⟩
    intro empty
    rw [empty] at length
    exact nonempty (List.eq_nil_of_length_eq_zero length.symm)
  refine ⟨requests, ready, permitted, fun input outputWords => ?_⟩
  have same := output input outputWords
  rw [presentation] at same
  exact same

omit [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
theorem enabled_source_iff (width : ℕ) :
    EnabledAt slots policy width before ↔ SourceEnabled policy width before := by
  refine ⟨enabled_is_source slots policy width, ?_⟩
  rintro ⟨batch, nonempty, bounded, allowed⟩
  obtain ⟨requests, listed, permitted, _⟩ :=
    source_models_covered slots policy width batch nonempty bounded allowed
  exact ⟨requests, listed, permitted⟩

theorem search_found_iff (width : ℕ) (before : LiveWorld signature) :
    (SnapshotMachine.search (schedule slots policy width) before).isSome = true ↔
      SourceEnabled policy width before := by
  cases result : SnapshotMachine.search (schedule slots policy width) before with
  | none =>
    have misses := (search_empty_iff slots policy width before).mp result
    have absent := fun source => misses ((enabled_source_iff slots policy width).mpr source)
    constructor
    · intro impossible
      cases impossible
    · intro enabled
      exact (absent enabled).elim
  | some accepted =>
    have enabled := ((search_sound slots policy width result).1)
    exact ⟨fun _ => enabled_is_source slots policy width enabled, fun _ => rfl⟩

/-- Every finite firing bag is found at a sufficiently large width.
A refusal at one width does not decide the unbounded question. -/
theorem finds_at_some_width (before : LiveWorld signature) :
    (∃ width, (SnapshotMachine.search (schedule slots policy width) before).isSome = true) ↔
      ∃ batch : ObservedBag before rules, batch.members ≠ [] ∧ Allows policy before batch := by
  constructor
  · rintro ⟨width, found⟩
    obtain ⟨batch, nonempty, _, allowed⟩ := (search_found_iff slots policy width before).mp found
    exact ⟨batch, nonempty, allowed⟩
  · rintro ⟨batch, nonempty, allowed⟩
    exact ⟨batch.members.length, (search_found_iff slots policy _ before).mpr
      ⟨batch, nonempty, Nat.le_refl _, allowed⟩⟩

theorem found_at_larger_width (before : LiveWorld signature) {small large : ℕ} (widened : small ≤ large)
    (found : (SnapshotMachine.search (schedule slots policy small) before).isSome = true) :
    (SnapshotMachine.search (schedule slots policy large) before).isSome = true := by
  obtain ⟨batch, nonempty, bounded, allowed⟩ := (search_found_iff slots policy small before).mp found
  exact (search_found_iff slots policy large before).mpr ⟨batch, nonempty, bounded.trans widened, allowed⟩

theorem every_complete_run_is_licensed (width fuel : ℕ) (before : LiveWorld signature)
    (outcome : SnapshotMachine.Outcome (LiveWorld signature))
    (ran : SnapshotMachine.Runs (schedule slots policy width) (.entry fuel before) (.halt outcome)) :
    SnapshotMachine.LegalRun (EnabledAt slots policy width) (Moves slots policy width) fuel before outcome := by
  have exactOutcome := (SnapshotMachine.machine_run_iff (schedule slots policy width) fuel before outcome).mp ran
  rw [exactOutcome]
  exact SnapshotMachine.run_legal (schedule slots policy width)
    (fun source none => (search_empty_iff slots policy width source).mp none)
    (fun computed => search_sound slots policy width computed) fuel before

theorem complete_run (width fuel : ℕ) (before : LiveWorld signature) :
    ∃ outcome, SnapshotMachine.Runs (schedule slots policy width) (.entry fuel before) (.halt outcome) ∧
      SnapshotMachine.LegalRun (EnabledAt slots policy width) (Moves slots policy width) fuel before outcome := by
  let outcome := SnapshotMachine.run (schedule slots policy width) fuel before
  have reaches := SnapshotMachine.complete_run (schedule slots policy width) fuel before
  exact ⟨outcome, reaches, every_complete_run_is_licensed slots policy width fuel before outcome reaches⟩

end Mettapedia.Machines.TIsa.Derivation.SymbolicSchedules
