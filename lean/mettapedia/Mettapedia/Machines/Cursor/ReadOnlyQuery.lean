import Mettapedia.Machines.Cursor.QueryCore
import Mettapedia.Machines.Cursor.Protocol
import Mettapedia.Machines.Cursor.FairObservation
import Mettapedia.Machines.ReadOnlyQuery
import Mettapedia.Machines.ResourceOwnership
import Mettapedia.Machines.RevisionDependencySet
import Mettapedia.Machines.OrderedDependencyStore
import Mettapedia.GSLT.Contracts.IndexedAuthority
import Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone
import Mettapedia.GSLT.Contracts.ReifiedActions
import Mettapedia.Machines.BranchLocalNeed.CacheLaws
import Mettapedia.Languages.MeTTa.MetavariableFrameStore

/-!
# Resumable adaptive queries with retained read certificates

The existing read-only query language is a client of the existing cursor
protocol. A suspension retains its reply-selected continuation and every
previous read. Completion is compared with the independently defined query
interpreter, including ordered duplicate and negative reads.

The unit charge counts provider reads. Cursor inspections and physical costs
of lookups, certificate storage and validation are separate quantities. A
fixed provider supplies one immutable store view; a concrete mutable store
must pin that view or validate its authority before further execution. A
validated revision may change unread dependencies while preserving every
recorded read. Validation and subsequent execution use the same new store
view; making that boundary atomic in a mutable runtime is a separate duty.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ReadOnlyQuery

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.Machines.ReadOnlyQuery (Program Reads Observation run Agrees checkReads)

universe u

variable {Key Value Answer : Type u}

def readCharge (store : Key → Value) : Charge (provider store) := fun _ _ => 1

abbrev Result (store : Key → Value) :=
  Outcome (provider store) (client (Answer := Answer)) .unit

/-- Change the provider's store while keeping the entire saved computation
and its accumulated charge. Sound reuse requires the read validation proved
below; changing this provider parameter alone grants no authority. -/
def rebase (first second : Key → Value) (previous : Nat × Result (Answer := Answer) first) :
    Nat × Result (Answer := Answer) second :=
  (previous.1, Outcome.mapState client (source := provider first) (target := provider second)
    (fun reads => reads) previous.2)

@[simp] theorem rebase_self (store : Key → Value)
    (previous : Nat × Result (Answer := Answer) store) :
    rebase store store previous = previous := by
  simp [rebase]

theorem rebase_comp (first second third : Key → Value)
    (previous : Nat × Result (Answer := Answer) first) :
    rebase second third (rebase first second previous) = rebase first third previous := by
  exact congrArg (fun outcome => (previous.1, outcome))
    (Outcome.mapState_comp client (source := provider first) (middle := provider second)
      (target := provider third) (fun reads => reads) (fun reads => reads) previous.2)

@[simp] theorem advance_pure (store : Key → Value) (fuel : Nat)
    (answer : Answer) (reads : Reads Key Value) :
    advance (provider store) client (readCharge store) (base := .unit)
      (fuel + 1) ⟨.unit, .pure answer, reads⟩ = (0, .done ⟨.unit, answer, reads⟩) := rfl

@[simp] theorem advance_read (store : Key → Value) (fuel : Nat) (key : Key)
    (next : Value → Program Key Value Answer) (reads : Reads Key Value) :
    advance (provider store) client (readCharge store) (base := .unit)
      (fuel + 1) ⟨.unit, .read key next, reads⟩ =
      let rest := advance (provider store) client (readCharge store) (base := .unit)
        fuel ⟨.unit, next (store key), (key, store key) :: reads⟩
      (1 + rest.1, rest.2) := rfl

/-- Only a completed cursor exposes an answer certificate. -/
def completed? (store : Key → Value) : Result (Answer := Answer) store →
    Option (Observation Key Value Answer)
  | .paused _ => none
  | .done ⟨.unit, answer, reads⟩ => some ⟨answer, reads.reverse⟩

def recorded (store : Key → Value) : Result (Answer := Answer) store → Reads Key Value
  | .paused ⟨.unit, _, reads⟩ => reads.reverse
  | .done ⟨.unit, _, reads⟩ => reads.reverse

/-- Mathematical completion of the retained residual, not an answer exposed
by an unfinished cursor. It uses the independent query interpreter. -/
def residualMeaning (store : Key → Value) : Result (Answer := Answer) store →
    Observation Key Value Answer
  | .paused ⟨.unit, program, reads⟩ =>
      let rest := run store program
      ⟨rest.answer, reads.reverse ++ rest.reads⟩
  | .done ⟨.unit, answer, reads⟩ => ⟨answer, reads.reverse⟩

/-- Any bounded prefix retains exactly what is needed to finish the same
adaptive query. Prior reads are retained rather than executed again. -/
theorem advance_meaning (store : Key → Value) (fuel : Nat)
    (program : Program Key Value Answer) (reads : Reads Key Value) :
    residualMeaning store
        (advance (provider store) client (readCharge store) (base := .unit) fuel ⟨.unit, program, reads⟩).2 =
      ⟨(run store program).answer, reads.reverse ++ (run store program).reads⟩ := by
  induction fuel generalizing program reads with
  | zero => rfl
  | succ fuel ih =>
      cases program with
      | pure answer => simp [residualMeaning, run]
      | read key next =>
          rw [advance_read]
          simpa [run, List.reverse_cons,
            List.append_assoc] using ih (next (store key)) ((key, store key) :: reads)

/-- The final read inspection is followed by an uncharged return inspection.
This bound is on this store-selected path, not on every possible reply path. -/
theorem advance_complete (store : Key → Value)
    (program : Program Key Value Answer) (reads : Reads Key Value) :
    advance (provider store) client (readCharge store) (base := .unit)
        ((run store program).reads.length + 1) ⟨.unit, program, reads⟩ =
      ((run store program).reads.length,
        .done ⟨.unit, (run store program).answer, (run store program).reads.reverse ++ reads⟩) := by
  induction program generalizing reads with
  | pure answer => rfl
  | read key next ih =>
      simp only [run, List.length_cons, List.reverse_cons]
      rw [advance_read, ih (store key)]
      simp [List.append_assoc, Nat.add_comm]

/-- Every charged read occurs once in the retained certificate, including
reads made before suspension and repeated reads of the same key. -/
theorem advance_read_account (store : Key → Value) (fuel : Nat)
    (program : Program Key Value Answer) (reads : Reads Key Value) :
    (recorded store
      (advance (provider store) client (readCharge store) (base := .unit) fuel ⟨.unit, program, reads⟩).2).length =
      reads.length +
        (advance (provider store) client (readCharge store) (base := .unit) fuel ⟨.unit, program, reads⟩).1 := by
  induction fuel generalizing program reads with
  | zero => simp [advance, recorded]
  | succ fuel ih =>
      cases program with
      | pure answer => simp [recorded]
      | read key next =>
          rw [advance_read]
          simpa [List.length_cons, Nat.add_assoc,
            Nat.add_left_comm, Nat.add_comm] using
              ih (next (store key)) ((key, store key) :: reads)

/-- A partial certificate covers the actual analysed prefix in order. It
does not certify the unexecuted continuation. -/
theorem recorded_prefix (store : Key → Value) (fuel : Nat)
    (program : Program Key Value Answer) :
    recorded store
        (advance (provider store) client (readCharge store) (base := .unit)
          fuel ⟨.unit, program, []⟩).2 <+:
      (run store program).reads := by
  have meaning := congrArg Observation.reads (advance_meaning store fuel program [])
  cases executed : (advance (provider store) client (readCharge store) (base := .unit)
      fuel ⟨.unit, program, []⟩).2 with
  | paused packet =>
      rcases packet with ⟨⟨⟩, remaining, reads⟩
      refine ⟨(run store remaining).reads, ?_⟩
      simpa only [executed, residualMeaning, recorded, List.reverse_nil, List.nil_append] using meaning
  | done result =>
      rcases result with ⟨⟨⟩, answer, reads⟩
      refine ⟨[], ?_⟩
      simpa only [executed, residualMeaning, recorded, List.reverse_nil, List.nil_append,
        List.append_nil] using meaning

theorem recorded_agrees (store : Key → Value) (fuel : Nat)
    (program : Program Key Value Answer) :
    Agrees store (recorded store
      (advance (provider store) client (readCharge store) (base := .unit)
        fuel ⟨.unit, program, []⟩).2) := by
  intro read member
  exact Mettapedia.Machines.ReadOnlyQuery.run_agrees store program read
    ((recorded_prefix store fuel program).subset member)

/-- Completion agrees with the independent unbounded interpreter. This
statement is conditional on actual completion, never on fuel exhaustion. -/
theorem completed_correct (store : Key → Value) (fuel : Nat)
    (program : Program Key Value Answer) (observation : Observation Key Value Answer)
    (finished : completed? store
      (advance (provider store) client (readCharge store) (base := .unit) fuel ⟨.unit, program, []⟩).2 =
        some observation) : observation = run store program := by
  have meaning := advance_meaning store fuel program []
  cases executed : (advance (provider store) client (readCharge store) (base := .unit) fuel
      ⟨.unit, program, []⟩).2 with
  | paused packet => simp [executed, completed?] at finished
  | done result =>
      rcases result with ⟨⟨⟩, answer, reads⟩
      simp only [executed, completed?, Option.some.injEq] at finished
      simpa only [executed, residualMeaning, List.reverse_nil, List.nil_append, finished] using meaning

/-- The common cursor composition law preserves the complete continuation,
read certificate and accumulated charges. -/
theorem advance_split (store : Key → Value) (first second : Nat)
    (program : Program Key Value Answer) (reads : Reads Key Value) :
    advance (provider store) client (readCharge store) (base := .unit) (first + second)
        ⟨.unit, program, reads⟩ =
      resume (provider store) client (readCharge store) second
        (advance (provider store) client (readCharge store) (base := .unit) first ⟨.unit, program, reads⟩) :=
  advance_add _ _ _ _ _ _

/-- Every previously recorded read remains in the certificate of a bounded
continuation. Repeated and negative reads retain their positions. -/
theorem recorded_keeps_prior (store : Key → Value) (fuel : Nat)
    (program : Program Key Value Answer) (reads : Reads Key Value) :
    reads.reverse <+: recorded store
      (advance (provider store) client (readCharge store) (base := .unit)
        fuel ⟨.unit, program, reads⟩).2 := by
  induction fuel generalizing program reads with
  | zero => exact ⟨[], by simp [advance, recorded]⟩
  | succ fuel ih =>
    cases program with
    | pure answer => exact ⟨[], by simp [recorded]⟩
    | read key next =>
      rw [advance_read]
      obtain ⟨suffix, equal⟩ := ih (next (store key)) ((key, store key) :: reads)
      exact ⟨[(key, store key)] ++ suffix, by
        simpa only [List.reverse_cons, List.append_assoc] using equal⟩

/-- Agreement on the actual retained prefix is enough to reproduce that
same prefix in a revised store. It makes no claim about unfinished reads.
The reply-selected continuation and accumulated charge are both preserved. -/
theorem advance_eq_of_recorded_agreement (first second : Key → Value) (fuel : Nat)
    (program : Program Key Value Answer) (reads : Reads Key Value)
    (valid : Agrees second (recorded first
      (advance (provider first) client (readCharge first) (base := .unit)
        fuel ⟨.unit, program, reads⟩).2)) :
    advance (provider second) client (readCharge second) (base := .unit)
        fuel ⟨.unit, program, reads⟩ =
      rebase first second (advance (provider first) client (readCharge first) (base := .unit)
        fuel ⟨.unit, program, reads⟩) := by
  induction fuel generalizing program reads with
  | zero => rfl
  | succ fuel ih =>
    cases program with
    | pure answer => rfl
    | read key next =>
      rw [advance_read] at valid
      have keyRecorded : (key, first key) ∈ recorded first
          (advance (provider first) client (readCharge first) (base := .unit)
            fuel ⟨.unit, next (first key), (key, first key) :: reads⟩).2 :=
        (recorded_keeps_prior first fuel (next (first key)) ((key, first key) :: reads)).subset
          (by simp)
      have sameReply : second key = first key := valid (key, first key) keyRecorded
      simp only [advance_read, sameReply]
      have equal := ih (next (first key)) ((key, first key) :: reads) valid
      simp only [rebase] at equal ⊢
      rw [equal]

/-- A changed but previously unread dependency can be inspected on resume.
Validating the saved prefix yields exactly a full run in the new view, without
executing or charging the saved prefix again. Snapshot semantics may instead
retain the old provider; this theorem states the validated-revision policy. -/
theorem validated_revision_resume (first second : Key → Value) (before after : Nat)
    (program : Program Key Value Answer) (reads : Reads Key Value)
    (valid : Agrees second (recorded first
      (advance (provider first) client (readCharge first) (base := .unit)
        before ⟨.unit, program, reads⟩).2)) :
    resume (provider second) client (readCharge second) after
        (rebase first second (advance (provider first) client (readCharge first) (base := .unit)
          before ⟨.unit, program, reads⟩)) =
      advance (provider second) client (readCharge second) (base := .unit)
        (before + after) ⟨.unit, program, reads⟩ := by
  rw [← advance_eq_of_recorded_agreement first second before program reads valid]
  exact (advance_split second before after program reads).symm

/-- A failed validation retains the old packet and its charges. Successful
validation resumes under one fixed new view. Validation work itself is not
a provider-read charge of the query being resumed. -/
def resumeValidated [DecidableEq Value] (first second : Key → Value) (fuel : Nat)
    (previous : Nat × Result (Answer := Answer) first) :
    Except (Nat × Result (Answer := Answer) first) (Nat × Result (Answer := Answer) second) :=
  if checkReads second (recorded first previous.2) then
    .ok (resume (provider second) client (readCharge second) fuel (rebase first second previous))
  else .error previous

theorem resumeValidated_refused [DecidableEq Value] (first second : Key → Value)
    (fuel : Nat) (previous : Nat × Result (Answer := Answer) first)
    (invalid : checkReads second (recorded first previous.2) = false) :
    resumeValidated first second fuel previous = .error previous := by
  simp [resumeValidated, invalid]

theorem resumeValidated_zero [DecidableEq Value] (first second : Key → Value)
    (previous : Nat × Result (Answer := Answer) first)
    (valid : checkReads second (recorded first previous.2) = true) :
    resumeValidated first second 0 previous = .ok (rebase first second previous) := by
  simp [resumeValidated, valid]

/-- Executable validation checks the exact premise needed for resumption;
the resulting packet, status and charge match uninterrupted new-view execution. -/
theorem resumeValidated_exact [DecidableEq Value] (first second : Key → Value)
    (before after : Nat) (program : Program Key Value Answer) (reads : Reads Key Value)
    (valid : checkReads second (recorded first
      (advance (provider first) client (readCharge first) (base := .unit)
        before ⟨.unit, program, reads⟩).2) = true) :
    resumeValidated first second after
        (advance (provider first) client (readCharge first) (base := .unit)
          before ⟨.unit, program, reads⟩) =
      .ok (advance (provider second) client (readCharge second) (base := .unit)
        (before + after) ⟨.unit, program, reads⟩) := by
  simp only [resumeValidated, valid, ↓reduceIte]
  rw [validated_revision_resume first second before after program reads
    ((Mettapedia.Machines.ReadOnlyQuery.checkReads_iff _ _).mp valid)]

theorem validated_revision_completed (first second : Key → Value) (before after : Nat)
    (program : Program Key Value Answer) (observation : Observation Key Value Answer)
    (valid : Agrees second (recorded first
      (advance (provider first) client (readCharge first) (base := .unit)
        before ⟨.unit, program, []⟩).2))
    (finished : completed? second
      (resume (provider second) client (readCharge second) after
        (rebase first second (advance (provider first) client (readCharge first) (base := .unit)
          before ⟨.unit, program, []⟩))).2 = some observation) :
    observation = run second program := by
  rw [validated_revision_resume first second before after program [] valid] at finished
  exact completed_correct second (before + after) program observation finished

/-- A completed certificate can be reused only after all of its reads
validate, including those chosen by earlier replies. -/
theorem validated_completion [DecidableEq Value] (first second : Key → Value)
    (fuel : Nat) (program : Program Key Value Answer) (observation : Observation Key Value Answer)
    (finished : completed? first
      (advance (provider first) client (readCharge first) (base := .unit) fuel ⟨.unit, program, []⟩).2 =
        some observation)
    (valid : checkReads second observation.reads = true) :
    run second program = observation := by
  have exactObservation := completed_correct first fuel program observation finished
  rw [exactObservation] at valid ⊢
  exact Mettapedia.Machines.ReadOnlyQuery.run_eq_of_agrees first second program
    ((Mettapedia.Machines.ReadOnlyQuery.checkReads_iff _ _).mp valid)

/-! ## Reads from an external region retained during private relocation

Keys contain a root in the region and an arbitrary ordered reference path.
The provider executes the actual heap walk. A checked relocation fixing the
closed external region gives equal replies, including negative reads; the
existing protocol then transports complete residuals and already paid work.
Physical store lifetime, revision validation and root enumeration are separate
runtime duties. This is a provider-read account, not a matcher-node count.
-/

section FixedRegion

open ResourceOwnership

variable {Address : Type} [DecidableEq Address] {Payload : Type u}

abbrev RegionKey (region : Finset Address) :=
  ULift.{u} {query : Address × List Address // query.1 ∈ region}

def regionStore (heap : Heap Address Payload) (region : Finset Address) :
    RegionKey.{u} region → Option (Address × Cell Address Payload) :=
  fun query => walk heap query.down.val.1 query.down.val.2

/-- Complete external path replies coincide by the heap transport theorem;
the two providers still use their independently supplied heaps. -/
def fixedRegionHom {source destination : Heap Address Payload}
    (copy : Relocation source destination) (region : Finset Address)
    (closed : ∀ a ∈ region, source.dependencies a ⊆ region)
    (fixed : ∀ a ∈ region, copy.address a = a)
    (values : ∀ a ∈ region, ∀ cell, source.lookup a = some cell →
      copy.payload cell.value = cell.value) :
    Hom (provider (regionStore source region)) (provider (regionStore destination region)) where
  map reads := reads
  step reads query := by
    have same := copy.walk_fixed_region region closed fixed values query.down.val.2 query.down.property
    simp only [provider, regionStore, same]

/-- Every bounded adaptive query preserves replies, duplicate reads, complete
status/residual and declared read charges while its private storage changes. -/
theorem fixed_region_advance_account {source destination : Heap Address Payload}
    (copy : Relocation source destination) (region : Finset Address)
    (closed : ∀ a ∈ region, source.dependencies a ⊆ region)
    (fixed : ∀ a ∈ region, copy.address a = a)
    (values : ∀ a ∈ region, ∀ cell, source.lookup a = some cell →
      copy.payload cell.value = cell.value) (fuel : Nat)
    (program : Program (RegionKey.{u} region) (Option (Address × Cell Address Payload)) Answer)
    (reads : Reads (RegionKey.{u} region) (Option (Address × Cell Address Payload))) :
    advance (provider (regionStore destination region)) client
        (readCharge (regionStore destination region)) (base := .unit) fuel ⟨.unit, program, reads⟩ =
      rebase (regionStore source region) (regionStore destination region)
        (advance (provider (regionStore source region)) client
          (readCharge (regionStore source region)) (base := .unit) fuel ⟨.unit, program, reads⟩) := by
  let hom := fixedRegionHom copy region closed fixed values
  simpa only [Hom.packet, Hom.outcome, fixedRegionHom, rebase, hom] using
    (hom.advance_account client (readCharge (regionStore source region))
      (readCharge (regionStore destination region)) (fun _ _ => rfl)
      fuel (base := .unit) ⟨.unit, program, reads⟩).symm

/-- A moved saved packet keeps its accumulated read charge and selected
continuation. Resume executes only the remaining provider interactions. -/
theorem fixed_region_resume_account {source destination : Heap Address Payload}
    (copy : Relocation source destination) (region : Finset Address)
    (closed : ∀ a ∈ region, source.dependencies a ⊆ region)
    (fixed : ∀ a ∈ region, copy.address a = a)
    (values : ∀ a ∈ region, ∀ cell, source.lookup a = some cell →
      copy.payload cell.value = cell.value) (fuel : Nat)
    (previous : Nat × Result (Answer := Answer) (regionStore source region)) :
    resume (provider (regionStore destination region)) client
        (readCharge (regionStore destination region)) fuel
        (rebase (regionStore source region) (regionStore destination region) previous) =
      rebase (regionStore source region) (regionStore destination region)
        (resume (provider (regionStore source region)) client
          (readCharge (regionStore source region)) fuel previous) := by
  let hom := fixedRegionHom copy region closed fixed values
  simpa only [Hom.outcome, fixedRegionHom, rebase, hom] using
    (hom.resume_account client (readCharge (regionStore source region))
      (readCharge (regionStore destination region)) (fun _ _ => rfl) fuel previous).symm

end FixedRegion

namespace Controls

open Mettapedia.Machines.ReadOnlyQuery.Controls (adaptive original absenceQuery)

private def execute (fuel : Nat) :=
  advance (provider original) client (readCharge original) (base := .unit)
    fuel ⟨.unit, adaptive, []⟩

theorem first_read_retains_selected_continuation :
    (execute 1).1 = 1 ∧ recorded original (execute 1).2 = [(0, 2)] ∧
      completed? original (execute 1).2 = none := by
  exact ⟨rfl, rfl, rfl⟩

theorem completed_reads_and_duplicate_answers :
    (execute 3).1 = 2 ∧
      completed? original (execute 3).2 = some ⟨[7, 7], [(0, 2), (2, 7)]⟩ := by
  exact ⟨rfl, rfl⟩

theorem split_does_not_repeat_selector :
    resume (provider original) client (readCharge original) 2 (execute 1) = execute 3 := by
  exact (advance_split original 1 2 adaptive []).symm

/-- The inspected selector remains valid even though the uninspected
dependency has changed. Hence prefix validation grants no completed answer. -/
theorem valid_prefix_does_not_certify_answer :
    checkReads (Function.update original 2 8) (recorded original (execute 1).2) = true ∧
      (run (Function.update original 2 8) adaptive).answer ≠ (run original adaptive).answer ∧
      completed? original (execute 1).2 = none := by
  exact ⟨by decide, by decide, rfl⟩

theorem changed_completed_dependency_rejected :
    checkReads (Function.update original 2 8) (recorded original (execute 3).2) = false := by
  decide

theorem revised_unread_dependency_resumes_without_replay :
    resumeValidated original (Function.update original 2 8) 2 (execute 1) =
      .ok (2, .done ⟨.unit, [8, 8], [(2, 8), (0, 2)]⟩) := by
  rfl

theorem revised_selector_refuses_complete_saved_packet :
    resumeValidated original (Function.update original 0 1) 2 (execute 1) =
      .error (execute 1) := by
  rfl

theorem zero_allowance_keeps_saved_packet :
    resumeValidated original original 0 (execute 1) = .ok (execute 1) := by
  rfl

/-- Ignoring failed validation follows the stale branch. The saved selector
chose key 2, whereas the revised query must now read key 1. -/
theorem unchecked_revision_follows_wrong_continuation :
    completed? (Function.update original 0 1)
      (resume (provider (Function.update original 0 1)) client
        (readCharge (Function.update original 0 1)) 2
        (rebase original (Function.update original 0 1) (execute 1))).2 ≠
      some (run (Function.update original 0 1) adaptive) := by
  intro same
  have answers := congrArg (Option.map Observation.answer) same
  contradiction

theorem completed_negative_read_refuses_new_presence :
    let absent := fun (_ : Nat) => (none : Option Nat)
    let previous := advance (provider absent) client (readCharge absent)
      (base := .unit) 2 ⟨.unit, absenceQuery, []⟩
    resumeValidated absent (Function.update absent 4 (some 9)) 1 previous = .error previous := by
  rfl

theorem negative_read_is_retained :
    completed? (fun (_ : Nat) => (none : Option Nat))
      (advance (provider (fun (_ : Nat) => (none : Option Nat))) client
        (readCharge (fun _ => none)) (base := .unit) 2 ⟨.unit, absenceQuery, []⟩).2 =
          some ⟨true, [(4, none)]⟩ := by
  rfl

namespace PinnedRegion

open ResourceOwnership

abbrev BorrowKey := RegionKey.{0} Examples.PinnedRegion.external
abbrev Reply := Option (Fin 4 × Cell (Fin 4) Nat)

def presentKey : BorrowKey := ⟨⟨(1, []), by decide⟩⟩
def missingKey : BorrowKey := ⟨⟨(1, [3]), by decide⟩⟩
def original := regionStore Examples.PinnedRegion.heap Examples.PinnedRegion.external
def moved := regionStore Examples.PinnedRegion.copied Examples.PinnedRegion.external
def row : Reply := some (1, Examples.PinnedRegion.cell 1)

/-- The second continuation retains the first physical reply, then repeats
that read and records a failed path. Duplicate answers remain ordered. -/
def echo : Program BorrowKey Reply (List Reply) :=
  .read presentKey fun before => .read presentKey fun again =>
    .read missingKey fun absent => .pure [before, again, absent]

private def savedPrefix :=
  advance (provider original) client (readCharge original) (base := .unit) 1 ⟨.unit, echo, []⟩

/-- Every future grant retains the same selected continuation and accumulated
account, even though the actual underlying private heap has changed. -/
theorem all_future_grants_preserve_saved_account (fuel : Nat) :
    resume (provider moved) client (readCharge moved) fuel (rebase original moved savedPrefix) =
      rebase original moved (resume (provider original) client (readCharge original) fuel savedPrefix) :=
  fixed_region_resume_account Examples.PinnedRegion.copy Examples.PinnedRegion.external
    Examples.PinnedRegion.external_closed Examples.PinnedRegion.external_fixed
    (fun _ _ _ _ => rfl) fuel savedPrefix

/-- One read was already paid; migration does not pay it again. Completion
contains both equal reply occurrences and the negative read in source order. -/
theorem moved_query_keeps_paid_prefix_duplicates_and_negative_read :
    savedPrefix.1 = 1 ∧
      (resume (provider moved) client (readCharge moved) 3 (rebase original moved savedPrefix)).1 = 3 ∧
      completed? moved
        (resume (provider moved) client (readCharge moved) 3 (rebase original moved savedPrefix)).2 =
        some ⟨[row, row, none], [(presentKey, row), (presentKey, row), (missingKey, none)]⟩ := by
  exact ⟨rfl, rfl, rfl⟩

end PinnedRegion

end Controls

#print axioms advance_meaning
#print axioms advance_complete
#print axioms advance_read_account
#print axioms recorded_prefix
#print axioms recorded_agrees
#print axioms completed_correct
#print axioms advance_split
#print axioms recorded_keeps_prior
#print axioms advance_eq_of_recorded_agreement
#print axioms validated_revision_resume
#print axioms resumeValidated_refused
#print axioms resumeValidated_zero
#print axioms resumeValidated_exact
#print axioms validated_revision_completed
#print axioms validated_completion
#print axioms Controls.first_read_retains_selected_continuation
#print axioms Controls.completed_reads_and_duplicate_answers
#print axioms Controls.split_does_not_repeat_selector
#print axioms Controls.valid_prefix_does_not_certify_answer
#print axioms Controls.changed_completed_dependency_rejected
#print axioms Controls.negative_read_is_retained
#print axioms Controls.revised_unread_dependency_resumes_without_replay
#print axioms Controls.revised_selector_refuses_complete_saved_packet
#print axioms Controls.zero_allowance_keeps_saved_packet
#print axioms Controls.unchecked_revision_follows_wrong_continuation
#print axioms Controls.completed_negative_read_refuses_new_presence

/-! ## Stateful query services and authorized own writes

The existing primitive program and cursor retain the reply-selected client.
The provider owns the actual dependency store. A write changes that store;
it does not rewrite values or read stamps already held by the continuation.
Authority is checked independently of observation and is not consumed by this
permission profile. Exclusive arbitration requires a separate discharge rule.
-/

namespace OwnWrite

open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.Contracts
open Mettapedia.GSLT.SeparationAlgebra


variable {Entry World : Type} {size : Nat} [Category.{0} World]

/-- Service operations, interpreted by the existing primitive program tree. -/
inductive Request (Entry : Type) (size : Nat) where
  | read (reader : Fin size)
  | validate (stamp : OrderedDependencyStore.ReadStamp size)
  | write (action : OrderedDependencyStore.Action Entry size)

def Reply : Request Entry size → Type
  | .read _ => OrderedDependencyStore.ReadStamp size × List Entry
  | .validate _ => Bool
  | .write _ => Unit

inductive Fault where
  | denied
  deriving DecidableEq

structure State (authority : IndexedAuthority.{0, 0, 0} World) (Entry : Type) (size : Nat) where
  store : OrderedDependencyStore.Store Entry size
  point : IndexedAuthority.Point authority

variable (authority : IndexedAuthority.{0, 0, 0} World)
  (required : OrderedDependencyStore.Action Entry size → (world : World) → authority.Fibre world)
  [permission : ∀ (point : IndexedAuthority.Point authority) (action : OrderedDependencyStore.Action Entry size),
    Decidable (FrameUpdate point.authority (required action point.world))]

/-- Actual store queries and updates. Only a successful write changes state.
Old stamps are data in the client, never refreshed by this operation. -/
def step (s : State authority Entry size) (request : Request Entry size) :
    State authority Entry size × Except Fault (Reply request) :=
  match request with
  | .read reader => (s, .ok (OrderedDependencyStore.readStamp s.store reader, OrderedDependencyStore.query s.store reader))
  | .validate stamp => (s, .ok (OrderedDependencyStore.checkRead s.store stamp))
  | .write change =>
      if FrameUpdate s.point.authority (required change s.point.world) then
        ({ s with store := OrderedDependencyStore.step s.store change }, .ok ())
      else (s, .error .denied)

/-- Independent primitive meaning over the existing store algorithm.
Observation has no permission conclusion. Writes require current authority. -/
def action (request : Request Entry size) : Action (State authority Entry size) (Reply request) :=
  match request with
  | .read reader =>
      ⟨fun _ => True, fun before reply after =>
        reply = (OrderedDependencyStore.readStamp before.store reader, OrderedDependencyStore.query before.store reader) ∧ after = before⟩
  | .validate stamp =>
      ⟨fun _ => True, fun before reply after => reply = OrderedDependencyStore.checkRead before.store stamp ∧ after = before⟩
  | .write change =>
      ⟨fun before => FrameUpdate before.point.authority (required change before.point.world),
        fun before _ after => after = { before with store := OrderedDependencyStore.step before.store change }⟩

theorem step_sound : PrimitiveProgram.ProviderSound (action authority required) (step authority required) := by
  intro s request safe
  cases request with
  | read reader => exact ⟨_, s, rfl, rfl, rfl⟩
  | validate stamp => exact ⟨_, s, rfl, rfl, rfl⟩
  | write change =>
      change FrameUpdate s.point.authority (required change s.point.world) at safe
      exact ⟨(), _, by simp only [step, if_pos safe], rfl⟩

theorem denied_write_keeps_state (s : State authority Entry size) (change : OrderedDependencyStore.Action Entry size)
    (denied : ¬ FrameUpdate s.point.authority (required change s.point.world)) :
    step authority required s (.write change) = (s, .error .denied) := by
  simp only [step, if_neg denied]

theorem own_write_uses_current_store (s : State authority Entry size) (change : OrderedDependencyStore.Action Entry size)
    (allowed : FrameUpdate s.point.authority (required change s.point.world)) :
    step authority required s (.write change) =
      ({ s with store := OrderedDependencyStore.step s.store change }, .ok ()) := by
  simp only [step, if_pos allowed]

abbrev provider := PrimitiveProgram.provider (step authority required)
abbrev client (Answer : Type) := PrimitiveProgram.client (Request Entry size) Reply Answer Fault
abbrev Saved (Answer : Type) := Nat × Outcome (provider authority required) (client (Entry := Entry) (size := size) Answer) PUnit.unit

/-- The common cursor is the executor; no additional stepping loop is used. -/
def advance {Answer : Type} (fuel : Nat) (program : Prog (Request Entry size) Reply Answer)
    (s : State authority Entry size) : Saved authority required Answer :=
  Cursor.advance (provider authority required) (client Answer) (fun _ _ => 1)
    fuel ⟨PUnit.unit, .ok program, s⟩

theorem finite_execution {Answer : Type} (fuel : Nat)
    (program : Prog (Request Entry size) Reply Answer) (s : State authority Entry size)
    (safe : program.Safe (action authority required) s) :
    PrimitiveProgram.SafeOutcome (action authority required) program s
      (PrimitiveProgram.readOutcome (step authority required) (advance authority required fuel program s).2) :=
  PrimitiveProgram.advance_safe_outcome (action authority required) (step authority required)
    (step_sound authority required) (fun _ _ => 1) fuel program s safe

theorem finite_is_direct {Answer : Type} (fuel : Nat)
    (program : Prog (Request Entry size) Reply Answer) (s : State authority Entry size) :
    let actual := advance authority required fuel program s
    (actual.1, PrimitiveProgram.readOutcome (step authority required) actual.2) =
      PrimitiveProgram.direct (step authority required) (fun _ _ => 1) fuel (.ok program) s :=
  PrimitiveProgram.advance_is_direct (step authority required) (fun _ _ => 1) fuel (.ok program) s

theorem split_resume {Answer : Type} (first second : Nat)
    (program : Prog (Request Entry size) Reply Answer) (s : State authority Entry size) :
    advance authority required (first + second) program s =
      Cursor.resume (provider authority required) (client Answer) (fun _ _ => 1) second
        (advance authority required first program s) :=
  Cursor.advance_add _ _ _ _ _ _

/-- Embed the existing adaptive pure query in the stateful service client.
Its observed rows select the real continuation, without recording a journal. -/
def query {Answer : Type} : Program (Fin size) (List Entry) Answer →
    Prog (Request Entry size) Reply Answer
  | .pure answer => .ret answer
  | .read reader next => .call (.read reader) fun observed => query (next observed.2)

omit permission in
theorem query_safe {Answer : Type} (program : Program (Fin size) (List Entry) Answer)
    (s : State authority Entry size) : (query program).Safe (action authority required) s := by
  induction program generalizing s with
  | pure answer => trivial
  | read reader next ih =>
      refine ⟨trivial, ?_⟩
      intro reply after permitted
      obtain ⟨rfl, same⟩ := permitted
      subst after
      exact ih _ s

omit permission in
theorem query_runs {Answer : Type} (program : Program (Fin size) (List Entry) Answer)
    (s after : State authority Entry size) (answer : Answer) :
    (query program).Runs (action authority required) s answer after ↔
      answer = (run (OrderedDependencyStore.query s.store) program).answer ∧ after = s := by
  induction program generalizing s after with
  | pure value => simp [query, Prog.Runs, run, eq_comm]
  | read reader next ih =>
      simp only [query, Prog.Runs, action, run]
      constructor
      · rintro ⟨reply, middle, ⟨rfl, same⟩, execution⟩
        subst middle
        exact (ih _ s after).mp execution
      · intro finished
        exact ⟨_, s, ⟨rfl, rfl⟩, (ih _ s after).mpr finished⟩

/- The old query's answer selects the continuation at the same actual
state. That continuation may perform authorized own writes. It need not
revalidate the captured past as if it had just been read in a later world. -/
omit permission in
theorem query_then_runs {Answer Other : Type}
    (program : Program (Fin size) (List Entry) Answer)
    (next : Answer → Prog (Request Entry size) Reply Other)
    (s after : State authority Entry size) (answer : Other) :
    ((query program).bind next).Runs (action authority required) s answer after ↔
      (next (run (OrderedDependencyStore.query s.store) program).answer).Runs
        (action authority required) s answer after := by
  rw [Prog.runs_bind]
  constructor
  · rintro ⟨value, middle, prior, suffix⟩
    obtain ⟨rfl, same⟩ := (query_runs authority required program s middle value).mp prior
    subst middle
    exact suffix
  · intro suffix
    exact ⟨_, s, (query_runs authority required program s s _).mpr ⟨rfl, rfl⟩, suffix⟩

theorem query_direct_complete {Answer : Type}
    (program : Program (Fin size) (List Entry) Answer) (s : State authority Entry size) :
    PrimitiveProgram.direct (step authority required) (fun _ _ => 1)
      ((run (OrderedDependencyStore.query s.store) program).reads.length + 1) (.ok (query program)) s =
      ((run (OrderedDependencyStore.query s.store) program).reads.length,
        (.inl (.ok (run (OrderedDependencyStore.query s.store) program).answer), s)) := by
  induction program generalizing s with
  | pure answer => rfl
  | read reader next ih =>
      simp only [run, List.length_cons, query]
      rw [PrimitiveProgram.direct]
      simpa only [step, Nat.add_comm]
        using congrArg (fun result => (1 + result.1, result.2))
          (ih (OrderedDependencyStore.query s.store reader) s)

theorem query_complete {Answer : Type}
    (program : Program (Fin size) (List Entry) Answer) (s : State authority Entry size) :
    advance authority required ((run (OrderedDependencyStore.query s.store) program).reads.length + 1)
      (query program) s =
      ((run (OrderedDependencyStore.query s.store) program).reads.length,
        .done ⟨PUnit.unit, .ok (run (OrderedDependencyStore.query s.store) program).answer, s⟩) := by
  have comparison := finite_is_direct authority required
    ((run (OrderedDependencyStore.query s.store) program).reads.length + 1) (query program) s
  rw [query_direct_complete authority required program s] at comparison
  have paid := congrArg Prod.fst comparison
  have result := congrArg Prod.snd comparison
  exact Prod.ext paid (PrimitiveProgram.readOutcome_injective (step authority required) result)

def current {Answer : Type} (saved : Saved authority required Answer) : State authority Entry size :=
  (PrimitiveProgram.readOutcome (step authority required) saved.2).2

/-- External changes enter only at this checked boundary. A terminal value or
an already returned/faulted client needs no new provider request. The check
protects the pending source; stamps closed over by its client stay unchanged.
Current permission is supplied separately, and each write checks it in step. -/
def resumeCurrent {Answer : Type} (live : OrderedDependencyStore.Store Entry size)
    (point : IndexedAuthority.Point authority) (reader : Fin size) (fuel : Nat)
    (previous : Saved authority required Answer) : Option (Saved authority required Answer) :=
  if fuel = 0 then some previous else
  match previous.2 with
  | .done _ => some previous
  | .paused ⟨index, control, saved⟩ =>
      match control with
      | .error _ | .ok (.ret _) =>
          some (Cursor.resume (provider authority required) (client Answer) (fun _ _ => 1) fuel previous)
      | .ok (.call _ _) =>
          if OrderedDependencyStore.checkRead live (OrderedDependencyStore.readStamp saved.store reader) then
            some (Cursor.resume (provider authority required) (client Answer) (fun _ _ => 1) fuel
              (previous.1, .paused ⟨index, control, ⟨live, point⟩⟩))
          else none

theorem zero_keeps_whole_saved {Answer : Type} (live : OrderedDependencyStore.Store Entry size)
    (point : IndexedAuthority.Point authority) (reader : Fin size) (previous : Saved authority required Answer) :
    resumeCurrent authority required live point reader 0 previous = some previous := rfl

theorem completed_reentry_inert {Answer : Type} (live : OrderedDependencyStore.Store Entry size)
    (point : IndexedAuthority.Point authority) (reader : Fin size) (fuel paid : Nat)
    (answer : Except Fault Answer) (saved : State authority Entry size) :
    resumeCurrent authority required live point reader fuel
      (paid, .done ⟨PUnit.unit, answer, saved⟩) = some (paid, .done ⟨PUnit.unit, answer, saved⟩) := by
  simp only [resumeCurrent, ite_self]

theorem stale_pending_refused {Answer : Type} (live : OrderedDependencyStore.Store Entry size)
    (point : IndexedAuthority.Point authority) (reader : Fin size) (fuel paid : Nat)
    (request : Request Entry size) (next : Reply request → Prog (Request Entry size) Reply Answer)
    (saved : State authority Entry size)
    (stale : OrderedDependencyStore.checkRead live (OrderedDependencyStore.readStamp saved.store reader) = false) :
    resumeCurrent authority required live point reader (fuel + 1)
      (paid, .paused ⟨PUnit.unit, .ok (.call request next), saved⟩) = none := by
  simp only [resumeCurrent, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, stale,
    Bool.false_eq_true]

theorem current_pending_resumes {Answer : Type} (live : OrderedDependencyStore.Store Entry size)
    (point : IndexedAuthority.Point authority) (reader : Fin size) (fuel paid : Nat)
    (request : Request Entry size) (next : Reply request → Prog (Request Entry size) Reply Answer)
    (saved : State authority Entry size)
    (valid : OrderedDependencyStore.checkRead live (OrderedDependencyStore.readStamp saved.store reader) = true) :
    resumeCurrent authority required live point reader (fuel + 1)
      (paid, .paused ⟨PUnit.unit, .ok (.call request next), saved⟩) =
      some (Cursor.resume (provider authority required) (client Answer) (fun _ _ => 1) (fuel + 1)
        (paid, .paused ⟨PUnit.unit, .ok (.call request next), ⟨live, point⟩⟩)) := by
  simp only [resumeCurrent, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, valid]

/-- Token equality is used with the actual store update history, never as an
unproved equality between arbitrary stores with coincident counters. -/
theorem current_source_agrees (saved : State authority Entry size)
    (changes : List (OrderedDependencyStore.Action Entry size)) (reader : Fin size)
    (lawful : OrderedDependencyStore.ObserverInvariant saved.store)
    (valid : OrderedDependencyStore.checkRead (OrderedDependencyStore.execute saved.store changes)
      (OrderedDependencyStore.readStamp saved.store reader) = true) :
    OrderedDependencyStore.query (OrderedDependencyStore.execute saved.store changes) reader =
      OrderedDependencyStore.query saved.store reader :=
  OrderedDependencyStore.validated_query saved.store lawful changes reader valid

/-- A complete past read survives its own actual write in the real client.
The returned stamp is the old stamp even when validation later fails. -/
def readWrite (reader : Fin size) (change : List Entry → OrderedDependencyStore.Action Entry size) :
    Prog (Request Entry size) Reply (OrderedDependencyStore.ReadStamp size × List Entry) :=
  .call (.read reader) fun captured => .call (.write (change captured.2)) fun _ => .ret captured

theorem captured_read_own_write (s : State authority Entry size) (reader : Fin size)
    (change : List Entry → OrderedDependencyStore.Action Entry size)
    (allowed : FrameUpdate s.point.authority
      (required (change (OrderedDependencyStore.query s.store reader)) s.point.world)) :
    advance authority required 3 (readWrite reader change) s =
      (2, .done ⟨PUnit.unit, .ok (OrderedDependencyStore.readStamp s.store reader,
        OrderedDependencyStore.query s.store reader),
        { s with store := OrderedDependencyStore.step s.store (change (OrderedDependencyStore.query s.store reader)) }⟩) := by
  have comparison := finite_is_direct authority required 3 (readWrite reader change) s
  have direct : PrimitiveProgram.direct (step authority required) (fun _ _ => 1) 3
      (.ok (readWrite reader change)) s =
      (2, (.inl (.ok (OrderedDependencyStore.readStamp s.store reader,
        OrderedDependencyStore.query s.store reader)),
        { s with store := OrderedDependencyStore.step s.store (change (OrderedDependencyStore.query s.store reader)) })) := by
    simp only [readWrite, PrimitiveProgram.direct, step, if_pos allowed]
  rw [direct] at comparison
  have paid := congrArg Prod.fst comparison
  have result := congrArg Prod.snd comparison
  exact Prod.ext paid (PrimitiveProgram.readOutcome_injective (step authority required) result)

/-- A proof-only origin of the current store, not an execution journal. -/
def OwnOrigin (before after : State authority Entry size) : Prop :=
  ∃ changes : List (OrderedDependencyStore.Action Entry size),
    after.store = OrderedDependencyStore.execute before.store changes ∧ after.point = before.point

private theorem execute_append (s : OrderedDependencyStore.Store Entry size)
    (first second : List (OrderedDependencyStore.Action Entry size)) :
    OrderedDependencyStore.execute s (first ++ second) =
      OrderedDependencyStore.execute (OrderedDependencyStore.execute s first) second := by
  induction first generalizing s with
  | nil => rfl
  | cons head tail ih => exact ih (OrderedDependencyStore.step s head)

private theorem origin_trans (first second third : State authority Entry size)
    (left : OwnOrigin authority first second) (right : OwnOrigin authority second third) :
    OwnOrigin authority first third := by
  obtain ⟨prefixActions, earlier, firstPoint⟩ := left
  obtain ⟨suffixActions, later, secondPoint⟩ := right
  exact ⟨prefixActions ++ suffixActions, by rw [execute_append, ← earlier, ← later],
    secondPoint.trans firstPoint⟩

theorem step_origin (s : State authority Entry size) (request : Request Entry size) :
    OwnOrigin authority s (step authority required s request).1 := by
  cases request with
  | read reader => exact ⟨[], rfl, rfl⟩
  | validate stamp => exact ⟨[], rfl, rfl⟩
  | write change =>
      by_cases allowed : FrameUpdate s.point.authority (required change s.point.world)
      · exact ⟨[change], by simp only [step, if_pos allowed]; rfl, by simp only [step, if_pos allowed]⟩
      · exact ⟨[], by simp only [step, if_neg allowed]; rfl, by simp only [step, if_neg allowed]⟩

private theorem direct_origin {Answer : Type} (fuel : Nat)
    (control : Except Fault (Prog (Request Entry size) Reply Answer)) (s : State authority Entry size) :
    OwnOrigin authority s (PrimitiveProgram.direct (step authority required) (fun _ _ => 1) fuel control s).2.2 := by
  induction fuel generalizing control s with
  | zero => exact ⟨[], rfl, rfl⟩
  | succ fuel ih =>
      cases control with
      | error fault => exact ⟨[], rfl, rfl⟩
      | ok program =>
          cases program with
          | ret answer => exact ⟨[], rfl, rfl⟩
          | call request next =>
              rcases moved : step authority required s request with ⟨middle, reply⟩
              have one := step_origin authority required s request
              rw [moved] at one
              cases reply with
              | error fault =>
                  simpa only [PrimitiveProgram.direct, moved] using
                    origin_trans authority s middle _ one (ih (.error fault) middle)
              | ok value =>
                  simpa only [PrimitiveProgram.direct, moved] using
                    origin_trans authority s middle _ one (ih (.ok (next value)) middle)

theorem finite_origin {Answer : Type} (fuel : Nat)
    (program : Prog (Request Entry size) Reply Answer) (s : State authority Entry size) :
    OwnOrigin authority s (current authority required (advance authority required fuel program s)) := by
  have comparison := finite_is_direct authority required fuel program s
  have worlds := congrArg (fun result => result.2.2) comparison
  change current authority required (advance authority required fuel program s) = _ at worlds
  rw [worlds]
  exact direct_origin authority required fuel (.ok program) s

theorem finite_observers {Answer : Type} (fuel : Nat)
    (program : Prog (Request Entry size) Reply Answer) (s : State authority Entry size)
    (lawful : OrderedDependencyStore.ObserverInvariant s.store) :
    OrderedDependencyStore.ObserverInvariant
      (current authority required (advance authority required fuel program s)).store := by
  obtain ⟨changes, origin, _⟩ := finite_origin authority required fuel program s
  rw [origin]
  exact OrderedDependencyStore.execute_observers s.store lawful changes

/-- Any finite partition of a fixed service run preserves full state and
accounts. This says nothing about changing external worlds or permissions. -/
def schedule {Answer : Type} (grants : List Nat) (saved : Saved authority required Answer) :
    Saved authority required Answer := grants.foldl
      (fun previous fuel => Cursor.resume (provider authority required) (client Answer) (fun _ _ => 1) fuel previous) saved

theorem schedule_sum {Answer : Type} (grants : List Nat) (saved : Saved authority required Answer) :
    schedule authority required grants saved =
      Cursor.resume (provider authority required) (client Answer) (fun _ _ => 1) grants.sum saved := by
  induction grants generalizing saved with
  | nil =>
      rcases saved with ⟨paid, outcome⟩
      cases outcome <;> simp [schedule, Cursor.resume]
  | cons fuel rest ih =>
      simpa only [schedule, List.foldl_cons, List.sum_cons, ← Cursor.resume_add] using
        ih (Cursor.resume (provider authority required) (client Answer) (fun _ _ => 1) fuel saved)

def completed {Answer : Type} (saved : Saved authority required Answer) : Option (Except Fault Answer) :=
  match saved.2 with
  | .paused _ => none
  | .done ⟨_, answer, _⟩ => some answer

namespace Invocation

variable (needed : (world : World) → authority.Fibre world)
  [admission : ∀ point : IndexedAuthority.Point authority,
    Decidable (FrameUpdate point.authority (needed point.world))]

/-- Enter the existing saved computation under the current invocation right.
Refusal returns its original packet and paid account. Zero allowance and an
earned result require no new service permission. This checks an entrance;
individual writes still use the original provider's action check. -/
def resume {Answer : Type} (live : OrderedDependencyStore.Store Entry size)
    (point : IndexedAuthority.Point authority) (reader : Fin size) (fuel : Nat)
    (previous : Saved authority required Answer) :
    Except (Saved authority required Answer) (Saved authority required Answer) :=
  if fuel = 0 then .ok previous else
  match previous.2 with
  | .done _ => .ok previous
  | .paused ⟨_, control, _⟩ =>
      match control with
      | .error _ | .ok (.ret _) =>
          .ok (Cursor.resume (provider authority required) (client Answer) (fun _ _ => 1) fuel previous)
      | .ok (.call _ _) =>
          if FrameUpdate point.authority (needed point.world) then
            match resumeCurrent authority required live point reader fuel previous with
            | some next => .ok next
            | none => .error previous
          else .error previous

theorem zero {Answer : Type} (live : OrderedDependencyStore.Store Entry size)
    (point : IndexedAuthority.Point authority) (reader : Fin size)
    (previous : Saved authority required Answer) :
    resume authority required needed live point reader 0 previous = .ok previous := rfl

theorem earned {Answer : Type} (live : OrderedDependencyStore.Store Entry size)
    (point : IndexedAuthority.Point authority) (reader : Fin size) (fuel paid : Nat)
    (answer : Except Fault Answer) (saved : State authority Entry size) :
    resume authority required needed live point reader fuel
      (paid, .done ⟨PUnit.unit, answer, saved⟩) =
        .ok (paid, .done ⟨PUnit.unit, answer, saved⟩) := by
  simp only [resume, ite_self]

theorem pending_admitted {Answer : Type} (live : OrderedDependencyStore.Store Entry size)
    (point : IndexedAuthority.Point authority) (reader : Fin size) (fuel paid : Nat)
    (request : Request Entry size) (next : Reply request → Prog (Request Entry size) Reply Answer)
    (saved : State authority Entry size)
    (allowed : FrameUpdate point.authority (needed point.world))
    (valid : OrderedDependencyStore.checkRead live (OrderedDependencyStore.readStamp saved.store reader) = true) :
    resume authority required needed live point reader (fuel + 1)
      (paid, .paused ⟨PUnit.unit, .ok (.call request next), saved⟩) =
    .ok (Cursor.resume (provider authority required) (client Answer) (fun _ _ => 1) (fuel + 1)
      (paid, .paused ⟨PUnit.unit, .ok (.call request next), ⟨live, point⟩⟩)) := by
  simp only [resume, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, allowed,
    current_pending_resumes authority required live point reader fuel paid request next saved valid]

theorem pending_refused {Answer : Type} (live : OrderedDependencyStore.Store Entry size)
    (point : IndexedAuthority.Point authority) (reader : Fin size) (fuel paid : Nat)
    (request : Request Entry size) (next : Reply request → Prog (Request Entry size) Reply Answer)
    (saved : State authority Entry size)
    (denied : ¬ FrameUpdate point.authority (needed point.world) ∨
      OrderedDependencyStore.checkRead live (OrderedDependencyStore.readStamp saved.store reader) = false) :
    resume authority required needed live point reader (fuel + 1)
      (paid, .paused ⟨PUnit.unit, .ok (.call request next), saved⟩) =
        .error (paid, .paused ⟨PUnit.unit, .ok (.call request next), saved⟩) := by
  rcases denied with denied | stale
  · simp only [resume, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, denied]
  · by_cases allowed : FrameUpdate point.authority (needed point.world)
    · simp only [resume, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, allowed,
        stale_pending_refused authority required live point reader fuel paid request next saved stale]
    · simp only [resume, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, allowed]

/-- The admitted slice is the independently defined primitive execution from
the actual live entrance, including its full state, fault and residual. -/
theorem pending_is_direct {Answer : Type} (live : OrderedDependencyStore.Store Entry size)
    (point : IndexedAuthority.Point authority) (reader : Fin size) (fuel paid : Nat)
    (request : Request Entry size) (next : Reply request → Prog (Request Entry size) Reply Answer)
    (saved : State authority Entry size)
    (allowed : FrameUpdate point.authority (needed point.world))
    (valid : OrderedDependencyStore.checkRead live (OrderedDependencyStore.readStamp saved.store reader) = true) :
    let actual := Cursor.resume (provider authority required) (client Answer) (fun _ _ => 1) (fuel + 1)
      (paid, .paused ⟨PUnit.unit, .ok (.call request next), ⟨live, point⟩⟩)
    resume authority required needed live point reader (fuel + 1)
        (paid, .paused ⟨PUnit.unit, .ok (.call request next), saved⟩) = .ok actual ∧
      (actual.1, PrimitiveProgram.readOutcome (step authority required) actual.2) =
        let direct := PrimitiveProgram.direct (step authority required) (fun _ _ => 1)
          (fuel + 1) (.ok (.call request next)) ⟨live, point⟩
        (paid + direct.1, direct.2) := by
  refine ⟨pending_admitted authority required needed live point reader fuel paid request next saved allowed valid, ?_⟩
  have comparison := PrimitiveProgram.advance_is_direct (step authority required) (fun _ _ => 1)
    (fuel + 1) (.ok (.call request next)) (⟨live, point⟩ : State authority Entry size)
  exact congrArg (fun result => (paid + result.1, result.2)) comparison

theorem resume_point {Answer : Type} (fuel : Nat) (previous : Saved authority required Answer) :
    (current authority required
      (Cursor.resume (provider authority required) (client Answer) (fun _ _ => 1) fuel previous)).point =
      (current authority required previous).point := by
  rcases previous with ⟨paid, outcome⟩
  cases outcome with
  | done result => rfl
  | paused packet =>
      rcases packet with ⟨index, control, saved⟩
      have comparison := PrimitiveProgram.advance_is_direct (step authority required) (fun _ _ => 1)
        fuel control saved
      have same := congrArg (fun result => result.2.2.point) comparison
      obtain ⟨_, _, point⟩ := direct_origin authority required fuel control saved
      exact same.trans point

/-- At the reached service state the current read is reflexive. The right is
still a genuine premise; it is not recovered from retained observations. -/
theorem at_reached_state {Answer : Type} (reader : Fin size) (fuel : Nat)
    (previous : Saved authority required Answer)
    (allowed : FrameUpdate (current authority required previous).point.authority
      (needed (current authority required previous).point.world)) :
    resume authority required needed (current authority required previous).store
      (current authority required previous).point reader fuel previous =
        .ok (Cursor.resume (provider authority required) (client Answer) (fun _ _ => 1) fuel previous) := by
  rcases previous with ⟨paid, outcome⟩
  cases outcome with
  | done result => simp only [resume, Cursor.resume, ite_self]
  | paused packet =>
      rcases packet with ⟨index, control, saved⟩
      cases fuel with
      | zero => rfl
      | succ fuel =>
          cases control with
          | error fault => rfl
          | ok program =>
              cases program with
              | ret answer => rfl
              | call request next =>
                  exact pending_admitted authority required needed saved.store saved.point reader fuel paid request next
                    saved allowed (by simp [OrderedDependencyStore.checkRead, OrderedDependencyStore.readStamp])

/-- Splitting a fixed reached-state invocation retains every actual control,
own write and paid operation. External changes are separate admissions. -/
theorem split {Answer : Type} (reader : Fin size) (first second : Nat)
    (previous : Saved authority required Answer)
    (allowed : FrameUpdate (current authority required previous).point.authority
      (needed (current authority required previous).point.world)) :
    (resume authority required needed (current authority required previous).store
      (current authority required previous).point reader first previous).bind (fun reached =>
        resume authority required needed (current authority required reached).store
          (current authority required reached).point reader second reached) =
    resume authority required needed (current authority required previous).store
      (current authority required previous).point reader (first + second) previous := by
  rw [at_reached_state authority required needed reader first previous allowed]
  simp only [Except.bind]
  have laterAllowed : FrameUpdate
      (current authority required
        (Cursor.resume (provider authority required) (client Answer) (fun _ _ => 1) first previous)).point.authority
      (needed (current authority required
        (Cursor.resume (provider authority required) (client Answer) (fun _ _ => 1) first previous)).point.world) := by
    rw [resume_point authority required first previous]
    exact allowed
  rw [at_reached_state authority required needed reader second _ laterAllowed,
    at_reached_state authority required needed reader (first + second) previous allowed,
    Cursor.resume_add]

end Invocation

theorem step_ok (s after : State authority Entry size) (request : Request Entry size)
    (reply : Reply request) (ran : step authority required s request = (after, .ok reply)) :
    (action authority required request).Safe s ∧ (action authority required request).Step s reply after := by
  cases request with
  | read reader =>
      simp only [step, Prod.mk.injEq] at ran
      exact ⟨trivial, (Except.ok.inj ran.2).symm, ran.1.symm⟩
  | validate stamp =>
      simp only [step, Prod.mk.injEq] at ran
      exact ⟨trivial, (Except.ok.inj ran.2).symm, ran.1.symm⟩
  | write change =>
      by_cases allowed : FrameUpdate s.point.authority (required change s.point.world)
      · simp only [step, if_pos allowed, Prod.mk.injEq] at ran
        exact ⟨allowed, ran.1.symm⟩
      · simp only [step, if_neg allowed, Prod.mk.injEq] at ran
        cases ran.2

/-- Successful completion reflects to the independently specified action
semantics without assuming a desired answer or whole-program safety. -/
theorem direct_ok_runs {Answer : Type} (fuel : Nat)
    (program : Prog (Request Entry size) Reply Answer) (s after : State authority Entry size)
    (answer : Answer)
    (finished : (PrimitiveProgram.direct (step authority required) (fun _ _ => 1)
      fuel (.ok program) s).2 = (.inl (.ok answer), after)) :
    program.Runs (action authority required) s answer after := by
  induction fuel generalizing program s with
  | zero => cases finished
  | succ fuel ih =>
      cases program with
      | ret value =>
          simpa only [PrimitiveProgram.direct, Prod.mk.injEq, Sum.inl.injEq, Except.ok.injEq,
            Prog.Runs] using finished
      | call request next =>
          rcases performed : step authority required s request with ⟨middle, reply⟩
          cases reply with
          | error fault =>
              cases fuel <;> simp only [PrimitiveProgram.direct, performed, Prod.mk.injEq] at finished
              · cases finished.1
              · cases Sum.inl.inj finished.1
          | ok reply =>
              exact ⟨reply, middle, (step_ok authority required s middle request reply performed).2,
                ih (next reply) middle (by simpa only [PrimitiveProgram.direct, performed] using finished)⟩

theorem slice_ok_runs {Answer : Type} (fuel paid spent : Nat)
    (program : Prog (Request Entry size) Reply Answer) (s after : State authority Entry size)
    (answer : Answer)
    (finished : Cursor.resume (provider authority required) (client Answer) (fun _ _ => 1) (base := PUnit.unit) fuel
      (paid, .paused ⟨PUnit.unit, .ok program, s⟩) =
        (spent, .done ⟨PUnit.unit, .ok answer, after⟩)) :
    program.Runs (action authority required) s answer after := by
  have comparison := PrimitiveProgram.advance_is_direct (step authority required) (fun _ _ => 1)
    fuel (.ok program) s
  have result := congrArg (fun value : Saved authority required Answer =>
    PrimitiveProgram.readOutcome (step authority required) value.2) finished
  change PrimitiveProgram.readOutcome (step authority required)
    (Cursor.advance (provider authority required) (client Answer) (fun _ _ => 1) fuel
      ⟨PUnit.unit, .ok program, s⟩).2 = (.inl (.ok answer), after) at result
  exact direct_ok_runs authority required fuel program s after answer
    ((congrArg Prod.snd comparison).symm.trans result)

namespace CapturedClosure

variable {Argument Answer : Type}

/-- The returned function closes over the actual stamped read reply. It
contains no authority point; invocation supplies its current service state. -/
def capture (reader : Fin size)
    (body : (OrderedDependencyStore.ReadStamp size × List Entry) →
      Argument → Prog (Request Entry size) Reply Answer) :
    Prog (Request Entry size) Reply (Argument → Prog (Request Entry size) Reply Answer) :=
  .call (.read reader) fun observed => .ret (body observed)

omit permission in
theorem capture_runs (reader : Fin size)
    (body : (OrderedDependencyStore.ReadStamp size × List Entry) →
      Argument → Prog (Request Entry size) Reply Answer)
    (s after : State authority Entry size)
    (closed : Argument → Prog (Request Entry size) Reply Answer) :
    (capture reader body).Runs (action authority required) s closed after ↔
      closed = body (OrderedDependencyStore.readStamp s.store reader,
        (run (OrderedDependencyStore.query s.store) (.read reader .pure)).answer) ∧ after = s := by
  simp only [capture, Prog.Runs, action, run]
  constructor
  · rintro ⟨reply, middle, ⟨rfl, rfl⟩, equal, same⟩
    exact ⟨equal.symm, same.symm⟩
  · rintro ⟨closedEq, same⟩
    subst closed
    subst after
    exact ⟨_, s, ⟨rfl, rfl⟩, rfl, rfl⟩

theorem capture_complete (reader : Fin size)
    (body : (OrderedDependencyStore.ReadStamp size × List Entry) →
      Argument → Prog (Request Entry size) Reply Answer) (s : State authority Entry size) :
    advance authority required 2 (capture reader body) s =
      (1, .done ⟨PUnit.unit,
        .ok (body (OrderedDependencyStore.readStamp s.store reader, OrderedDependencyStore.query s.store reader)), s⟩) := rfl

/-- Prepare invocation only from an actual completed successful callback.
The earned capture and its paid prefix are retained by the caller. Preparation
executes no service and does not copy an old authority into the new call. -/
def start (live : OrderedDependencyStore.Store Entry size) (point : IndexedAuthority.Point authority)
    (argument : Argument)
    (earned : Saved authority required (Argument → Prog (Request Entry size) Reply Answer)) :
    Option (Saved authority required Answer) :=
  match earned.2 with
  | .done ⟨_, .ok closed, _⟩ =>
      some (earned.1, .paused ⟨PUnit.unit, .ok (closed argument), ⟨live, point⟩⟩)
  | .done ⟨_, .error _, _⟩ | .paused _ => none

variable (needed : (world : World) → authority.Fibre world)
  [admission : ∀ point : IndexedAuthority.Point authority,
    Decidable (FrameUpdate point.authority (needed point.world))]

def invoke (live : OrderedDependencyStore.Store Entry size) (point : IndexedAuthority.Point authority)
    (reader : Fin size) (fuel : Nat) (argument : Argument)
    (earned : Saved authority required (Argument → Prog (Request Entry size) Reply Answer)) :
    Option (Except (Saved authority required Answer) (Saved authority required Answer)) :=
  (start authority required live point argument earned).map
    (Invocation.resume authority required needed live point reader fuel)

omit permission admission in
theorem capture_then_runs (reader : Fin size)
    (body : (OrderedDependencyStore.ReadStamp size × List Entry) →
      Argument → Prog (Request Entry size) Reply Answer)
    (argument : Argument) (s after : State authority Entry size) (answer : Answer) :
    ((capture reader body).bind (fun closed => closed argument)).Runs (action authority required) s answer after ↔
      (body (OrderedDependencyStore.readStamp s.store reader,
        (run (OrderedDependencyStore.query s.store) (.read reader .pure)).answer) argument).Runs
          (action authority required) s answer after := by
  rw [Prog.runs_bind]
  constructor
  · rintro ⟨closed, middle, captured, suffix⟩
    obtain ⟨rfl, rfl⟩ := (capture_runs authority required reader body s middle closed).mp captured
    exact suffix
  · intro suffix
    exact ⟨_, s, (capture_runs authority required reader body s s _).mpr ⟨rfl, rfl⟩, suffix⟩

/-- The old rows select the actual pending program, but its store and
authority are the newly supplied service entrance, not the capture state. -/
theorem start_capture (reader : Fin size)
    (body : (OrderedDependencyStore.ReadStamp size × List Entry) →
      Argument → Prog (Request Entry size) Reply Answer)
    (argument : Argument) (captured : State authority Entry size)
    (live : OrderedDependencyStore.Store Entry size) (point : IndexedAuthority.Point authority) :
    start authority required live point argument (advance authority required 2 (capture reader body) captured) =
      some (1, .paused ⟨PUnit.unit,
        .ok (body (OrderedDependencyStore.readStamp captured.store reader,
          OrderedDependencyStore.query captured.store reader) argument), ⟨live, point⟩⟩) := rfl

/-- Earned closure invocation reflects to the independent stateful body
meaning in its current entrance world, with the original captured reply. -/
theorem completed_source (reader : Fin size)
    (body : (OrderedDependencyStore.ReadStamp size × List Entry) →
      Argument → Prog (Request Entry size) Reply Answer)
    (argument : Argument) (captured : State authority Entry size)
    (live : OrderedDependencyStore.Store Entry size) (point : IndexedAuthority.Point authority)
    (fuel spent : Nat) (answer : Answer) (after : State authority Entry size)
    (allowed : FrameUpdate point.authority (needed point.world))
    (finished : invoke authority required needed live point reader fuel argument
      (advance authority required 2 (capture reader body) captured) =
        some (.ok (spent, .done ⟨PUnit.unit, .ok answer, after⟩))) :
    (body (OrderedDependencyStore.readStamp captured.store reader,
      (run (OrderedDependencyStore.query captured.store) (.read reader .pure)).answer) argument).Runs
        (action authority required) ⟨live, point⟩ answer after := by
  have entered := Invocation.at_reached_state authority required needed reader fuel
    (1, .paused ⟨PUnit.unit, .ok (body (OrderedDependencyStore.readStamp captured.store reader,
      OrderedDependencyStore.query captured.store reader) argument), ⟨live, point⟩⟩) allowed
  simp only [current, PrimitiveProgram.readOutcome] at entered
  simp only [invoke, start_capture, Option.map_some, Option.some.injEq] at finished
  rw [entered] at finished
  exact slice_ok_runs authority required fuel 1 spent _ ⟨live, point⟩ after answer (Except.ok.inj finished)

end CapturedClosure

namespace ReturnMap

variable {A B C : Type}

/-- Change only the final return of the actual retained program. No service
is requested, and reply-dependent continuations keep their original suffix. -/
def control (f : A → B) : Except Fault (Prog (Request Entry size) Reply A) →
    Except Fault (Prog (Request Entry size) Reply B)
  | .error fault => .error fault
  | .ok program => .ok (program.bind (fun value => .ret (f value)))

def outcome (f : A → B) :
    Outcome (provider authority required) (client A) PUnit.unit →
    Outcome (provider authority required) (client B) PUnit.unit
  | .paused ⟨index, code, state⟩ => .paused ⟨index, control f code, state⟩
  | .done ⟨index, .ok value, state⟩ => .done ⟨index, .ok (f value), state⟩
  | .done ⟨index, .error fault, state⟩ => .done ⟨index, .error fault, state⟩

def saved (f : A → B) (previous : Saved authority required A) : Saved authority required B :=
  (previous.1, outcome authority required f previous.2)

theorem state_and_paid (f : A → B) (previous : Saved authority required A) :
    current authority required (saved authority required f previous) = current authority required previous ∧
      (saved authority required f previous).1 = previous.1 := by
  rcases previous with ⟨paid, result⟩
  cases result with
  | paused packet => rcases packet with ⟨index, code, state⟩; exact ⟨rfl, rfl⟩
  | done result =>
      rcases result with ⟨index, value, state⟩
      cases value <;> exact ⟨rfl, rfl⟩

theorem completed_map (f : A → B) (previous : Saved authority required A) :
    completed authority required (saved authority required f previous) =
      (completed authority required previous).map (Except.map f) := by
  rcases previous with ⟨paid, result⟩
  cases result with
  | paused packet => rfl
  | done result => rcases result with ⟨index, value, state⟩; cases value <;> rfl

theorem compose (f : A → B) (g : B → C) (previous : Saved authority required A) :
    saved authority required g (saved authority required f previous) =
      saved authority required (g ∘ f) previous := by
  rcases previous with ⟨paid, result⟩
  cases result with
  | done result => rcases result with ⟨index, value, state⟩; cases value <;> rfl
  | paused packet =>
      rcases packet with ⟨index, code, state⟩
      cases code with
      | error fault => rfl
      | ok program => simp [saved, outcome, control, Prog.bind_assoc]

theorem identity (previous : Saved authority required A) :
    saved authority required id previous = previous := by
  rcases previous with ⟨paid, result⟩
  cases result with
  | done result => rcases result with ⟨index, value, state⟩; cases value <;> rfl
  | paused packet =>
      rcases packet with ⟨index, code, state⟩
      cases code with
      | error fault => rfl
      | ok program => simp [saved, outcome, control, Prog.bind_ret]

private def readout (f : A → B) :
    ((Except Fault A ⊕ Except Fault (Prog (Request Entry size) Reply A)) × State authority Entry size) →
    ((Except Fault B ⊕ Except Fault (Prog (Request Entry size) Reply B)) × State authority Entry size)
  | (.inl value, state) => (.inl (value.map f), state)
  | (.inr code, state) => (.inr (control f code), state)

private theorem readout_outcome (f : A → B)
    (result : Outcome (provider authority required) (client A) PUnit.unit) :
    PrimitiveProgram.readOutcome (step authority required) (outcome authority required f result) =
      readout authority f (PrimitiveProgram.readOutcome (step authority required) result) := by
  cases result with
  | paused packet => rfl
  | done result => rcases result with ⟨index, value, state⟩; cases value <;> rfl

theorem direct_map (f : A → B) (fuel : Nat)
    (code : Except Fault (Prog (Request Entry size) Reply A)) (state : State authority Entry size) :
    PrimitiveProgram.direct (step authority required) (fun _ _ => 1) fuel (control f code) state =
      let original := PrimitiveProgram.direct (step authority required) (fun _ _ => 1) fuel code state
      (original.1, readout authority f original.2) := by
  induction fuel generalizing code state with
  | zero => rfl
  | succ fuel ih =>
      cases code with
      | error fault => rfl
      | ok program =>
          cases program with
          | ret value => rfl
          | call request next =>
              rcases performed : step authority required state request with ⟨middle, reply⟩
              cases reply with
              | error fault =>
                  simpa only [PrimitiveProgram.direct, control, Prog.bind, performed] using
                    congrArg (fun result : Nat × ((Except Fault B ⊕ Except Fault (Prog (Request Entry size) Reply B)) × State authority Entry size) =>
                      (1 + result.1, result.2)) (ih (.error fault) middle)
              | ok value =>
                  simpa only [PrimitiveProgram.direct, control, Prog.bind, performed] using
                    congrArg (fun result : Nat × ((Except Fault B ⊕ Except Fault (Prog (Request Entry size) Reply B)) × State authority Entry size) =>
                      (1 + result.1, result.2)) (ih (.ok (next value)) middle)

theorem advance_map (f : A → B) (fuel : Nat)
    (code : Except Fault (Prog (Request Entry size) Reply A)) (state : State authority Entry size) :
    Cursor.advance (provider authority required) (client B) (fun _ _ => 1) fuel
      ⟨PUnit.unit, control f code, state⟩ =
      saved authority required f
        (Cursor.advance (provider authority required) (client A) (fun _ _ => 1) fuel
          ⟨PUnit.unit, code, state⟩) := by
  have first := PrimitiveProgram.advance_is_direct (step authority required) (fun _ _ => 1) fuel (control f code) state
  have second := PrimitiveProgram.advance_is_direct (step authority required) (fun _ _ => 1) fuel code state
  have exactPair := first.trans ((direct_map authority required f fuel code state).trans
    (congrArg (fun result => (result.1, readout authority f result.2)) second.symm))
  have paid : (Cursor.advance (provider authority required) (client B) (fun _ _ => 1) fuel
      ⟨PUnit.unit, control f code, state⟩).1 =
      (Cursor.advance (provider authority required) (client A) (fun _ _ => 1) fuel
        ⟨PUnit.unit, code, state⟩).1 := congrArg Prod.fst exactPair
  have residual : (Cursor.advance (provider authority required) (client B) (fun _ _ => 1) fuel
      ⟨PUnit.unit, control f code, state⟩).2 =
      outcome authority required f
        (Cursor.advance (provider authority required) (client A) (fun _ _ => 1) fuel
          ⟨PUnit.unit, code, state⟩).2 :=
    PrimitiveProgram.readOutcome_injective (step authority required)
      ((congrArg Prod.snd exactPair).trans (readout_outcome authority required f _).symm)
  exact Prod.ext paid residual

/-- Result mapping commutes with arbitrary subdivision of the same actual
computation, including a nonfresh cut and faults. -/
theorem resume_map (f : A → B) (fuel : Nat) (previous : Saved authority required A) :
    Cursor.resume (provider authority required) (client B) (fun _ _ => 1) fuel
        (saved authority required f previous) =
      saved authority required f
        (Cursor.resume (provider authority required) (client A) (fun _ _ => 1) fuel previous) := by
  rcases previous with ⟨paid, result⟩
  cases result with
  | done result => rcases result with ⟨index, value, state⟩; cases value <;> rfl
  | paused packet =>
      rcases packet with ⟨index, code, state⟩
      cases index
      change (paid + (Cursor.advance (provider authority required) (client B) (fun _ _ => 1) fuel ⟨PUnit.unit, control f code, state⟩).1,
        (Cursor.advance (provider authority required) (client B) (fun _ _ => 1) fuel ⟨PUnit.unit, control f code, state⟩).2) = _
      rw [advance_map]
      rfl

theorem schedule_map (f : A → B) (grants : List Nat) (previous : Saved authority required A) :
    schedule authority required grants (saved authority required f previous) =
      saved authority required f (schedule authority required grants previous) := by
  induction grants generalizing previous with
  | nil => rfl
  | cons fuel rest ih =>
      simp only [schedule, List.foldl_cons]
      rw [resume_map]
      exact ih _

variable (needed : (world : World) → authority.Fibre world)
  [admission : ∀ point : IndexedAuthority.Point authority,
    Decidable (FrameUpdate point.authority (needed point.world))]

/-- Mapping a return changes neither the current entrance decision nor the
retained refused cut. No authority is obtained from the mapped value. -/
theorem invocation_map (f : A → B) (live : OrderedDependencyStore.Store Entry size)
    (point : IndexedAuthority.Point authority) (reader : Fin size) (fuel : Nat)
    (previous : Saved authority required A) :
    Invocation.resume authority required needed live point reader fuel (saved authority required f previous) =
      match Invocation.resume authority required needed live point reader fuel previous with
      | .error refused => .error (saved authority required f refused)
      | .ok admitted => .ok (saved authority required f admitted) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      rcases previous with ⟨paid, result⟩
      cases result with
      | done result => rcases result with ⟨index, value, state⟩; cases value <;> rfl
      | paused packet =>
          rcases packet with ⟨index, code, state⟩
          cases index
          cases code with
          | error fault => exact congrArg Except.ok (resume_map authority required f (fuel + 1) _)
          | ok program =>
              cases program with
              | ret value => exact congrArg Except.ok (resume_map authority required f (fuel + 1) _)
              | call request next =>
                  change Invocation.resume authority required needed live point reader (fuel + 1)
                    (paid, .paused ⟨PUnit.unit, .ok (.call request
                      (fun reply => (next reply).bind (fun value => .ret (f value)))), state⟩) = _
                  by_cases allowed : FrameUpdate point.authority (needed point.world)
                  · cases valid : OrderedDependencyStore.checkRead live (OrderedDependencyStore.readStamp state.store reader) with
                    | false =>
                        rw [Invocation.pending_refused authority required needed live point reader fuel paid
                          request (fun reply => (next reply).bind (fun value => .ret (f value))) state (Or.inr valid),
                          Invocation.pending_refused authority required needed live point reader fuel paid request next state (Or.inr valid)]
                        rfl
                    | true =>
                        rw [Invocation.pending_admitted authority required needed live point reader fuel paid
                          request (fun reply => (next reply).bind (fun value => .ret (f value))) state allowed valid,
                          Invocation.pending_admitted authority required needed live point reader fuel paid request next state allowed valid]
                        exact congrArg Except.ok (resume_map authority required f (fuel + 1)
                          (paid, .paused ⟨PUnit.unit, .ok (.call request next), ⟨live, point⟩⟩))
                  · rw [Invocation.pending_refused authority required needed live point reader fuel paid
                      request (fun reply => (next reply).bind (fun value => .ret (f value))) state (Or.inl allowed),
                      Invocation.pending_refused authority required needed live point reader fuel paid request next state (Or.inl allowed)]
                    rfl

omit permission in
theorem runs (f : A → B) (program : Prog (Request Entry size) Reply A)
    (before after : State authority Entry size) (answer : B) :
    (program.bind (fun value => .ret (f value))).Runs (action authority required) before answer after ↔
      ∃ value, program.Runs (action authority required) before value after ∧ f value = answer := by
  rw [Prog.runs_bind]
  constructor
  · rintro ⟨value, middle, execution, equal, rfl⟩
    exact ⟨value, execution, equal⟩
  · rintro ⟨value, execution, equal⟩
    exact ⟨value, after, execution, equal, rfl⟩

/-- A mapped return completed from an actual retained producer cut has an
independently interpreted producer origin. This applies equally to closed
functions and to records carrying a recipe with its continuation. -/
theorem producer_source (f : A → B)
    (producer : Prog (Request Entry size) Reply A) (initial after : State authority Entry size)
    (first later paid : Nat) (mapped : B)
    (finished : Cursor.resume (provider authority required) (client _) (fun _ _ => 1) later
      (saved authority required f (advance authority required first producer initial)) =
        (paid, .done ⟨PUnit.unit, .ok mapped, after⟩)) :
    ∃ value, producer.Runs (action authority required) initial value after ∧ f value = mapped := by
  unfold advance at finished
  rw [← advance_map authority required f first (.ok producer) initial,
    ← Cursor.advance_add] at finished
  have reflection := slice_ok_runs authority required (first + later) 0 paid
    (producer.bind (fun value => .ret (f value))) initial after mapped
    (by simpa only [Cursor.resume, Nat.zero_add, control, Prod.eta] using finished)
  exact (runs authority required f producer initial after mapped).mp reflection

end ReturnMap

namespace CapturedClosure

variable {Environment Argument Answer : Type}

/-- Close the actual producer cut, rather than restarting its source. The
complete environment is supplied only by its eventual real return. -/
abbrev close (body : Environment → Argument → Prog (Request Entry size) Reply Answer)
    (producer : Saved authority required Environment) := ReturnMap.saved authority required body producer

/-- A closure completed after attaching its return map at an arbitrary cut
originates in an actual independently interpreted producer execution. -/
theorem producer_source (body : Environment → Argument → Prog (Request Entry size) Reply Answer)
    (producer : Prog (Request Entry size) Reply Environment) (initial after : State authority Entry size)
    (first later paid : Nat) (closed : Argument → Prog (Request Entry size) Reply Answer)
    (finished : Cursor.resume (provider authority required) (client _) (fun _ _ => 1) later
      (close authority required body (advance authority required first producer initial)) =
        (paid, .done ⟨PUnit.unit, .ok closed, after⟩)) :
    ∃ environment, producer.Runs (action authority required) initial environment after ∧ body environment = closed :=
  ReturnMap.producer_source authority required body producer initial after first later paid closed finished

variable (needed : (world : World) → authority.Fibre world)
  [admission : ∀ point : IndexedAuthority.Point authority,
    Decidable (FrameUpdate point.authority (needed point.world))]

/-- The producer may have performed effects before closing. Its earned
environment selects the body; invocation executes that body in its current
service world. Neither the producer nor its saved permission is replayed. -/
theorem nonfresh_completed_source
    (body : Environment → Argument → Prog (Request Entry size) Reply Answer)
    (producer : Prog (Request Entry size) Reply Environment) (initial : State authority Entry size)
    (first later : Nat) (live : OrderedDependencyStore.Store Entry size)
    (point : IndexedAuthority.Point authority) (reader : Fin size) (fuel paid : Nat)
    (argument : Argument) (answer : Answer) (after : State authority Entry size)
    (allowed : FrameUpdate point.authority (needed point.world))
    (finished : invoke authority required needed live point reader fuel argument
      (Cursor.resume (provider authority required) (client _) (fun _ _ => 1) later
        (close authority required body (advance authority required first producer initial))) =
          some (.ok (paid, .done ⟨PUnit.unit, .ok answer, after⟩))) :
    ∃ environment capturedState,
      producer.Runs (action authority required) initial environment capturedState ∧
      (body environment argument).Runs (action authority required) ⟨live, point⟩ answer after := by
  generalize earned : Cursor.resume (provider authority required) (client _) (fun _ _ => 1) later
    (close authority required body (advance authority required first producer initial)) = cut at finished
  rcases cut with ⟨priorPaid, result⟩
  cases result with
  | paused packet => simp only [invoke, start, Option.map_none, reduceCtorEq] at finished
  | done result =>
      rcases result with ⟨index, value, capturedState⟩
      cases index
      cases value with
      | error fault => simp only [invoke, start, Option.map_none, reduceCtorEq] at finished
      | ok closed =>
          obtain ⟨environment, produced, same⟩ := producer_source authority required body producer initial capturedState
            first later priorPaid closed earned
          have entered := Invocation.at_reached_state authority required needed reader fuel
            (priorPaid, .paused ⟨PUnit.unit, .ok (closed argument), ⟨live, point⟩⟩) allowed
          simp only [current, PrimitiveProgram.readOutcome] at entered
          simp only [invoke, start, Option.map_some, Option.some.injEq] at finished
          rw [entered] at finished
          refine ⟨environment, capturedState, produced, ?_⟩
          rw [same]
          exact slice_ok_runs authority required fuel priorPaid paid (closed argument) ⟨live, point⟩ after answer
            (Except.ok.inj finished)

end CapturedClosure

/-! ## Current service entrances for the existing owned return boundary

The retained source and the reached live invocation state remain separate.
Both producing a new loan and publishing a held loan require a current service
entrance. Reading an already earned value grants neither entrance. The callback
consumer, including a refusal's context update, is the existing retained adapter.
-/

namespace CallService

open Fold.OwnedSequence.CallbackBoundary

variable {Answer Context : Type}
  (needed : (world : World) → authority.Fibre world)
  [admission : ∀ point : IndexedAuthority.Point authority,
    Decidable (FrameUpdate point.authority (needed point.world))]

abbrev Loan := Finished (OwnWrite.provider authority required)
  (Return := fun _ _ => Except Fault Answer) PUnit.unit

abbrev Session := Retained.State (OwnWrite.provider authority required)
  (OwnWrite.client Answer) PUnit.unit (State authority Entry size × Context)

variable (reader : Fin size)

/-- Current data and permission are checked from actual retained states.
No stamp, return payload or recording issues a permission. -/
def eligible (state : Session authority required (Answer := Answer) (Context := Context)) : Prop :=
  FrameUpdate state.context.1.point.authority (needed state.context.1.point.world) ∧
    OrderedDependencyStore.checkRead state.context.1.store
      (OrderedDependencyStore.readStamp (current authority required state.computation).store reader) = true

instance eligibleDecision (state : Session authority required (Answer := Answer) (Context := Context)) :
    Decidable (eligible authority required needed reader state) := inferInstanceAs (Decidable (_ ∧ _))

variable (quantum : Context → Nat)
  (isReturn : Loan authority required (Answer := Answer) → Bool)
  (rearm : Loan authority required (Answer := Answer) →
    Packet (OwnWrite.provider authority required) (OwnWrite.client Answer) PUnit.unit)
  (consume : (State authority Entry size × Context) → Loan authority required (Answer := Answer) →
    Bool × (State authority Entry size × Context))

/-- A zero-work use of the existing retained adapter classifies the actual
source outcome and implements acceptance/rearming without another source pull. -/
abbrev boundary := Retained.provider (OwnWrite.provider authority required) (OwnWrite.client Answer)
  PUnit.unit (fun _ _ => 1) 0 isReturn rearm consume

/-- Only an actual positive pending service entrance can replace the live
context by its reached state. Administrative completion and zero source work
must not discard newer compatible data or current authority. -/
def liveAfter (state : Session authority required (Answer := Answer) (Context := Context))
    (later : Saved authority required Answer) : State authority Entry size :=
  match state.computation.2 with
  | .paused ⟨_, .ok (.call _ _), _⟩ =>
      if quantum state.context.2 = 0 then state.context.1 else current authority required later
  | _ => state.context.1

/-- The provider invokes the actual saved program at the current service
point. Authorized own writes install their reached state. Refused entry keeps
the whole source, paid prefix and consumer context. -/
def provider : Provider (Fold.OwnedSequence.CallbackBoundary.protocol (Loan authority required (Answer := Answer))
    (Loan authority required (Answer := Answer))) where
  State _ _ := Session authority required (Answer := Answer) (Context := Context)
  step state request :=
    if eligible authority required needed reader state then
      match request with
      | .accept item => (boundary authority required isReturn rearm consume).step state (.accept item)
      | .next =>
          match Invocation.resume authority required needed state.context.1.store state.context.1.point
              reader (quantum state.context.2) state.computation with
          | .error _ => ⟨.paused, state⟩
          | .ok later =>
              (boundary authority required isReturn rearm consume).step
                ⟨later, liveAfter authority required quantum state later, state.context.2⟩ .next
    else match request with
      | .next => ⟨.paused, state⟩
      | .accept _ => ⟨false, state⟩

theorem next_refused (state : Session authority required (Answer := Answer) (Context := Context))
    (denied : ¬ eligible authority required needed reader state) :
    (provider authority required needed reader quantum isReturn rearm consume).step
      (base := ()) (index := ()) state .next = ⟨.paused, state⟩ := by
  simp only [provider, if_neg denied]

theorem publication_refused (state : Session authority required (Answer := Answer) (Context := Context))
    (item : Loan authority required (Answer := Answer))
    (denied : ¬ eligible authority required needed reader state) :
    (provider authority required needed reader quantum isReturn rearm consume).step
      (base := ()) (index := ()) state (.accept item) = ⟨false, state⟩ := by
  change (if eligible authority required needed reader state then _ else _) = _
  exact if_neg denied

/-- Acceptance never advances the source. A refused consumer may still update
its actual private context, exactly as in the common retained boundary. -/
theorem publication_is_retained (state : Session authority required (Answer := Answer) (Context := Context))
    (item : Loan authority required (Answer := Answer))
    (allowed : eligible authority required needed reader state) :
    (provider authority required needed reader quantum isReturn rearm consume).step
      (base := ()) (index := ()) state (.accept item) =
      (boundary authority required isReturn rearm consume).step state (.accept item) := by
  change (if eligible authority required needed reader state then _ else _) = _
  exact if_pos allowed

theorem publication_preserves_paid (state : Session authority required (Answer := Answer) (Context := Context))
    (item : Loan authority required (Answer := Answer)) :
    ((provider authority required needed reader quantum isReturn rearm consume).step
      (base := ()) (index := ()) state (.accept item)).2.computation.1 = state.computation.1 := by
  by_cases allowed : eligible authority required needed reader state
  · rw [publication_is_retained authority required needed reader quantum isReturn rearm consume state item allowed]
    exact Retained.accept_preserves_source_charge _ _ _ _ _ _ _ _ state item
  · rw [publication_refused authority required needed reader quantum isReturn rearm consume state item allowed]

/-- Exact actual invocation: the zero-work retained adapter performs only
classification after this invocation, retaining its complete reached state. -/
theorem next_invoked (state : Session authority required (Answer := Answer) (Context := Context))
    (allowed : eligible authority required needed reader state)
    (later : Saved authority required Answer)
    (invoked : Invocation.resume authority required needed state.context.1.store state.context.1.point
      reader (quantum state.context.2) state.computation = .ok later) :
    ((provider authority required needed reader quantum isReturn rearm consume).step
      (base := ()) (index := ()) state .next).2 =
      ⟨later, liveAfter authority required quantum state later, state.context.2⟩ := by
  simp only [provider]
  rw [if_pos allowed, invoked]
  exact (Retained.next_retains_outcome (OwnWrite.provider authority required) (OwnWrite.client Answer)
    PUnit.unit (fun _ _ => 1) 0 isReturn rearm consume
    ⟨later, liveAfter authority required quantum state later, state.context.2⟩).trans (by rw [resume_zero])

/-- The real source-progress entrance agrees with the independent primitive
executor, including faults, the residual program, reached state and paid work. -/
theorem pending_is_direct (fuel paid : Nat) (context : Context)
    (live saved : State authority Entry size) (request : Request Entry size)
    (next : Reply request → Prog (Request Entry size) Reply Answer)
    (allowed : FrameUpdate live.point.authority (needed live.point.world))
    (valid : OrderedDependencyStore.checkRead live.store
      (OrderedDependencyStore.readStamp saved.store reader) = true) :
    let previous : Session authority required (Answer := Answer) (Context := Context) :=
      ⟨(paid, .paused ⟨PUnit.unit, .ok (.call request next), saved⟩), live, context⟩
    let after := ((provider authority required needed reader (fun _ => fuel + 1)
      isReturn rearm consume).step (base := ()) (index := ()) previous .next).2
    let direct := PrimitiveProgram.direct (OwnWrite.step authority required) (fun _ _ => 1)
      (fuel + 1) (.ok (.call request next)) live
    (after.computation.1, PrimitiveProgram.readOutcome (OwnWrite.step authority required)
      after.computation.2) = (paid + direct.1, direct.2) ∧
      after.context = (current authority required after.computation, context) := by
  dsimp only
  have comparison := Invocation.pending_is_direct authority required needed live.store live.point reader
    fuel paid request next saved allowed valid
  have actual := next_invoked authority required needed reader (fun _ => fuel + 1) isReturn rearm consume
    ⟨(paid, .paused ⟨PUnit.unit, .ok (.call request next), saved⟩), live, context⟩ ⟨allowed, valid⟩ _ comparison.1
  rw [actual]
  exact ⟨comparison.2, rfl⟩

#print axioms next_refused
#print axioms publication_refused
#print axioms publication_preserves_paid
#print axioms next_invoked
#print axioms pending_is_direct

end CallService

namespace Controls

local instance : Fintype Access :=
  ⟨{.none, .read, .consume}, by intro access; cases access <;> simp⟩

def requirement (_ : OrderedDependencyStore.Action Nat 3) (world : Bool) :
    revocationWorlds.Fibre world := Access.consume

local instance permissionDecision (point : IndexedAuthority.Point revocationWorlds)
    (change : OrderedDependencyStore.Action Nat 3) :
    Decidable (FrameUpdate point.authority (requirement change point.world)) :=
  inferInstanceAs (Decidable (∀ frame : Access,
    Access.separate point.authority frame = true → Access.separate Access.consume frame = true))

def held : IndexedAuthority.Point revocationWorlds := ⟨false, .consume⟩
def revoked : IndexedAuthority.Point revocationWorlds :=
  IndexedAuthority.push held (homOfLE (by decide) : false ⟶ true)
def readerOnly : IndexedAuthority.Point revocationWorlds := ⟨false, .read⟩
def source : State revocationWorlds Nat 3 :=
  ⟨OrderedDependencyStore.initial 71 (fun reader => if reader = 0 then [7, 7] else []), held⟩

def program := readWrite (Entry := Nat) (size := 3) 0 (fun _ => .append 0 [11])
def paused := advance revocationWorlds requirement 1 program source
def own := (resumeCurrent revocationWorlds requirement source.store held 0 1 paused).getD paused
def earned := (resumeCurrent revocationWorlds requirement (current revocationWorlds requirement own).store
  held 0 1 own).getD own
def external := OrderedDependencyStore.appendOwn source.store 0 [99]
def unrelated := OrderedDependencyStore.appendOwn source.store 2 [99]

theorem own_write_returns_captured_duplicate_rows :
    completed revocationWorlds requirement paused = none ∧
      completed revocationWorlds requirement own = none ∧
      completed revocationWorlds requirement earned =
        some (.ok (OrderedDependencyStore.readStamp source.store 0, [7, 7])) ∧
      earned.1 = 2 ∧
      OrderedDependencyStore.query (current revocationWorlds requirement earned).store 0 = [7, 7, 11] ∧
      OrderedDependencyStore.checkRead (current revocationWorlds requirement earned).store
        (OrderedDependencyStore.readStamp source.store 0) = false := by decide

def inspectOldAndFresh : Prog (Request Nat 3) Reply (List Nat × List Nat × Bool) :=
  .call (.read 0) fun captured =>
    .call (.write (.replace 0 [11])) fun _ =>
      .call (.validate captured.1) fun stillCurrent =>
        .call (.read 0) fun fresh => .ret (captured.2, fresh.2, stillCurrent)

theorem past_observation_is_neither_fresh_nor_a_validated_future_obligation :
    let actual := advance revocationWorlds requirement 5 inspectOldAndFresh source
    completed revocationWorlds requirement actual = some (.ok ([7, 7], [11], false)) ∧
      actual.1 = 4 ∧ OrderedDependencyStore.query (current revocationWorlds requirement actual).store 0 = [11] := by
  decide

theorem external_interference_refuses_without_healing_the_saved_client :
    (resumeCurrent revocationWorlds requirement external held 0 8 paused).isNone = true ∧
      paused.1 = 1 ∧ completed revocationWorlds requirement paused = none ∧
      OrderedDependencyStore.query (current revocationWorlds requirement paused).store 0 = [7, 7] := by
  decide

theorem unrelated_change_is_retained_by_a_genuine_granted_resume :
    let actual := (resumeCurrent revocationWorlds requirement unrelated held 0 8 paused).getD paused
    completed revocationWorlds requirement actual =
      some (.ok (OrderedDependencyStore.readStamp source.store 0, [7, 7])) ∧
      OrderedDependencyStore.query (current revocationWorlds requirement actual).store 0 = [7, 7, 11] ∧
      OrderedDependencyStore.query (current revocationWorlds requirement actual).store 2 = [99] ∧ actual.1 = 2 := by
  decide

theorem captured_read_supplies_no_write_authority :
    let noRight := (resumeCurrent revocationWorlds requirement source.store revoked 0 8 paused).getD paused
    let readRight := (resumeCurrent revocationWorlds requirement source.store readerOnly 0 8 paused).getD paused
    completed revocationWorlds requirement noRight = some (.error .denied) ∧
      completed revocationWorlds requirement readRight = some (.error .denied) ∧
      OrderedDependencyStore.query (current revocationWorlds requirement noRight).store 0 = [7, 7] ∧
      OrderedDependencyStore.query (current revocationWorlds requirement readRight).store 0 = [7, 7] ∧
      noRight.1 = 2 ∧ readRight.1 = 2 := by decide

theorem zero_and_completed_reentry_keep_the_whole_original_cut :
    resumeCurrent revocationWorlds requirement external revoked 0 0 paused = some paused ∧
      resumeCurrent revocationWorlds requirement external revoked 0 9 earned = some earned := by
  exact ⟨zero_keeps_whole_saved revocationWorlds requirement external revoked 0 paused, by rfl⟩

theorem finite_grants_keep_captured_answer_and_actual_state :
    let actual := schedule revocationWorlds requirement [0, 1, 0, 1, 1, 0]
      (advance revocationWorlds requirement 0 program source)
    completed revocationWorlds requirement actual = completed revocationWorlds requirement earned ∧
      actual.1 = 2 ∧ OrderedDependencyStore.query (current revocationWorlds requirement actual).store 0 = [7, 7, 11] := by
  decide

#print axioms own_write_returns_captured_duplicate_rows
#print axioms past_observation_is_neither_fresh_nor_a_validated_future_obligation
#print axioms external_interference_refuses_without_healing_the_saved_client
#print axioms unrelated_change_is_retained_by_a_genuine_granted_resume
#print axioms captured_read_supplies_no_write_authority
#print axioms zero_and_completed_reentry_keep_the_whole_original_cut
#print axioms finite_grants_keep_captured_answer_and_actual_state

end Controls

namespace InvocationControls

open Mettapedia.Machines.Cursor.ReadOnlyQuery.OwnWrite.Controls (requirement held revoked readerOnly source external)

local instance : Fintype Access :=
  ⟨{.none, .read, .consume}, by intro access; cases access <;> simp⟩

local instance permissionDecision (point : IndexedAuthority.Point revocationWorlds)
    (change : OrderedDependencyStore.Action Nat 3) :
    Decidable (FrameUpdate point.authority (requirement change point.world)) :=
  Controls.permissionDecision point change

def needed (_ : Bool) : Access := .consume
def noRequirement (_ : Bool) : Access := .none

local instance admissionDecision (point : IndexedAuthority.Point revocationWorlds) :
    Decidable (FrameUpdate point.authority (needed point.world)) :=
  inferInstanceAs (Decidable (∀ frame : Access,
    Access.separate point.authority frame = true → Access.separate Access.consume frame = true))

local instance noAdmissionDecision (point : IndexedAuthority.Point revocationWorlds) :
    Decidable (FrameUpdate point.authority (noRequirement point.world)) :=
  inferInstanceAs (Decidable (∀ frame : Access,
    Access.separate point.authority frame = true → Access.separate Access.none frame = true))

abbrev Readout := List Nat × List Nat × Bool

def body (captured : OrderedDependencyStore.ReadStamp 3 × List Nat) (argument : Nat) :
    Prog (Request Nat 3) Reply Readout :=
  .call (.write (.append 0 [argument])) fun _ =>
    .call (.validate captured.1) fun valid =>
      .call (.read 0) fun fresh => .ret (captured.2, fresh.2, valid)

def closed := advance revocationWorlds requirement 2 (CapturedClosure.capture 0 body) source
def pending : Saved revocationWorlds requirement Readout :=
  (CapturedClosure.start revocationWorlds requirement source.store held 11 closed).getD
    (advance revocationWorlds requirement 0 (.ret ([], [], false)) source)

def refused := Invocation.resume revocationWorlds requirement needed source.store readerOnly 0 8 pending
def retained := match refused with | .error saved | .ok saved => saved
def retried := Invocation.resume revocationWorlds requirement needed source.store held 0 4 retained

def observe (attempt : Except (Saved revocationWorlds requirement Readout)
    (Saved revocationWorlds requirement Readout)) :=
  attempt.toOption.map fun saved => (saved.1, completed revocationWorlds requirement saved,
    OrderedDependencyStore.query (current revocationWorlds requirement saved).store 0)

theorem read_only_refusal_keeps_the_actual_closure_call :
    refused = .error pending ∧ pending.1 = 1 ∧ completed revocationWorlds requirement pending = none := by
  refine ⟨?_, rfl, rfl⟩
  apply Invocation.pending_refused
  exact Or.inl (by decide)

theorem genuine_retry_uses_old_capture_and_current_fresh_read :
    observe retried = some (4, some (.ok ([7, 7], [7, 7, 11], false)), [7, 7, 11]) := by rfl

def afterWrite := (Invocation.resume revocationWorlds requirement needed source.store held 0 1 pending).toOption.getD pending
def refusedAfterWrite := Invocation.resume revocationWorlds requirement needed
  (current revocationWorlds requirement afterWrite).store revoked 0 8 afterWrite
def retainedAfterWrite := match refusedAfterWrite with | .error saved | .ok saved => saved
def finishedAfterRetry := Invocation.resume revocationWorlds requirement needed
  (current revocationWorlds requirement retainedAfterWrite).store held 0 3 retainedAfterWrite

theorem refusal_after_paid_effect_does_not_repeat_it :
    refusedAfterWrite = .error afterWrite ∧ afterWrite.1 = 2 ∧
      observe finishedAfterRetry = some (4, some (.ok ([7, 7], [7, 7, 11], false)), [7, 7, 11]) := by
  refine ⟨?_, rfl, by rfl⟩
  apply Invocation.pending_refused
  exact Or.inl (by decide)

theorem stale_pending_source_is_not_refreshed_by_held_permission :
    Invocation.resume revocationWorlds requirement needed external held 0 8 pending = .error pending := by
  apply Invocation.pending_refused
  exact Or.inr (by decide)

theorem earned_closure_can_start_a_new_current_world_call :
    ((CapturedClosure.invoke revocationWorlds requirement needed external held 0 4 11 closed).map observe) =
      some (some (4, some (.ok ([7, 7], [7, 7, 99, 11], false)), [7, 7, 99, 11])) := by rfl

theorem zero_and_earned_result_need_no_new_effect_permission :
    Invocation.resume revocationWorlds requirement needed external revoked 0 0 pending = .ok pending ∧
      (retried.toOption.map fun saved =>
        (Invocation.resume revocationWorlds requirement needed external revoked 0 8 saved).toOption.map
          (completed revocationWorlds requirement)) = some (some (some (.ok ([7, 7], [7, 7, 11], false)))) := by
  exact ⟨rfl, by rfl⟩

theorem unfinished_capture_is_not_an_invocable_closure :
    (CapturedClosure.start revocationWorlds requirement source.store held 11
      (advance revocationWorlds requirement 1 (CapturedClosure.capture 0 body) source)).isNone = true ∧
      (CapturedClosure.start revocationWorlds requirement source.store held 11 closed).isSome = true ∧
      OrderedDependencyStore.query (current revocationWorlds requirement closed).store 0 = [7, 7] := by decide

theorem entrance_eligibility_does_not_hide_an_inner_action_fault :
    let begun := (CapturedClosure.start revocationWorlds requirement source.store readerOnly 11 closed).getD pending
    observe (Invocation.resume revocationWorlds requirement noRequirement source.store readerOnly 0 8 begun) =
      some (2, some (.error .denied), [7, 7]) := by rfl

end InvocationControls

namespace NonfreshControls

open Mettapedia.Machines.Cursor.ReadOnlyQuery.OwnWrite.Controls (requirement held revoked readerOnly source)
open Mettapedia.Machines.Cursor.ReadOnlyQuery.OwnWrite.InvocationControls (needed)

local instance permissionDecision (point : IndexedAuthority.Point revocationWorlds)
    (change : OrderedDependencyStore.Action Nat 3) :
    Decidable (FrameUpdate point.authority (requirement change point.world)) :=
  Controls.permissionDecision point change

local instance admissionDecision (point : IndexedAuthority.Point revocationWorlds) :
    Decidable (FrameUpdate point.authority (needed point.world)) :=
  InvocationControls.admissionDecision point

abbrev Environment := OrderedDependencyStore.ReadStamp 3 × List Nat × List Nat
abbrev Readout := List Nat × List Nat × List Nat × Bool

def adaptive : Program (Fin 3) (List Nat) (List Nat) :=
  .read 1 fun rows => if rows.isEmpty then .read 0 .pure else .pure rows

def producer : Prog (Request Nat 3) Reply Environment :=
  .call (.read 0) fun old =>
    .call (.write (.append 2 [11])) fun _ =>
      (query adaptive).bind fun seen => .ret (old.1, old.2, seen)

def body (environment : Environment) (argument : Nat) : Prog (Request Nat 3) Reply Readout :=
  .call (.write (.append 2 [argument])) fun _ =>
    .call (.validate environment.1) fun valid =>
      .call (.read 0) fun fresh => .ret (environment.2.1, environment.2.2, fresh.2, valid)

def cut := advance revocationWorlds requirement 2 producer source
def closing := CapturedClosure.close revocationWorlds requirement body cut
def earned := Cursor.resume (provider revocationWorlds requirement) (client _) (fun _ _ => 1) 3 closing
def liveC := OrderedDependencyStore.appendOwn (current revocationWorlds requirement earned).store 0 [99]
def fallback : Saved revocationWorlds requirement Readout :=
  advance revocationWorlds requirement 0 (.ret ([], [], [], false)) source
def first := ((CapturedClosure.invoke revocationWorlds requirement needed liveC held 0 4 33 earned).bind
  Except.toOption).getD fallback
def liveD := OrderedDependencyStore.appendOwn (current revocationWorlds requirement first).store 0 [100]
def second := ((CapturedClosure.invoke revocationWorlds requirement needed liveD held 0 4 33 earned).bind
  Except.toOption).getD fallback

def answer (saved : Saved revocationWorlds requirement Readout) : Option Readout :=
  match completed revocationWorlds requirement saved with
  | some (.ok value) => some value
  | _ => none

theorem late_closing_keeps_the_paid_effect_and_actual_suffix :
    cut.1 = 2 ∧ closing.1 = 2 ∧
      OrderedDependencyStore.query (current revocationWorlds requirement closing).store 2 = [11] ∧
      (CapturedClosure.start revocationWorlds requirement liveC held 33 closing).isNone = true ∧
      earned.1 = 4 ∧ (CapturedClosure.start revocationWorlds requirement liveC held 33 earned).isSome = true ∧
      OrderedDependencyStore.query (current revocationWorlds requirement earned).store 2 = [11] := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem repeated_invocation_reuses_environment_without_replaying_producer :
    answer first = some ([7, 7], [7, 7], [7, 7, 99], false) ∧
      answer second = some ([7, 7], [7, 7], [7, 7, 99, 100], false) ∧
      OrderedDependencyStore.query (current revocationWorlds requirement first).store 2 = [11, 33] ∧
      OrderedDependencyStore.query (current revocationWorlds requirement second).store 2 = [11, 33, 33] ∧
      OrderedDependencyStore.query (current revocationWorlds requirement earned).store 2 = [11] := ⟨rfl, rfl, rfl, rfl, rfl⟩

def deniedPending := (CapturedClosure.start revocationWorlds requirement liveC readerOnly 33 earned).getD fallback
def denied := Invocation.resume revocationWorlds requirement needed liveC readerOnly 0 4 deniedPending
def retained := match denied with | .error saved | .ok saved => saved
def retried := (Invocation.resume revocationWorlds requirement needed liveC held 0 4 retained).toOption.getD fallback

theorem captured_producer_permission_does_not_authorize_invocation :
    denied = .error deniedPending ∧ retained.1 = 4 ∧
      answer retried = some ([7, 7], [7, 7], [7, 7, 99], false) ∧
      OrderedDependencyStore.query (current revocationWorlds requirement retried).store 2 = [11, 33] := by
  refine ⟨?_, rfl, rfl, rfl⟩
  apply Invocation.pending_refused
  exact Or.inl (by decide)

def pending := (CapturedClosure.start revocationWorlds requirement liveC held 33 earned).getD fallback
def stale := OrderedDependencyStore.appendOwn liveC 0 [101]

theorem held_current_permission_does_not_heal_a_pending_source :
    Invocation.resume revocationWorlds requirement needed stale held 0 4 pending = .error pending := by
  apply Invocation.pending_refused
  exact Or.inr (by decide)

def faulted := advance revocationWorlds requirement 3 producer { source with point := readerOnly }
def closedFault := CapturedClosure.close revocationWorlds requirement body faulted

theorem zero_incomplete_and_faulted_cuts_do_not_run_a_body :
    Invocation.resume revocationWorlds requirement needed stale revoked 0 0 pending = .ok pending ∧
      completed revocationWorlds requirement closedFault = some (.error .denied) ∧
      (CapturedClosure.start revocationWorlds requirement liveC held 33 closedFault).isNone = true ∧
      (CapturedClosure.start revocationWorlds requirement liveC held 33 closing).isNone = true := ⟨rfl, rfl, rfl, rfl⟩

def otherSource : State revocationWorlds Nat 3 :=
  ⟨OrderedDependencyStore.initial 91 (fun reader => if reader = 0 then [8] else []), held⟩
def otherEarned := Cursor.resume (provider revocationWorlds requirement) (client _) (fun _ _ => 1) 3
  (CapturedClosure.close revocationWorlds requirement body (advance revocationWorlds requirement 2 producer otherSource))
def other := ((CapturedClosure.invoke revocationWorlds requirement needed liveC held 0 4 33 otherEarned).bind
  Except.toOption).getD fallback

theorem equal_fixed_code_does_not_erase_different_captured_environments :
    answer other = some ([8], [8], [7, 7, 99], false) ∧
      answer other ≠ answer first := by
  constructor
  · rfl
  · decide

end NonfreshControls

namespace ServiceControls

open Fold.OwnedSequence.CallbackBoundary
open Mettapedia.GSLT.Contracts
open Mettapedia.Machines.Cursor.ReadOnlyQuery.OwnWrite.Controls (requirement held revoked source)
open Mettapedia.Machines.Cursor.ReadOnlyQuery.OwnWrite.InvocationControls (needed)

local instance permissionDecision (point : IndexedAuthority.Point revocationWorlds)
    (change : OrderedDependencyStore.Action Nat 3) :
    Decidable (FrameUpdate point.authority (requirement change point.world)) := Controls.permissionDecision point change

local instance admissionDecision (point : IndexedAuthority.Point revocationWorlds) :
    Decidable (FrameUpdate point.authority (needed point.world)) := InvocationControls.admissionDecision point

abbrev Row := Nat × Option Nat × NonfreshControls.Environment × NonfreshControls.Readout
abbrev WorkResult := Option Row
abbrev Context := List NonfreshControls.Readout × Bool

/-- Each accepted return rearms this same fixed captured body at its reached
state. `none` is an ongoing producer, not a precomputed answer collection. -/
def work (environment : NonfreshControls.Environment) (limit : Option Nat) (index : Nat) :
    Prog (Request Nat 3) Reply WorkResult :=
  if limit.any (fun count => decide (count ≤ index)) then .ret none else
    (NonfreshControls.body environment 33).bind fun reply =>
      .ret (some (index + 1, limit, environment, reply))

def isReturn (item : CallService.Loan revocationWorlds requirement (Answer := WorkResult)) : Bool :=
  match item.2.1 with
  | .ok (some _) => true
  | _ => false

def rearm (item : CallService.Loan revocationWorlds requirement (Answer := WorkResult)) :
    Packet (OwnWrite.provider revocationWorlds requirement) (OwnWrite.client WorkResult) PUnit.unit :=
  ⟨PUnit.unit, match item.2.1 with
    | .ok (some (index, limit, environment, _)) => .ok (work environment limit index)
    | _ => .error .denied, item.2.2⟩

/-- Every ongoing work unit has the independently specified stateful source
meaning and rearms the next actual unit at exactly that reached state. No
finite collection of future replies is present in this construction. -/
theorem ongoing_unit_source_and_residual (captured : NonfreshControls.Environment)
    (index : Nat) (store : OrderedDependencyStore.Store Nat 3) :
    let reached : State revocationWorlds Nat 3 := ⟨OrderedDependencyStore.appendOwn store 2 [33], held⟩
    let row : Row := (index + 1, none, captured,
      captured.2.1, captured.2.2, OrderedDependencyStore.query reached.store 0,
      OrderedDependencyStore.checkRead reached.store captured.1)
    (work captured none index).Runs (action revocationWorlds requirement) ⟨store, held⟩
      (some row) reached ∧
      rearm ⟨PUnit.unit, .ok (some row), reached⟩ =
        ⟨PUnit.unit, .ok (work captured none (index + 1)), reached⟩ := by
  dsimp only
  refine ⟨?_, rfl⟩
  apply slice_ok_runs revocationWorlds requirement 4 0 3
  rfl

def consume (context : State revocationWorlds Nat 3 × Context)
    (item : CallService.Loan revocationWorlds requirement (Answer := WorkResult)) :
    Bool × (State revocationWorlds Nat 3 × Context) :=
  if context.2.2 then
    match item.2.1 with
    | .ok (some (_, _, _, reply)) => ⟨true, context.1, context.2.1 ++ [reply], true⟩
    | _ => ⟨false, context⟩
  else ⟨false, context.1, context.2.1, true⟩

abbrev agent := CallService.provider revocationWorlds requirement needed 0
  (fun (_ : Context) => 2) isReturn rearm consume

/-- This receipt counts next callbacks, not source instructions, accepted
returns, native quanta or elapsed time. The source keeps its own paid prefix. -/
def callbackCharge : Charge agent := fun _ request => match request with
  | .next => 1
  | .accept _ => 0

def produced := Cursor.resume (OwnWrite.provider revocationWorlds requirement) (OwnWrite.client _)
  (fun _ _ => 1) 3 NonfreshControls.cut

def environment : NonfreshControls.Environment :=
  match completed revocationWorlds requirement produced with
  | some (.ok result) => result
  | _ => (OrderedDependencyStore.readStamp source.store 0, [], [])

def session (limit : Option Nat) : CallService.Session revocationWorlds requirement
    (Answer := WorkResult) (Context := Context) :=
  let live := current revocationWorlds requirement produced
  ⟨(produced.1, .paused ⟨PUnit.unit, .ok (work environment limit 0), live⟩), live, [], false⟩

def initial : FairObservation.OwnedService.State agent :=
  ⟨⟨3, [41, 99]⟩, fun owner => (0, ⟨none, none, 0⟩, session (if owner = 41 then none else some 1))⟩

def after (slots : Nat) := FairObservation.OwnedService.run agent callbackCharge
  (fun _ => none) slots (fun _ => 1) (fun _ => []) initial

def view (state : FairObservation.OwnedService.State agent) (owner : Nat) :=
  let call := state.pool owner
  (call.2.1.terminal.isSome, call.2.1.pending.isSome, call.2.1.accepted,
    call.2.2.computation.1, call.2.2.context.2.1,
    OrderedDependencyStore.query (current revocationWorlds requirement call.2.2.computation).store 2)

def reply : NonfreshControls.Readout := ([7, 7], [7, 7], [7, 7], true)

theorem yielding_loop_does_not_block_finite_retirement :
    view (after 1) 41 = (false, false, 0, 6, [], [11, 33]) ∧
      (after 8).ready.tasks = [41] ∧
      view (after 8) 99 = (true, false, 1, 7, [reply], [11, 33]) ∧
      view (after 9) 41 = (false, false, 2, 10, [reply, reply], [11, 33, 33]) := ⟨rfl, rfl, rfl, rfl⟩

theorem refusal_then_retry_keeps_the_earned_loan :
    view (after 3) 41 = (false, true, 0, 7, [], [11, 33]) ∧
      ((after 3).pool 41).2.2.context.2.2 = true ∧
      view (after 5) 41 = (false, false, 1, 7, [reply], [11, 33]) ∧
      ((after 3).pool 41).1 = ((after 5).pool 41).1 := ⟨rfl, rfl, rfl, rfl⟩

theorem zero_grant_preserves_pending_and_all_siblings :
    (FairObservation.OwnedService.service agent callbackCharge (fun _ => none) 0 [77]
      (after 3)).pool = (after 3).pool :=
  FairObservation.OwnedService.zero_preserves_pool _ _ _ _ _

theorem arrivals_duplicates_and_cancellation_use_existing_queue :
    (FairObservation.OwnedService.service agent callbackCharge (fun _ => none) 1 [41, 77, 77, 88]
      initial).ready.tasks = [99, 41, 77] ∧
      (FairObservation.OwnedService.cancel agent 41 (after 3)).ready.tasks = [99] ∧
      (FairObservation.OwnedService.cancel agent 41 (after 3)).pool 99 = (after 3).pool 99 := ⟨rfl, rfl, rfl⟩

def heldSession := ((after 3).pool 41).2.2

def heldLoan : CallService.Loan revocationWorlds requirement (Answer := WorkResult) :=
  match heldSession.computation.2 with
  | .done result => result
  | .paused _ => ⟨PUnit.unit, .ok none, current revocationWorlds requirement heldSession.computation⟩

def staleSession : CallService.Session revocationWorlds requirement (Answer := WorkResult) (Context := Context) :=
  { heldSession with context :=
    ({heldSession.context.1 with store := OrderedDependencyStore.appendOwn heldSession.context.1.store 0 [99]},
      heldSession.context.2) }

def revokedSession : CallService.Session revocationWorlds requirement (Answer := WorkResult) (Context := Context) :=
  { heldSession with context := ({heldSession.context.1 with point := revoked}, heldSession.context.2) }

theorem stale_or_revoked_publication_does_not_erase_earned_readout :
    (agent.step (base := ()) (index := ()) staleSession .next) = ⟨.paused, staleSession⟩ ∧
      (agent.step (base := ()) (index := ()) staleSession (.accept heldLoan)) = ⟨false, staleSession⟩ ∧
      (agent.step (base := ()) (index := ()) revokedSession (.accept heldLoan)) = ⟨false, revokedSession⟩ ∧
      (completed revocationWorlds requirement staleSession.computation).isSome = true := by
  exact ⟨CallService.next_refused _ _ _ _ _ _ _ _ _ (by unfold CallService.eligible; decide),
    CallService.publication_refused _ _ _ _ _ _ _ _ _ _ (by unfold CallService.eligible; decide),
    CallService.publication_refused _ _ _ _ _ _ _ _ _ _ (by unfold CallService.eligible; decide), rfl⟩

def newerSession : CallService.Session revocationWorlds requirement (Answer := WorkResult) (Context := Context) :=
  { heldSession with context :=
    ({heldSession.context.1 with store := OrderedDependencyStore.appendOwn heldSession.context.1.store 2 [99]},
      heldSession.context.2) }

theorem earned_classification_preserves_newer_live_context :
    ((agent.step (base := ()) (index := ()) newerSession .next).2.context) = newerSession.context ∧
      ((agent.step (base := ()) (index := ()) newerSession .next).2.computation) =
        newerSession.computation := ⟨rfl, rfl⟩

#print axioms yielding_loop_does_not_block_finite_retirement
#print axioms refusal_then_retry_keeps_the_earned_loan
#print axioms zero_grant_preserves_pending_and_all_siblings
#print axioms arrivals_duplicates_and_cancellation_use_existing_queue
#print axioms stale_or_revoked_publication_does_not_erase_earned_readout
#print axioms earned_classification_preserves_newer_live_context
#print axioms ongoing_unit_source_and_residual

end ServiceControls

#print axioms ReturnMap.state_and_paid
#print axioms ReturnMap.completed_map
#print axioms ReturnMap.compose
#print axioms ReturnMap.identity
#print axioms ReturnMap.direct_map
#print axioms ReturnMap.advance_map
#print axioms ReturnMap.resume_map
#print axioms ReturnMap.schedule_map
#print axioms ReturnMap.invocation_map
#print axioms ReturnMap.runs
#print axioms ReturnMap.producer_source
#print axioms CapturedClosure.producer_source
#print axioms CapturedClosure.nonfresh_completed_source
#print axioms NonfreshControls.late_closing_keeps_the_paid_effect_and_actual_suffix
#print axioms NonfreshControls.repeated_invocation_reuses_environment_without_replaying_producer
#print axioms NonfreshControls.captured_producer_permission_does_not_authorize_invocation
#print axioms NonfreshControls.held_current_permission_does_not_heal_a_pending_source
#print axioms NonfreshControls.zero_incomplete_and_faulted_cuts_do_not_run_a_body
#print axioms NonfreshControls.equal_fixed_code_does_not_erase_different_captured_environments

#print axioms Invocation.zero
#print axioms Invocation.earned
#print axioms Invocation.pending_admitted
#print axioms Invocation.pending_refused
#print axioms Invocation.pending_is_direct
#print axioms Invocation.resume_point
#print axioms Invocation.at_reached_state
#print axioms Invocation.split
#print axioms step_ok
#print axioms direct_ok_runs
#print axioms slice_ok_runs
#print axioms CapturedClosure.capture_runs
#print axioms CapturedClosure.capture_complete
#print axioms CapturedClosure.capture_then_runs
#print axioms CapturedClosure.start_capture
#print axioms CapturedClosure.completed_source
#print axioms InvocationControls.read_only_refusal_keeps_the_actual_closure_call
#print axioms InvocationControls.genuine_retry_uses_old_capture_and_current_fresh_read
#print axioms InvocationControls.refusal_after_paid_effect_does_not_repeat_it
#print axioms InvocationControls.stale_pending_source_is_not_refreshed_by_held_permission
#print axioms InvocationControls.earned_closure_can_start_a_new_current_world_call
#print axioms InvocationControls.zero_and_earned_result_need_no_new_effect_permission
#print axioms InvocationControls.unfinished_capture_is_not_an_invocable_closure
#print axioms InvocationControls.entrance_eligibility_does_not_hide_an_inner_action_fault

#print axioms step_sound
#print axioms denied_write_keeps_state
#print axioms own_write_uses_current_store
#print axioms finite_execution
#print axioms finite_is_direct
#print axioms split_resume
#print axioms query_safe
#print axioms query_runs
#print axioms query_then_runs
#print axioms query_complete
#print axioms zero_keeps_whole_saved
#print axioms completed_reentry_inert
#print axioms stale_pending_refused
#print axioms current_pending_resumes
#print axioms current_source_agrees
#print axioms captured_read_own_write
#print axioms step_origin
#print axioms finite_origin
#print axioms finite_observers
#print axioms schedule_sum

namespace Invocation

/-- The existing invocation boundary with its primitive handler supplied
explicitly. A refused pending entrance retains the complete paid packet.
The guard may depend on the actual pending request; it is not recovered from
a stamp, a captured program or an already retained reply. -/
abbrev SavedWith (handle : State authority Entry size → (request : Request Entry size) →
    State authority Entry size × Except Fault (Reply request)) (Answer : Type) :=
  Nat × Outcome (PrimitiveProgram.provider handle) (client Answer) PUnit.unit

def resumeWith (handle : State authority Entry size → (request : Request Entry size) →
    State authority Entry size × Except Fault (Reply request))
    (enter : IndexedAuthority.Point authority → Request Entry size → OrderedDependencyStore.ReadStamp size → Prop)
    [∀ point request stamp, Decidable (enter point request stamp)] {Answer : Type}
    (live : OrderedDependencyStore.Store Entry size) (point : IndexedAuthority.Point authority)
    (reader : Fin size) (fuel : Nat) (previous : SavedWith authority handle Answer) :
    Except (SavedWith authority handle Answer) (SavedWith authority handle Answer) :=
  if fuel = 0 then .ok previous else
  match previous.2 with
  | .done _ => .ok previous
  | .paused ⟨index, control, saved⟩ =>
      match control with
      | .error _ | .ok (.ret _) =>
          .ok (Cursor.resume (PrimitiveProgram.provider handle) (client Answer)
            (fun _ _ => 1) fuel previous)
      | .ok (.call request _) =>
          if enter point request (OrderedDependencyStore.readStamp saved.store reader) then
            if OrderedDependencyStore.checkRead live (OrderedDependencyStore.readStamp saved.store reader) then
              .ok (Cursor.resume (PrimitiveProgram.provider handle) (client Answer) (fun _ _ => 1) fuel
                (previous.1, .paused ⟨index, control, ⟨live, point⟩⟩))
            else .error previous
          else .error previous

theorem resumeWith_zero (handle : State authority Entry size → (request : Request Entry size) →
    State authority Entry size × Except Fault (Reply request))
    (enter : IndexedAuthority.Point authority → Request Entry size → OrderedDependencyStore.ReadStamp size → Prop)
    [∀ point request stamp, Decidable (enter point request stamp)] {Answer : Type}
    (live : OrderedDependencyStore.Store Entry size) (point : IndexedAuthority.Point authority)
    (reader : Fin size) (previous : SavedWith authority handle Answer) :
    resumeWith authority handle enter live point reader 0 previous = .ok previous := rfl

/-- The ordinary private-store invocation is exactly the existing one.
Supplying a protected handler adds no alternate evaluator. -/
theorem resumeWith_private (needed : (world : World) → authority.Fibre world)
    [∀ point : IndexedAuthority.Point authority,
      Decidable (FrameUpdate point.authority (needed point.world))]
    {Answer : Type} (live : OrderedDependencyStore.Store Entry size)
    (point : IndexedAuthority.Point authority) (reader : Fin size) (fuel : Nat)
    (previous : Saved authority required Answer) :
    resumeWith authority (OwnWrite.step authority required)
      (fun point _ _ => FrameUpdate point.authority (needed point.world)) live point reader fuel previous =
      resume authority required needed live point reader fuel previous := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      rcases previous with ⟨paid, outcome⟩
      cases outcome with
      | done result => rfl
      | paused packet =>
          rcases packet with ⟨index, control, saved⟩
          cases control with
          | error fault => rfl
          | ok program =>
              cases program with
              | ret answer => rfl
              | call request next =>
                  by_cases allowed : FrameUpdate point.authority (needed point.world)
                  · cases valid : OrderedDependencyStore.checkRead live
                      (OrderedDependencyStore.readStamp saved.store reader) <;>
                      simp [resumeWith, resume, resumeCurrent, allowed, valid]
                  · simp [resumeWith, resume, allowed]

theorem resumeWith_pending_refused
    (handle : State authority Entry size → (request : Request Entry size) →
      State authority Entry size × Except Fault (Reply request))
    (enter : IndexedAuthority.Point authority → Request Entry size → OrderedDependencyStore.ReadStamp size → Prop)
    [∀ point request stamp, Decidable (enter point request stamp)] {Answer : Type}
    (live : OrderedDependencyStore.Store Entry size) (point : IndexedAuthority.Point authority)
    (reader : Fin size) (fuel paid : Nat) (request : Request Entry size)
    (next : Reply request → Prog (Request Entry size) Reply Answer) (saved : State authority Entry size)
    (denied : ¬ enter point request (OrderedDependencyStore.readStamp saved.store reader) ∨
      OrderedDependencyStore.checkRead live (OrderedDependencyStore.readStamp saved.store reader) = false) :
    resumeWith authority handle enter live point reader (fuel + 1)
      (paid, .paused ⟨PUnit.unit, .ok (.call request next), saved⟩) =
        .error (paid, .paused ⟨PUnit.unit, .ok (.call request next), saved⟩) := by
  rcases denied with denied | stale
  · simp [resumeWith, denied]
  · by_cases allowed : enter point request (OrderedDependencyStore.readStamp saved.store reader) <;>
      simp [resumeWith, allowed, stale]

/-- Current entrance and source validation precede the actual saved call.
Its full execution is the independent primitive interpreter, including paid
work, faults and the dependent residual. -/
theorem resumeWith_pending_is_direct
    (handle : State authority Entry size → (request : Request Entry size) →
      State authority Entry size × Except Fault (Reply request))
    (enter : IndexedAuthority.Point authority → Request Entry size → OrderedDependencyStore.ReadStamp size → Prop)
    [∀ point request stamp, Decidable (enter point request stamp)] {Answer : Type}
    (live : OrderedDependencyStore.Store Entry size) (point : IndexedAuthority.Point authority)
    (reader : Fin size) (fuel paid : Nat) (request : Request Entry size)
    (next : Reply request → Prog (Request Entry size) Reply Answer) (saved : State authority Entry size)
    (allowed : enter point request (OrderedDependencyStore.readStamp saved.store reader))
    (valid : OrderedDependencyStore.checkRead live (OrderedDependencyStore.readStamp saved.store reader) = true) :
    let actual := Cursor.resume (PrimitiveProgram.provider handle) (client Answer)
      (fun _ _ => 1) (fuel + 1) (paid, .paused ⟨PUnit.unit, .ok (.call request next), ⟨live, point⟩⟩)
    resumeWith authority handle enter live point reader (fuel + 1)
        (paid, .paused ⟨PUnit.unit, .ok (.call request next), saved⟩) = .ok actual ∧
      (actual.1, PrimitiveProgram.readOutcome handle actual.2) =
        let direct := PrimitiveProgram.direct handle (fun _ _ => 1) (fuel + 1)
          (.ok (.call request next)) ⟨live, point⟩
        (paid + direct.1, direct.2) := by
  refine ⟨by simp [resumeWith, allowed, valid], ?_⟩
  exact congrArg (fun result => (paid + result.1, result.2))
    (PrimitiveProgram.advance_is_direct handle (fun _ _ => 1) (fuel + 1)
      (.ok (.call request next)) ⟨live, point⟩)

end Invocation

namespace Protected

variable
  (readRequired : Fin size → (world : World) → authority.Fibre world)
  (validateRequired : OrderedDependencyStore.ReadStamp size → (world : World) → authority.Fibre world)
  [readPermission : ∀ point : IndexedAuthority.Point authority, ∀ reader,
    Decidable (FrameUpdate point.authority (readRequired reader point.world))]
  [validatePermission : ∀ point : IndexedAuthority.Point authority, ∀ stamp,
    Decidable (FrameUpdate point.authority (validateRequired stamp point.world))]

/-- Observation requirements are supplied by the invocation's scope policy.
The private handler retains responsibility for write authority. A module-self
designation or a stamp is a request coordinate, not a permission. -/
def mayObserve (point : IndexedAuthority.Point authority) : Request Entry size → Prop
  | .read reader => FrameUpdate point.authority (readRequired reader point.world)
  | .validate stamp => FrameUpdate point.authority (validateRequired stamp point.world)
  | .write _ => True

instance mayObserveDecision (point : IndexedAuthority.Point authority) (request : Request Entry size) :
    Decidable (mayObserve authority readRequired validateRequired point request) := by
  cases request <;> dsimp [mayObserve] <;> infer_instance

/-- Check before evaluating a protected read or metadata query. The ordinary
write implementation and its authority contract are unchanged. -/
def step (state : State authority Entry size) (request : Request Entry size) :
    State authority Entry size × Except Fault (Reply request) :=
  if mayObserve authority readRequired validateRequired state.point request then
    OwnWrite.step authority required state request
  else (state, .error .denied)

/-- Independent allowed action: the original ordered store observation or
write, together with its separately declared observation requirement. -/
def action (request : Request Entry size) : Action (State authority Entry size) (Reply request) :=
  ⟨fun before => mayObserve authority readRequired validateRequired before.point request ∧
      (OwnWrite.action authority required request).Safe before,
    fun before reply after =>
      mayObserve authority readRequired validateRequired before.point request ∧
      (OwnWrite.action authority required request).Safe before ∧
      (OwnWrite.action authority required request).Step before reply after⟩

theorem step_sound : PrimitiveProgram.ProviderSound
    (action authority required readRequired validateRequired)
    (step authority required readRequired validateRequired) := by
  intro state request safe
  obtain ⟨value, following, ran, permitted⟩ := OwnWrite.step_sound authority required state request safe.2
  exact ⟨value, following, by simp only [step, if_pos safe.1]; exact ran, safe.1, safe.2, permitted⟩

theorem step_ok (state after : State authority Entry size) (request : Request Entry size)
    (reply : Reply request)
    (ran : step authority required readRequired validateRequired state request = (after, .ok reply)) :
    (action authority required readRequired validateRequired request).Safe state ∧
      (action authority required readRequired validateRequired request).Step state reply after := by
  unfold step at ran
  split at ran
  · rename_i allowed
    have original := OwnWrite.step_ok authority required state after request reply ran
    exact ⟨⟨allowed, original.1⟩, allowed, original.1, original.2⟩
  · cases Prod.mk.inj ran |>.2

theorem step_iff_action (state after : State authority Entry size) (request : Request Entry size)
    (reply : Reply request) :
    step authority required readRequired validateRequired state request = (after, .ok reply) ↔
      (action authority required readRequired validateRequired request).Safe state ∧
        (action authority required readRequired validateRequired request).Step state reply after := by
  constructor
  · exact step_ok authority required readRequired validateRequired state after request reply
  · rintro ⟨⟨allowed, safe⟩, meaning⟩
    rw [step, if_pos allowed]
    have original := meaning.2.2
    cases request with
    | read reader =>
        obtain ⟨rfl, rfl⟩ := original
        rfl
    | validate stamp =>
        obtain ⟨rfl, rfl⟩ := original
        rfl
    | write change =>
        change after = {state with store := OrderedDependencyStore.step state.store change} at original
        subst after
        cases reply
        exact OwnWrite.own_write_uses_current_store authority required state change safe

theorem denied_observation_keeps_world (state : State authority Entry size) (request : Request Entry size)
    (denied : ¬ mayObserve authority readRequired validateRequired state.point request) :
    step authority required readRequired validateRequired state request = (state, .error .denied) := by
  simp only [step, if_neg denied]

theorem write_is_private (state : State authority Entry size) (change : OrderedDependencyStore.Action Entry size) :
    step authority required readRequired validateRequired state (.write change) =
      OwnWrite.step authority required state (.write change) := by
  simp only [step, mayObserve, ↓reduceIte]

abbrev provider := PrimitiveProgram.provider (step authority required readRequired validateRequired)
abbrev Saved (Answer : Type) := Invocation.SavedWith authority
  (step authority required readRequired validateRequired) Answer

def advance {Answer : Type} (fuel : Nat) (program : Prog (Request Entry size) Reply Answer)
    (state : State authority Entry size) : Saved authority required readRequired validateRequired Answer :=
  Cursor.advance (provider authority required readRequired validateRequired) (client Answer)
    (fun _ _ => 1) fuel ⟨PUnit.unit, .ok program, state⟩

theorem finite_is_direct {Answer : Type} (fuel : Nat)
    (program : Prog (Request Entry size) Reply Answer) (state : State authority Entry size) :
    let actual := advance authority required readRequired validateRequired fuel program state
    (actual.1, PrimitiveProgram.readOutcome (step authority required readRequired validateRequired) actual.2) =
      PrimitiveProgram.direct (step authority required readRequired validateRequired) (fun _ _ => 1)
        fuel (.ok program) state := by
  exact PrimitiveProgram.advance_is_direct (step authority required readRequired validateRequired)
    (fun _ _ => 1) fuel (.ok program) state

theorem finite_execution {Answer : Type} (fuel : Nat)
    (program : Prog (Request Entry size) Reply Answer) (state : State authority Entry size)
    (safe : program.Safe (action authority required readRequired validateRequired) state) :
    PrimitiveProgram.SafeOutcome (action authority required readRequired validateRequired) program state
      (PrimitiveProgram.readOutcome (step authority required readRequired validateRequired)
        (advance authority required readRequired validateRequired fuel program state).2) := by
  exact PrimitiveProgram.advance_safe_outcome (action authority required readRequired validateRequired)
    (step authority required readRequired validateRequired)
    (step_sound authority required readRequired validateRequired) (fun _ _ => 1) fuel program state safe

theorem split_resume {Answer : Type} (first second : Nat)
    (program : Prog (Request Entry size) Reply Answer) (state : State authority Entry size) :
    advance authority required readRequired validateRequired (first + second) program state =
      Cursor.resume (provider authority required readRequired validateRequired) (client Answer)
        (fun _ _ => 1) second
        (advance authority required readRequired validateRequired first program state) :=
  Cursor.advance_add _ _ _ _ _ _

/-- Successful execution reflects the independently specified protected
actions. Each action in the reflected path includes current permission. -/
theorem direct_ok_runs {Answer : Type} (fuel : Nat)
    (program : Prog (Request Entry size) Reply Answer) (state after : State authority Entry size)
    (answer : Answer)
    (finished : (PrimitiveProgram.direct (step authority required readRequired validateRequired)
      (fun _ _ => 1) fuel (.ok program) state).2 = (.inl (.ok answer), after)) :
    program.Runs (action authority required readRequired validateRequired) state answer after := by
  induction fuel generalizing program state with
  | zero => cases finished
  | succ fuel ih =>
      cases program with
      | ret value =>
          simpa only [PrimitiveProgram.direct, Prod.mk.injEq, Sum.inl.injEq, Except.ok.injEq,
            Prog.Runs] using finished
      | call request next =>
          rcases performed : step authority required readRequired validateRequired state request with ⟨middle, reply⟩
          cases reply with
          | error fault =>
              cases fuel <;> simp only [PrimitiveProgram.direct, performed, Prod.mk.injEq] at finished
              · cases finished.1
              · cases Sum.inl.inj finished.1
          | ok reply =>
              exact ⟨reply, middle,
                (step_ok authority required readRequired validateRequired state middle request reply performed).2,
                ih (next reply) middle (by simpa only [PrimitiveProgram.direct, performed] using finished)⟩

theorem slice_ok_runs {Answer : Type} (fuel paid spent : Nat)
    (program : Prog (Request Entry size) Reply Answer) (state after : State authority Entry size)
    (answer : Answer)
    (finished : Cursor.resume (provider authority required readRequired validateRequired) (client Answer)
      (fun _ _ => 1) (base := PUnit.unit) fuel
      (paid, .paused ⟨PUnit.unit, .ok program, state⟩) =
        (spent, .done ⟨PUnit.unit, .ok answer, after⟩)) :
    program.Runs (action authority required readRequired validateRequired) state answer after := by
  have comparison := PrimitiveProgram.advance_is_direct (step authority required readRequired validateRequired)
    (fun _ _ => 1) fuel (.ok program) state
  have result := congrArg (fun value : Saved authority required readRequired validateRequired Answer =>
    PrimitiveProgram.readOutcome (step authority required readRequired validateRequired) value.2) finished
  change PrimitiveProgram.readOutcome (step authority required readRequired validateRequired)
    (Cursor.advance (provider authority required readRequired validateRequired) (client Answer) (fun _ _ => 1) fuel
      ⟨PUnit.unit, .ok program, state⟩).2 = (.inl (.ok answer), after) at result
  exact direct_ok_runs authority required readRequired validateRequired fuel program state after answer
    ((congrArg Prod.snd comparison).symm.trans result)

/-- Change the handler at an already retained private-store boundary without
executing its code or changing the captured control, world or paid prefix.
Subsequent protected invocation supplies its current observation permission. -/
def fromPrivate {Answer : Type} (saved : OwnWrite.Saved authority required Answer) :
    Saved authority required readRequired validateRequired Answer :=
  (saved.1, Outcome.mapState (client Answer) (source := OwnWrite.provider authority required)
    (target := provider authority required readRequired validateRequired) (fun state => state) saved.2)

theorem fromPrivate_state_and_paid {Answer : Type} (saved : OwnWrite.Saved authority required Answer) :
    (fromPrivate authority required readRequired validateRequired saved).1 = saved.1 ∧
      PrimitiveProgram.readOutcome (step authority required readRequired validateRequired)
        (fromPrivate authority required readRequired validateRequired saved).2 =
        PrimitiveProgram.readOutcome (OwnWrite.step authority required) saved.2 := by
  rcases saved with ⟨paid, outcome⟩
  cases outcome with
  | done result => rcases result with ⟨index, answer, state⟩; exact ⟨rfl, rfl⟩
  | paused packet => rcases packet with ⟨index, control, state⟩; exact ⟨rfl, rfl⟩

def completed {Answer : Type} (saved : Saved authority required readRequired validateRequired Answer) :
    Option (Except Fault Answer) :=
  match saved.2 with
  | .paused _ => none
  | .done ⟨_, answer, _⟩ => some answer

variable (needed : (world : World) → authority.Fibre world)
  [admission : ∀ point : IndexedAuthority.Point authority,
    Decidable (FrameUpdate point.authority (needed point.world))]

def entrance (point : IndexedAuthority.Point authority) (request : Request Entry size)
    (stamp : OrderedDependencyStore.ReadStamp size) : Prop :=
  FrameUpdate point.authority (needed point.world) ∧
    mayObserve authority readRequired validateRequired point request ∧
    FrameUpdate point.authority (validateRequired stamp point.world)

instance entranceDecision (point : IndexedAuthority.Point authority) (request : Request Entry size)
    (stamp : OrderedDependencyStore.ReadStamp size) :
    Decidable (entrance authority readRequired validateRequired needed point request stamp) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Use the common invocation boundary with the real protected handler.
Denial before the pending call retains its paid account and exact residual;
later requests in an admitted slice still check their own observation rights. -/
def resume {Answer : Type} (live : OrderedDependencyStore.Store Entry size)
    (point : IndexedAuthority.Point authority) (reader : Fin size) (fuel : Nat)
    (previous : Saved authority required readRequired validateRequired Answer) :
    Except (Saved authority required readRequired validateRequired Answer)
      (Saved authority required readRequired validateRequired Answer) :=
  Invocation.resumeWith authority (step authority required readRequired validateRequired)
    (entrance authority readRequired validateRequired needed) live point reader fuel previous

theorem zero {Answer : Type} (live : OrderedDependencyStore.Store Entry size)
    (point : IndexedAuthority.Point authority) (reader : Fin size)
    (previous : Saved authority required readRequired validateRequired Answer) :
    resume authority required readRequired validateRequired needed live point reader 0 previous = .ok previous := rfl

theorem pending_refused {Answer : Type} (live : OrderedDependencyStore.Store Entry size)
    (point : IndexedAuthority.Point authority) (reader : Fin size) (fuel paid : Nat)
    (request : Request Entry size) (next : Reply request → Prog (Request Entry size) Reply Answer)
    (saved : State authority Entry size)
    (denied : ¬ entrance authority readRequired validateRequired needed point request
        (OrderedDependencyStore.readStamp saved.store reader) ∨
      OrderedDependencyStore.checkRead live (OrderedDependencyStore.readStamp saved.store reader) = false) :
    resume authority required readRequired validateRequired needed live point reader (fuel + 1)
      (paid, .paused ⟨PUnit.unit, .ok (.call request next), saved⟩) =
        .error (paid, .paused ⟨PUnit.unit, .ok (.call request next), saved⟩) :=
  Invocation.resumeWith_pending_refused authority (step authority required readRequired validateRequired)
    (entrance authority readRequired validateRequired needed) live point reader fuel paid request next saved denied

theorem pending_is_direct {Answer : Type} (live : OrderedDependencyStore.Store Entry size)
    (point : IndexedAuthority.Point authority) (reader : Fin size) (fuel paid : Nat)
    (request : Request Entry size) (next : Reply request → Prog (Request Entry size) Reply Answer)
    (saved : State authority Entry size)
    (allowed : entrance authority readRequired validateRequired needed point request
      (OrderedDependencyStore.readStamp saved.store reader))
    (valid : OrderedDependencyStore.checkRead live (OrderedDependencyStore.readStamp saved.store reader) = true) :
    let actual := Cursor.resume (provider authority required readRequired validateRequired) (client Answer)
      (fun _ _ => 1) (fuel + 1) (paid, .paused ⟨PUnit.unit, .ok (.call request next), ⟨live, point⟩⟩)
    resume authority required readRequired validateRequired needed live point reader (fuel + 1)
        (paid, .paused ⟨PUnit.unit, .ok (.call request next), saved⟩) = .ok actual ∧
      (actual.1, PrimitiveProgram.readOutcome (step authority required readRequired validateRequired) actual.2) =
        let direct := PrimitiveProgram.direct (step authority required readRequired validateRequired)
          (fun _ _ => 1) (fuel + 1) (.ok (.call request next)) ⟨live, point⟩
        (paid + direct.1, direct.2) :=
  Invocation.resumeWith_pending_is_direct authority (step authority required readRequired validateRequired)
    (entrance authority readRequired validateRequired needed) live point reader fuel paid request next saved allowed valid

/-- Even a pending write needs permission for the internal source-metadata
validation. Refusal precedes that comparison for every supplied live store. -/
theorem pending_metadata_refused {Answer : Type} (live : OrderedDependencyStore.Store Entry size)
    (point : IndexedAuthority.Point authority) (reader : Fin size) (fuel paid : Nat)
    (request : Request Entry size) (next : Reply request → Prog (Request Entry size) Reply Answer)
    (saved : State authority Entry size)
    (denied : ¬ FrameUpdate point.authority
      (validateRequired (OrderedDependencyStore.readStamp saved.store reader) point.world)) :
    resume authority required readRequired validateRequired needed live point reader (fuel + 1)
      (paid, .paused ⟨PUnit.unit, .ok (.call request next), saved⟩) =
        .error (paid, .paused ⟨PUnit.unit, .ok (.call request next), saved⟩) := by
  apply pending_refused authority required readRequired validateRequired needed live point reader fuel paid request next saved
  exact Or.inl (fun allowed => denied allowed.2.2)

namespace Delivery

open Fold.OwnedSequence.CallbackBoundary

variable {Answer Context : Type}

abbrev Loan := Finished (Protected.provider authority required readRequired validateRequired)
  (Return := fun _ _ => Except Fault Answer) PUnit.unit

abbrev Session := Retained.State (Protected.provider authority required readRequired validateRequired)
  (client Answer) PUnit.unit (State authority Entry size × Context)

variable (reader : Fin size)

/-- Permission for delivery is explicitly declared by the service. It is
checked at the current live point; retained source data only supplies the
source-currency obligation. This need not be the producer's entrance right. -/
def eligible (session : Session authority required readRequired validateRequired
    (Answer := Answer) (Context := Context)) : Prop :=
  FrameUpdate session.context.1.point.authority (needed session.context.1.point.world) ∧
    FrameUpdate session.context.1.point.authority
      (validateRequired (OrderedDependencyStore.readStamp
        (PrimitiveProgram.readOutcome (Protected.step authority required readRequired validateRequired)
          session.computation.2).2.store reader) session.context.1.point.world) ∧
    OrderedDependencyStore.checkRead session.context.1.store
      (OrderedDependencyStore.readStamp
        (PrimitiveProgram.readOutcome (Protected.step authority required readRequired validateRequired)
          session.computation.2).2.store reader) = true

instance eligibleDecision (session : Session authority required readRequired validateRequired
    (Answer := Answer) (Context := Context)) :
    Decidable (eligible authority required readRequired validateRequired needed reader session) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable (isReturn : Loan authority required readRequired validateRequired (Answer := Answer) → Bool)
  (rearm : Loan authority required readRequired validateRequired (Answer := Answer) →
    Packet (Protected.provider authority required readRequired validateRequired) (client Answer) PUnit.unit)
  (consume : (State authority Entry size × Context) →
    Loan authority required readRequired validateRequired (Answer := Answer) →
      Bool × (State authority Entry size × Context))

/-- Use the maintained retained adapter for classification and acceptance.
It performs no source requests here: production uses protected invocation,
and delivery cannot replay the producer to reconstruct an earned answer. -/
abbrev boundary := Retained.provider (Protected.provider authority required readRequired validateRequired)
  (client Answer) PUnit.unit (fun _ _ => 1) 0 isReturn rearm consume

def provider : Provider (Fold.OwnedSequence.CallbackBoundary.protocol
    (Loan authority required readRequired validateRequired (Answer := Answer))
    (Loan authority required readRequired validateRequired (Answer := Answer))) where
  State _ _ := Session authority required readRequired validateRequired (Answer := Answer) (Context := Context)
  step session request :=
    if eligible authority required readRequired validateRequired needed reader session then
      (boundary authority required readRequired validateRequired isReturn rearm consume).step session request
    else match request with
      | .next => ⟨.paused, session⟩
      | .accept _ => ⟨false, session⟩

theorem refused (session : Session authority required readRequired validateRequired
    (Answer := Answer) (Context := Context))
    (item : Loan authority required readRequired validateRequired (Answer := Answer))
    (denied : ¬ eligible authority required readRequired validateRequired needed reader session) :
    (provider authority required readRequired validateRequired needed reader isReturn rearm consume).step
      (base := ()) (index := ()) session (.accept item) = ⟨false, session⟩ := by
  change (if eligible authority required readRequired validateRequired needed reader session then _ else _) = _
  exact if_neg denied

theorem admitted (session : Session authority required readRequired validateRequired
    (Answer := Answer) (Context := Context))
    (item : Loan authority required readRequired validateRequired (Answer := Answer))
    (allowed : eligible authority required readRequired validateRequired needed reader session) :
    (provider authority required readRequired validateRequired needed reader isReturn rearm consume).step
      (base := ()) (index := ()) session (.accept item) =
      (boundary authority required readRequired validateRequired isReturn rearm consume).step session (.accept item) := by
  change (if eligible authority required readRequired validateRequired needed reader session then _ else _) = _
  exact if_pos allowed

theorem success_requires_current_policy (session : Session authority required readRequired validateRequired
    (Answer := Answer) (Context := Context))
    (item : Loan authority required readRequired validateRequired (Answer := Answer))
    (accepted : ((provider authority required readRequired validateRequired needed reader isReturn rearm consume).step
      (base := ()) (index := ()) session (.accept item)).1 = true) :
    eligible authority required readRequired validateRequired needed reader session := by
  by_contra denied
  rw [refused authority required readRequired validateRequired needed reader isReturn rearm consume
    session item denied] at accepted
  cases accepted

theorem preserves_paid (session : Session authority required readRequired validateRequired
    (Answer := Answer) (Context := Context))
    (item : Loan authority required readRequired validateRequired (Answer := Answer)) :
    ((provider authority required readRequired validateRequired needed reader isReturn rearm consume).step
      (base := ()) (index := ()) session (.accept item)).2.computation.1 = session.computation.1 := by
  by_cases allowed : eligible authority required readRequired validateRequired needed reader session
  · rw [admitted authority required readRequired validateRequired needed reader isReturn rearm consume session item allowed]
    exact Retained.accept_preserves_source_charge _ _ _ _ _ _ _ _ session item
  · rw [refused authority required readRequired validateRequired needed reader isReturn rearm consume session item allowed]

theorem metadata_refused (session : Session authority required readRequired validateRequired
    (Answer := Answer) (Context := Context))
    (item : Loan authority required readRequired validateRequired (Answer := Answer))
    (denied : ¬ FrameUpdate session.context.1.point.authority
      (validateRequired (OrderedDependencyStore.readStamp
        (PrimitiveProgram.readOutcome (Protected.step authority required readRequired validateRequired)
          session.computation.2).2.store reader) session.context.1.point.world)) :
    (provider authority required readRequired validateRequired needed reader isReturn rearm consume).step
      (base := ()) (index := ()) session (.accept item) = ⟨false, session⟩ :=
  refused authority required readRequired validateRequired needed reader isReturn rearm consume
    session item (fun allowed => denied allowed.2.1)

end Delivery

namespace Controls

open OwnWrite.Controls (requirement held revoked readerOnly source)

local instance : Fintype Access :=
  ⟨{.none, .read, .consume}, by intro access; cases access <;> simp⟩

local instance writeDecision (point : IndexedAuthority.Point revocationWorlds)
    (change : OrderedDependencyStore.Action Nat 3) :
    Decidable (FrameUpdate point.authority (requirement change point.world)) :=
  OwnWrite.Controls.permissionDecision point change

def moduleSelf : Fin 3 := 0
def readRequirement (reader : Fin 3) (_world : Bool) : Access :=
  if reader = moduleSelf then .read else .consume
def validationRequirement (_stamp : OrderedDependencyStore.ReadStamp 3) (_world : Bool) : Access := .consume
def noEntranceRequirement (_world : Bool) : Access := .none
def deliveryRequirement (_world : Bool) : Access := .read

local instance readDecision (point : IndexedAuthority.Point revocationWorlds) (reader : Fin 3) :
    Decidable (FrameUpdate point.authority (readRequirement reader point.world)) :=
  inferInstanceAs (Decidable (∀ frame : Access,
    Access.separate point.authority frame = true → Access.separate (readRequirement reader point.world) frame = true))

local instance validationDecision (point : IndexedAuthority.Point revocationWorlds)
    (stamp : OrderedDependencyStore.ReadStamp 3) :
    Decidable (FrameUpdate point.authority (validationRequirement stamp point.world)) :=
  inferInstanceAs (Decidable (∀ frame : Access,
    Access.separate point.authority frame = true → Access.separate Access.consume frame = true))

local instance entranceDecision (point : IndexedAuthority.Point revocationWorlds) :
    Decidable (FrameUpdate point.authority (noEntranceRequirement point.world)) :=
  isTrue (FrameUpdate.to_zero point.authority)

local instance deliveryDecision (point : IndexedAuthority.Point revocationWorlds) :
    Decidable (FrameUpdate point.authority (deliveryRequirement point.world)) :=
  inferInstanceAs (Decidable (∀ frame : Access,
    Access.separate point.authority frame = true → Access.separate Access.read frame = true))

abbrev handle := Protected.step revocationWorlds requirement readRequirement validationRequirement
abbrev machine := Protected.provider revocationWorlds requirement readRequirement validationRequirement
abbrev slice {Result : Type} :=
  Protected.advance revocationWorlds requirement readRequirement validationRequirement (Answer := Result)
abbrev enter {Result : Type} := Protected.resume revocationWorlds requirement readRequirement validationRequirement
  noEntranceRequirement (Answer := Result)
abbrev done? {Result : Type} :=
  Protected.completed revocationWorlds requirement readRequirement validationRequirement (Answer := Result)

def readOnly : State revocationWorlds Nat 3 := {source with point := readerOnly}
def noRightsPoint : IndexedAuthority.Point revocationWorlds := ⟨false, .none⟩
def noRights : State revocationWorlds Nat 3 := {source with point := noRightsPoint}

def readSelf : Prog (Request Nat 3) Reply (OrderedDependencyStore.ReadStamp 3 × List Nat) :=
  .call (.read moduleSelf) .ret

theorem same_module_self_does_not_imply_same_permission :
    handle readOnly (.read moduleSelf) =
      (readOnly, .ok (OrderedDependencyStore.readStamp source.store moduleSelf, [7, 7])) ∧
      handle noRights (.read moduleSelf) = (noRights, .error .denied) := ⟨rfl, rfl⟩

theorem metadata_validation_is_not_authorized_by_a_stamp :
    let stamp := OrderedDependencyStore.readStamp source.store moduleSelf
    handle readOnly (.validate stamp) = (readOnly, .error .denied) ∧
      handle source (.validate stamp) = (source, .ok true) ∧
      handle {source with store := OrderedDependencyStore.appendOwn source.store moduleSelf [99]}
        (.validate stamp) =
        ({source with store := OrderedDependencyStore.appendOwn source.store moduleSelf [99]}, .ok false) :=
  ⟨rfl, rfl, rfl⟩

theorem denied_read_is_distinct_from_successful_empty_read :
    let empty : Prog (Request Nat 3) Reply (OrderedDependencyStore.ReadStamp 3 × List Nat) :=
      .call (.read 1) .ret
    done? (slice 2 empty source) = some (.ok (OrderedDependencyStore.readStamp source.store 1, [])) ∧
      done? (slice 2 empty noRights) = some (.error .denied) ∧
      (slice 2 empty source).1 = 1 ∧ (slice 2 empty noRights).1 = 1 := ⟨rfl, rfl, rfl, rfl⟩

def work : Prog (Request Nat 3) Reply (OrderedDependencyStore.ReadStamp 3 × List Nat) :=
  .call (.write (.append 2 [99])) fun _ => readSelf
def cut := slice 1 work source
def reached := {source with store := OrderedDependencyStore.step source.store (.append 2 [99])}

theorem revocation_before_resumed_read_retains_exact_paid_cut :
    cut = (1, .paused ⟨PUnit.unit, .ok readSelf, reached⟩) ∧
      enter reached.store revoked moduleSelf 2 cut = .error cut ∧
      enter reached.store noRightsPoint moduleSelf 2 cut = .error cut := by
  refine ⟨rfl, ?_, ?_⟩
  · exact Protected.pending_refused revocationWorlds requirement readRequirement validationRequirement
      noEntranceRequirement reached.store revoked moduleSelf 1 1 (.read moduleSelf) .ret reached
      (Or.inl (by unfold Protected.entrance Protected.mayObserve; decide))
  · exact Protected.pending_refused revocationWorlds requirement readRequirement validationRequirement
      noEntranceRequirement reached.store noRightsPoint moduleSelf 1 1 (.read moduleSelf) .ret reached
      (Or.inl (by unfold Protected.entrance Protected.mayObserve; decide))

theorem authorized_retry_does_not_replay_paid_write :
    enter reached.store held moduleSelf 2 cut =
      .ok (2, .done ⟨PUnit.unit,
        .ok (OrderedDependencyStore.readStamp reached.store moduleSelf, [7, 7]),
        reached⟩) ∧
      OrderedDependencyStore.query reached.store 2 = [99] := ⟨rfl, rfl⟩

theorem missing_metadata_permission_refuses_any_live_view (live : OrderedDependencyStore.Store Nat 3) :
    FrameUpdate readerOnly.authority (readRequirement moduleSelf readerOnly.world) ∧
      enter live readerOnly moduleSelf 2 cut = .error cut := by
  refine ⟨by decide, ?_⟩
  exact Protected.pending_metadata_refused revocationWorlds requirement readRequirement validationRequirement
    noEntranceRequirement live readerOnly moduleSelf 1 1 (.read moduleSelf) .ret reached (by decide)

theorem zero_allowance_is_inert_despite_stale_data_and_revocation :
    enter (OrderedDependencyStore.appendOwn reached.store moduleSelf [22]) revoked moduleSelf 0 cut = .ok cut :=
  Protected.zero revocationWorlds requirement readRequirement validationRequirement noEntranceRequirement _ _ _ _

theorem later_reads_inside_one_slice_still_check_their_own_scope :
    let program : Prog (Request Nat 3) Reply (List Nat) :=
      .call (.read moduleSelf) fun _ => .call (.read 1) fun reply => .ret reply.2
    done? (slice 3 program readOnly) = some (.error .denied) ∧
      (slice 3 program readOnly).1 = 2 := ⟨rfl, rfl⟩

def capturedBody (old : OrderedDependencyStore.ReadStamp 3 × List Nat) (_argument : Unit) :
    Prog (Request Nat 3) Reply (List Nat × List Nat) :=
  .call (.read moduleSelf) fun fresh => .ret (old.2, fresh.2)

def captured := OwnWrite.advance revocationWorlds requirement 2
  (CapturedClosure.capture moduleSelf capturedBody) source

theorem captured_code_and_rows_do_not_grant_new_invocation_permission :
    let started := CapturedClosure.start revocationWorlds requirement source.store noRightsPoint () captured
    started.isSome = true ∧
      started.map (fun saved =>
        (enter source.store noRightsPoint moduleSelf 2
          (fromPrivate revocationWorlds requirement readRequirement validationRequirement saved)).toOption.isNone) =
        some true := ⟨rfl, rfl⟩

abbrev Readout := OrderedDependencyStore.ReadStamp 3 × List Nat
abbrev Context := List (List Nat)
abbrev Loan := Delivery.Loan revocationWorlds requirement readRequirement validationRequirement (Answer := Readout)
abbrev Session := Delivery.Session revocationWorlds requirement readRequirement validationRequirement
  (Answer := Readout) (Context := Context)

def loan : Loan := ⟨PUnit.unit,
  .ok (OrderedDependencyStore.readStamp source.store moduleSelf, [7, 7]), source⟩
def earned := slice 2 readSelf source
def session : Session := ⟨earned, source, []⟩
def revokedSession : Session := {session with context := ({source with point := revoked}, [])}
def staleSession : Session :=
  {session with context := ({source with store := OrderedDependencyStore.appendOwn source.store moduleSelf [22]}, [])}

def isReturn (item : Loan) : Bool := match item.2.1 with
  | .ok _ => true
  | .error _ => false

def rearm (item : Loan) : Packet machine (client Readout) PUnit.unit :=
  ⟨PUnit.unit, .ok readSelf, item.2.2⟩

def consume (context : State revocationWorlds Nat 3 × Context) (item : Loan) :
    Bool × (State revocationWorlds Nat 3 × Context) :=
  match item.2.1 with
  | .ok (_, rows) => (true, context.1, context.2 ++ [rows])
  | .error _ => (false, context)

abbrev delivery := Delivery.provider revocationWorlds requirement readRequirement validationRequirement
  deliveryRequirement moduleSelf isReturn rearm consume

theorem revocation_or_stale_source_before_delivery_keeps_earned_work :
    earned = (1, .done loan) ∧
      delivery.step (base := ()) (index := ()) revokedSession (.accept loan) = ⟨false, revokedSession⟩ ∧
      delivery.step (base := ()) (index := ()) staleSession (.accept loan) = ⟨false, staleSession⟩ ∧
      done? revokedSession.computation = some (.ok (OrderedDependencyStore.readStamp source.store moduleSelf, [7, 7])) := by
  refine ⟨rfl, ?_, ?_, rfl⟩
  · exact Delivery.refused revocationWorlds requirement readRequirement validationRequirement deliveryRequirement
      moduleSelf isReturn rearm consume revokedSession loan (by unfold Delivery.eligible; decide)
  · exact Delivery.refused revocationWorlds requirement readRequirement validationRequirement deliveryRequirement
      moduleSelf isReturn rearm consume staleSession loan (by unfold Delivery.eligible; decide)

theorem missing_metadata_permission_refuses_delivery_for_any_live_view
    (live : OrderedDependencyStore.Store Nat 3) :
    let denied : Session := {session with context := (⟨live, readerOnly⟩, [])}
    FrameUpdate readerOnly.authority (deliveryRequirement readerOnly.world) ∧
      delivery.step (base := ()) (index := ()) denied (.accept loan) = ⟨false, denied⟩ := by
  refine ⟨by decide, ?_⟩
  exact Delivery.metadata_refused revocationWorlds requirement readRequirement validationRequirement
    deliveryRequirement moduleSelf isReturn rearm consume _ loan
    (by change ¬ FrameUpdate Access.read Access.consume; exact Access.not_frameUpdate_read_consume)

theorem authorized_delivery_uses_actual_held_result_without_reexecution :
    let forged : Loan := ⟨PUnit.unit, .ok (OrderedDependencyStore.readStamp source.store moduleSelf, [100]), source⟩
    let actual := delivery.step (base := ()) (index := ()) session (.accept forged)
    actual.1 = true ∧ actual.2.context.2 = [[7, 7]] ∧ actual.2.computation.1 = 1 ∧
      actual.2.computation.2 = .paused (rearm loan) := ⟨rfl, rfl, rfl, rfl⟩

end Controls

#print axioms step_sound
#print axioms step_ok
#print axioms step_iff_action
#print axioms denied_observation_keeps_world
#print axioms write_is_private
#print axioms finite_is_direct
#print axioms finite_execution
#print axioms split_resume
#print axioms direct_ok_runs
#print axioms slice_ok_runs
#print axioms fromPrivate_state_and_paid
#print axioms zero
#print axioms pending_refused
#print axioms pending_is_direct
#print axioms pending_metadata_refused
#print axioms Delivery.refused
#print axioms Delivery.admitted
#print axioms Delivery.success_requires_current_policy
#print axioms Delivery.preserves_paid
#print axioms Delivery.metadata_refused
#print axioms Controls.same_module_self_does_not_imply_same_permission
#print axioms Controls.metadata_validation_is_not_authorized_by_a_stamp
#print axioms Controls.denied_read_is_distinct_from_successful_empty_read
#print axioms Controls.revocation_before_resumed_read_retains_exact_paid_cut
#print axioms Controls.authorized_retry_does_not_replay_paid_write
#print axioms Controls.missing_metadata_permission_refuses_any_live_view
#print axioms Controls.zero_allowance_is_inert_despite_stale_data_and_revocation
#print axioms Controls.later_reads_inside_one_slice_still_check_their_own_scope
#print axioms Controls.captured_code_and_rows_do_not_grant_new_invocation_permission
#print axioms Controls.revocation_or_stale_source_before_delivery_keeps_earned_work
#print axioms Controls.missing_metadata_permission_refuses_delivery_for_any_live_view
#print axioms Controls.authorized_delivery_uses_actual_held_result_without_reexecution

end Protected

#print axioms Invocation.resumeWith_zero
#print axioms Invocation.resumeWith_private
#print axioms Invocation.resumeWith_pending_refused
#print axioms Invocation.resumeWith_pending_is_direct

end OwnWrite

/-! ## Manifest-local cached planning and atomic binding publication

The retained computation reads a pure projection of one captured environment.
Only a completed plan may be validated and published. The projection supplies
complete reply values: a row list may include occurrence identities and
versions, and an empty list may express a complete absence/range observation.
No generic frame law about an arbitrary projection is assumed here.
-/

namespace ManifestPlan

open Mettapedia.Machines

variable {Cell Scope Value Reply Metadata : Type}

abbrev World (Cell Value Metadata : Type) := BindingPublication.Environment Cell Value Metadata
abbrev Plan (Cell Value Metadata : Type) := BindingPublication.Patch Cell Value Metadata
abbrev Code (Cell Scope Value Reply Metadata : Type) :=
  Program Scope Reply (Plan Cell Value Metadata)

variable (observe : World Cell Value Metadata → Scope → Reply)

/-- The existing source cursor with its original world and fixed program.
The dependent tuple adds no evaluation grammar or execution journal. -/
abbrev Cached := Σ captured : World Cell Value Metadata,
  Code Cell Scope Value Reply Metadata ×
    (Nat × Result (Answer := Plan Cell Value Metadata) (observe captured))

def capture (captured : World Cell Value Metadata) (program : Code Cell Scope Value Reply Metadata) :
    Cached observe := ⟨captured, program, 0, .paused ⟨PUnit.unit, program, []⟩⟩

def resume (allowance : Nat) (cached : Cached observe) : Cached observe :=
  ⟨cached.1, cached.2.1, Cursor.resume (provider (observe cached.1)) client
    (readCharge (observe cached.1)) allowance cached.2.2⟩

/-- Source reachability authenticates the cached cut. It is proof evidence,
not another stored list of events or a loop oracle. -/
def Reachable (cached : Cached observe) : Prop :=
  ∃ allowance, cached.2.2 = advance (provider (observe cached.1)) client
    (readCharge (observe cached.1)) allowance ⟨PUnit.unit, cached.2.1, []⟩

theorem capture_reachable (captured : World Cell Value Metadata)
    (program : Code Cell Scope Value Reply Metadata) : Reachable observe (capture observe captured program) :=
  ⟨0, rfl⟩

theorem resume_reachable (allowance : Nat) (cached : Cached observe)
    (reachable : Reachable observe cached) : Reachable observe (resume observe allowance cached) := by
  obtain ⟨earlier, actual⟩ := reachable
  refine ⟨earlier + allowance, ?_⟩
  change Cursor.resume _ _ _ allowance cached.2.2 = _
  rw [actual, ← advance_add]
  rfl

theorem resume_add (first second : Nat) (cached : Cached observe) :
    resume observe second (resume observe first cached) = resume observe (first + second) cached := by
  rcases cached with ⟨captured, program, computation⟩
  simp [resume, Cursor.resume_add]

theorem resume_zero (cached : Cached observe) : resume observe 0 cached = cached := by
  rcases cached with ⟨captured, program, computation⟩
  simp [resume, Cursor.resume_zero]

/-- Conversion of the actual ordered manifest to the existing finite
revision dependency view. Order/duplicates stay in the cursor certificate;
the dependency set only deduplicates equal validation obligations. -/
def manifest [DecidableEq Scope] [DecidableEq Reply]
    (captured : Scope → Reply) (reads : Reads Scope Reply) : CapturedReadView Scope Reply :=
  ⟨⟨captured⟩, reads.map Prod.fst, none, true⟩

theorem manifest_validation [DecidableEq Scope] [DecidableEq Reply]
    (captured current : Scope → Reply) (reads : Reads Scope Reply)
    (authentic : Agrees captured reads) :
    checkReads current reads = true ↔
      (manifest captured reads).CanPublish ⟨current⟩ := by
  rw [Mettapedia.Machines.ReadOnlyQuery.checkReads_iff]
  simp only [CapturedReadView.CanPublish, manifest, true_and,
    CapturedReadView.valid_dependencies_iff, RevisionEnvironment.AgreesOn, List.mem_toFinset]
  constructor
  · intro valid key member
    obtain ⟨read, readMember, same⟩ := List.mem_map.mp member
    subst key
    exact (valid read readMember).trans (authentic read readMember).symm
  · intro valid read member
    exact (valid read.1 (List.mem_map.mpr ⟨read, member, rfl⟩)).trans (authentic read member)

inductive Refusal where
  | unfinished | changed
  deriving DecidableEq, Repr

/-- Validate the complete actual read manifest, then stage the finite patch
in the existing private slot builder. A refusal returns the identical paid
source cut; no private candidate or partial writes become the live world. -/
def commit [DecidableEq Cell] [DecidableEq Reply]
    (inventory : List Cell) (spare : Nat) (current : World Cell Value Metadata)
    (cached : Cached observe) : Except (Refusal × Cached observe) (World Cell Value Metadata) :=
  match completed? (observe cached.1) cached.2.2.2 with
  | none => .error (.unfinished, cached)
  | some observation =>
      if checkReads (observe current) observation.reads then
        .ok (((BindingPublication.prepare current inventory spare).stage observation.answer).denote)
      else .error (.changed, cached)

/-- Independent sequential meaning: read the current world using the original
adaptive source program, then apply its ordered writes to that same world.
The cached execution/validator/private slot representation is not called. -/
def fresh [DecidableEq Cell] (current : World Cell Value Metadata)
    (program : Code Cell Scope Value Reply Metadata) : World Cell Value Metadata :=
  BindingPublication.applyPatch current (run (observe current) program).answer

theorem completed_manifest (cached : Cached observe) (reachable : Reachable observe cached)
    (observation : Observation Scope Reply (Plan Cell Value Metadata))
    (complete : completed? (observe cached.1) cached.2.2.2 = some observation) :
    observation = run (observe cached.1) cached.2.1 ∧ Agrees (observe cached.1) observation.reads := by
  obtain ⟨allowance, actual⟩ := reachable
  have done := completed_correct (observe cached.1) allowance cached.2.1 observation (by rw [← actual]; exact complete)
  exact ⟨done, done ▸ Mettapedia.Machines.ReadOnlyQuery.run_agrees _ _⟩

/-- Successful current-manifest validation preserves the entire adaptive
observation, including its control-selected later reads and ordered result. -/
theorem validated_control [DecidableEq Reply]
    (current : World Cell Value Metadata) (cached : Cached observe)
    (reachable : Reachable observe cached)
    (observation : Observation Scope Reply (Plan Cell Value Metadata))
    (complete : completed? (observe cached.1) cached.2.2.2 = some observation)
    (valid : checkReads (observe current) observation.reads = true) :
    run (observe current) cached.2.1 = observation := by
  obtain ⟨allowance, actual⟩ := reachable
  exact validated_completion (observe cached.1) (observe current) allowance cached.2.1 observation
    (by rw [← actual]; exact complete) valid

theorem commit_incomplete [DecidableEq Cell] [DecidableEq Reply]
    (inventory : List Cell) (spare : Nat) (current : World Cell Value Metadata)
    (cached : Cached observe) (incomplete : completed? (observe cached.1) cached.2.2.2 = none) :
    commit observe inventory spare current cached = .error (.unfinished, cached) := by
  simp [commit, incomplete]

theorem commit_changed [DecidableEq Cell] [DecidableEq Reply]
    (inventory : List Cell) (spare : Nat) (current : World Cell Value Metadata)
    (cached : Cached observe) (observation : Observation Scope Reply (Plan Cell Value Metadata))
    (complete : completed? (observe cached.1) cached.2.2.2 = some observation)
    (changed : checkReads (observe current) observation.reads = false) :
    commit observe inventory spare current cached = .error (.changed, cached) := by
  simp [commit, complete, changed]

theorem commit_admitted [DecidableEq Cell] [DecidableEq Reply]
    (inventory : List Cell) (spare : Nat) (current next : World Cell Value Metadata)
    (cached : Cached observe) (accepted : commit observe inventory spare current cached = .ok next) :
    ∃ observation, completed? (observe cached.1) cached.2.2.2 = some observation ∧
      checkReads (observe current) observation.reads = true ∧
      next = BindingPublication.applyPatch current observation.answer := by
  unfold commit at accepted
  cases complete : completed? (observe cached.1) cached.2.2.2 with
  | none => simp [complete] at accepted
  | some observation =>
      simp only [complete] at accepted
      split at accepted
      · rename_i valid
        have next := Except.ok.inj accepted
        refine ⟨observation, rfl, valid, next.symm.trans ?_⟩
        rw [BindingPublication.Builder.stage_exact, BindingPublication.prepare_exact]
      · cases accepted

/-- The executable cached validator and private publication agree with a
fresh current-world source execution. No plan/source equality is a premise. -/
theorem commit_is_fresh [DecidableEq Cell] [DecidableEq Reply]
    (inventory : List Cell) (spare : Nat) (current next : World Cell Value Metadata)
    (cached : Cached observe) (reachable : Reachable observe cached)
    (accepted : commit observe inventory spare current cached = .ok next) :
    next = fresh observe current cached.2.1 := by
  obtain ⟨observation, complete, valid, actual⟩ := commit_admitted observe inventory spare current next cached accepted
  have same := validated_control observe current cached reachable observation complete valid
  simp only [fresh, same]
  exact actual

/-- A cached cut may be arbitrarily old. Its manifest determines whether it
can be admitted at this point, independently of unrelated world changes. -/
theorem commit_manifest [DecidableEq Cell] [DecidableEq Scope] [DecidableEq Reply]
    (inventory : List Cell) (spare : Nat) (current : World Cell Value Metadata)
    (cached : Cached observe) (reachable : Reachable observe cached)
    (observation : Observation Scope Reply (Plan Cell Value Metadata))
    (complete : completed? (observe cached.1) cached.2.2.2 = some observation) :
    (∃ next, commit observe inventory spare current cached = .ok next) ↔
      (manifest (observe cached.1) observation.reads).CanPublish ⟨observe current⟩ := by
  rw [← manifest_validation (observe cached.1) (observe current) observation.reads
    (completed_manifest observe cached reachable observation complete).2]
  by_cases valid : checkReads (observe current) observation.reads = true <;>
    simp [commit, complete, valid]

/-- A denied commit leaves the live world unchanged. Acceptance uses the
single actual validated/private-publication result. -/
def service [DecidableEq Cell] [DecidableEq Reply]
    (inventory : List Cell) (spare : Nat) (current : World Cell Value Metadata) (cached : Cached observe) :
    World Cell Value Metadata :=
  match commit observe inventory spare current cached with
  | .error _ => current
  | .ok next => next

def execute [DecidableEq Cell] [DecidableEq Reply]
    (inventory : List Cell) (spare : Nat) (current : World Cell Value Metadata)
    (requests : List (Cached observe)) : World Cell Value Metadata :=
  requests.foldl (service observe inventory spare) current

/-- A proof observation of accepted source programs, not a mandatory runtime
journal. It follows actual validation results and never computes future answers. -/
def acceptedPrograms [DecidableEq Cell] [DecidableEq Reply]
    (inventory : List Cell) (spare : Nat) (current : World Cell Value Metadata) :
    List (Cached observe) → List (Code Cell Scope Value Reply Metadata)
  | [] => []
  | cached :: rest => match commit observe inventory spare current cached with
    | .error _ => acceptedPrograms inventory spare current rest
    | .ok next => cached.2.1 :: acceptedPrograms inventory spare next rest

/-- Accepted commit order is a serialization order for independently executed
fresh source programs. Failed attempts are absent from that order and leave the
live world unchanged; their original saved packets remain available. -/
theorem execute_serializes [DecidableEq Cell] [DecidableEq Reply]
    (inventory : List Cell) (spare : Nat) (current : World Cell Value Metadata)
    (requests : List (Cached observe)) (reachable : ∀ cached ∈ requests, Reachable observe cached) :
    execute observe inventory spare current requests =
      (acceptedPrograms observe inventory spare current requests).foldl (fresh observe) current := by
  induction requests generalizing current with
  | nil => rfl
  | cons cached rest ih =>
      have actual := reachable cached List.mem_cons_self
      have remaining : ∀ later ∈ rest, Reachable observe later :=
        fun later member => reachable later (List.mem_cons_of_mem cached member)
      cases outcome : commit observe inventory spare current cached with
      | error refusal =>
          simpa only [execute, List.foldl_cons, service, acceptedPrograms, outcome] using ih current remaining
      | ok next =>
          have same := commit_is_fresh observe inventory spare current next cached actual outcome
          simpa only [execute, List.foldl_cons, service, acceptedPrograms, outcome, ← same] using ih next remaining


theorem execute_append [DecidableEq Cell] [DecidableEq Reply]
    (inventory : List Cell) (spare : Nat) (current : World Cell Value Metadata)
    (first second : List (Cached observe)) :
    execute observe inventory spare current (first ++ second) =
      execute observe inventory spare (execute observe inventory spare current first) second := by
  exact List.foldl_append

/-- Accepted publication preserves every map coordinate outside the writes
computed by the independent current-world source program. Metadata is retained
as the plan's declared result, not silently treated as an unchanged frame. -/
theorem commit_frame [DecidableEq Cell] [DecidableEq Reply]
    (inventory : List Cell) (spare : Nat) (current next : World Cell Value Metadata)
    (cached : Cached observe) (reachable : Reachable observe cached)
    (accepted : commit observe inventory spare current cached = .ok next)
    (key : Cell) (outside : key ∉ (run (observe current) cached.2.1).answer.writes.map Prod.fst) :
    next.get key = current.get key := by
  rw [commit_is_fresh observe inventory spare current next cached reachable accepted]
  exact BindingPublication.applyWrites_lookup_of_not_mem current.get _ key outside

/-- A complete ordered finite-key range projection. Returned pairs retain the
source key as well as the whole value; versions and occurrence payloads can be
part of that value. An absent key contributes no row. -/
def rangeObserve (current : World Cell Value Metadata) (keys : List Cell) : List (Cell × Value) :=
  keys.filterMap fun key => (current.get key).map fun value => (key, value)

/-- This projection's frame law follows from the actual binding write
algorithm. It is not a generic assumed law for arbitrary observation services. -/
theorem rangeObserve_frame [DecidableEq Cell]
    (current : World Cell Value Metadata) (patch : Plan Cell Value Metadata) (keys : List Cell)
    (outside : List.Disjoint keys (patch.writes.map Prod.fst)) :
    rangeObserve (BindingPublication.applyPatch current patch) keys = rangeObserve current keys := by
  apply List.filterMap_congr
  intro key member
  have unchanged := BindingPublication.applyWrites_lookup_of_not_mem current.get patch.writes key
    (List.disjoint_left.mp outside member)
  simp only [BindingPublication.applyPatch, unchanged]

/-- Every finite range actually consulted by the adaptive query is protected.
Writes outside their union preserve the full manifest, including empty ranges. -/
theorem range_validation_frame [DecidableEq Cell] [DecidableEq Value]
    (current : World Cell Value Metadata) (patch : Plan Cell Value Metadata)
    (reads : Reads (List Cell) (List (Cell × Value)))
    (outside : ∀ read ∈ reads, List.Disjoint read.1 (patch.writes.map Prod.fst)) :
    checkReads (rangeObserve (BindingPublication.applyPatch current patch)) reads =
      checkReads (rangeObserve current) reads := by
  apply Bool.eq_iff_iff.mpr
  rw [Mettapedia.Machines.ReadOnlyQuery.checkReads_iff,
    Mettapedia.Machines.ReadOnlyQuery.checkReads_iff]
  constructor
  · intro valid read member
    rw [← rangeObserve_frame current patch read.1 (outside read member)]
    exact valid read member
  · intro valid read member
    rw [rangeObserve_frame current patch read.1 (outside read member)]
    exact valid read member


namespace Controls

abbrev Record := Nat × Nat
abbrev State := World Nat Record (List Nat)
abbrev Rows := List (Nat × Record)

def initial : State :=
  ⟨fun key => match key with
    | 0 | 1 => some (1,10)
    | 3 => some (1,100)
    | 4 => some (8,1)
    | 5 => some (1,500)
    | 6 => some (1,3)
    | 7 => some (1,5)
    | _ => none, []⟩

def observed (world : State) : List Nat → Rows := rangeObserve world

def readValue (rows : Rows) : Record := (rows.headD (0,(0,0))).2

/-- The actual route reply selects a later state read and write. Requests have
stable map keys and may have equal payloads. The range includes an absent key;
the versioned grant and a separate absence are both actual reads. -/
def program (route : Nat) : Code Nat (List Nat) Record Rows (List Nat) :=
  .read [route] fun routes =>
    let target := (readValue routes).2
    .read [0,1,10] fun requests => .read [target] fun state =>
      .read [4] fun grants => .read [2] fun absent =>
        let values := requests.map fun row => row.2.2
        let old := readValue state
        .pure (if (readValue grants).2 = 1 ∧ absent = [] then
          ⟨[(target,(old.1+1,old.2+values.length)), (8,(1,values.sum))], values⟩
          else ⟨[], []⟩)

def cached (route : Nat) : Cached observed :=
  resume observed 6 (capture observed initial (program route))

def changed (key : Nat) (value : Record) : State :=
  { initial with get := Function.update initial.get key (some value) }

def inventory : List Nat := [3,3,5,8]
def outcome : Except (Refusal × Cached observed) State → Nat
  | .error (.unfinished, _) => 0
  | .error (.changed, _) => 1
  | .ok _ => 2

def published : State := service observed inventory 2 initial (cached 6)

theorem retained_manifest_has_real_adaptive_reads :
    let earlier := resume observed 5 (capture observed initial (program 6))
    (completed? (observed initial) earlier.2.2.2).isNone = true ∧ earlier.2.2.1 = 5 ∧
      (cached 6).2.2.1 = 5 ∧
      (recorded (observed initial) (cached 6).2.2.2).map Prod.fst = [[6],[0,1,10],[3],[4],[2]] ∧
      ((completed? (observed initial) (cached 6).2.2.2).map fun answer => answer.answer.metadata) =
        some [10,10] ∧
      outcome (commit observed inventory 2 initial (capture observed initial (program 6))) = 0 := by decide

theorem unrelated_write_is_admitted_with_duplicates_and_its_frame :
    let current := changed 9 (1,77)
    let result := service observed inventory 2 current (cached 6)
    outcome (commit observed inventory 2 current (cached 6)) = 2 ∧
      result.get 3 = some (2,102) ∧ result.get 8 = some (1,20) ∧
      result.get 9 = some (1,77) ∧ result.metadata = [10,10] ∧
      (service observed [] 0 current (cached 6)).get 3 = result.get 3 ∧
      (service observed [] 0 current (cached 6)).metadata = result.metadata := by decide

theorem consulted_range_absence_and_version_changes_refuse :
    outcome (commit observed inventory 2 (changed 3 (2,101)) (cached 6)) = 1 ∧
      outcome (commit observed inventory 2 (changed 10 (1,10)) (cached 6)) = 1 ∧
      outcome (commit observed inventory 2 (changed 2 (1,99)) (cached 6)) = 1 ∧
      outcome (commit observed inventory 2 (changed 4 (9,1)) (cached 6)) = 1 ∧
      outcome (commit observed inventory 2 (changed 4 (9,0)) (cached 6)) = 1 ∧
      outcome (commit observed inventory 2 (changed 0 (2,10)) (cached 6)) = 1 := by decide

/-- Replaying an old plan without checking the route would write the wrong
state coordinate. Actual manifest validation refuses before publication. -/
theorem changed_control_path_is_not_replayed_as_fresh :
    let current := changed 6 (2,5)
    let oldPatch := (run (observed initial) (program 6)).answer
    outcome (commit observed inventory 2 current (cached 6)) = 1 ∧
      (BindingPublication.applyPatch current oldPatch).get 3 = some (2,102) ∧
      (fresh observed current (program 6)).get 3 = some (1,100) ∧
      (fresh observed current (program 6)).get 5 = some (2,502) ∧
      (service observed inventory 2 current (cached 6)).get 3 = some (1,100) := by decide

theorem independent_cached_commits_serialize_and_competing_one_refuses :
    let requests := [cached 6, cached 6, cached 7]
    let result := execute observed inventory 2 initial requests
    (acceptedPrograms observed inventory 2 initial requests).length = 2 ∧
      result.get 3 = some (2,102) ∧ result.get 5 = some (2,502) ∧
      result.get 8 = some (1,20) ∧ result.metadata = [10,10] ∧
      outcome (commit observed inventory 2 published (cached 6)) = 1 ∧
      outcome (commit observed inventory 2 published (cached 7)) = 2 := by decide

theorem refusal_retains_the_original_paid_cut :
    let result := commit observed inventory 2 (changed 4 (9,0)) (cached 6)
    match result with
    | .ok _ => False
    | .error (reason, retained) =>
        reason = .changed ∧ retained.2.2.1 = 5 ∧
          retained.1.get 4 = some (8,1) ∧
          (recorded (observed retained.1) retained.2.2.2).map Prod.fst =
            [[6],[0,1,10],[3],[4],[2]] ∧
          outcome (commit observed inventory 2 (changed 9 (1,77)) retained) = 2 := by
  have refused : commit observed inventory 2 (changed 4 (9,0)) (cached 6) =
      .error (.changed, cached 6) := rfl
  dsimp only
  rw [refused]
  decide

end Controls


/-- The concrete consumer's cached cut is constructed by the actual source
cursor. No caller-supplied reachability certificate is needed. -/
theorem consumer_reachable (route : Nat) :
    Reachable Controls.observed (Controls.cached route) :=
  resume_reachable Controls.observed 6 _
    (capture_reachable Controls.observed Controls.initial (Controls.program route))

/-- Arbitrary finite words of the concrete adaptive planning consumer inherit
fresh-at-commit serialization, discharging every source-origin premise from its
capture/resume construction. Refused routes do not enter the accepted word. -/
theorem consumer_serializes (current : Controls.State) (routes : List Nat) :
    execute Controls.observed Controls.inventory 2 current (routes.map Controls.cached) =
      (acceptedPrograms Controls.observed Controls.inventory 2 current (routes.map Controls.cached)).foldl
        (fresh Controls.observed) current := by
  apply execute_serializes
  intro cached member
  obtain ⟨route, _, rfl⟩ := List.mem_map.mp member
  exact consumer_reachable route

#print axioms consumer_reachable
#print axioms consumer_serializes

#print axioms Controls.retained_manifest_has_real_adaptive_reads
#print axioms Controls.unrelated_write_is_admitted_with_duplicates_and_its_frame
#print axioms Controls.consulted_range_absence_and_version_changes_refuse
#print axioms Controls.changed_control_path_is_not_replayed_as_fresh
#print axioms Controls.independent_cached_commits_serialize_and_competing_one_refuses
#print axioms Controls.refusal_retains_the_original_paid_cut

#print axioms execute_append
#print axioms commit_frame
#print axioms rangeObserve_frame
#print axioms range_validation_frame

#print axioms capture_reachable
#print axioms resume_reachable
#print axioms resume_add
#print axioms resume_zero
#print axioms manifest_validation
#print axioms completed_manifest
#print axioms validated_control
#print axioms commit_incomplete
#print axioms commit_changed
#print axioms commit_admitted
#print axioms commit_is_fresh
#print axioms commit_manifest
#print axioms execute_serializes

end ManifestPlan


/-! ## A completed policy observation followed by an adaptive plan

Earlier policy observations remain private dependencies of the fixed plan.
Beginning and committing validate them; pure planning resumes only its captured
source. The dependency view is not a grant array or writable authority.
-/

namespace PolicyPlan

set_option synthInstance.maxSize 256

open ManifestPlan (World Code Cached)

variable {Cell Scope Value Reply Metadata Epoch Config : Type}
variable (observe : World Cell Value Metadata → Scope → Reply)
    (sourceId : World Cell Value Metadata → Epoch)

abbrev Saved (Epoch : Type) := Observation Scope Reply Epoch × Cached observe

def begin [DecidableEq Epoch] [DecidableEq Reply]
    (policyWorld planWorld : World Cell Value Metadata)
    (previous : Nat × Result (Answer := Config) (observe policyWorld))
    (make : Config → Code Cell Scope Value Reply Metadata) : Option (Saved observe Epoch) :=
  match completed? (observe policyWorld) previous.2 with
  | none => none
  | some policy =>
      if sourceId planWorld = sourceId policyWorld ∧ checkReads (observe planWorld) policy.reads = true then
        some (⟨sourceId policyWorld, policy.reads⟩, ManifestPlan.capture observe planWorld (make policy.answer))
      else none

def resume (allowance : Nat) (saved : Saved observe Epoch) : Saved observe Epoch :=
  (saved.1, ManifestPlan.resume observe allowance saved.2)

theorem resume_zero (saved : Saved observe Epoch) : resume observe 0 saved = saved := by
  rcases saved with ⟨required, cached⟩
  simp [resume, ManifestPlan.resume_zero]

theorem resume_add (first second : Nat) (saved : Saved observe Epoch) :
    resume observe second (resume observe first saved) = resume observe (first + second) saved := by
  simp [resume, ManifestPlan.resume_add]

/-- The source/epoch and every retained policy dependency are checked at the
same current world used by the existing plan validator and private builder.
Refusal retains the whole earlier dependency view and actual plan cursor. -/
def commit [DecidableEq Cell] [DecidableEq Epoch] [DecidableEq Reply]
    (inventory : List Cell) (spare : Nat) (current : World Cell Value Metadata)
    (saved : Saved observe Epoch) :
    Except (ManifestPlan.Refusal × Saved observe Epoch) (World Cell Value Metadata) :=
  if sourceId current = saved.1.answer ∧ checkReads (observe current) saved.1.reads = true then
    match ManifestPlan.commit observe inventory spare current saved.2 with
    | .error (reason, _) => .error (reason, saved)
    | .ok next => .ok next
  else .error (.changed, saved)

theorem begin_admitted [DecidableEq Epoch] [DecidableEq Reply]
    (policyWorld planWorld : World Cell Value Metadata)
    (previous : Nat × Result (Answer := Config) (observe policyWorld))
    (make : Config → Code Cell Scope Value Reply Metadata) (saved : Saved observe Epoch)
    (issued : begin observe sourceId policyWorld planWorld previous make = some saved) :
    ∃ policy, completed? (observe policyWorld) previous.2 = some policy ∧
      sourceId planWorld = sourceId policyWorld ∧ checkReads (observe planWorld) policy.reads = true ∧
      saved = (⟨sourceId policyWorld, policy.reads⟩, ManifestPlan.capture observe planWorld (make policy.answer)) := by
  unfold begin at issued
  cases done : completed? (observe policyWorld) previous.2 with
  | none => simp [done] at issued
  | some policy =>
      simp only [done] at issued
      split at issued
      · rename_i valid
        exact ⟨policy, rfl, valid.1, valid.2, (Option.some.inj issued).symm⟩
      · cases issued

theorem commit_admitted [DecidableEq Cell] [DecidableEq Epoch] [DecidableEq Reply]
    (inventory : List Cell) (spare : Nat) (current next : World Cell Value Metadata)
    (saved : Saved observe Epoch) (accepted : commit observe sourceId inventory spare current saved = .ok next) :
    sourceId current = saved.1.answer ∧ checkReads (observe current) saved.1.reads = true ∧
      ManifestPlan.commit observe inventory spare current saved.2 = .ok next := by
  unfold commit at accepted
  split at accepted
  · rename_i valid
    cases inner : ManifestPlan.commit observe inventory spare current saved.2 with
    | error reason => simp [inner] at accepted
    | ok result =>
        simp only [inner, Except.ok.injEq] at accepted
        subst result
        exact ⟨valid.1, valid.2, rfl⟩
  · cases accepted

theorem commit_prior_refused [DecidableEq Cell] [DecidableEq Epoch] [DecidableEq Reply]
    (inventory : List Cell) (spare : Nat) (current : World Cell Value Metadata)
    (saved : Saved observe Epoch)
    (denied : ¬ (sourceId current = saved.1.answer ∧ checkReads (observe current) saved.1.reads = true)) :
    commit observe sourceId inventory spare current saved = .error (.changed, saved) := by
  simp [commit, denied]

/-- A completed policy really generates the plan's fixed body. Its observed
manifest remains a current dependency after arbitrary finite plan resumption.
Accepted publication equals independently executing policy then adaptive plan
at commit; no desired configuration or plan equality is supplied. -/
theorem issued_commit_is_fresh [DecidableEq Cell] [DecidableEq Epoch] [DecidableEq Reply]
    (inventory : List Cell) (spare before allowance : Nat)
    (policyWorld planWorld current next : World Cell Value Metadata)
    (policyCode : Program Scope Reply Config) (make : Config → Code Cell Scope Value Reply Metadata)
    (saved : Saved observe Epoch)
    (issued : begin observe sourceId policyWorld planWorld
      (advance (provider (observe policyWorld)) client (readCharge (observe policyWorld))
        before ⟨PUnit.unit, policyCode, []⟩) make = some saved)
    (accepted : commit observe sourceId inventory spare current (resume observe allowance saved) = .ok next) :
    next = ManifestPlan.fresh observe current (Mettapedia.Machines.ReadOnlyQuery.bind policyCode make) := by
  obtain ⟨policy, completed, _, _, exactSaved⟩ :=
    begin_admitted observe sourceId policyWorld planWorld _ make saved issued
  subst saved
  obtain ⟨_, valid, inner⟩ := commit_admitted observe sourceId inventory spare current next _ accepted
  have actualPolicy := validated_completion (observe policyWorld) (observe current) before policyCode policy completed valid
  have reachable := ManifestPlan.resume_reachable observe allowance _
    (ManifestPlan.capture_reachable observe planWorld (make policy.answer))
  have actualPlan := ManifestPlan.commit_is_fresh observe inventory spare current next _ reachable inner
  rw [actualPlan]
  simp only [ManifestPlan.fresh, Mettapedia.Machines.ReadOnlyQuery.run_bind, actualPolicy]
  rfl

/-- New adaptive reads precede retained policy views in the joined array.
The source interpreter's chronological certificate is a different observation;
pure validation accepts exactly the conjunction in either array order. -/
theorem joined_validation [DecidableEq Cell] [DecidableEq Epoch] [DecidableEq Reply]
    (inventory : List Cell) (spare : Nat) (current : World Cell Value Metadata)
    (saved : Saved observe Epoch) (plan : Observation Scope Reply (ManifestPlan.Plan Cell Value Metadata))
    (complete : completed? (observe saved.2.1) saved.2.2.2.2 = some plan) :
    (∃ next, commit observe sourceId inventory spare current saved = .ok next) ↔
      sourceId current = saved.1.answer ∧
        checkReads (observe current) (plan.reads ++ saved.1.reads) = true := by
  rw [Mettapedia.Machines.ReadOnlyQuery.checkReads_append, Bool.and_eq_true]
  by_cases epoch : sourceId current = saved.1.answer <;>
    by_cases prior : checkReads (observe current) saved.1.reads = true <;>
    by_cases actual : checkReads (observe current) plan.reads = true <;>
    simp [commit, ManifestPlan.commit, complete, epoch, prior, actual]


/-- The metadata-only joined source service justifies the actual full policy
begin operation. Query origin is discharged from the completed policy cursor;
immutable version materialization, not equality of arbitrary integers, lifts
the original manifest to the newly captured plan world. -/
theorem joined_begins {Generation Space Letter Revision Payload : Type}
    [DecidableEq Epoch] [DecidableEq Space] [DecidableEq Letter]
    [DecidableEq Revision] [DecidableEq Payload]
    (readSource : World Cell Value Metadata → Mettapedia.Machines.ScopedRecords.Source Epoch Generation Space Letter Revision)
    (contents : Epoch → Mettapedia.Machines.ScopedRecords.Stamp Space Letter Revision → Payload)
    (policyWorld planWorld : World Cell Value Metadata)
    (policyCode : Program (Mettapedia.Machines.ScopedRecords.Scope Space Letter)
      (Mettapedia.Machines.ScopedRecords.FullReply Epoch Space Letter Revision Payload) Config)
    (before : Nat)
    (policy : Observation (Mettapedia.Machines.ScopedRecords.Scope Space Letter)
      (Mettapedia.Machines.ScopedRecords.FullReply Epoch Space Letter Revision Payload) Config)
    (complete : completed? (Mettapedia.Machines.ScopedRecords.observe contents (readSource policyWorld))
      (advance (provider (Mettapedia.Machines.ScopedRecords.observe contents (readSource policyWorld))) client
        (readCharge (Mettapedia.Machines.ScopedRecords.observe contents (readSource policyWorld))) before
          ⟨PUnit.unit, policyCode, []⟩).2 = some policy)
    (make : Config → Code Cell (Mettapedia.Machines.ScopedRecords.Scope Space Letter) Value
      (Mettapedia.Machines.ScopedRecords.FullReply Epoch Space Letter Revision Payload) Metadata)
    (scopes : List (Mettapedia.Machines.ScopedRecords.Scope Space Letter))
    (result : Mettapedia.Machines.ScopedRecords.Captured Epoch Space Letter Revision Payload)
    (issued : Mettapedia.Machines.ScopedRecords.joined contents (readSource planWorld)
      ⟨(readSource policyWorld).storeId, policy.reads⟩ scopes = some result) :
    begin (fun world => Mettapedia.Machines.ScopedRecords.observe contents (readSource world))
      (fun world => (readSource world).storeId) policyWorld planWorld
      (advance (provider (Mettapedia.Machines.ScopedRecords.observe contents (readSource policyWorld))) client
        (readCharge (Mettapedia.Machines.ScopedRecords.observe contents (readSource policyWorld))) before
          ⟨PUnit.unit, policyCode, []⟩) make =
      some (({ answer := (readSource policyWorld).storeId, reads := policy.reads } :
          Mettapedia.Machines.ScopedRecords.Captured Epoch Space Letter Revision Payload),
        ManifestPlan.capture (fun world => Mettapedia.Machines.ScopedRecords.observe contents (readSource world))
          planWorld (make policy.answer)) := by
  have original := completed_correct _ before policyCode policy complete
  have authentic : Mettapedia.Machines.ReadOnlyQuery.Agrees
      (Mettapedia.Machines.ScopedRecords.observe contents (readSource policyWorld)) policy.reads := by
    rw [original]
    exact Mettapedia.Machines.ReadOnlyQuery.run_agrees _ _
  have valid := (Mettapedia.Machines.ScopedRecords.joined_admitted contents (readSource planWorld)
    ⟨(readSource policyWorld).storeId, policy.reads⟩ result scopes issued).1
  have current := (Mettapedia.Machines.ScopedRecords.validate_exact contents (readSource policyWorld)
    (readSource planWorld) ⟨(readSource policyWorld).storeId, policy.reads⟩ authentic).mp valid
  have checked : checkReads (Mettapedia.Machines.ScopedRecords.observe contents (readSource planWorld))
      policy.reads = true := (Mettapedia.Machines.ReadOnlyQuery.checkReads_iff _ _).mpr current.2
  simp [begin, complete, current.1, checked]

#print axioms joined_begins

#print axioms resume_zero
#print axioms resume_add
#print axioms begin_admitted
#print axioms commit_admitted
#print axioms commit_prior_refused
#print axioms issued_commit_is_fresh
#print axioms joined_validation

namespace RecordClient

open Mettapedia.Machines

abbrev Source := ScopedRecords.Source Nat Nat Nat Nat Nat
abbrev Stamp := ScopedRecords.Stamp Nat Nat Nat
abbrev ClientScope := ScopedRecords.Scope Nat Nat
abbrev ClientReply := ScopedRecords.FullReply Nat Nat Nat Nat Nat
abbrev ClientCell := Sum Unit (ScopedRecords.Key Nat Nat)
abbrev ClientValue := Sum Source Nat
abbrev State := World ClientCell ClientValue Unit

/-- The immutable version interface; equal payloads can have distinct keys. -/
def contents (_epoch : Nat) (stamp : Stamp) : Nat :=
  if stamp.1 = (0, [0]) then if stamp.2 = 2 then 0 else 10
  else if stamp.1 = (1, [11]) then 99 + stamp.2
  else if stamp.1.1 = 1 then 7 else 5

def sourceCell : ClientCell := .inl ()
def source (world : State) : Source :=
  match world.get sourceCell with
  | some (.inl current) => current
  | _ => ⟨0, 0, []⟩

def observed (world : State) : ClientScope → ClientReply := ScopedRecords.observe contents (source world)
def epoch (world : State) : Nat := (source world).storeId

def world (current : Source) : State :=
  ⟨fun key => match key with | .inl _ => some (.inl current) | .inr _ => none, ()⟩

def payload (reply : ClientReply) : Nat := (reply.2.headD (((0, []), 0), 0)).2

/-- A versioned policy selects a channel and its state coordinate. A complete
negative prefix read also participates in the decision. -/
def policyCode : Program ClientScope ClientReply Nat :=
  .read (.key 0 [0]) fun policy => .read (.prefix 0 [99]) fun denials =>
    .pure (if denials.2.isEmpty then payload policy else 0)

def policyCut (current : State) : Nat × Result (Answer := Nat) (observed current) :=
  advance (provider (observed current)) client (readCharge (observed current))
    3 ⟨PUnit.unit, policyCode, []⟩

def policyView (current : State) : Observation ClientScope ClientReply Nat :=
  (completed? (observed current) (policyCut current).2).getD ⟨0, []⟩

def required (current : State) : ScopedRecords.Captured Nat Nat Nat Nat Nat :=
  ⟨epoch current, (policyView current).reads⟩

def planScopes (channel : Nat) : List ClientScope :=
  [.prefix 1 [channel], .key 1 [channel + 1], .key 1 [99]]

/-- The chosen policy drives real adaptive reads. Output bindings are separate
from the source cell; publication preserves the current input view by the
existing binding-write frame law. -/
def makePlan (channel : Nat) : Code ClientCell ClientScope ClientValue ClientReply Unit :=
  .read (.prefix 1 [channel]) fun requests =>
    .read (.key 1 [channel + 1]) fun state => .read (.key 1 [99]) fun absent =>
      .pure (if channel ≠ 0 ∧ absent.2.isEmpty then
        ⟨[(.inr (1, [channel + 1]), .inr (payload state + requests.2.length)),
          (.inr (2, [0]), .inr ((requests.2.map Prod.snd).sum))], ()⟩
        else ⟨[], ()⟩)

def prepare (policyWorld planWorld : State) : Option (Saved observed Nat) :=
  begin observed epoch policyWorld planWorld (policyCut policyWorld) makePlan

def inventory : List ClientCell := [.inr (1, [11]), .inr (2, [0])]

def output (current : State) (key : ScopedRecords.Key Nat Nat) : Option Nat :=
  match current.get (.inr key) with
  | some (.inr number) => some number
  | _ => none

def outcome : Except (ManifestPlan.Refusal × Saved observed Nat) State → Nat
  | .error (.unfinished, _) => 0
  | .error (.changed, _) => 1
  | .ok _ => 2

theorem policy_completed (current : State) :
    completed? (observed current) (policyCut current).2 = some (policyView current) := rfl

/-- This consumer's independent comparison discharges source reachability
through its actual policy cursor, capture and finite plan resumption. -/
theorem prepared_commit_fresh (policyWorld planWorld current next : State)
    (saved : Saved observed Nat) (allowance : Nat)
    (issued : prepare policyWorld planWorld = some saved)
    (accepted : commit observed epoch inventory 0 current (resume observed allowance saved) = .ok next) :
    next = ManifestPlan.fresh observed current
      (Mettapedia.Machines.ReadOnlyQuery.bind policyCode makePlan) :=
  issued_commit_is_fresh observed epoch inventory 0 3 allowance policyWorld planWorld current next
    policyCode makePlan saved issued accepted

/-- A metadata-only joined source snapshot supplies the actual consumer's
begin checks. Its earlier policy reads are constructed, not caller asserted. -/
theorem joined_prepare (policyWorld planWorld : State) (scopes : List ClientScope)
    (result : ScopedRecords.Captured Nat Nat Nat Nat Nat)
    (issued : ScopedRecords.joined contents (source planWorld) (required policyWorld) scopes = some result) :
    prepare policyWorld planWorld = some
      (required policyWorld, ManifestPlan.capture observed planWorld (makePlan (policyView policyWorld).answer)) := by
  exact joined_begins source contents policyWorld planWorld policyCode 3 (policyView policyWorld)
    (policy_completed policyWorld) makePlan scopes result issued

/-- A real joined backend capture and this consumer's actual retained plan
suffice for the fresh sequential policy/plan theorem. No separate full-payload
agreement or source-reachability premise is supplied. -/
theorem joined_commit_fresh (policyWorld planWorld current next : State)
    (scopes : List ClientScope) (result : ScopedRecords.Captured Nat Nat Nat Nat Nat)
    (allowance : Nat)
    (issued : ScopedRecords.joined contents (source planWorld) (required policyWorld) scopes = some result)
    (accepted : commit observed epoch inventory 0 current
      (resume observed allowance (required policyWorld,
        ManifestPlan.capture observed planWorld (makePlan (policyView policyWorld).answer))) = .ok next) :
    next = ManifestPlan.fresh observed current
      (Mettapedia.Machines.ReadOnlyQuery.bind policyCode makePlan) :=
  prepared_commit_fresh policyWorld planWorld current next _ allowance
    (joined_prepare policyWorld planWorld scopes result issued) accepted

/-- Actual accepted patches never overwrite the current source cell. This
frame is derived from the generated writes, not assumed for arbitrary stores. -/
theorem prepared_source_frame (policyWorld planWorld current next : State)
    (saved : Saved observed Nat) (allowance : Nat)
    (issued : prepare policyWorld planWorld = some saved)
    (accepted : commit observed epoch inventory 0 current (resume observed allowance saved) = .ok next) :
    source next = source current := by
  rw [prepared_commit_fresh policyWorld planWorld current next saved allowance issued accepted]
  unfold source ManifestPlan.fresh
  have outside : sourceCell ∉
      (run (observed current) (Mettapedia.Machines.ReadOnlyQuery.bind policyCode makePlan)).answer.writes.map Prod.fst := by
    simp [policyCode, makePlan, Mettapedia.Machines.ReadOnlyQuery.run_bind,
      Mettapedia.Machines.ReadOnlyQuery.run, sourceCell]
    split <;> simp
  simp only [BindingPublication.applyPatch]
  rw [BindingPublication.applyWrites_lookup_of_not_mem current.get _ sourceCell outside]

namespace Controls

def policyStamp (revision : Nat) : Stamp := ((0, [0]), revision)
def first : Stamp := ((1, [10, 0]), 1)
def second : Stamp := ((1, [10, 1]), 1)
def stateStamp (revision : Nat) : Stamp := ((1, [11]), revision)
def initialSource : Source := ⟨17, 4, [policyStamp 1, first, second, stateStamp 1]⟩
def initial : State := world initialSource

def appendSource (generation : Nat) (added : List Stamp) : Source :=
  initialSource.replaceRevision generation (initialSource.entries ++ added)
def unrelated : State := world (appendSource 5 [((2, [88]), 1)])
def later : State := world (appendSource 6 [((2, [88]), 1), ((3, [77]), 1)])
def policyChanged (revision : Nat) : State :=
  world ⟨17, 5, [policyStamp revision, first, second, stateStamp 1]⟩
def consultedChanged : State := world ⟨17, 5, [policyStamp 1, first, second, stateStamp 2]⟩
def phantom : State := world (appendSource 5 [((1, [10, 2]), 1)])
def insertedAbsent : State := world (appendSource 5 [((1, [99]), 1)])
def denial : State := world (appendSource 5 [((0, [99, 0]), 1)])
def otherEpoch : State := world ⟨18, 4, initialSource.entries⟩

def started : Saved observed Nat :=
  (prepare initial unrelated).get (by decide)
def finished : Saved observed Nat := resume observed 4 started

def result : State :=
  match commit observed epoch inventory 0 later finished with
  | .ok next => next
  | .error _ => later

theorem complete_open_scopes_preserve_order_identity_and_absence :
    ((observed initial (.prefix 1 [10])).2.map Prod.fst) = [first, second] ∧
      ((observed initial (.prefix 1 [10])).2.map Prod.snd) = [7, 7] ∧
      first ≠ second ∧
      ((observed initial (.space 1)).2.map Prod.fst) = [first, second, stateStamp 1] ∧
      (observed initial (.key 1 [99])).2 = [] ∧
      (observed initial (.prefix 0 [99])).2 = [] := by decide

theorem joined_views_have_new_then_original_policy_dependencies :
    let joined := ScopedRecords.joined contents (source unrelated) (required initial) (planScopes 10)
    (joined.map fun view => view.reads.map Prod.fst) =
      some [.prefix 1 [10], .key 1 [11], .key 1 [99], .key 0 [0], .prefix 0 [99]] ∧
      (joined.map fun view => view.answer) = some 17 ∧
      (source unrelated).revision = 5 ∧ (source initial).revision = 4 ∧
      (prepare initial unrelated).isSome = true := by decide

theorem unrelated_current_updates_publish_the_real_policy_plan :
    outcome (commit observed epoch inventory 0 later finished) = 2 ∧
      output result (1, [11]) = some 102 ∧ output result (2, [0]) = some 14 ∧
      (source result).entries = (source later).entries ∧
      (source result).revision = 6 ∧
      (policyView initial).answer = 10 ∧ finished.2.2.2.1 = 3 := by decide

theorem complete_manifest_refuses_consulted_changes_and_phantoms :
    outcome (commit observed epoch inventory 0 consultedChanged finished) = 1 ∧
      outcome (commit observed epoch inventory 0 phantom finished) = 1 ∧
      outcome (commit observed epoch inventory 0 insertedAbsent finished) = 1 ∧
      outcome (commit observed epoch inventory 0 later (resume observed 2 started)) = 0 := by decide

theorem revoked_restored_and_epoch_changed_policy_refuse :
    (prepare initial (policyChanged 2)).isNone = true ∧
      (prepare initial (policyChanged 3)).isNone = true ∧
      payload (observed (policyChanged 3) (.key 0 [0])) = payload (observed initial (.key 0 [0])) ∧
      (prepare initial denial).isNone = true ∧ (prepare initial otherEpoch).isNone = true ∧
      outcome (commit observed epoch inventory 0 (policyChanged 2) finished) = 1 ∧
      outcome (commit observed epoch inventory 0 (policyChanged 3) finished) = 1 ∧
      outcome (commit observed epoch inventory 0 denial finished) = 1 ∧
      outcome (commit observed epoch inventory 0 otherEpoch finished) = 1 := by decide

theorem refusal_keeps_the_exact_paid_cut_for_retry :
    match commit observed epoch inventory 0 (policyChanged 2) finished with
    | .ok _ => False
    | .error (reason, retained) =>
      reason = .changed ∧ retained.2.2.2.1 = 3 ∧
        (recorded (observed retained.2.1) retained.2.2.2.2).map Prod.fst = planScopes 10 ∧
        retained.1.reads.map Prod.fst = [.key 0 [0], .prefix 0 [99]] ∧
        outcome (commit observed epoch inventory 0 later retained) = 2 := by
  have refused : commit observed epoch inventory 0 (policyChanged 2) finished =
      .error (.changed, finished) := rfl
  rw [refused]
  decide

/-- Metadata alone does not protect mutable contents reusing the same stamp.
This intentionally violates the declared immutable version interface. -/
theorem same_revision_different_contents_is_not_full_agreement :
    let changedContents := fun epoch stamp => if stamp = policyStamp 1 then 99 else contents epoch stamp
    ScopedRecords.validate initialSource (required initial) = true ∧
      checkReads (ScopedRecords.observe changedContents initialSource) (required initial).reads = false := by decide

end Controls

#print axioms policy_completed
#print axioms prepared_commit_fresh
#print axioms joined_prepare
#print axioms joined_commit_fresh
#print axioms prepared_source_frame
#print axioms Controls.complete_open_scopes_preserve_order_identity_and_absence
#print axioms Controls.joined_views_have_new_then_original_policy_dependencies
#print axioms Controls.unrelated_current_updates_publish_the_real_policy_plan
#print axioms Controls.complete_manifest_refuses_consulted_changes_and_phantoms
#print axioms Controls.revoked_restored_and_epoch_changed_policy_refuse
#print axioms Controls.refusal_keeps_the_exact_paid_cut_for_retry
#print axioms Controls.same_revision_different_contents_is_not_full_agreement

end RecordClient

/-! ## A single-parent attenuating delegation profile

Grant references retain an authorization generation, independently of source
epochs and row revisions. Every decision reads the actual selected grant,
revocation scope and trust anchor. The finite construction depth is an admission
limit, not a negative authorization answer or a catalogue observation. Lookup,
set comparison and validation costs remain separate native-service obligations.
Construction-depth exhaustion completes with an incomplete decision; increasing
that limit constructs a new query. The ordinary cursor alone supplies the
proved no-replay pause/resume route. Authentic principal/key issuance, fresh
authorization generations and authority to author policy records are separate
service contracts; this validator does not provide them.
-/

namespace Delegation

structure Reference (Space Letter Generation : Type) where
  slot : ScopedRecords.Key Space Letter
  generation : Generation
  deriving DecidableEq, Repr

namespace Reference

/-- The native-generation instance uses the canonical provider/resource/
generation handle.  The grant slot's space and letter path are the provider
and resource; no second nominal authority identity is introduced. -/
def toHandle {Space Letter : Type} (reference : Reference Space Letter Nat) :
    Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone.Handle Space (List Letter) :=
  ⟨reference.slot.1, reference.slot.2, reference.generation⟩

theorem toHandle_injective {Space Letter : Type} :
    Function.Injective (toHandle (Space := Space) (Letter := Letter)) := by
  intro first second same
  cases first with
  | mk firstSlot firstGeneration =>
      cases second with
      | mk secondSlot secondGeneration =>
          cases firstSlot with
          | mk firstSpace firstLetters =>
              cases secondSlot with
              | mk secondSpace secondLetters =>
                  simp only [toHandle] at same
                  cases same
                  rfl

@[simp] theorem toHandle_inj {Space Letter : Type}
    {first second : Reference Space Letter Nat} :
    first.toHandle = second.toHandle ↔ first = second :=
  toHandle_injective.eq_iff

end Reference

structure Grant (Space Letter Generation Principal Realm Right : Type) where
  generation : Generation
  issuer : Principal
  grantee : Principal
  realm : Realm
  rights : Finset Right
  delegable : Bool
  parent : Option (Reference Space Letter Generation)
  deriving DecidableEq

inductive Record (Space Letter Generation Principal Realm Right : Type) where
  | grant (value : Grant Space Letter Generation Principal Realm Right)
  | anchor (issuer : Principal) (realm : Realm) (rights : Finset Right)
  | denial
  deriving DecidableEq

structure Profile (Space Letter Generation Principal Realm : Type) where
  revocations : Reference Space Letter Generation → ScopedRecords.Scope Space Letter
  anchor : Principal → Realm → ScopedRecords.Key Space Letter

structure Demand (Space Letter Generation Principal Realm Right : Type) where
  reference : Reference Space Letter Generation
  principal : Principal
  realm : Realm
  rights : Finset Right
  delegation : Bool
  deriving DecidableEq

inductive Denial where
  | cycle | missingGrant | attenuation | revoked | missingRoot
  deriving DecidableEq, Repr

inductive Decision where
  | allowed
  | denied (reason : Denial)
  | incomplete
  deriving DecidableEq, Repr

variable {Space Letter Generation Principal Realm Right Epoch Revision : Type}

abbrev GrantScope := ScopedRecords.Scope Space Letter
abbrev GrantReply := ScopedRecords.FullReply Epoch Space Letter Revision
  (Record Space Letter Generation Principal Realm Right)

def keyScope (reference : Reference Space Letter Generation) : GrantScope (Space := Space) (Letter := Letter) :=
  .key reference.slot.1 reference.slot.2

def parentDemand (grant : Grant Space Letter Generation Principal Realm Right)
    (reference : Reference Space Letter Generation) : Demand Space Letter Generation Principal Realm Right :=
  ⟨reference, grant.issuer, grant.realm, grant.rights, true⟩

/-- Permission flags are attenuated here; the decision creates no exclusive
resource or native principal. Those remain separate invocation boundaries. -/
def Eligible (demand : Demand Space Letter Generation Principal Realm Right)
    (grant : Grant Space Letter Generation Principal Realm Right) : Prop :=
  grant.grantee = demand.principal ∧ grant.realm = demand.realm ∧ demand.rights ⊆ grant.rights ∧
    (demand.delegation = true → grant.delegable = true)

variable [DecidableEq Space] [DecidableEq Letter] [DecidableEq Generation]
  [DecidableEq Principal] [DecidableEq Realm] [DecidableEq Right]

instance eligibleDecision (demand : Demand Space Letter Generation Principal Realm Right)
    (grant : Grant Space Letter Generation Principal Realm Right) : Decidable (Eligible demand grant) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- A key lookup must return exactly one current grant at the requested slot
and authorization generation. Duplicate active rows are refused. -/
def decodeGrant (reference : Reference Space Letter Generation)
    (reply : GrantReply (Space := Space) (Letter := Letter) (Generation := Generation)
      (Principal := Principal) (Realm := Realm) (Right := Right) (Epoch := Epoch) (Revision := Revision)) :
    Option (Grant Space Letter Generation Principal Realm Right) :=
  match reply.2 with
  | [(stamp, .grant grant)] =>
      if stamp.1 = reference.slot ∧ grant.generation = reference.generation then some grant else none
  | _ => none

def rootAllowed (profile : Profile Space Letter Generation Principal Realm)
    (grant : Grant Space Letter Generation Principal Realm Right)
    (reply : GrantReply (Space := Space) (Letter := Letter) (Generation := Generation)
      (Principal := Principal) (Realm := Realm) (Right := Right) (Epoch := Epoch) (Revision := Revision)) : Bool :=
  match reply.2 with
  | [(stamp, .anchor issuer realm rights)] =>
      decide (stamp.1 = profile.anchor grant.issuer grant.realm ∧ issuer = grant.issuer ∧
        realm = grant.realm ∧ grant.rights ⊆ rights)
  | _ => false

variable (profile : Profile Space Letter Generation Principal Realm)
  (store : GrantScope (Space := Space) (Letter := Letter) →
    GrantReply (Space := Space) (Letter := Letter) (Generation := Generation)
      (Principal := Principal) (Realm := Realm) (Right := Right) (Epoch := Epoch) (Revision := Revision))

def currentGrant (reference : Reference Space Letter Generation) :=
  decodeGrant reference (store (keyScope reference))

def currentRoot (grant : Grant Space Letter Generation Principal Realm Right) : Bool :=
  let slot := profile.anchor grant.issuer grant.realm
  rootAllowed profile grant (store (.key slot.1 slot.2))

/-- Independent finite authorization evidence. The height counts grants, not
query inspections. A repeated issued reference cannot occur on this lineage. -/
inductive AuthorizedChain : List (Reference Space Letter Generation) →
    Demand Space Letter Generation Principal Realm Right → Nat → Prop where
  | root {seen demand grant}
      (fresh : demand.reference ∉ seen)
      (found : currentGrant store demand.reference = some grant)
      (eligible : Eligible demand grant)
      (clear : (store (profile.revocations demand.reference)).2 = [])
      (root : grant.parent = none)
      (trusted : currentRoot profile store grant = true) :
      AuthorizedChain seen demand 1
  | parent {seen demand grant reference height}
      (fresh : demand.reference ∉ seen)
      (found : currentGrant store demand.reference = some grant)
      (eligible : Eligible demand grant)
      (clear : (store (profile.revocations demand.reference)).2 = [])
      (linked : grant.parent = some reference)
      (ancestor : AuthorizedChain (demand.reference :: seen) (parentDemand grant reference) height) :
      AuthorizedChain seen demand (height + 1)

theorem AuthorizedChain.height_pos {seen demand height}
    (chain : AuthorizedChain profile store seen demand height) : 0 < height := by
  cases chain <;> omega

omit store in
/-- Construction depth limits the generated finite query. Cursor resumption
has its own allowance and retains every performed read in the common protocol. -/
def query : Nat → List (Reference Space Letter Generation) →
    Demand Space Letter Generation Principal Realm Right →
    Program (GrantScope (Space := Space) (Letter := Letter))
      (GrantReply (Space := Space) (Letter := Letter) (Generation := Generation)
        (Principal := Principal) (Realm := Realm) (Right := Right) (Epoch := Epoch) (Revision := Revision)) Decision
  | 0, _, _ => .pure .incomplete
  | depth + 1, seen, demand =>
      if demand.reference ∈ seen then .pure (.denied .cycle) else
        .read (keyScope demand.reference) fun reply => match decodeGrant demand.reference reply with
        | none => .pure (.denied .missingGrant)
        | some grant =>
            if Eligible demand grant then .read (profile.revocations demand.reference) fun revocations =>
              if revocations.2.isEmpty then
                match grant.parent with
                | some reference => query depth (demand.reference :: seen) (parentDemand grant reference)
                | none =>
                    let slot := profile.anchor grant.issuer grant.realm
                    .read (.key slot.1 slot.2) fun root =>
                      .pure (if rootAllowed profile grant root then .allowed else .denied .missingRoot)
              else .pure (.denied .revoked)
            else .pure (.denied .attenuation)

theorem query_sound (depth : Nat) (seen : List (Reference Space Letter Generation))
    (demand : Demand Space Letter Generation Principal Realm Right)
    (accepted : (run store (query profile depth seen demand)).answer = .allowed) :
    ∃ height, height ≤ depth ∧ AuthorizedChain profile store seen demand height := by
  induction depth generalizing seen demand with
  | zero => simp [query, run] at accepted
  | succ depth ih =>
      by_cases fresh : demand.reference ∈ seen
      · simp [query, fresh, run] at accepted
      · cases found : currentGrant store demand.reference with
        | none =>
          unfold currentGrant at found
          simp [query, fresh, run, found] at accepted
        | some grant =>
          have found' := found
          unfold currentGrant at found'
          by_cases eligible : Eligible demand grant
          · by_cases clear : (store (profile.revocations demand.reference)).2 = []
            · cases linked : grant.parent with
              | none =>
                have trusted : currentRoot profile store grant = true := by
                  simpa [query, fresh, run, found', eligible, clear, linked, currentRoot] using accepted
                exact ⟨1, by omega, .root fresh found eligible clear linked trusted⟩
              | some reference =>
                have child : (run store (query profile depth (demand.reference :: seen)
                    (parentDemand grant reference))).answer = .allowed := by
                  simpa [query, fresh, run, found', eligible, clear, linked] using accepted
                obtain ⟨height, bound, ancestor⟩ := ih _ _ child
                exact ⟨height + 1, by omega, .parent fresh found eligible clear linked ancestor⟩
            · simp [query, fresh, run, found', eligible, clear] at accepted
          · simp [query, fresh, run, found', eligible] at accepted

theorem query_complete {seen demand height}
    (chain : AuthorizedChain profile store seen demand height) (depth : Nat) (enough : height ≤ depth) :
    (run store (query profile depth seen demand)).answer = .allowed := by
  induction chain generalizing depth with
  | root fresh found eligible clear linked trusted =>
      cases depth with
      | zero => omega
      | succ depth =>
          unfold currentGrant at found
          simpa [query, fresh, run, found, eligible, clear, linked, currentRoot] using trusted
  | parent fresh found eligible clear linked ancestor ih =>
      cases depth with
      | zero => omega
      | succ depth =>
          unfold currentGrant at found
          simpa [query, fresh, run, found, eligible, clear, linked] using ih depth (by omega)

theorem query_allowed_iff (depth : Nat) (seen : List (Reference Space Letter Generation))
    (demand : Demand Space Letter Generation Principal Realm Right) :
    (run store (query profile depth seen demand)).answer = .allowed ↔
      ∃ height, height ≤ depth ∧ AuthorizedChain profile store seen demand height :=
  ⟨query_sound profile store depth seen demand, fun ⟨_, enough, chain⟩ => query_complete profile store chain depth enough⟩

theorem authorized_eventually_decides {seen demand height}
    (chain : AuthorizedChain profile store seen demand height) :
    ∃ depth, (run store (query profile depth seen demand)).answer = .allowed :=
  ⟨height, query_complete profile store chain height (Nat.le_refl _)⟩

theorem cycle_is_denied (depth : Nat) (seen : List (Reference Space Letter Generation))
    (demand : Demand Space Letter Generation Principal Realm Right) (cycled : demand.reference ∈ seen) :
    run store (query profile (depth + 1) seen demand) = ⟨.denied .cycle, []⟩ := by
  simp [query, cycled, run]

theorem cycle_has_no_authorized_chain (seen : List (Reference Space Letter Generation))
    (demand : Demand Space Letter Generation Principal Realm Right) (cycled : demand.reference ∈ seen)
    (height : Nat) : ¬ AuthorizedChain profile store seen demand height := by
  intro chain
  cases chain with
  | root fresh => exact fresh cycled
  | parent fresh => exact fresh cycled

theorem zero_depth_is_incomplete (seen : List (Reference Space Letter Generation))
    (demand : Demand Space Letter Generation Principal Realm Right) :
    run store (query profile 0 seen demand) = ⟨.incomplete, []⟩ := rfl

theorem cursor_split (depth first second : Nat) (seen : List (Reference Space Letter Generation))
    (demand : Demand Space Letter Generation Principal Realm Right) :
    advance (provider store) client (readCharge store) (base := PUnit.unit) (first + second)
        ⟨PUnit.unit, query profile depth seen demand, []⟩ =
      Cursor.resume (provider store) client (readCharge store) (base := PUnit.unit) second
        (advance (provider store) client (readCharge store) (base := PUnit.unit) first
          ⟨PUnit.unit, query profile depth seen demand, []⟩) :=
  advance_split store first second _ []

theorem cursor_eventually_returns (depth : Nat) (seen : List (Reference Space Letter Generation))
    (demand : Demand Space Letter Generation Principal Realm Right) :
    completed? store (advance (provider store) client (readCharge store) (base := PUnit.unit)
      ((run store (query profile depth seen demand)).reads.length + 1)
        ⟨PUnit.unit, query profile depth seen demand, []⟩).2 =
      some (run store (query profile depth seen demand)) := by
  rw [advance_complete]
  simp [completed?]

theorem query_records_selected_key (depth : Nat) (seen : List (Reference Space Letter Generation))
    (demand : Demand Space Letter Generation Principal Realm Right) (fresh : demand.reference ∉ seen) :
    ∃ rest, (run store (query profile (depth + 1) seen demand)).reads =
      (keyScope demand.reference, store (keyScope demand.reference)) :: rest := by
  simp only [query, if_neg fresh, run]
  exact ⟨_, rfl⟩

theorem missing_grant_records_negative (depth : Nat) (seen : List (Reference Space Letter Generation))
    (demand : Demand Space Letter Generation Principal Realm Right) (fresh : demand.reference ∉ seen)
    (missing : currentGrant store demand.reference = none) :
    run store (query profile (depth + 1) seen demand) =
      ⟨.denied .missingGrant, [(keyScope demand.reference, store (keyScope demand.reference))]⟩ := by
  unfold currentGrant at missing
  simp [query, fresh, run, missing]

theorem parent_preserves_complete_reads (depth : Nat) (seen : List (Reference Space Letter Generation))
    (demand : Demand Space Letter Generation Principal Realm Right)
    (grant : Grant Space Letter Generation Principal Realm Right) (reference : Reference Space Letter Generation)
    (fresh : demand.reference ∉ seen) (found : currentGrant store demand.reference = some grant)
    (eligible : Eligible demand grant) (clear : (store (profile.revocations demand.reference)).2 = [])
    (linked : grant.parent = some reference) :
    run store (query profile (depth + 1) seen demand) =
      let ancestor := run store (query profile depth (demand.reference :: seen) (parentDemand grant reference))
      ⟨ancestor.answer,
        [(keyScope demand.reference, store (keyScope demand.reference)),
          (profile.revocations demand.reference, store (profile.revocations demand.reference))] ++ ancestor.reads⟩ := by
  unfold currentGrant at found
  simp [query, fresh, run, found, eligible, clear, linked]

theorem root_records_trust_and_absence (depth : Nat) (seen : List (Reference Space Letter Generation))
    (demand : Demand Space Letter Generation Principal Realm Right)
    (grant : Grant Space Letter Generation Principal Realm Right)
    (fresh : demand.reference ∉ seen) (found : currentGrant store demand.reference = some grant)
    (eligible : Eligible demand grant) (clear : (store (profile.revocations demand.reference)).2 = [])
    (root : grant.parent = none) :
    (run store (query profile (depth + 1) seen demand)).reads =
      [(keyScope demand.reference, store (keyScope demand.reference)),
        (profile.revocations demand.reference, store (profile.revocations demand.reference)),
        (.key (profile.anchor grant.issuer grant.realm).1 (profile.anchor grant.issuer grant.realm).2,
          store (.key (profile.anchor grant.issuer grant.realm).1 (profile.anchor grant.issuer grant.realm).2))] := by
  unfold currentGrant at found
  simp [query, fresh, run, found, eligible, clear, root]

/-- A completed decision is stable under greater construction depth. This
compares two fresh query meanings; it does not resume a depth frontier. -/
theorem decided_depth_stable (depth extra : Nat) (seen : List (Reference Space Letter Generation))
    (demand : Demand Space Letter Generation Principal Realm Right)
    (decided : (run store (query profile depth seen demand)).answer ≠ .incomplete) :
    run store (query profile (depth + extra) seen demand) = run store (query profile depth seen demand) := by
  induction depth generalizing seen demand with
  | zero => simp [query, run] at decided
  | succ depth ih =>
      by_cases fresh : demand.reference ∈ seen
      · simp [query, Nat.succ_add, fresh, run]
      · cases found : currentGrant store demand.reference with
        | none =>
          unfold currentGrant at found
          simp [query, Nat.succ_add, fresh, run, found]
        | some grant =>
          have rawFound := found
          unfold currentGrant at rawFound
          by_cases eligible : Eligible demand grant
          · by_cases clear : (store (profile.revocations demand.reference)).2 = []
            · cases linked : grant.parent with
              | none => simp [query, Nat.succ_add, fresh, run, rawFound, eligible, clear, linked]
              | some reference =>
                have childDecided : (run store (query profile depth (demand.reference :: seen)
                    (parentDemand grant reference))).answer ≠ .incomplete := by
                  simpa [query, fresh, run, rawFound, eligible, clear, linked] using decided
                rw [Nat.succ_add]
                rw [parent_preserves_complete_reads profile store (depth + extra) seen demand grant reference
                  fresh found eligible clear linked,
                  parent_preserves_complete_reads profile store depth seen demand grant reference
                    fresh found eligible clear linked,
                  ih _ _ childDecided]
            · simp [query, Nat.succ_add, fresh, run, rawFound, eligible, clear]
          · simp [query, Nat.succ_add, fresh, run, rawFound, eligible]

theorem denied_has_no_authorized_chain (depth : Nat) (seen : List (Reference Space Letter Generation))
    (demand : Demand Space Letter Generation Principal Realm Right) (reason : Denial)
    (denied : (run store (query profile depth seen demand)).answer = .denied reason) (height : Nat) :
    ¬ AuthorizedChain profile store seen demand height := by
  intro chain
  have accepted := query_complete profile store chain (depth + height) (by omega)
  have same := congrArg Observation.answer (decided_depth_stable profile store depth height seen demand
    (by rw [denied]; simp))
  rw [accepted, denied] at same
  cases same

/-- A bound on actual provider reads, including failed grant/root lookups.
It does not price lookup scans, continuation guards or metadata validation. -/
theorem query_read_bound (depth : Nat) (seen : List (Reference Space Letter Generation))
    (demand : Demand Space Letter Generation Principal Realm Right) :
    (run store (query profile depth seen demand)).reads.length ≤ 2 * depth + 1 := by
  induction depth generalizing seen demand with
  | zero => simp [query, run]
  | succ depth ih =>
      by_cases fresh : demand.reference ∈ seen
      · simp [query, fresh, run]
      · cases found : currentGrant store demand.reference with
        | none =>
          rw [missing_grant_records_negative profile store depth seen demand fresh found]
          simp
        | some grant =>
          unfold currentGrant at found
          by_cases eligible : Eligible demand grant
          · by_cases clear : (store (profile.revocations demand.reference)).2 = []
            · cases linked : grant.parent with
              | none => simp [query, fresh, run, found, eligible, clear, linked]
              | some reference =>
                have smaller := ih (demand.reference :: seen) (parentDemand grant reference)
                simp [query, fresh, run, found, eligible, clear, linked]
                omega
            · simp [query, fresh, run, found, eligible, clear]
              omega
          · simp [query, fresh, run, found, eligible]

variable {SourceGeneration : Type}
  (contents : Epoch → ScopedRecords.Stamp Space Letter Revision →
    Record Space Letter Generation Principal Realm Right)

theorem unrelated_append_preserves_decision
    (source : ScopedRecords.Source Epoch SourceGeneration Space Letter Revision)
    (nextGeneration : SourceGeneration) (added : List (ScopedRecords.Stamp Space Letter Revision))
    (depth : Nat) (seen : List (Reference Space Letter Generation))
    (demand : Demand Space Letter Generation Principal Realm Right)
    (outside : ∀ read ∈ (run (ScopedRecords.observe contents source) (query profile depth seen demand)).reads,
      ∀ stamp ∈ added, ScopedRecords.accepts read.1 stamp = false) :
    run (ScopedRecords.observe contents (source.replaceRevision nextGeneration (source.entries ++ added)))
        (query profile depth seen demand) =
      run (ScopedRecords.observe contents source) (query profile depth seen demand) := by
  apply Mettapedia.Machines.ReadOnlyQuery.run_eq_of_agrees
  intro read member
  rw [ScopedRecords.nonmatching_append contents source nextGeneration added read.1 (outside read member)]
  exact Mettapedia.Machines.ReadOnlyQuery.run_agrees _ _ read member

variable [DecidableEq Epoch] [DecidableEq Revision]

theorem completed_metadata_preserves_decision
    (captured current : ScopedRecords.Source Epoch SourceGeneration Space Letter Revision)
    (depth before : Nat) (seen : List (Reference Space Letter Generation))
    (demand : Demand Space Letter Generation Principal Realm Right)
    (observation : Observation (GrantScope (Space := Space) (Letter := Letter))
      (GrantReply (Space := Space) (Letter := Letter) (Generation := Generation)
        (Principal := Principal) (Realm := Realm) (Right := Right) (Epoch := Epoch) (Revision := Revision)) Decision)
    (finished : completed? (ScopedRecords.observe contents captured)
      (advance (provider (ScopedRecords.observe contents captured)) client
        (readCharge (ScopedRecords.observe contents captured)) before
        ⟨PUnit.unit, query profile depth seen demand, []⟩).2 = some observation)
    (valid : ScopedRecords.validate current ⟨captured.storeId, observation.reads⟩ = true) :
    run (ScopedRecords.observe contents current) (query profile depth seen demand) = observation := by
  classical
  have origin := completed_correct (ScopedRecords.observe contents captured) before _ observation finished
  have authentic : Agrees (ScopedRecords.observe contents captured) observation.reads :=
    origin ▸ Mettapedia.Machines.ReadOnlyQuery.run_agrees _ _
  have agreement := (ScopedRecords.validate_exact contents captured current
    ⟨captured.storeId, observation.reads⟩ authentic).mp valid
  exact validated_completion (ScopedRecords.observe contents captured) (ScopedRecords.observe contents current)
    before _ observation finished ((Mettapedia.Machines.ReadOnlyQuery.checkReads_iff _ _).mpr agreement.2)

abbrev Held (SourceGeneration : Type) := Σ captured : ScopedRecords.Source Epoch SourceGeneration Space Letter Revision,
  Nat × Result (Answer := Decision) (ScopedRecords.observe contents captured)

def manifest (saved : Held contents SourceGeneration) : ScopedRecords.Captured Epoch Space Letter Revision
    (Record Space Letter Generation Principal Realm Right) :=
  ⟨saved.1.storeId, recorded (ScopedRecords.observe contents saved.1) saved.2.2⟩

/-- A zero allowance performs no validation. A changed positive entrance
retains the exact original source, paid amount, reads and selected residual. -/
def resumeCurrent (current : ScopedRecords.Source Epoch SourceGeneration Space Letter Revision)
    (allowance : Nat) (saved : Held contents SourceGeneration) : Except (Held contents SourceGeneration) (Held contents SourceGeneration) :=
  if allowance = 0 then .ok saved else
    if ScopedRecords.validate current (manifest contents saved) then
      .ok ⟨current, Cursor.resume (provider (ScopedRecords.observe contents current)) client
        (readCharge (ScopedRecords.observe contents current)) allowance
        (rebase (ScopedRecords.observe contents saved.1) (ScopedRecords.observe contents current) saved.2)⟩
    else .error saved

omit [DecidableEq Generation] [DecidableEq Principal] [DecidableEq Realm] [DecidableEq Right] in
theorem resumeCurrent_zero (current : ScopedRecords.Source Epoch SourceGeneration Space Letter Revision)
    (saved : Held contents SourceGeneration) : resumeCurrent contents current 0 saved = .ok saved := by
  simp [resumeCurrent]

omit [DecidableEq Generation] [DecidableEq Principal] [DecidableEq Realm] [DecidableEq Right] in
theorem resumeCurrent_refused (current : ScopedRecords.Source Epoch SourceGeneration Space Letter Revision)
    (allowance : Nat) (saved : Held contents SourceGeneration) (positive : allowance ≠ 0)
    (changed : ScopedRecords.validate current (manifest contents saved) = false) :
    resumeCurrent contents current allowance saved = .error saved := by
  simp [resumeCurrent, positive, changed]

theorem resumeCurrent_exact
    (captured current : ScopedRecords.Source Epoch SourceGeneration Space Letter Revision)
    (depth before after : Nat) (seen : List (Reference Space Letter Generation))
    (demand : Demand Space Letter Generation Principal Realm Right) (positive : after ≠ 0)
    (valid : ScopedRecords.validate current
      (manifest contents ⟨captured, advance (provider (ScopedRecords.observe contents captured)) client
        (readCharge (ScopedRecords.observe contents captured)) before
          ⟨PUnit.unit, query profile depth seen demand, []⟩⟩) = true) :
    resumeCurrent contents current after
      ⟨captured, advance (provider (ScopedRecords.observe contents captured)) client
        (readCharge (ScopedRecords.observe contents captured)) before
          ⟨PUnit.unit, query profile depth seen demand, []⟩⟩ =
      .ok ⟨current, advance (provider (ScopedRecords.observe contents current)) client
        (readCharge (ScopedRecords.observe contents current)) (before + after)
          ⟨PUnit.unit, query profile depth seen demand, []⟩⟩ := by
  classical
  have agrees := recorded_agrees (ScopedRecords.observe contents captured) before
    (query profile depth seen demand)
  have checked := (ScopedRecords.validate_exact contents captured current _ agrees).mp valid
  have exactResume := validated_revision_resume (ScopedRecords.observe contents captured)
    (ScopedRecords.observe contents current) before after (query profile depth seen demand) [] checked.2
  simp only [resumeCurrent, positive, ↓reduceIte, valid]
  exact congrArg (fun cut => Except.ok (⟨current, cut⟩ : Held contents SourceGeneration)) exactResume

inductive BeginFailure where
  | unfinished | depth | changed
  | denied (reason : Denial)
  deriving DecidableEq, Repr

section Publication

variable {Cell Scope Value Reply Metadata Epoch : Type}
  (observe : World Cell Value Metadata → Scope → Reply)
  (sourceId : World Cell Value Metadata → Epoch)
  [DecidableEq Epoch] [DecidableEq Reply]

/-- Only a completed positive decision enters the existing policy/plan
validator. Negative decisions and resource frontiers retain their actual cut. -/
def beginAllowed (policyWorld planWorld : World Cell Value Metadata)
    (previous : Nat × Result (Answer := Decision) (observe policyWorld))
    (plan : Code Cell Scope Value Reply Metadata) :
    Except (BeginFailure × (Nat × Result (Answer := Decision) (observe policyWorld))) (Saved observe Epoch) :=
  match completed? (observe policyWorld) previous.2 with
  | none => .error (.unfinished, previous)
  | some decision => match decision.answer with
      | .incomplete => .error (.depth, previous)
      | .denied reason => .error (.denied reason, previous)
      | .allowed => match PolicyPlan.begin observe sourceId policyWorld planWorld previous (fun _ => plan) with
          | none => .error (.changed, previous)
          | some saved => .ok saved

theorem beginAllowed_admitted (policyWorld planWorld : World Cell Value Metadata)
    (previous : Nat × Result (Answer := Decision) (observe policyWorld))
    (plan : Code Cell Scope Value Reply Metadata) (saved : Saved observe Epoch)
    (issued : beginAllowed observe sourceId policyWorld planWorld previous plan = .ok saved) :
    ∃ decision, completed? (observe policyWorld) previous.2 = some decision ∧ decision.answer = .allowed ∧
      PolicyPlan.begin observe sourceId policyWorld planWorld previous (fun _ => plan) = some saved := by
  unfold beginAllowed at issued
  cases complete : completed? (observe policyWorld) previous.2 with
  | none => simp [complete] at issued
  | some decision =>
      simp only [complete] at issued
      cases value : decision.answer with
      | incomplete => simp [value] at issued
      | denied reason => simp [value] at issued
      | allowed =>
          simp only [value] at issued
          cases began : PolicyPlan.begin observe sourceId policyWorld planWorld previous (fun _ => plan) with
          | none => simp [began] at issued
          | some actual =>
              have same : actual = saved := by simpa [began] using issued
              cases same
              exact ⟨decision, rfl, value, rfl⟩

theorem accepted_publication_is_fresh [DecidableEq Cell]
    (inventory : List Cell) (spare before allowance : Nat)
    (policyWorld planWorld current next : World Cell Value Metadata)
    (policyCode : Program Scope Reply Decision) (plan : Code Cell Scope Value Reply Metadata)
    (saved : Saved observe Epoch)
    (issued : beginAllowed observe sourceId policyWorld planWorld
      (advance (provider (observe policyWorld)) client (readCharge (observe policyWorld))
        before ⟨PUnit.unit, policyCode, []⟩) plan = .ok saved)
    (accepted : PolicyPlan.commit observe sourceId inventory spare current
      (PolicyPlan.resume observe allowance saved) = .ok next) :
    (run (observe current) policyCode).answer = .allowed ∧ next = ManifestPlan.fresh observe current plan := by
  obtain ⟨decision, complete, allowed, began⟩ :=
    beginAllowed_admitted observe sourceId policyWorld planWorld _ plan saved issued
  obtain ⟨actual, actualComplete, _, _, exactSaved⟩ :=
    PolicyPlan.begin_admitted observe sourceId policyWorld planWorld _ (fun _ => plan) saved began
  have same : actual = decision := Option.some.inj (actualComplete.symm.trans complete)
  subst actual
  obtain ⟨_, valid, _⟩ := PolicyPlan.commit_admitted observe sourceId inventory spare current next _ accepted
  have validDecision : checkReads (observe current) decision.reads = true := by
    simpa only [exactSaved, PolicyPlan.resume] using valid
  have freshDecision := validated_completion (observe policyWorld) (observe current) before policyCode
    decision complete validDecision
  have freshPlan := PolicyPlan.issued_commit_is_fresh observe sourceId inventory spare before allowance
    policyWorld planWorld current next policyCode (fun _ => plan) saved began accepted
  refine ⟨by rw [freshDecision]; exact allowed, ?_⟩
  simpa [ManifestPlan.fresh, Mettapedia.Machines.ReadOnlyQuery.run_bind] using freshPlan

end Publication

/-- The generated grant validator, not an arbitrary supplied positive flag,
selects the real plan. Acceptance derives a chain in the current scoped source
and the independently interpreted plan at that same publication world. -/
theorem accepted_delegation_is_fresh {Cell Value Metadata : Type} [DecidableEq Cell]
    [DecidableEq (Record Space Letter Generation Principal Realm Right)]
    (readSource : World Cell Value Metadata → ScopedRecords.Source Epoch SourceGeneration Space Letter Revision)
    (inventory : List Cell) (spare depth before allowance : Nat)
    (policyWorld planWorld current next : World Cell Value Metadata)
    (demand : Demand Space Letter Generation Principal Realm Right)
    (plan : Code Cell (GrantScope (Space := Space) (Letter := Letter)) Value
      (GrantReply (Space := Space) (Letter := Letter) (Generation := Generation)
        (Principal := Principal) (Realm := Realm) (Right := Right) (Epoch := Epoch) (Revision := Revision)) Metadata)
    (saved : Saved (fun world => ScopedRecords.observe contents (readSource world)) Epoch)
    (issued : beginAllowed (fun world => ScopedRecords.observe contents (readSource world))
      (fun world => (readSource world).storeId) policyWorld planWorld
      (advance (provider (ScopedRecords.observe contents (readSource policyWorld))) client
        (readCharge (ScopedRecords.observe contents (readSource policyWorld))) before
        ⟨PUnit.unit, query profile depth [] demand, []⟩) plan = .ok saved)
    (accepted : PolicyPlan.commit (fun world => ScopedRecords.observe contents (readSource world))
      (fun world => (readSource world).storeId) inventory spare current
      (PolicyPlan.resume (fun world => ScopedRecords.observe contents (readSource world)) allowance saved) = .ok next) :
    (∃ height, height ≤ depth ∧ AuthorizedChain profile (ScopedRecords.observe contents (readSource current))
      [] demand height) ∧
      next = ManifestPlan.fresh (fun world => ScopedRecords.observe contents (readSource world)) current plan := by
  obtain ⟨allowed, fresh⟩ := accepted_publication_is_fresh
    (fun world => ScopedRecords.observe contents (readSource world)) (fun world => (readSource world).storeId)
    inventory spare before allowance policyWorld planWorld current next (query profile depth [] demand) plan
    saved issued accepted
  exact ⟨query_sound profile _ depth [] demand allowed, fresh⟩

namespace Controls

omit [DecidableEq Space] [DecidableEq Letter] [DecidableEq Generation]
  [DecidableEq Principal] [DecidableEq Realm] [DecidableEq Right]
  [DecidableEq Epoch] [DecidableEq Revision]

abbrev Ref := Reference Nat Nat Nat
abbrev Row := Record Nat Nat Nat Nat Nat Nat
abbrev Rows := ScopedRecords.Source Nat Nat Nat Nat Nat
abbrev CScope := ScopedRecords.Scope Nat Nat
abbrev CReply := ScopedRecords.FullReply Nat Nat Nat Nat Row
abbrev CGrant := Grant Nat Nat Nat Nat Nat Nat

def leaf : Ref := ⟨(0, [10]), 101⟩
def parent : Ref := ⟨(0, [11]), 102⟩
def root : Ref := ⟨(0, [12]), 103⟩
def policy : Profile Nat Nat Nat Nat Nat :=
  ⟨fun reference => .prefix 1 reference.slot.2, fun issuer _ => (2, [issuer])⟩
def demand : Demand Nat Nat Nat Nat Nat Nat := ⟨leaf, 30, 7, {1}, false⟩

/-- Reissuing identical rights at revision two uses a new authorization
generation. Revision three intentionally violates that issuance discipline. -/
def materialize (_epoch : Nat) (stamp : ScopedRecords.Stamp Nat Nat Nat) : Row :=
  if stamp.1 = leaf.slot then .grant ⟨if stamp.2 = 2 then 201 else 101,
    20, 30, 7, {1}, false, some parent⟩
  else if stamp.1 = parent.slot then .grant ⟨if stamp.2 = 2 then 202 else 102,
    10, 20, 7, if stamp.2 = 4 then {2} else {1, 2}, stamp.2 != 3, some root⟩
  else if stamp.1 = root.slot then .grant ⟨103, 0, 10, 7, {1, 2}, true,
    if stamp.2 = 2 then some leaf else none⟩
  else if stamp.1 = (2, [0]) then .anchor 0 7 {1, 2}
  else .denial

def initial : Rows := ⟨17, 5, [(leaf.slot, 1), (parent.slot, 1), (root.slot, 1), ((2, [0]), 1)]⟩
def replace (slot : ScopedRecords.Key Nat Nat) (revision : Nat) : Rows :=
  ⟨17, 6, initial.entries.map fun stamp => if stamp.1 = slot then (slot, revision) else stamp⟩
def missing (slot : ScopedRecords.Key Nat Nat) : Rows :=
  ⟨17, 6, initial.entries.filter fun stamp => stamp.1 != slot⟩
def revoked : Rows := ⟨17, 6, initial.entries ++ [((1, [12, 0]), 1)]⟩
def unrelated : Rows := ⟨17, 6, initial.entries ++ [((0, [99]), 1), ((3, [7]), 1)]⟩
def duplicate : Rows := ⟨17, 6, initial.entries ++ [(leaf.slot, 1)]⟩
def duplicateAnchor : Rows := ⟨17, 6, initial.entries ++ [((2, [0]), 1)]⟩
def observed (current : Rows) : CScope → CReply := ScopedRecords.observe materialize current
def program (depth : Nat) := query (Epoch := Nat) (Revision := Nat) policy depth [] demand
def decision (current : Rows) (depth : Nat) := (run (observed current) (program depth)).answer
def cut (current : Rows) (depth allowance : Nat) : Nat × Result (Answer := Decision) (observed current) :=
  advance (provider (observed current)) client (readCharge (observed current)) allowance
    ⟨PUnit.unit, program depth, []⟩
def held (current : Rows) (depth allowance : Nat) : Held materialize Nat := ⟨current, cut current depth allowance⟩
def required := manifest materialize (held initial 3 8)

theorem three_hops_check_real_ancestors_and_root :
    decision initial 3 = .allowed ∧ (cut initial 3 8).1 = 7 ∧
      required.reads.map Prod.fst =
        [.key 0 [10], .prefix 1 [10], .key 0 [11], .prefix 1 [11],
          .key 0 [12], .prefix 1 [12], .key 2 [0]] ∧
      ScopedRecords.validate unrelated required = true := by decide

theorem malformed_missing_and_cyclic_lineages_refuse :
    decision (missing parent.slot) 3 = .denied .missingGrant ∧
      decision (missing (2, [0])) 3 = .denied .missingRoot ∧
      decision duplicate 3 = .denied .missingGrant ∧
      decision duplicateAnchor 3 = .denied .missingRoot ∧
      decision (replace root.slot 2) 4 = .denied .cycle := by decide

theorem identities_realms_and_attenuation_are_checked :
    (run (observed initial) (query policy 3 [] {demand with principal := 31})).answer = .denied .attenuation ∧
      (run (observed initial) (query policy 3 [] {demand with realm := 8})).answer = .denied .attenuation ∧
      (run (observed initial) (query policy 3 [] {demand with rights := {1, 99}})).answer = .denied .attenuation ∧
      decision (replace parent.slot 3) 3 = .denied .attenuation ∧
      decision (replace parent.slot 4) 3 = .denied .attenuation := by decide

theorem fresh_generation_does_not_revive_copied_references :
    decision (replace leaf.slot 2) 3 = .denied .missingGrant ∧
      decision (replace parent.slot 2) 3 = .denied .missingGrant ∧
      ScopedRecords.validate (replace leaf.slot 2) required = false ∧
      ScopedRecords.validate (replace parent.slot 2) required = false ∧
      (run (observed (replace leaf.slot 2))
        (query policy 3 [] {demand with reference := {leaf with generation := 201}})).answer = .allowed := by
  decide

theorem reused_authorization_generation_requires_an_issuance_contract :
    materialize 17 (leaf.slot, 3) = materialize 17 (leaf.slot, 1) ∧
      decision (replace leaf.slot 3) 3 = .allowed ∧
      ScopedRecords.validate (replace leaf.slot 3) required = false := by decide

theorem recorded_ancestor_revocation_retains_the_exact_cut :
    resumeCurrent materialize revoked 3 (held initial 3 6) = .error (held initial 3 6) :=
  resumeCurrent_refused materialize revoked 3 (held initial 3 6) (by decide) (by decide)

theorem zero_does_not_inspect_revoked_metadata :
    resumeCurrent materialize revoked 0 (held initial 3 6) = .ok (held initial 3 6) := rfl

theorem fixed_query_resume_keeps_paid_prefix :
    resumeCurrent materialize unrelated 6 (held initial 3 2) = .ok (held unrelated 3 8) := by
  exact resumeCurrent_exact policy materialize initial unrelated 3 2 6 [] demand (by decide) (by decide)

def resumedDecision (result : Except (Held materialize Nat) (Held materialize Nat)) : Option (Nat × Option Decision) :=
  match result with
  | .error _ => none
  | .ok saved => some (saved.2.1, (completed? (observed saved.1) saved.2.2).map Observation.answer)

theorem unread_revocation_is_checked_when_reached :
    resumedDecision (resumeCurrent materialize revoked 5 (held initial 3 2)) =
      some (6, some (.denied .revoked)) := by decide

theorem construction_frontier_is_not_a_denial_or_a_resumable_depth_extension :
    decision initial 1 = .incomplete ∧
      resumedDecision (resumeCurrent materialize initial 100 (held initial 1 3)) =
        some (2, some .incomplete) ∧
      decision initial 3 = .allowed := by decide

theorem completed_policy_is_rechecked_before_delivery :
    resumeCurrent materialize revoked 1 (held initial 3 8) = .error (held initial 3 8) :=
  resumeCurrent_refused materialize revoked 1 (held initial 3 8) (by decide) (by decide)

abbrev CCell := Sum Unit Nat
abbrev CValue := Sum Rows Nat
abbrev CWorld := World CCell CValue Unit

def source (current : CWorld) : Rows :=
  match current.get (.inl ()) with
  | some (.inl rows) => rows
  | _ => ⟨0, 0, []⟩
def world (rows : Rows) : CWorld :=
  ⟨fun cell => match cell with | .inl _ => some (.inl rows) | .inr _ => none, ()⟩
def worldObserve (current : CWorld) : CScope → CReply := observed (source current)
def worldEpoch (current : CWorld) := (source current).storeId
def plan : Code CCell CScope CValue CReply Unit :=
  .read (.key 0 [10]) fun grant => .pure ⟨[(.inr 0, .inr (100 + grant.2.length))], ()⟩
def launch (depth allowance : Nat) :=
  beginAllowed worldObserve worldEpoch (world initial) (world unrelated) (cut initial depth allowance) plan
def prepared : Saved worldObserve Nat := (launch 3 8).toOption.get (by decide)
def published (current : Rows) : Except (ManifestPlan.Refusal × Saved worldObserve Nat) CWorld :=
  PolicyPlan.commit worldObserve worldEpoch [.inr 0] 0 (world current)
    (PolicyPlan.resume worldObserve 2 prepared)
def output (result : Except (ManifestPlan.Refusal × Saved worldObserve Nat) CWorld) : Option Nat :=
  match result with
  | .error _ => none
  | .ok next => match next.get (.inr 0) with | some (.inr value) => some value | _ => none
def launchFailure (depth allowance : Nat) : Option BeginFailure :=
  match launch depth allowance with | .ok _ => none | .error (reason, _) => some reason

def deniedLaunch : Option BeginFailure :=
  match beginAllowed worldObserve worldEpoch (world revoked) (world revoked) (cut revoked 3 8) plan with
  | .ok _ => none
  | .error (reason, _) => some reason

theorem actual_nonempty_plan_publishes_under_local_validation :
    output (published unrelated) = some 101 ∧ output (published initial) = some 101 ∧
      launchFailure 3 2 = some .unfinished ∧ launchFailure 1 3 = some .depth ∧
      deniedLaunch = some (.denied .revoked) := by decide

theorem changed_ancestor_and_negative_scope_refuse_publication :
    output (published revoked) = none ∧ output (published (replace parent.slot 2)) = none ∧
      output (published (missing (2, [0]))) = none ∧ output (published duplicate) = none := by decide

end Controls

end Delegation

end PolicyPlan

/-! ## Scoped occurrences, retained contexts and current force authority

These adapters use the existing scoped source, adaptive query interpreter,
cursor and Need transition. Names may move between contexts; a retained value
never acquires permission merely because its description was copied.
-/

namespace ScopedOccurrence

open Mettapedia.GSLT.Contracts
open Mettapedia.Machines

variable {Epoch Space Letter Revision Payload Answer : Type}
variable [DecidableEq Space] [DecidableEq Letter]

abbrev Source (Epoch Space Letter Revision : Type) :=
  ScopedRecords.Source Epoch Nat Space Letter Revision
abbrev Scope (Space Letter : Type) := ScopedRecords.Scope Space Letter
abbrev FullReply (Epoch Space Letter Revision Payload : Type) :=
  ScopedRecords.FullReply Epoch Space Letter Revision Payload

/-- The target really queries the transported space and normalizes only the
namespace coordinates of its reply. Payload and row multiplicity are intact. -/
def contextualStore
    (contents : Epoch → ScopedRecords.Stamp Space Letter Revision → Payload)
    (names : Space ≃ Space) (source : Source Epoch Space Letter Revision) :
    Scope Space Letter → FullReply Epoch Space Letter Revision Payload :=
  fun scope => OccurrenceSpace.normalizeReply names
    (ScopedRecords.observe (OccurrenceSpace.renamedContents contents names)
      (OccurrenceSpace.rename names source) (OccurrenceSpace.renameScope names scope))

theorem contextualStore_eq
    (contents : Epoch → ScopedRecords.Stamp Space Letter Revision → Payload)
    (names : Space ≃ Space) (source : Source Epoch Space Letter Revision) :
    contextualStore contents names source = ScopedRecords.observe contents source := by
  funext scope
  exact OccurrenceSpace.normalized_renamed_observe contents names source scope

def contextHom
    (contents : Epoch → ScopedRecords.Stamp Space Letter Revision → Payload)
    (names : Space ≃ Space) (source : Source Epoch Space Letter Revision) :
    Hom (provider (ScopedRecords.observe contents source)) (provider (contextualStore contents names source)) where
  map reads := reads
  step reads scope := by simp only [provider, contextualStore_eq]

/-- Bounded adaptive runs retain the actual reply-selected continuation,
ordered reads and paid account across the constructed context adapter. -/
theorem context_advance_account
    (contents : Epoch → ScopedRecords.Stamp Space Letter Revision → Payload)
    (names : Space ≃ Space) (source : Source Epoch Space Letter Revision) (allowance : Nat)
    (program : Program (Scope Space Letter) (FullReply Epoch Space Letter Revision Payload) Answer)
    (reads : Reads (Scope Space Letter) (FullReply Epoch Space Letter Revision Payload)) :
    Cursor.advance (provider (contextualStore contents names source)) client
      (readCharge (contextualStore contents names source)) (base := .unit) allowance ⟨.unit, program, reads⟩ =
      rebase (ScopedRecords.observe contents source) (contextualStore contents names source)
        (Cursor.advance (provider (ScopedRecords.observe contents source)) client
          (readCharge (ScopedRecords.observe contents source)) (base := .unit) allowance ⟨.unit, program, reads⟩) := by
  let hom := contextHom contents names source
  simpa only [Hom.packet, Hom.outcome, contextHom, rebase, hom] using
    (hom.advance_account client (readCharge (ScopedRecords.observe contents source))
      (readCharge (contextualStore contents names source)) (fun _ _ => rfl)
      allowance (base := .unit) ⟨.unit, program, reads⟩).symm

theorem context_resume_account
    (contents : Epoch → ScopedRecords.Stamp Space Letter Revision → Payload)
    (names : Space ≃ Space) (source : Source Epoch Space Letter Revision) (allowance : Nat)
    (saved : Nat × Result (Answer := Answer) (ScopedRecords.observe contents source)) :
    Cursor.resume (provider (contextualStore contents names source)) client
      (readCharge (contextualStore contents names source)) allowance
      (rebase (ScopedRecords.observe contents source) (contextualStore contents names source) saved) =
      rebase (ScopedRecords.observe contents source) (contextualStore contents names source)
        (Cursor.resume (provider (ScopedRecords.observe contents source)) client
          (readCharge (ScopedRecords.observe contents source)) allowance saved) := by
  let hom := contextHom contents names source
  simpa only [Hom.outcome, contextHom, rebase, hom] using
    (hom.resume_account client (readCharge (ScopedRecords.observe contents source))
      (readCharge (contextualStore contents names source)) (fun _ _ => rfl) allowance saved).symm

/-- Metadata validation of the actual performed prefix supplies the complete
reply agreement required by the existing fresh-resumption theorem. -/
theorem metadata_validated_resume
    [DecidableEq Epoch] [DecidableEq Revision] [DecidableEq Payload]
    (contents : Epoch → ScopedRecords.Stamp Space Letter Revision → Payload)
    (captured current : Source Epoch Space Letter Revision) (before after : Nat)
    (program : Program (Scope Space Letter) (FullReply Epoch Space Letter Revision Payload) Answer)
    (valid : ScopedRecords.validate current
      ⟨captured.storeId, recorded (ScopedRecords.observe contents captured)
        (Cursor.advance (provider (ScopedRecords.observe contents captured)) client
          (readCharge (ScopedRecords.observe contents captured)) before ⟨.unit, program, []⟩).2⟩ = true) :
    Cursor.resume (provider (ScopedRecords.observe contents current)) client
      (readCharge (ScopedRecords.observe contents current)) after
      (rebase (ScopedRecords.observe contents captured) (ScopedRecords.observe contents current)
        (Cursor.advance (provider (ScopedRecords.observe contents captured)) client
          (readCharge (ScopedRecords.observe contents captured)) before ⟨.unit, program, []⟩)) =
      Cursor.advance (provider (ScopedRecords.observe contents current)) client
        (readCharge (ScopedRecords.observe contents current)) (before + after) ⟨.unit, program, []⟩ := by
  apply validated_revision_resume
  exact ((ScopedRecords.validate_exact contents captured current _
    (recorded_agrees _ before program)).mp valid).2

/-- A selected observer is applied after the full adaptive observation has
been justified. It cannot turn a missing negative read into agreement. -/
theorem validated_selected_observer {View : Type}
    [DecidableEq Epoch] [DecidableEq Revision] [DecidableEq Payload]
    (contents : Epoch → ScopedRecords.Stamp Space Letter Revision → Payload)
    (captured current : Source Epoch Space Letter Revision)
    (program : Program (Scope Space Letter) (FullReply Epoch Space Letter Revision Payload) Answer)
    (observer : Observation (Scope Space Letter) (FullReply Epoch Space Letter Revision Payload) Answer → View)
    (valid : ScopedRecords.validate current
      ⟨captured.storeId, (run (ScopedRecords.observe contents captured) program).reads⟩ = true) :
    observer (run (ScopedRecords.observe contents current) program) =
      observer (run (ScopedRecords.observe contents captured) program) := by
  apply congrArg observer
  apply Mettapedia.Machines.ReadOnlyQuery.run_eq_of_agrees
  exact ((ScopedRecords.validate_exact contents captured current _
    (Mettapedia.Machines.ReadOnlyQuery.run_agrees _ program)).mp valid).2

/-- The read manifest may materialize a different immutable payload view.
Complete key/version/epoch agreement still transports the original adaptive
query, including its binding and Need fields. This is not payload erasure
without an immutable-version interpretation. -/
theorem scope_manifest_preserves_adaptive_query {Certificate : Type}
    [DecidableEq Epoch] [DecidableEq Revision] [DecidableEq Certificate]
    (contents : Epoch → ScopedRecords.Stamp Space Letter Revision → Payload)
    (certificateContents : Epoch → ScopedRecords.Stamp Space Letter Revision → Certificate)
    (captured current : Source Epoch Space Letter Revision)
    (program : Program (Scope Space Letter) (FullReply Epoch Space Letter Revision Payload) Answer)
    (valid : ScopedRecords.validate current
      (ScopedRecords.capture certificateContents captured
        ((run (ScopedRecords.observe contents captured) program).reads.map Prod.fst)) = true) :
    run (ScopedRecords.observe contents current) program =
      run (ScopedRecords.observe contents captured) program := by
  let scopes := (run (ScopedRecords.observe contents captured) program).reads.map Prod.fst
  have authentic : Agrees (ScopedRecords.observe certificateContents captured)
      (ScopedRecords.capture certificateContents captured scopes).reads :=
    (Mettapedia.Machines.ReadOnlyQuery.agrees_samples_iff _ _ _).mpr (fun _ _ => rfl)
  have checked := (ScopedRecords.validate_exact certificateContents captured current _ authentic).mp valid
  apply Mettapedia.Machines.ReadOnlyQuery.run_eq_of_agrees
  intro read member
  have keyMember : read.1 ∈ scopes := List.mem_map.mpr ⟨read, member, rfl⟩
  have sameCertificate := checked.2 (read.1, ScopedRecords.observe certificateContents captured read.1)
    (List.mem_map.mpr ⟨read.1, keyMember, rfl⟩)
  have sameMetadata : ScopedRecords.metadata current read.1 = ScopedRecords.metadata captured read.1 := by
    simpa only [ScopedRecords.observe_metadata] using congrArg ScopedRecords.eraseReply sameCertificate
  exact (ScopedRecords.metadata_preserves_full contents current captured read.1 sameMetadata).trans
    (Mettapedia.Machines.ReadOnlyQuery.run_agrees _ program read member)

/-- Current read permission is checked before the source is inspected. A
refusal is distinct from a successfully observed empty occurrence list. -/
def guardedObserve
    (contents : Epoch → ScopedRecords.Stamp Space Letter Revision → Payload)
    (held : OccurrenceSpace.Authority Space Letter Revision)
    (current : Source Epoch Space Letter Revision) (scope : Scope Space Letter) :
    Except OwnWrite.Fault (FullReply Epoch Space Letter Revision Payload) :=
  match Mettapedia.Machines.CMemory.CellPermission.read (held scope.owner) with
  | none => .error .denied
  | some _ => .ok (ScopedRecords.observe contents current scope)

theorem revoked_observation_refuses
    (contents : Epoch → ScopedRecords.Stamp Space Letter Revision → Payload)
    (current : Source Epoch Space Letter Revision) (scope : Scope Space Letter) :
    guardedObserve contents 0 current scope = .error .denied := rfl

theorem guarded_observation_issued
    (contents : Epoch → ScopedRecords.Stamp Space Letter Revision → Payload)
    (held : OccurrenceSpace.Authority Space Letter Revision)
    (current : Source Epoch Space Letter Revision) (scope : Scope Space Letter)
    (expected : List (List Letter × Revision))
    (permitted : Mettapedia.Machines.CMemory.CellPermission.read (held scope.owner) = some expected) :
    guardedObserve contents held current scope = .ok (ScopedRecords.observe contents current scope) := by
  simp only [guardedObserve, permitted]

end ScopedOccurrence

namespace RetainedForce

open Mettapedia.Machines.BranchLocalNeed.NeedReference
open Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone

variable {Epoch Holder Binding Payload : Type}
variable [DecidableEq Epoch] [DecidableEq Holder]
variable {Origin Local Resume Rule Value StableFault RetryableFault Effect : Type}

/-- Row data retains the complete binding identity and Need allocation name.
Neither field is a permission or a newly allocated producer. -/
structure Row (Binding Payload : Type) where
  binding : Binding
  need : CellId
  value : Payload
  deriving DecidableEq

abbrev BindingRef (Epoch : Type) := Epoch × Mettapedia.Languages.MeTTa.MetavariableFrameStore.Ref

/-- Resolve the original full frame reference in the supplied current image.
The existing owned read preserves valid-unbound slots and their clocks. -/
def bindingRead {Stored : Type} (lineage : Epoch)
    (allocator : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Allocator)
    (image : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.ImageOf Stored)
    (row : Row (BindingRef Epoch) Payload) :=
  if row.binding.1 = lineage then image.readSlotOwned? allocator row.binding.2 else none

omit [DecidableEq Holder] in
theorem binding_read_current {Stored : Type} (lineage : Epoch)
    (allocator : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Allocator)
    (image : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.ImageOf Stored)
    (row : Row (BindingRef Epoch) Payload) (sameLineage : row.binding.1 = lineage)
    (live : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Live allocator
      ⟨row.binding.2.handle, row.binding.2.generation⟩) :
    bindingRead lineage allocator image row = image.readSlot? row.binding.2 := by
  simp only [bindingRead, if_pos sameLineage,
    Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.ImageOf.readSlotOwned?, if_pos live]

omit [DecidableEq Holder] in
theorem binding_read_different_lineage {Stored : Type} (lineage : Epoch)
    (allocator : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.Allocator)
    (image : Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared.ImageOf Stored)
    (row : Row (BindingRef Epoch) Payload) (different : row.binding.1 ≠ lineage) :
    bindingRead lineage allocator image row = none := by
  simp only [bindingRead, if_neg different]

def handle (epoch : Epoch) (cell : CellId) : Handle Epoch CellId :=
  ⟨epoch, cell, cell.generation⟩

omit [DecidableEq Epoch] [DecidableEq Holder] in
theorem handle_injective (epoch : Epoch) : Function.Injective (handle epoch) := by
  intro first second equal
  exact congrArg Handle.resource equal

/-- One actual Need instruction, interpreted at the supplied current machine.
The shared reference transition owns caching, receipts, alternatives and work. -/
def operation
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (stack : List (Frame Resume)) (_ : Unit) (selected : Handle Epoch CellId) :
    Except Unit (List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)) :=
  .ok (step spec {machine with control := .force selected.resource stack})

def force
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (stack : List (Frame Resume))
    (frontier : Frontier Epoch CellId Holder) (holder : Holder) (epoch : Epoch)
    (row : Row Binding Payload) :
    BoundaryOutcome (Row Binding Payload)
      (List (Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)) Unit :=
  dispatch (operation spec machine stack) frontier holder (handle epoch row.need) () row

theorem force_without_current_lease
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (stack : List (Frame Resume))
    (frontier : Frontier Epoch CellId Holder) (holder : Holder) (epoch : Epoch)
    (row : Row Binding Payload)
    (denied : ¬ Authorized frontier holder (handle epoch row.need)) :
    force spec machine stack frontier holder epoch row = .inert row :=
  dispatch_eq_inert_of_not_authorized _ _ _ _ _ _ denied

theorem force_with_current_lease
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (stack : List (Frame Resume))
    (frontier : Frontier Epoch CellId Holder) (holder : Holder) (epoch : Epoch)
    (row : Row Binding Payload)
    (permitted : Authorized frontier holder (handle epoch row.need)) :
    force spec machine stack frontier holder epoch row =
      .returned (step spec {machine with control := .force row.need stack}) := by
  change authorizedB frontier holder (handle epoch row.need) = true at permitted
  unfold force dispatch
  rw [permitted]
  rfl

/-- A copied row in another holder's hands is still inert without a current
lease. The original shared cell and binding identity remain in the row. -/
theorem copying_description_does_not_force
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (stack : List (Frame Resume)) (holder : Holder) (epoch : Epoch) (row : Row Binding Payload) :
    force spec machine stack 0 holder epoch row = .inert row := by
  apply force_without_current_lease
  simp [Authorized, authorizedB]

/-- The actual share transition both retains the original lease and grants
the second holder the same complete allocation identity. -/
theorem actual_share_authorizes
    (world : World Epoch CellId Holder) (lease : Lease Epoch CellId Holder) (target : Holder)
    (present : lease ∈ world.frontier) (copyable : lease.permission = .shared) :
    Step world (.share lease target)
      ⟨{lease with holder := target} ::ₘ world.frontier, world.history ++ [.share lease target]⟩ ∧
    Authorized ({lease with holder := target} ::ₘ world.frontier) target lease.handle := by
  refine ⟨Step.share world lease target present copyable, ?_⟩
  simp [Authorized, authorizedB, copyable]

/-- Ownership does not admit the shared-copy transition. -/
theorem owned_lease_cannot_be_shared
    (world next : World Epoch CellId Holder) (lease : Lease Epoch CellId Holder) (target : Holder)
    (exclusive : lease.permission = .owned) : ¬ Step world (.share lease target) next := by
  intro attempted
  cases attempted with
  | share _ _ _ copyable => simp [exclusive] at copyable

/-- Cached delivery is the proved singleton Need step. It retains the exact
heap, charges one semantic lookup and writes no second producer cache. The
authorization/transport overhead is not priced by this semantic account. -/
theorem authorized_cached_delivery
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (stack : List (Frame Resume))
    (frontier : Frontier Epoch CellId Holder) (holder : Holder) (epoch : Epoch)
    (row : Row Binding Payload) (origin : Origin) (value : Value)
    (permitted : Authorized frontier holder (handle epoch row.need))
    (cached : machine.world.heap.lookup row.need = some ⟨origin, .value value⟩) :
    force spec machine stack frontier holder epoch row =
      .returned [finished {machine with control := .force row.need stack}
        (Mettapedia.Machines.BranchLocalNeed.NeedReference.recorded machine.world (.observe row.need (.value value)))
        (.returned (.value value) stack) 1 0 1 0] := by
  rw [force_with_current_lease spec machine stack frontier holder epoch row permitted]
  rw [Mettapedia.Machines.BranchLocalNeed.NeedCacheLaws.force_cached_value_step spec
    {machine with control := .force row.need stack} rfl cached]

/-- A retained adaptive query may select one row for a later force. Full
manifest agreement preserves that selection, while the force still uses the
current machine and current lease frontier supplied to this invocation. -/
theorem validated_query_then_current_force {Space Letter Revision Certificate : Type}
    [DecidableEq Space] [DecidableEq Letter] [DecidableEq Revision] [DecidableEq Certificate]
    (contents : Epoch → ScopedRecords.Stamp Space Letter Revision → Row Binding Payload)
    (certificateContents : Epoch → ScopedRecords.Stamp Space Letter Revision → Certificate)
    (captured current : ScopedOccurrence.Source Epoch Space Letter Revision)
    (program : Program (ScopedRecords.Scope Space Letter)
      (ScopedRecords.FullReply Epoch Space Letter Revision (Row Binding Payload)) (Option (Row Binding Payload)))
    (spec : Spec Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (machine : Machine Origin Local Resume Rule Value StableFault RetryableFault Effect)
    (stack : List (Frame Resume)) (frontier : Frontier Epoch CellId Holder) (holder : Holder)
    (valid : ScopedRecords.validate current
      (ScopedRecords.capture certificateContents captured
        ((run (ScopedRecords.observe contents captured) program).reads.map Prod.fst)) = true) :
    (run (ScopedRecords.observe contents current) program).answer.map
        (force spec machine stack frontier holder current.storeId) =
      (run (ScopedRecords.observe contents captured) program).answer.map
        (force spec machine stack frontier holder current.storeId) := by
  exact congrArg (fun result => result.answer.map (force spec machine stack frontier holder current.storeId))
    (ScopedOccurrence.scope_manifest_preserves_adaptive_query contents certificateContents captured current program valid)

end RetainedForce

namespace ScopedOccurrence.OwnClient

open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Mettapedia.GSLT.Contracts
open Mettapedia.Machines

variable {Entry World : Type} {size : Nat} [DecidableEq Entry] [Category.{0} World]
variable (authority : IndexedAuthority.{0, 0, 0} World)
  (required : OrderedDependencyStore.Action Entry size → (world : World) → authority.Fibre world)
  [∀ point : IndexedAuthority.Point authority, ∀ change : OrderedDependencyStore.Action Entry size,
    Decidable (FrameUpdate point.authority (required change point.world))]

/-- A normal programmable client of the existing stateful service. It retains
the old full reply and replaces the local list with its one-erased query view.
The own-only take interpretation requires `take_own_only` below. -/
def readEraseReplace (reader : Fin size) (selected : Entry) :
    Prog (OwnWrite.Request Entry size) OwnWrite.Reply (OrderedDependencyStore.ReadStamp size × List Entry) :=
  OwnWrite.readWrite reader (fun rows => .replace reader (rows.erase selected))

theorem read_replace_returns_captured_reply
    (state : OwnWrite.State authority Entry size) (reader : Fin size) (selected : Entry)
    (allowed : FrameUpdate state.point.authority
      (required (.replace reader ((OrderedDependencyStore.query state.store reader).erase selected)) state.point.world)) :
    OwnWrite.advance authority required 3 (readEraseReplace reader selected) state =
      (2, .done ⟨PUnit.unit,
        .ok (OrderedDependencyStore.readStamp state.store reader, OrderedDependencyStore.query state.store reader),
        {state with store := (OrderedDependencyStore.step state.store
          (.replace reader ((OrderedDependencyStore.query state.store reader).erase selected)))}⟩) :=
  OwnWrite.captured_read_own_write authority required state reader
    (fun rows => .replace reader (rows.erase selected)) allowed

/-- Imported segments must not be republished as the owner's own rows. The
own-only profile is explicit at this client boundary. -/
theorem take_own_only (state : OwnWrite.State authority Entry size) (reader : Fin size)
    (noImports : (state.store.members reader).deps = []) (selected : Entry) :
    OrderedDependencyStore.query state.store reader = (state.store.members reader).own ∧
      ((OrderedDependencyStore.step state.store
        (.replace reader ((OrderedDependencyStore.query state.store reader).erase selected))).members reader).own =
        (state.store.members reader).own.erase selected := by
  have query := OrderedDependencyStore.query_eq_view state.store reader
  simp only [OrderedDependencyStore.view, noImports, List.flatMap_nil, List.append_nil] at query
  exact ⟨query, by simp only [OrderedDependencyStore.step, OrderedDependencyStore.replaceOwn,
    OrderedDependencyStore.contentUpdate_own, query]⟩

theorem take_keeps_other_own_rows (state : OwnWrite.State authority Entry size) (reader other : Fin size)
    (different : other ≠ reader) (selected : Entry) :
    ((OrderedDependencyStore.step state.store
      (.replace reader ((OrderedDependencyStore.query state.store reader).erase selected))).members other).own =
      (state.store.members other).own :=
  OrderedDependencyStore.contentUpdate_own_other state.store different _ true

end ScopedOccurrence.OwnClient

namespace ScopedOccurrence.Controls

open Mettapedia.GSLT.Contracts
open Mettapedia.Machines
open Mettapedia.Machines.BranchLocalNeed.NeedReference

abbrev Stamp := ScopedRecords.Stamp Nat Nat Nat
abbrev Row := RetainedForce.Row (RetainedForce.BindingRef Nat) Nat
abbrev Rows := Source Nat Nat Nat Nat
abbrev QueryReply := FullReply Nat Nat Nat Nat Row

local instance : DecidableEq Row := inferInstanceAs (DecidableEq (RetainedForce.Row (RetainedForce.BindingRef Nat) Nat))
local instance : DecidableEq (Stamp × Row) := inferInstance
local instance : DecidableEq (List (Stamp × Row)) := inferInstance
local instance : DecidableEq QueryReply := inferInstance

local instance : DecidableEq (Except OwnWrite.Fault QueryReply)
  | .error firstReply, .error secondReply =>
      if same : firstReply = secondReply then isTrue (congrArg Except.error same)
      else isFalse (fun equal => same (Except.error.inj equal))
  | .ok firstReply, .ok secondReply =>
      if same : firstReply = secondReply then isTrue (congrArg Except.ok same)
      else isFalse (fun equal => same (Except.ok.inj equal))
  | .error _, .ok _ => isFalse (by intro equal; cases equal)
  | .ok _, .error _ => isFalse (by intro equal; cases equal)

def sharedCell : CellId := ⟨7, [3], 4, 2⟩
def first : Stamp := ((1, [10, 0]), 1)
def second : Stamp := ((1, [10, 1]), 1)
def child : Stamp := ((2, [20]), 1)
def newNegative : Stamp := ((2, [99]), 1)
def source : Rows := ⟨17, 4, [first, second, child]⟩

def contents (_epoch : Nat) (stamp : Stamp) : Row :=
  ⟨(17, ⟨8, 3, stamp.1.2.getLast!⟩), sharedCell,
    if stamp.1.1 = 1 then 42 else if stamp.1.2 = [99] then 99 else 20 + stamp.2⟩

def program : Program (Scope Nat Nat) QueryReply (List (Stamp × Row)) :=
  .read (.prefix 1 [10]) fun parent =>
    .read (.key 2 [99]) fun absent =>
      if absent.2.isEmpty then .read (.key 2 [20]) fun nested => .pure (parent.2 ++ nested.2)
      else .pure absent.2

def changed (stamp : Stamp) : Rows := ⟨17, 5, source.entries ++ [stamp]⟩
def unread : Rows := changed ((3, [77]), 1)
def inserted : Rows := changed newNegative
def mutatedChild : Rows := OccurrenceSpace.replace source 2 [([20], 2)] 6
def observed (current : Rows) := ScopedRecords.observe contents current
def required : ScopedRecords.Captured Nat Nat Nat Nat Row :=
  ⟨source.storeId, (run (observed source) program).reads⟩

theorem actual_adaptive_reads_include_complete_match_absence_and_child :
    ((run (observed source) program).reads.map Prod.fst) =
      [.prefix 1 [10], .key 2 [99], .key 2 [20]] ∧
      ((run (observed source) program).answer.map (fun entry => entry.2.value)) = [42, 42, 21] ∧
      ((run (observed source) program).answer.map (fun entry => entry.2.binding.2.slot)) = [0, 1, 20] := by decide

theorem unrelated_change_preserves_but_both_consulted_changes_refuse :
    ScopedRecords.validate unread required = true ∧
      ScopedRecords.validate inserted required = false ∧
      ScopedRecords.validate mutatedChild required = false := by decide

theorem omitting_negative_read_accepts_a_different_answer :
    ScopedRecords.validate inserted (ScopedRecords.capture contents source [.prefix 1 [10]]) = true ∧
      (run (observed inserted) program).answer ≠ (run (observed source) program).answer := by decide

def changedPayloadSource : Rows := ⟨17, 5, source.entries⟩
def changedPayload (epoch : Nat) (stamp : Stamp) : Row :=
  {contents epoch stamp with value := (contents epoch stamp).value + 1}

/-- Keeping stamps while changing their interpretation violates the immutable
version interface. Metadata agreement alone cannot repair that provider. -/
theorem metadata_is_insufficient_for_unversioned_mutable_payloads :
    ScopedRecords.metadata changedPayloadSource (.prefix 1 [10]) =
        ScopedRecords.metadata source (.prefix 1 [10]) ∧
      ScopedRecords.observe changedPayload changedPayloadSource (.prefix 1 [10]) ≠
        ScopedRecords.observe contents source (.prefix 1 [10]) := by decide

theorem selected_payload_observer_is_preserved :
    (run (observed unread) program).answer.map (fun entry => entry.2.value) =
      (run (observed source) program).answer.map (fun entry => entry.2.value) :=
  validated_selected_observer contents source unread program
    (fun result => result.answer.map (fun entry => entry.2.value)) (by decide)

def contextNames : Nat ≃ Nat := Equiv.swap 1 3

theorem namespace_change_is_real_and_preserves_binding_and_need_names :
    (OccurrenceSpace.rename contextNames source).entries ≠ source.entries ∧
      contextualStore contents contextNames source (.prefix 1 [10]) = observed source (.prefix 1 [10]) ∧
      ((contextualStore contents contextNames source (.prefix 1 [10])).2.map (fun row => row.2.need)) =
        [sharedCell, sharedCell] := by
  refine ⟨by decide, ?_, ?_⟩
  · exact congrFun (contextualStore_eq contents contextNames source) _
  · rw [contextualStore_eq]
    rfl

def saved : Nat × Result (Answer := List (Stamp × Row)) (observed source) :=
  Cursor.advance (provider (observed source)) client (readCharge (observed source)) 2 ⟨.unit, program, []⟩

theorem retained_prefix_validation_resumes_same_account :
    Cursor.resume (provider (observed unread)) client (readCharge (observed unread)) 2
      (rebase (observed source) (observed unread) saved) =
      Cursor.advance (provider (observed unread)) client (readCharge (observed unread)) 4
        ⟨.unit, program, []⟩ :=
  metadata_validated_resume contents source unread 2 2 program (by decide)

def held : OccurrenceSpace.Authority Nat Nat Nat :=
  OccurrenceSpace.owned 1 (OccurrenceSpace.rows source 1) +
    OccurrenceSpace.owned 2 (OccurrenceSpace.rows source 2)
def protectedStore (current : Rows) := guardedObserve contents held current
def revokedStore (current : Rows) := guardedObserve contents 0 current

def protectedProgram : Program (Scope Nat Nat) (Except OwnWrite.Fault QueryReply)
    (Except OwnWrite.Fault (List (Stamp × Row))) :=
  .read (.prefix 1 [10]) fun parent =>
    match parent with
    | .error refused => .pure (.error refused)
    | .ok rows => .read (.key 2 [99]) fun absent =>
        match absent with
        | .error refused => .pure (.error refused)
        | .ok _ => .pure (.ok rows.2)

def protectedCut : Nat × Result (Answer := Except OwnWrite.Fault (List (Stamp × Row))) (protectedStore source) :=
  Cursor.advance (provider (protectedStore source)) client (readCharge (protectedStore source))
    1 ⟨.unit, protectedProgram, []⟩

theorem successful_empty_read_and_revoked_read_are_distinct :
    protectedStore source (.key 2 [99]) = .ok (17, []) ∧
      revokedStore source (.key 2 [99]) = .error .denied := by decide

theorem capture_across_revocation_keeps_exact_paid_work :
    resumeValidated (protectedStore source) (revokedStore source) 5 protectedCut = .error protectedCut := by
  exact resumeValidated_refused _ _ _ _ (by decide)

end ScopedOccurrence.Controls

namespace ScopedOccurrence.OwnClient.Controls

open Mettapedia.GSLT.Contracts
open Mettapedia.Machines
open scoped Mettapedia.GSLT.SeparationAlgebra

abbrev Item := Nat × Nat

local instance : Fintype Access :=
  ⟨{.none, .read, .consume}, by intro access; cases access <;> simp⟩

def required (_ : OrderedDependencyStore.Action Item 2) (_ : Bool) : Access := .consume
def needed (_ : Bool) : Access := .consume

local instance permissionDecision (point : IndexedAuthority.Point revocationWorlds)
    (change : OrderedDependencyStore.Action Item 2) :
    Decidable (FrameUpdate point.authority (required change point.world)) :=
  inferInstanceAs (Decidable (∀ frame : Access,
    Access.separate point.authority frame = true → Access.separate Access.consume frame = true))

local instance admissionDecision (point : IndexedAuthority.Point revocationWorlds) :
    Decidable (FrameUpdate point.authority (needed point.world)) :=
  permissionDecision point (.append 0 [])

def held : IndexedAuthority.Point revocationWorlds := ⟨false, .consume⟩
def revoked : IndexedAuthority.Point revocationWorlds := ⟨true, .none⟩
def source : OwnWrite.State revocationWorlds Item 2 :=
  ⟨OrderedDependencyStore.initial 17 (fun site => if site = 0 then [(10, 42), (11, 42)] else [(20, 9)]), held⟩
def program := readEraseReplace (Entry := Item) (size := 2) 0 (10, 42)
def cut := OwnWrite.advance revocationWorlds required 1 program source
def finished := OwnWrite.advance revocationWorlds required 3 program source

def capturedRows : Option (List Item) :=
  (OwnWrite.completed revocationWorlds required finished).bind fun result =>
    result.toOption.map Prod.snd

theorem actual_read_then_own_take_keeps_old_reply_and_other_space :
    capturedRows = some [(10, 42), (11, 42)] ∧ finished.1 = 2 ∧
      ((OwnWrite.current revocationWorlds required finished).store.members 0).own = [(11, 42)] ∧
      ((OwnWrite.current revocationWorlds required finished).store.members 1).own = [(20, 9)] ∧
      OrderedDependencyStore.checkRead (OwnWrite.current revocationWorlds required finished).store
        (OrderedDependencyStore.readStamp source.store 0) = false := by decide

theorem revocation_before_take_retains_the_paid_cut :
    OwnWrite.Invocation.resume revocationWorlds required needed source.store revoked 0 2 cut = .error cut := by
  have denied : ¬ FrameUpdate revoked.authority (needed revoked.world) := by
    intro update
    have impossible := update Access.read (by rfl)
    exact (by decide : ¬ (Access.consume ## Access.read)) impossible
  exact OwnWrite.Invocation.pending_refused revocationWorlds required needed source.store revoked
    0 1 1 (.write (.replace 0 [(11, 42)]))
    (fun _ => .ret (OrderedDependencyStore.readStamp source.store 0, [(10, 42), (11, 42)]))
    source (.inl denied)

end ScopedOccurrence.OwnClient.Controls

namespace RetainedForce.Controls

open Mettapedia.Machines.BranchLocalNeed.NeedReference
open Mettapedia.GSLT.LanguageDef.ForeignCapabilityLightcone
open ScopedOccurrence.Controls (sharedCell contents first second)

abbrev Machine := Mettapedia.Machines.BranchLocalNeed.NeedReference.Machine Unit Nat Nat Unit Nat Unit Unit Unit
abbrev Row := ScopedOccurrence.Controls.Row

def spec : Spec Unit Nat Nat Unit Nat Unit Unit Unit :=
  Mettapedia.Machines.BranchLocalNeed.NeedCacheLaws.CompletedReceiptControls.spec

def cached : Machine :=
  { world := {
      lineage := 7
      path := [3]
      heap := {
        current := fun cell => if cell = sharedCell then some ⟨(), .value 21⟩ else none
        spine := [.cache sharedCell (.value 21), .allocate sharedCell ()] }
      receipts := ReceiptGraph.empty
      nextCell := 5
      nextEvaluator := 1 }
    control := .run 0 [] }

def lease : Lease Nat CellId Nat := ⟨handle 17 sharedCell, 1, .shared⟩
def initial : World Nat CellId Nat := ⟨{lease}, []⟩
def shared : World Nat CellId Nat := ⟨{lease with holder := 2} ::ₘ initial.frontier, [.share lease 2]⟩

def valueWork : BoundaryOutcome Row (List Machine) Unit → Option (Nat × Work)
  | .returned (machine :: _) =>
      match machine.control with
      | .returned (.value value) _ => some (value, machine.work)
      | _ => none
  | _ => none

def outcomeTag : BoundaryOutcome Row (List Machine) Unit → Nat
  | .inert _ => 0
  | .fault _ => 1
  | .returned [] => 2
  | .returned (machine :: _) =>
      match machine.control with
      | .returned (.value _) _ => 3
      | .returned (.retryableFault _) _ => 4
      | _ => 5

theorem distinct_bindings_share_one_original_need_cell :
    (contents 17 first).binding ≠ (contents 17 second).binding ∧
      (contents 17 first).need = (contents 17 second).need ∧
      (contents 17 first).value = (contents 17 second).value := by decide

theorem copy_without_lease_is_inert :
    force spec cached [] initial.frontier 2 17 (contents 17 first) = .inert (contents 17 first) :=
  force_without_current_lease spec cached [] initial.frontier 2 17 (contents 17 first)
    (by unfold Authorized; decide)

theorem real_share_keeps_identity_and_authorizes_second_holder :
    Step initial (.share lease 2) shared ∧ Authorized shared.frontier 2 lease.handle := by
  exact actual_share_authorizes initial lease 2 (by simp [initial]) rfl

theorem both_shared_holders_deliver_cached_value_without_producing_again :
    valueWork (force spec cached [] shared.frontier 1 17 (contents 17 first)) =
      some (21, ⟨1, 1, 0, 1, 0⟩) ∧
      valueWork (force spec cached [] shared.frontier 2 17 (contents 17 second)) =
        some (21, ⟨1, 1, 0, 1, 0⟩) := by decide

theorem copied_generation_and_other_store_do_not_acquire_force :
    force spec cached [] shared.frontier 1 18 (contents 17 first) = .inert (contents 17 first) ∧
      force spec cached [] shared.frontier 1 17
        {contents 17 first with need := {sharedCell with generation := 3}} =
          .inert {contents 17 first with need := {sharedCell with generation := 3}} := by
  constructor <;> apply force_without_current_lease <;> unfold Authorized <;> decide

def olderHeap : Machine := {cached with world := {cached.world with heap := Heap.empty}}

/-- Current permission alone does not certify an arbitrary old heap. The real
Need transition reports out-of-scope waiting rather than a successful value
or an empty relational answer. A provider must supply its current retained world. -/
theorem authority_is_not_heap_currency :
    outcomeTag (force spec olderHeap [] shared.frontier 1 17 (contents 17 first)) = 4 := by decide

def selectingProgram := Mettapedia.Machines.ReadOnlyQuery.map
  (fun rows => rows.head?.map Prod.snd) ScopedOccurrence.Controls.program

def selected (frontier : Frontier Nat CellId Nat) :=
  (run (ScopedOccurrence.Controls.observed ScopedOccurrence.Controls.unread) selectingProgram).answer.map
    (force spec cached [] frontier 1 17)

theorem selected_query_composes_with_current_force :
    (run (ScopedOccurrence.Controls.observed ScopedOccurrence.Controls.unread) selectingProgram).answer.map
        (force spec cached [] shared.frontier 1 17) =
      (run (ScopedOccurrence.Controls.observed ScopedOccurrence.Controls.source) selectingProgram).answer.map
        (force spec cached [] shared.frontier 1 17) :=
  validated_query_then_current_force contents (fun (_ : Nat) (_ : ScopedRecords.Stamp Nat Nat Nat) => 42)
    ScopedOccurrence.Controls.source ScopedOccurrence.Controls.unread selectingProgram spec cached [] shared.frontier 1 (by decide)

theorem validated_selection_is_not_a_live_force_grant :
    (selected shared.frontier).map outcomeTag = some 3 ∧
      (selected 0).map outcomeTag = some 0 := by decide

def producingSpec : Spec Unit Nat Nat Unit Nat Unit Unit Unit where
  alternatives _ := [((), 0)]
  action state :=
    if state = 0 then .perform () 1
    else if state = 2 then .demand sharedCell 3
    else .done (.value 21)
  afterDemand token _ := token
  afterAllocation token _ := token

def suspended : Machine :=
  {cached with
    world := {cached.world with heap := {
      current := fun cell => if cell = sharedCell then some ⟨(), .suspended⟩ else none
      spine := [.allocate sharedCell ()] }}
    control := .force sharedCell [.resume 2] }

def authorizedProduction : List Machine :=
  match force producingSpec suspended [.resume 2] shared.frontier 1 17 (contents 17 first) with
  | .returned successors => runFrontier producingSpec 9 successors
  | _ => []

/-- A suspended producer actually emits an effect, commits, and is demanded
again by its retained consumer. That second demand uses the original cache. -/
theorem actual_production_then_shared_demand_emits_once :
    (authorizedProduction.map fun machine => machine.world.receipts.effects) = [[()]] ∧
      (authorizedProduction.map fun machine => machine.work.allocations) = [0] ∧
      (authorizedProduction.map fun machine => machine.world.heap.lookup sharedCell) =
        [some ⟨(), .value 21⟩] ∧
      (authorizedProduction.map fun machine => isHalted machine) = [true] := by decide

open Mettapedia.Languages.MeTTa.MetavariableFrameStore

def bindingEntry : EntryOf Nat :=
  { generation := 3
    frame := ["x", "y"]
    values := #[none, some 9]
    size_eq := rfl
    writeVersions := #[4, 5]
    versions_size_eq := rfl
    activationBoundary := some 2 }
def image : Shared.ImageOf Nat := ⟨#[some bindingEntry], 6⟩
def allocator : Shared.Allocator := ⟨#[⟨3, 1⟩], 10⟩
def unbound : Row := {contents 17 first with binding := (17, ⟨0, 3, 0⟩)}

theorem actual_binding_read_retains_unbound_clock_and_activation :
    bindingRead 17 allocator image unbound = some ⟨none, 4, 6, some 2⟩ ∧
      bindingRead 18 allocator image unbound = none ∧
      bindingRead 17 allocator image {unbound with binding := (17, ⟨0, 2, 0⟩)} = none := by decide

end RetainedForce.Controls

#print axioms ScopedOccurrence.context_advance_account
#print axioms ScopedOccurrence.context_resume_account
#print axioms ScopedOccurrence.metadata_validated_resume
#print axioms ScopedOccurrence.validated_selected_observer
#print axioms ScopedOccurrence.scope_manifest_preserves_adaptive_query
#print axioms RetainedForce.binding_read_current
#print axioms RetainedForce.force_with_current_lease
#print axioms RetainedForce.copying_description_does_not_force
#print axioms RetainedForce.actual_share_authorizes
#print axioms RetainedForce.owned_lease_cannot_be_shared
#print axioms RetainedForce.authorized_cached_delivery
#print axioms RetainedForce.validated_query_then_current_force
#print axioms ScopedOccurrence.OwnClient.read_replace_returns_captured_reply
#print axioms ScopedOccurrence.OwnClient.Controls.revocation_before_take_retains_the_paid_cut
#print axioms RetainedForce.Controls.actual_production_then_shared_demand_emits_once

end Mettapedia.Machines.Cursor.ReadOnlyQuery

/-! ## Earned sampled replies and a fixed comparison view

The sampler returns its actual reply and next context. The existing query
client records those replies without assuming a fixed source. Agreement of
the earned log with one fixed view then determines its residual, status and
matching pure request tariff. Provider context effects and source protection
remain separate; logged agreement does not itself grant current authority.
-/

namespace Mettapedia.Machines.Cursor.ReadOnlyQuery.Sampled

open Mettapedia.Machines.ReadOnlyQuery (Program Reads Observation Agrees checkReads)

universe u
variable {Key Value Answer Context : Type u}

/-- The existing state projection keeps the whole client residual/status.
It asserts no step law on contexts not visited by this execution. -/
def project (sample : Context → Key → Value × Context) (store : Key → Value)
    (previous : Nat × Cursor.Outcome (provider sample) (client (Answer := Answer)) PUnit.unit) :
    Nat × Cursor.Outcome (ReadOnlyQuery.provider store) (client (Answer := Answer)) PUnit.unit :=
  (previous.1, Cursor.Outcome.mapState client (source := provider sample)
    (target := ReadOnlyQuery.provider store) (fun saved => saved.2) previous.2)

@[simp] theorem advance_zero (sample : Context → Key → Value × Context) (price : Key → Nat)
    (program : Program Key Value Answer) (context : Context) (reads : Reads Key Value) :
    advance sample price 0 program context reads =
      (0, .paused ⟨PUnit.unit, program, context, reads⟩) := rfl

@[simp] theorem advance_pure (sample : Context → Key → Value × Context) (price : Key → Nat)
    (fuel : Nat) (answer : Answer) (context : Context) (reads : Reads Key Value) :
    advance sample price (fuel + 1) (.pure answer) context reads =
      (0, .done ⟨PUnit.unit, answer, context, reads⟩) := rfl

@[simp] theorem advance_read (sample : Context → Key → Value × Context) (price : Key → Nat)
    (fuel : Nat) (key : Key) (next : Value → Program Key Value Answer)
    (context : Context) (reads : Reads Key Value) :
    advance sample price (fuel + 1) (.read key next) context reads =
      let observed := sample context key
      let rest := advance sample price fuel (next observed.1) observed.2 ((key, observed.1) :: reads)
      (price key + rest.1, rest.2) := rfl

@[simp] theorem fixedAdvance_read (store : Key → Value) (price : Key → Nat)
    (fuel : Nat) (key : Key) (next : Value → Program Key Value Answer) (reads : Reads Key Value) :
    fixedAdvance store price (fuel + 1) (.read key next) reads =
      let rest := fixedAdvance store price fuel (next (store key)) ((key, store key) :: reads)
      (price key + rest.1, rest.2) := rfl

/-- Every actual old read remains, including duplicate and negative replies. -/
theorem recorded_keeps_prior (sample : Context → Key → Value × Context) (price : Key → Nat)
    (fuel : Nat) (program : Program Key Value Answer) (context : Context) (reads : Reads Key Value) :
    reads.reverse <+: recorded sample (advance sample price fuel program context reads).2 := by
  induction fuel generalizing program context reads with
  | zero => exact ⟨[], by simp [recorded, savedState]⟩
  | succ fuel ih =>
      cases program with
      | pure answer => exact ⟨[], by simp [recorded, savedState]⟩
      | read key next =>
          rw [advance_read]
          obtain ⟨suffix, equal⟩ := ih (next (sample context key).1) (sample context key).2
            ((key, (sample context key).1) :: reads)
          exact ⟨[(key, (sample context key).1)] ++ suffix, by
            simpa only [List.reverse_cons, List.append_assoc] using equal⟩

/-- The declared invoice is the tariff of the actual newly logged requests,
including repeats. It holds even when no fixed view can validate the log. -/
theorem actual_read_invoice (sample : Context → Key → Value × Context) (price : Key → Nat)
    (fuel : Nat) (program : Program Key Value Answer) (context : Context) (reads : Reads Key Value) :
    ((recorded sample (advance sample price fuel program context reads).2).map
        (fun observed => price observed.1)).sum =
      (reads.reverse.map (fun observed => price observed.1)).sum +
        (advance sample price fuel program context reads).1 := by
  induction fuel generalizing program context reads with
  | zero => simp [recorded, savedState]
  | succ fuel ih =>
      cases program with
      | pure answer => simp [recorded, savedState]
      | read key next =>
          rw [advance_read]
          have paid := ih (next (sample context key).1) (sample context key).2
            ((key, (sample context key).1) :: reads)
          simp only [List.reverse_cons, List.map_append, List.sum_append,
            List.map_singleton, List.sum_singleton] at paid
          change ((recorded sample (advance sample price fuel (next (sample context key).1)
              (sample context key).2 ((key, (sample context key).1) :: reads)).2).map
                (fun observed => price observed.1)).sum =
            (reads.reverse.map (fun observed => price observed.1)).sum +
              (price key + (advance sample price fuel (next (sample context key).1)
                (sample context key).2 ((key, (sample context key).1) :: reads)).1)
          omega

/-- Agreement concerns this earned finite path. The sampler may disagree at
other contexts/requests; no globally lawful provider homomorphism is assumed.
The conclusion keeps exact status, reply-selected residual, log and tariff. -/
theorem earned_prefix_eq_fixed (sample : Context → Key → Value × Context) (price : Key → Nat)
    (store : Key → Value) (fuel : Nat) (program : Program Key Value Answer)
    (context : Context) (reads : Reads Key Value)
    (valid : Agrees store (recorded sample (advance sample price fuel program context reads).2)) :
    project sample store (advance sample price fuel program context reads) =
      fixedAdvance store price fuel program reads := by
  induction fuel generalizing program context reads with
  | zero => rfl
  | succ fuel ih =>
      cases program with
      | pure answer => rfl
      | read key next =>
          rw [advance_read] at valid ⊢
          have seen : (key, (sample context key).1) ∈ recorded sample
              (advance sample price fuel (next (sample context key).1) (sample context key).2
                ((key, (sample context key).1) :: reads)).2 :=
            (recorded_keeps_prior sample price fuel (next (sample context key).1)
              (sample context key).2 ((key, (sample context key).1) :: reads)).subset (by simp)
          have reply : store key = (sample context key).1 := valid _ seen
          rw [fixedAdvance_read, reply]
          have suffix := ih (next (sample context key).1) (sample context key).2
            ((key, (sample context key).1) :: reads) valid
          exact congrArg (fun saved => (price key + saved.1, saved.2)) suffix

theorem projected_paid (sample : Context → Key → Value × Context) (store : Key → Value)
    (previous : Nat × Cursor.Outcome (provider sample) (client (Answer := Answer)) PUnit.unit) :
    (project sample store previous).1 = previous.1 := rfl

theorem projected_recorded (sample : Context → Key → Value × Context) (store : Key → Value)
    (previous : Nat × Cursor.Outcome (provider sample) (client (Answer := Answer)) PUnit.unit) :
    ReadOnlyQuery.recorded store (project sample store previous).2 = recorded sample previous.2 := by
  rcases previous with ⟨paid, outcome⟩
  cases outcome with
  | paused packet => rcases packet with ⟨⟨⟩, program, context, reads⟩; rfl
  | done finished => rcases finished with ⟨⟨⟩, answer, context, reads⟩; rfl

theorem projected_completed (sample : Context → Key → Value × Context) (store : Key → Value)
    (previous : Nat × Cursor.Outcome (provider sample) (client (Answer := Answer)) PUnit.unit) :
    ReadOnlyQuery.completed? store (project sample store previous).2 =
      completed? sample previous.2 := by
  rcases previous with ⟨paid, outcome⟩
  cases outcome with
  | paused packet => rcases packet with ⟨⟨⟩, program, context, reads⟩; rfl
  | done finished => rcases finished with ⟨⟨⟩, answer, context, reads⟩; rfl

theorem earned_account_eq (sample : Context → Key → Value × Context) (price : Key → Nat)
    (store : Key → Value) (fuel : Nat) (program : Program Key Value Answer)
    (context : Context) (reads : Reads Key Value)
    (valid : Agrees store (recorded sample (advance sample price fuel program context reads).2)) :
    (advance sample price fuel program context reads).1 =
      (fixedAdvance store price fuel program reads).1 :=
  congrArg Prod.fst (earned_prefix_eq_fixed sample price store fuel program context reads valid)

theorem checked_prefix_eq_fixed [DecidableEq Value]
    (sample : Context → Key → Value × Context) (price : Key → Nat)
    (store : Key → Value) (fuel : Nat) (program : Program Key Value Answer)
    (context : Context) (reads : Reads Key Value)
    (checked : checkReads store (recorded sample (advance sample price fuel program context reads).2) = true) :
    project sample store (advance sample price fuel program context reads) =
      fixedAdvance store price fuel program reads :=
  earned_prefix_eq_fixed sample price store fuel program context reads
    ((Mettapedia.Machines.ReadOnlyQuery.checkReads_iff _ _).mp checked)

/-- Outcome is independent of the declared tariff, by the existing identity
provider homomorphism. This does not identify different tariffs' invoices. -/
theorem fixed_outcome (store : Key → Value) (price : Key → Nat) (fuel : Nat)
    (program : Program Key Value Answer) (reads : Reads Key Value) :
    (fixedAdvance store price fuel program reads).2 =
      (Cursor.advance (ReadOnlyQuery.provider store) client (readCharge store) fuel
        (base := PUnit.unit) ⟨PUnit.unit, program, reads⟩).2 := by
  have same := (Cursor.Hom.id (ReadOnlyQuery.provider store)).advance client
    (fixedCharge store price) (readCharge store) fuel
    (base := PUnit.unit) ⟨PUnit.unit, program, reads⟩
  simpa only [Cursor.Hom.outcome, Cursor.Hom.id, Cursor.Hom.packet,
    Cursor.Outcome.mapState_id, fixedAdvance] using same

/-- Actual completion and validated replies reflect to the independent query
meaning. No fixed-provider origin is supplied for the sampled execution. -/
theorem earned_completion_correct (sample : Context → Key → Value × Context) (price : Key → Nat)
    (store : Key → Value) (fuel : Nat) (program : Program Key Value Answer) (context : Context)
    (observation : Observation Key Value Answer)
    (finished : completed? sample (advance sample price fuel program context []).2 = some observation)
    (valid : Agrees store (recorded sample (advance sample price fuel program context []).2)) :
    observation = Mettapedia.Machines.ReadOnlyQuery.run store program := by
  have same := earned_prefix_eq_fixed sample price store fuel program context [] valid
  have completed : ReadOnlyQuery.completed? store (fixedAdvance store price fuel program []).2 =
      some observation := by
    rw [← same, projected_completed]
    exact finished
  rw [fixed_outcome] at completed
  exact ReadOnlyQuery.completed_correct store fuel program observation completed

theorem resume_zero (sample : Context → Key → Value × Context) (price : Key → Nat)
    (previous : Nat × Cursor.Outcome (provider sample) (client (Answer := Answer)) PUnit.unit) :
    resume sample price 0 previous = previous := Cursor.resume_zero ..

theorem advance_split (sample : Context → Key → Value × Context) (price : Key → Nat)
    (first second : Nat) (program : Program Key Value Answer) (context : Context)
    (reads : Reads Key Value) :
    advance sample price (first + second) program context reads =
      resume sample price second (advance sample price first program context reads) :=
  Cursor.advance_add ..

theorem resume_keeps_recorded (sample : Context → Key → Value × Context) (price : Key → Nat)
    (fuel : Nat)
    (previous : Nat × Cursor.Outcome (provider sample) (client (Answer := Answer)) PUnit.unit) :
    recorded sample previous.2 <+: recorded sample (resume sample price fuel previous).2 := by
  rcases previous with ⟨paid, outcome⟩
  cases outcome with
  | done finished => exact ⟨[], by simp [resume, Cursor.resume]⟩
  | paused packet =>
      rcases packet with ⟨⟨⟩, program, context, reads⟩
      exact recorded_keeps_prior sample price fuel program context reads

theorem resumed_prefix_eq_fixed (sample : Context → Key → Value × Context) (price : Key → Nat)
    (store : Key → Value) (fuel : Nat)
    (previous : Nat × Cursor.Outcome (provider sample) (client (Answer := Answer)) PUnit.unit)
    (valid : Agrees store (recorded sample (resume sample price fuel previous).2)) :
    project sample store (resume sample price fuel previous) =
      fixedResume store price fuel (project sample store previous) := by
  rcases previous with ⟨paid, outcome⟩
  cases outcome with
  | done finished => rfl
  | paused packet =>
      rcases packet with ⟨⟨⟩, program, context, reads⟩
      have same := earned_prefix_eq_fixed sample price store fuel program context reads valid
      exact congrArg (fun saved => (paid + saved.1, saved.2)) same

/-- The fixed-view comparison starts at the same original program, while both
actual and fixed cursors reuse the saved prefix rather than execute it again. -/
theorem earned_split_eq_fixed (sample : Context → Key → Value × Context) (price : Key → Nat)
    (store : Key → Value) (first second : Nat) (program : Program Key Value Answer)
    (context : Context) (reads : Reads Key Value)
    (valid : Agrees store
      (recorded sample (advance sample price (first + second) program context reads).2)) :
    project sample store
        (resume sample price second (advance sample price first program context reads)) =
      fixedResume store price second (fixedAdvance store price first program reads) := by
  rw [advance_split] at valid
  have priorAgreement : Agrees store (recorded sample (advance sample price first program context reads).2) := by
    intro observed member
    exact valid observed ((resume_keeps_recorded sample price second
      (advance sample price first program context reads)).subset member)
  rw [resumed_prefix_eq_fixed sample price store second _ valid,
    earned_prefix_eq_fixed sample price store first program context reads priorAgreement]

namespace Controls

/-- Key 1 changes after the first sample. Key 0 remains unchanged. -/
private def viewAt (clock key : Nat) : Nat :=
  if key = 0 then 1 else if key = 1 then (if clock = 0 then 2 else 11) else 0

private def changing (clock key : Nat) : Nat × Nat := (viewAt clock key, clock + 1)
private def tariff (key : Nat) : Nat := key + 1
private def adaptive : Program Nat Nat (List Nat) :=
  .read 0 fun first => .read first fun second => .pure [first, second]
private def actual := advance changing tariff 3 adaptive 0 []
private def firstCut := advance changing tariff 1 adaptive 0 []

theorem actual_changing_provider_records_its_replies :
    completed? changing actual.2 = some ⟨[1, 11], [(0, 1), (1, 11)]⟩ ∧
      (savedState changing actual.2).1 = 2 ∧ actual.1 = 3 := ⟨rfl, rfl, rfl⟩

theorem changing_execution_is_not_initial_fixed_execution :
    (Mettapedia.Machines.ReadOnlyQuery.run (viewAt 0) adaptive).answer = [1, 2] ∧
      completed? changing actual.2 ≠
        some (Mettapedia.Machines.ReadOnlyQuery.run (viewAt 0) adaptive) := by
  refine ⟨rfl, ?_⟩
  intro equal
  have answers := congrArg (Option.map Observation.answer) equal
  change some [1, 11] = some [1, 2] at answers
  cases answers

theorem actual_log_validates_at_protected_view :
    checkReads (viewAt 2) (recorded changing actual.2) = true := by decide

theorem earned_changing_execution_matches_fixed_view :
    project changing (viewAt 2) actual = fixedAdvance (viewAt 2) tariff 3 adaptive [] :=
  checked_prefix_eq_fixed changing tariff (viewAt 2) 3 adaptive 0 [] actual_log_validates_at_protected_view

/-- The actual path validates even though a request at an unvisited initial
context would disagree. A globally lawful provider map is unnecessary. -/
theorem path_agreement_does_not_assume_global_provider_agreement :
    (changing 0 1).1 ≠ viewAt 2 1 ∧
      project changing (viewAt 2) actual = fixedAdvance (viewAt 2) tariff 3 adaptive [] :=
  ⟨by decide, earned_changing_execution_matches_fixed_view⟩

theorem partial_reply_selects_actual_residual :
    project changing (viewAt 2) firstCut =
      (1, .paused ⟨PUnit.unit, .read 1 (fun second => .pure [1, second]), [(0, 1)]⟩) := rfl

theorem changing_split_reuses_earned_prefix :
    resume changing tariff 2 firstCut = actual := (advance_split changing tariff 1 2 adaptive 0 []).symm

theorem changing_split_matches_fixed_resumption :
    project changing (viewAt 2) (resume changing tariff 2 firstCut) =
      fixedResume (viewAt 2) tariff 2 (fixedAdvance (viewAt 2) tariff 1 adaptive []) :=
  earned_split_eq_fixed changing tariff (viewAt 2) 1 2 adaptive 0 []
    ((Mettapedia.Machines.ReadOnlyQuery.checkReads_iff _ _).mp actual_log_validates_at_protected_view)

theorem zero_resume_keeps_context_log_and_invoice :
    resume changing tariff 0 firstCut = firstCut := resume_zero ..

theorem changed_selected_reply_rejects_log :
    checkReads (Function.update (viewAt 2) 0 8) (recorded changing actual.2) = false := by decide

private def repeated : Program Nat Nat (List Nat) :=
  .read 0 fun first => .read 0 fun second => .pure [first, second]
private def increments (clock : Nat) (_key : Nat) : Nat × Nat := (clock, clock + 1)
private def conflicting := advance increments (fun _ => 1) 3 repeated 0 []

theorem conflicting_repeat_has_no_fixed_view (store : Nat → Nat) :
    ¬ Agrees store (recorded increments conflicting.2) := by
  intro valid
  change Agrees store [(0, 0), (0, 1)] at valid
  have first := valid (0, 0) (by simp)
  have second := valid (0, 1) (by simp)
  simp only at first second
  omega

theorem conflicting_repeat_is_not_silently_deduplicated :
    recorded increments conflicting.2 = [(0, 0), (0, 1)] ∧
      checkReads (fun _ => 0) (recorded increments conflicting.2) = false := by decide

private def optionalRepeated : Program Nat (Option Nat) (List (Option Nat)) :=
  .read 0 fun first => .read 0 fun second => .pure [first, second]
private def presenceChanges (clock : Nat) (_key : Nat) : Option Nat × Nat :=
  (if clock = 0 then none else some 9, clock + 1)
private def absentThenPresent := advance presenceChanges (fun _ => 1) 3 optionalRepeated 0 []

theorem negative_reply_is_part_of_actual_certificate :
    recorded presenceChanges absentThenPresent.2 = [(0, none), (0, some 9)] ∧
      checkReads (fun _ => some 9) (recorded presenceChanges absentThenPresent.2) = false := by decide

private def oneRead : Program Nat Nat Nat := .read 0 .pure
private def constantReply (hop clock : Nat) (_key : Nat) : Nat × Nat := (7, clock + hop)

/-- Read agreement does not transport the sampler's arbitrary context effects. -/
theorem equal_replies_do_not_identify_provider_contexts :
    completed? (constantReply 1) (advance (constantReply 1) (fun _ => 1) 2 oneRead 0 []).2 =
      completed? (constantReply 2) (advance (constantReply 2) (fun _ => 1) 2 oneRead 0 []).2 ∧
      (savedState (constantReply 1) (advance (constantReply 1) (fun _ => 1) 2 oneRead 0 []).2).1 ≠
        (savedState (constantReply 2) (advance (constantReply 2) (fun _ => 1) 2 oneRead 0 []).2).1 := ⟨rfl, by decide⟩

/-- Matching reply certificates alone do not make unrelated tariffs equal. -/
theorem account_condition_is_separate_from_reply_agreement :
    completed? (constantReply 1) (advance (constantReply 1) (fun _ => 2) 2 oneRead 0 []).2 =
      ReadOnlyQuery.completed? (fun _ => 7) (fixedAdvance (fun _ => 7) (fun _ => 1) 2 oneRead []).2 ∧
      (advance (constantReply 1) (fun _ => 2) 2 oneRead 0 []).1 ≠
        (fixedAdvance (fun _ => 7) (fun _ => 1) 2 oneRead []).1 := ⟨rfl, by decide⟩

private def scopeStore (key : Nat × Nat) : Nat := key.1 + key.2 + 1
private def oldScope : Program (Nat × Nat) Nat Nat := .read (0, 0) .pure
private def otherScope : Program (Nat × Nat) Nat Nat := .read (1, 0) .pure

theorem validated_old_scope_does_not_replace_the_query_scope :
    checkReads scopeStore [( (0, 0), 1)] = true ∧
      (Mettapedia.Machines.ReadOnlyQuery.run scopeStore oldScope).answer ≠
        (Mettapedia.Machines.ReadOnlyQuery.run scopeStore otherScope).answer := by decide

namespace LateCheck

open Mettapedia.Machines.AuthorityObservationControls
open Mettapedia.Machines.RevisionDependencySetCanary (Store environment)

private def sample (state : State) (key : Store) : Nat × State := lateObserve key state
private def program : Program Store Nat (Nat × Nat) :=
  .read .evidence fun evidence => .read .model fun model => .pure (evidence, model)
private def earned := advance sample (fun _ => 1) 3 program initial []

theorem actual_late_observer_returns_truthful_earlier_replies :
    completed? sample earned.2 = some ⟨(7, 3), [(.evidence, 7), (.model, 3)]⟩ ∧
      (savedState sample earned.2).1 = { initial with evidence := 8, cacheTicks := 2 } := ⟨rfl, rfl⟩

theorem historical_view_agrees_with_actual_late_log :
    checkReads environment.current (recorded sample earned.2) = true := by decide

theorem earned_late_log_reflects_only_the_historical_view :
    project sample environment.current earned = fixedAdvance environment.current (fun _ => 1) 3 program [] :=
  checked_prefix_eq_fixed sample (fun _ => 1) environment.current 3 program initial []
    historical_view_agrees_with_actual_late_log

/-- The existing late-check counterexample is now also an actual query-cursor
execution. Its earlier successful comparison cannot grant current publication. -/
theorem actual_late_current_publication_is_refused :
    ¬ capture.CanPublish (projection (savedState sample earned.2).1) :=
  late_checks_cannot_publish

theorem actual_late_log_fails_current_full_agreement :
    checkReads (projection (savedState sample earned.2).1).current (recorded sample earned.2) = false := by decide

end LateCheck
end Controls

end Mettapedia.Machines.Cursor.ReadOnlyQuery.Sampled
