import Mettapedia.Machines.Cursor.Protocol
import Mettapedia.Machines.ReadOnlyQuery
import Mettapedia.Machines.ResourceOwnership

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

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.Machines.ReadOnlyQuery (Program Reads Observation run Agrees checkReads)

universe u

variable {Key Value Answer : Type u}

abbrev protocol (Key Value : Type u) :
    IndexedPolynomial PUnit.{u + 1} (fun _ => PUnit.{u + 1}) where
  Shape _ _ := Key
  Position _ := Value
  next _ _ := .unit

/-- Reads are retained in reverse chronological order so a new read is a
single list constructor. The immutable store view is supplied by the provider. -/
def provider (store : Key → Value) : Provider (protocol Key Value) where
  State _ _ := Reads Key Value
  step reads key := ⟨store key, (key, store key) :: reads⟩

def client : Client (P := protocol Key Value) (Return := fun _ _ => Answer) where
  V _ _ := Program Key Value Answer
  str := fun _ _ => ↾(fun program => match program with
    | .pure answer => ⟨.inl answer, fun impossible => nomatch impossible⟩
    | .read key next => ⟨.inr key, next⟩)

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

end Mettapedia.Machines.Cursor.ReadOnlyQuery
