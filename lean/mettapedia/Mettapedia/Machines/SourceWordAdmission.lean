import Mettapedia.Machines.ContextualSourceAdmission
import Mettapedia.Machines.SourceAccounting

/-!
# Source admission around a common computation word

The source places an occurrence/charge annotation around the current raw
computation. Its administrative annotation step is followed by the operation.
The native boundary instead reads the occurrence from immutable metadata,
pays the bounded-word purse, and executes that same raw common operation.
Both retain the entire contextual state, including pending workers, lexical
frames, alternatives, effects and publications.

One physical visit in this interface includes the source annotation and its
operation. Physical room is tested before the source purse. An annotation
already present in the raw operation is refused, rather than charged twice.
This joins annotation erasure to the existing metered kernel; C goal selection,
dialect elaboration and pointer/collection correspondence remain obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SourceWordAdmission

open ContextualCBPV
open ContextualCBPV.EpisodeAccounting

variable (Value Call Effect Fault Delay Suspension Context World Worker : Type)

abbrev Kernel := State Value Call Effect Fault Delay Suspension Context World Worker
abbrev Sem := Semantics Value Call Effect Fault Delay Suspension Context World Worker
abbrev Meter := ContextualSourceAdmission.Meter Value Call Effect Fault Delay Suspension Context World Worker
abbrev Native := ContextualSourceAdmission.Native Value Call Effect Fault Delay Suspension Context World Worker
abbrev Reference := ContextualSourceAdmission.Reference Value Call Effect Fault Delay Suspension Context World Worker

variable {Value Call Effect Fault Delay Suspension Context World Worker}

/-- Derived canonical work retains its explicit unit charge. -/
def price (origin : SourceAccounting.Origin) (debit : Nat) : Nat :=
  if origin.position = 0 then 1 else debit

def raw : Code Value Call Effect Fault Delay Suspension → Bool
  | .source _ _ _ => false
  | _ => true

/-- The source owns the annotation in its computation syntax. -/
def annotate (origin : SourceAccounting.Origin) (debit : Nat)
    (state : Meter Value Call Effect Fault Delay Suspension Context World Worker) :
    Option (Meter Value Call Effect Fault Delay Suspension Context World Worker) :=
  match state.state.focus.control with
  | .compute context code =>
      if raw code then some {state with state := {state.state with focus :=
        {state.state.focus with control := .compute context (.source origin.encode (price origin debit) code)}}}
      else none
  | _ => none

def referenceOperation (sem : Sem Value Call Effect Fault Delay Suspension Context World Worker)
    (origin : SourceAccounting.Origin) (debit : Nat)
    (state : Meter Value Call Effect Fault Delay Suspension Context World Worker) :=
  (annotate origin debit state).bind fun annotated =>
    (meteredStep sem annotated).bind (meteredStep sem)

/-- Native execution gets the charge from the plan, without entering a
second source-annotation computation or inspecting a returned value. -/
def nativeOperation (sem : Sem Value Call Effect Fault Delay Suspension Context World Worker)
    (maximum : Nat) (origin : SourceAccounting.Origin) (debit : Nat)
    (state : Meter Value Call Effect Fault Delay Suspension Context World Worker) :
    Option (Meter Value Call Effect Fault Delay Suspension Context World Worker) :=
  match state.state.focus.control with
  | .compute _ code =>
      if raw code then
        (nativeDebit maximum (price origin debit) ⟨state.remaining, state.state.spent⟩).bind fun paid =>
          let entered := {state.state with
            spent := paid.spent
            sourceTrace := state.state.sourceTrace ++ [origin.encode]}
          (step sem entered).map fun next => ⟨next, paid.remaining⟩
      else none
  | _ => none

private theorem uncharged_compute
    (sem : Sem Value Call Effect Fault Delay Suspension Context World Worker)
    (state : Meter Value Call Effect Fault Delay Suspension Context World Worker)
    (context : Context) (code : Code Value Call Effect Fault Delay Suspension)
    (focused : state.state.focus.control = .compute context code) (plain : raw code = true) :
    meteredStep sem state = (step sem state.state).map (fun next => ⟨next, state.remaining⟩) := by
  cases code <;> simp_all [raw, meteredStep, ContextualCBPV.debit]

private theorem annotation_step
    (sem : Sem Value Call Effect Fault Delay Suspension Context World Worker)
    (state : Meter Value Call Effect Fault Delay Suspension Context World Worker)
    (context : Context) (code : Code Value Call Effect Fault Delay Suspension)
    (occurrence cost : Nat) :
    meteredStep sem {state with state := {state.state with focus :=
      {state.state.focus with control := .compute context (.source occurrence cost code)}}} =
      if cost ≤ state.remaining then
        some {
          state := {state.state with
            focus := {state.state.focus with control := .compute context code}
            spent := state.state.spent + cost
            sourceTrace := state.state.sourceTrace ++ [occurrence]}
          remaining := state.remaining - cost}
      else none := by
  rcases state with ⟨⟨world, ⟨control, frames⟩, alternatives, published, entries, spent, trace⟩, credit⟩
  by_cases enough : cost ≤ credit <;>
    simp [meteredStep, step, ContextualCBPV.debit, ContextualCBPV.origin, advance, enough]

/-- Source annotation followed by its operation equals the directly charged
native word, including exact refusal and the full pending contextual state. -/
theorem operation_refines
    (sem : Sem Value Call Effect Fault Delay Suspension Context World Worker)
    (maximum : Nat) (origin : SourceAccounting.Origin) (debit : Nat)
    (state : Meter Value Call Effect Fault Delay Suspension Context World Worker)
    (inRange : state.state.spent + state.remaining ≤ maximum) :
    nativeOperation sem maximum origin debit state = referenceOperation sem origin debit state := by
  rcases state with ⟨⟨world, ⟨control, frames⟩, alternatives, published, entries, spent, trace⟩, credit⟩
  cases control with
  | compute context code =>
      by_cases plain : raw code = true
      · simp only [nativeOperation, referenceOperation, annotate, plain, ↓reduceIte, Option.bind_some]
        rw [annotation_step sem
          ⟨⟨world, ⟨.compute context code, frames⟩, alternatives, published, entries, spent, trace⟩, credit⟩
          context code origin.encode (price origin debit)]
        rw [native_debit_refines maximum _ _ inRange]
        by_cases enough : price origin debit ≤ credit
        · simp only [EpisodeAccounting.debit, enough, ↓reduceIte, Option.bind_some]
          rw [uncharged_compute sem _ context code rfl plain]
        · simp [EpisodeAccounting.debit, enough]
      · simp [nativeOperation, referenceOperation, annotate, plain]
  | delivery worker => simp [nativeOperation, referenceOperation, annotate]
  | returned context packet => simp [nativeOperation, referenceOperation, annotate]
  | failed => simp [nativeOperation, referenceOperation, annotate]
  | stopped reason => simp [nativeOperation, referenceOperation, annotate]
  | unhandled fault => simp [nativeOperation, referenceOperation, annotate]

private theorem annotation_ledger
    (origin : SourceAccounting.Origin) (debit : Nat)
    (before after : Meter Value Call Effect Fault Delay Suspension Context World Worker)
    (made : annotate origin debit before = some after) :
    after.state.spent = before.state.spent ∧ after.remaining = before.remaining := by
  unfold annotate at made
  split at made
  · split at made
    · cases Option.some.inj made
      exact ⟨rfl, rfl⟩
    · simp at made
  · simp at made

theorem operation_preserves_total
    (sem : Sem Value Call Effect Fault Delay Suspension Context World Worker)
    (maximum : Nat) (origin : SourceAccounting.Origin) (debit : Nat)
    (before after : Meter Value Call Effect Fault Delay Suspension Context World Worker)
    (inRange : before.state.spent + before.remaining ≤ maximum)
    (advanced : nativeOperation sem maximum origin debit before = some after) :
    after.state.spent + after.remaining = before.state.spent + before.remaining := by
  rw [operation_refines sem maximum origin debit before inRange] at advanced
  obtain ⟨annotated, made, rest⟩ := Option.bind_eq_some_iff.mp advanced
  obtain ⟨paid, charged, executed⟩ := Option.bind_eq_some_iff.mp rest
  have kept := annotation_ledger origin debit before annotated made
  have first := semantic_purse_conserved sem annotated paid charged
  have later := semantic_purse_conserved sem paid after executed
  omega

def referenceStep (sem : Sem Value Call Effect Fault Delay Suspension Context World Worker)
    (origin : SourceAccounting.Origin) (debit : Nat)
    (state : Reference Value Call Effect Fault Delay Suspension Context World Worker) :
    Option (Reference Value Call Effect Fault Delay Suspension Context World Worker) :=
  if ContextualSourceAdmission.room state.physical then
    (referenceOperation sem origin debit state.meter).map fun next =>
      ⟨next, state.physical.map (· - 1)⟩
  else none

def nativeStep (sem : Sem Value Call Effect Fault Delay Suspension Context World Worker)
    (maximum : Nat) (limit : Option Nat) (origin : SourceAccounting.Origin) (debit : Nat)
    (state : Native Value Call Effect Fault Delay Suspension Context World Worker) :
    Option (Native Value Call Effect Fault Delay Suspension Context World Worker) :=
  if limit.all (state.permitted < ·) then
    (nativeOperation sem maximum origin debit state.meter).map fun next =>
      ⟨next, if limit.isSome then state.permitted + 1 else state.permitted⟩
  else none

theorem step_refines
    (sem : Sem Value Call Effect Fault Delay Suspension Context World Worker)
    (maximum : Nat) (limit : Option Nat) (origin : SourceAccounting.Origin) (debit : Nat)
    (state : Native Value Call Effect Fault Delay Suspension Context World Worker)
    (inRange : state.meter.state.spent + state.meter.remaining ≤ maximum) :
    (nativeStep sem maximum limit origin debit state).map (ContextualSourceAdmission.decode limit) =
      referenceStep sem origin debit (ContextualSourceAdmission.decode limit state) := by
  cases limit with
  | none =>
      simp [nativeStep, referenceStep, ContextualSourceAdmission.decode,
        ContextualSourceAdmission.remaining, ContextualSourceAdmission.room,
        operation_refines sem maximum origin debit state.meter inRange,
        Option.map_map, Function.comp_def]
  | some limit =>
      by_cases available : state.permitted < limit
      · have positive : 0 < limit - state.permitted := by omega
        have next : limit - (state.permitted + 1) = limit - state.permitted - 1 := by omega
        simp [nativeStep, referenceStep, ContextualSourceAdmission.decode,
          ContextualSourceAdmission.remaining, ContextualSourceAdmission.room, available,
          positive, next, operation_refines sem maximum origin debit state.meter inRange,
          Option.map_map, Function.comp_def]
      · have empty : limit - state.permitted = 0 := by omega
        simp [nativeStep, referenceStep, ContextualSourceAdmission.decode,
          ContextualSourceAdmission.remaining, ContextualSourceAdmission.room, available, empty]

private theorem native_total
    (sem : Sem Value Call Effect Fault Delay Suspension Context World Worker)
    (maximum : Nat) (limit : Option Nat) (origin : SourceAccounting.Origin) (debit : Nat)
    (before after : Native Value Call Effect Fault Delay Suspension Context World Worker)
    (inRange : before.meter.state.spent + before.meter.remaining ≤ maximum)
    (advanced : nativeStep sem maximum limit origin debit before = some after) :
    after.meter.state.spent + after.meter.remaining =
      before.meter.state.spent + before.meter.remaining := by
  unfold nativeStep at advanced
  split at advanced
  · obtain ⟨next, moved, equal⟩ := Option.map_eq_some_iff.mp advanced
    subst after
    exact operation_preserves_total sem maximum origin debit before.meter next inRange moved
  · simp at advanced

/-- The occurrence reader is one immutable source-plan owner. It may select
another occurrence after a call or branch; neither machine keeps a second
binding state or reloads the entry computation between physical slices. -/
def nativeCore (sem : Sem Value Call Effect Fault Delay Suspension Context World Worker)
    (maximum : Nat) (limit : Option Nat)
    (read : Kernel Value Call Effect Fault Delay Suspension Context World Worker → SourceAccounting.Origin × Nat) :
    MachineCore (Native Value Call Effect Fault Delay Suspension Context World Worker) :=
  ⟨_, id, fun state => nativeStep sem maximum limit
    (read state.meter.state).1 (read state.meter.state).2 state⟩

def referenceCore (sem : Sem Value Call Effect Fault Delay Suspension Context World Worker)
    (read : Kernel Value Call Effect Fault Delay Suspension Context World Worker → SourceAccounting.Origin × Nat) :
    MachineCore (Reference Value Call Effect Fault Delay Suspension Context World Worker) :=
  ⟨_, id, fun state => referenceStep sem (read state.meter.state).1 (read state.meter.state).2 state⟩

theorem slice_refines
    (sem : Sem Value Call Effect Fault Delay Suspension Context World Worker)
    (maximum allowance : Nat) (limit : Option Nat)
    (read : Kernel Value Call Effect Fault Delay Suspension Context World Worker → SourceAccounting.Origin × Nat)
    (state : Native Value Call Effect Fault Delay Suspension Context World Worker)
    (inRange : state.meter.state.spent + state.meter.remaining ≤ maximum) :
    (ContextualSourceAdmission.decode limit ((nativeCore sem maximum limit read).runSlice allowance state).1,
      ((nativeCore sem maximum limit read).runSlice allowance state).2) =
      (referenceCore sem read).runSlice allowance (ContextualSourceAdmission.decode limit state) := by
  induction allowance generalizing state with
  | zero => rfl
  | succ allowance ih =>
      let receipt := read state.meter.state
      have exactStep := step_refines sem maximum limit receipt.1 receipt.2 state inRange
      have decodedRead : read (ContextualSourceAdmission.decode limit state).meter.state =
          read state.meter.state := rfl
      cases advanced : nativeStep sem maximum limit receipt.1 receipt.2 state with
      | none =>
          simp only [advanced, Option.map_none] at exactStep
          simp [MachineCore.runSlice, nativeCore, referenceCore, decodedRead, receipt, advanced, ← exactStep]
      | some next =>
          have conserved := native_total sem maximum limit receipt.1 receipt.2 state next inRange advanced
          have later := ih next (by omega)
          simp only [advanced, Option.map_some] at exactStep
          simpa only [MachineCore.runSlice, nativeCore, referenceCore, decodedRead, receipt, advanced, ← exactStep]
            using congrArg (fun result => (result.1, result.2 + 1)) later

theorem split_resume
    (sem : Sem Value Call Effect Fault Delay Suspension Context World Worker)
    (maximum first later : Nat) (limit : Option Nat)
    (read : Kernel Value Call Effect Fault Delay Suspension Context World Worker → SourceAccounting.Origin × Nat)
    (state : Native Value Call Effect Fault Delay Suspension Context World Worker) :
    (nativeCore sem maximum limit read).runSlice (first + later) state =
      let earlier := (nativeCore sem maximum limit read).runSlice first state
      let suffix := (nativeCore sem maximum limit read).runSlice later earlier.1
      (suffix.1, earlier.2 + suffix.2) :=
  MachineCore.runSlice_add (nativeCore sem maximum limit read) first later state

namespace Controls

open ContextualCBPV.Controls

abbrev TestNative := ContextualSourceAdmission.Controls.TestNative

def initialState (used credit : Nat) (code : TestCode) : TestNative :=
  ⟨⟨ContextualCBPV.initial 0 4 code, credit⟩, used⟩

def receipt : SourceAccounting.Origin := ⟨7, 11⟩

theorem physical_refusal_keeps_source_credit :
    nativeStep semantics 100 (some 0) receipt 3 (initialState 0 8 (.native 1)) = none := by rfl

theorem source_refusal_keeps_effect_unentered :
    nativeStep semantics 100 (some 8) receipt 3 (initialState 0 2 (.native 1)) = none := by rfl

theorem admitted_word_enters_once :
    (nativeStep semantics 100 (some 1) receipt 3 (initialState 0 8 (.native 1))).map
      (fun next => (next.meter.state.world, next.meter.state.nativeEntries,
        next.meter.state.spent, next.meter.remaining, next.meter.state.sourceTrace)) =
      some (1, 1, 3, 5, [receipt.encode]) := by decide +kernel

theorem zero_source_still_needs_physical_room :
    nativeStep semantics 100 (some 0) receipt 0 (initialState 0 0 (.native 1)) = none ∧
    (nativeStep semantics 100 (some 1) receipt 0 (initialState 0 0 (.native 1))).map
      (fun next => (next.meter.state.world, next.meter.state.spent)) = some (1, 0) := by decide +kernel

theorem inline_annotation_refused :
    nativeStep semantics 100 none receipt 3
      (initialState 0 8 (.source 9 2 (.native 1))) = none := by rfl

theorem completed_code_value_stays_data :
    (nativeStep semantics 100 (some 1) receipt 3
      (initialState 0 8 (.returned (.suspended 5 9)))).map
        (fun next => (next.meter.state.world, next.meter.state.nativeEntries)) = some (0, 0) := by decide +kernel

theorem derived_position_retains_unit_price (debit root : Nat) : price ⟨root, 0⟩ debit = 1 := by rfl

end Controls

end Mettapedia.Machines.SourceWordAdmission

#print axioms Mettapedia.Machines.SourceWordAdmission.operation_refines
