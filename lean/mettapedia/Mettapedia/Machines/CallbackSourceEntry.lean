import Mettapedia.Machines.SourceAccounting

/-!
# Callback entry selects the complete canonical source schedule

A computation owns a retained canonical instruction schedule. Its entrance,
operand and body visits are already in that schedule; entry selection does not
invent a further debit. A completed packet has no computation entrance at all.
A computation that eventually returns the same packet nevertheless executes and
pays its actual schedule.

The independent finite source consumes charged jobs. The native algorithm reads
instructions at a retained program counter and uses the maintained bounded-word
account. Both honor physical slices. With an unbounded granted purse, a direct
program-counter loop refines recursive job execution without maintaining a fuel
ledger. Worlds and pending work still agree, not only the final answer bag.

Instructions may act on any world, including the maintained contextual CBPV
state, so bindings, effects and pending continuations are not reconstructed or
assumed idempotent. This does not derive the schedule of arbitrary source text,
certify C dialect elaboration or a primitive worker's implementation, or identify
an expression that looks like a value with a delivered completed packet. Those
are native correspondence obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CallbackSourceEntry

open ContextualCBPV.EpisodeAccounting
open SourceAccounting

variable {World Packet : Type}

/-- Source interpretation with no granted finite purse. It neither charges nor
refunds an inactive ledger, but retains all unexecuted jobs. -/
def unboundedSourceStep (state : Source World) : Option (Source World) :=
  match state.pending with
  | [] => none
  | first :: rest => some {state with pending := rest, world := first.execute state.world}

/-- The unbounded specialization reads program-owned operands at its current
counter. It does not restart a callback or rebuild a source suffix. -/
def unboundedNativeStep (state : Compiled World) : Option (Compiled World) :=
  match state.code.drop state.pc with
  | [] => none
  | first :: _ => some {state with pc := state.pc + 1, world := first.execute state.world}

theorem unbounded_step_refines (state : Compiled World) :
    unboundedSourceStep (decode state) = (unboundedNativeStep state).map decode := by
  cases pending : state.code.drop state.pc with
  | nil => simp [unboundedSourceStep, unboundedNativeStep, decode, pending]
  | cons first rest =>
      have tail := drop_next state.code state.pc first rest pending
      simp [unboundedSourceStep, unboundedNativeStep, decode, pending, tail]

def unboundedSourceCore : MachineCore (Source World) :=
  ⟨_, id, unboundedSourceStep⟩

def unboundedNativeCore : MachineCore (Compiled World) :=
  ⟨_, id, unboundedNativeStep⟩

/-- Direct execution agrees for every physical prefix, with exact world,
remaining jobs and actual number of admitted visits. -/
theorem unbounded_slice_refines (allowance : Nat) (state : Compiled World) :
    (unboundedSourceCore.runSlice allowance (decode state)).1 =
        decode (unboundedNativeCore.runSlice allowance state).1 ∧
      (unboundedSourceCore.runSlice allowance (decode state)).2 =
        (unboundedNativeCore.runSlice allowance state).2 := by
  induction allowance generalizing state with
  | zero => exact ⟨rfl, rfl⟩
  | succ allowance ih =>
      have localLaw := unbounded_step_refines state
      cases advanced : unboundedNativeStep state with
      | none =>
          simp only [advanced, Option.map_none] at localLaw
          simp [MachineCore.runSlice, unboundedSourceCore, unboundedNativeCore,
            localLaw, advanced]
      | some next =>
          simp only [advanced, Option.map_some] at localLaw
          have later := ih next
          simpa only [MachineCore.runSlice, unboundedSourceCore, unboundedNativeCore,
            localLaw, advanced] using ⟨later.1, congrArg (· + 1) later.2⟩

def sourceRun (_maximum allowance : Nat) (credit : Option Nat) (state : Source World) :
    Source World × Nat :=
  match credit with
  | none => unboundedSourceCore.runSlice allowance state
  | some remaining => sourceCore.runSlice allowance
      {state with purse := ⟨remaining, 0⟩}

def nativeRun (maximum allowance : Nat) (credit : Option Nat) (state : Compiled World) :
    Compiled World × Nat :=
  match credit with
  | none => unboundedNativeCore.runSlice allowance state
  | some remaining => (compiledCore maximum).runSlice allowance
      {state with purse := ⟨remaining, 0⟩}

/-- Routing a finite callback to the whole canonical schedule preserves source
and physical refusal. No extra wrapper debit precedes the canonical entrance. -/
theorem selected_schedule_refines (maximum allowance : Nat) (credit : Option Nat)
    (state : Compiled World) (inRange : ∀ amount, credit = some amount → amount ≤ maximum) :
    (sourceRun maximum allowance credit (decode state)).1 =
        decode (nativeRun maximum allowance credit state).1 ∧
      (sourceRun maximum allowance credit (decode state)).2 =
        (nativeRun maximum allowance credit state).2 := by
  cases credit with
  | none => exact unbounded_slice_refines allowance state
  | some amount =>
      have bounded : amount ≤ maximum := inRange amount rfl
      have refined := SourceAccounting.slice_refines maximum allowance
        {state with purse := ⟨amount, 0⟩} (by simpa using bounded)
      exact refined

/-- A request for unlimited credit cannot discard a finite inherited purse. -/
theorem inherited_finite_uses_canonical (requested : Option Nat) (available : Nat)
    (state : Compiled World) (maximum allowance : Nat) :
    nativeRun maximum allowance (grant requested (some available)) state =
      (compiledCore maximum).runSlice allowance
        {state with purse := ⟨(requested.map (min available)).getD available, 0⟩} := by
  cases requested with
  | none => rfl
  | some requested =>
      simp only [grant, nativeRun, Option.map_some, Option.getD_some, Nat.min_comm]
      rfl

inductive Input (World Packet : Type) where
  | completed (packet : Packet)
  | computation (root : Nat) (instructions : List (Instruction World))
      (result : World → Packet)

structure Observation (World Packet : Type) where
  residual : Source World
  packet : Option Packet
  visits : Nat

/-- Independent source loading: each instruction becomes one retained job.
No entry-selection instruction is added before these jobs. -/
def loadSource (root : Nat) (instructions : List (Instruction World))
    (world : World) : Source World :=
  ⟨instructions.map (fun instruction =>
      ⟨⟨root, instruction.position⟩, instruction.charge, instruction.execute⟩),
    world, ⟨0, 0⟩, []⟩

/-- Native loading retains the single program owner and starts its counter. -/
def loadNative (root : Nat) (instructions : List (Instruction World))
    (world : World) : Compiled World :=
  ⟨root, instructions, 0, world, ⟨0, 0⟩, []⟩

private theorem load_refines (root : Nat) (instructions : List (Instruction World))
    (world : World) : decode (loadNative root instructions world) =
      loadSource root instructions world := by rfl

/-- Publication reads only a completed schedule. A partial world and its
residual survive a refused debit without certifying a completed answer. -/
def observe (read : World → Packet) (run : Source World × Nat) : Observation World Packet :=
  ⟨run.1, if run.1.pending.isEmpty then some (read run.1.world) else none, run.2⟩

def sourceEntry (maximum allowance : Nat) (requested inherited : Option Nat)
    (world : World) (input : Input World Packet) : Observation World Packet :=
  match input with
  | .completed packet =>
      ⟨{loadSource 0 [] world with purse := ⟨(grant requested inherited).getD 0, 0⟩},
        some packet, 0⟩
  | .computation root instructions read => observe read
      (sourceRun maximum allowance (grant requested inherited)
        (loadSource root instructions world))

def nativeEntry (maximum allowance : Nat) (requested inherited : Option Nat)
    (world : World) (input : Input World Packet) : Observation World Packet :=
  match input with
  | .completed packet =>
      ⟨decode {loadNative 0 [] world with purse := ⟨(grant requested inherited).getD 0, 0⟩},
        some packet, 0⟩
  | .computation root instructions read =>
      let run := nativeRun maximum allowance (grant requested inherited)
        (loadNative root instructions world)
      ⟨decode run.1, if run.1.pc < run.1.code.length then none else some (read run.1.world),
        run.2⟩

/-- Finite and unlimited entry agree on full worlds, exact retained source
work, publication, source receipt trace and the physical prefix. -/
theorem entry_refines (maximum allowance : Nat) (requested inherited : Option Nat)
    (world : World) (input : Input World Packet)
    (inRange : ∀ amount, grant requested inherited = some amount → amount ≤ maximum) :
    nativeEntry maximum allowance requested inherited world input =
      sourceEntry maximum allowance requested inherited world input := by
  cases input with
  | completed packet => rfl
  | computation root instructions read =>
      have joined := selected_schedule_refines maximum allowance (grant requested inherited)
        (loadNative root instructions world) inRange
      rw [load_refines] at joined
      simp only [nativeEntry, sourceEntry, observe]
      rw [joined.1, joined.2]
      simp only [decode, List.isEmpty_map]
      split <;> simp_all

/-- A delivered packet has no source entrance, regardless of its value's
shape, requested credit, inherited credit or the physical computation window. -/
theorem delivered_packet_no_entry (maximum allowance : Nat) (requested inherited : Option Nat)
    (world : World) (packet : Packet) :
    nativeEntry maximum allowance requested inherited world (.completed packet) =
      ⟨{loadSource 0 [] world with purse := ⟨(grant requested inherited).getD 0, 0⟩},
        some packet, 0⟩ := by rfl

theorem delivered_packet_keeps_unused_credit (maximum allowance credit : Nat)
    (requested inherited : Option Nat) (world : World) (packet : Packet)
    (finite : grant requested inherited = some credit) :
    let returned := nativeEntry maximum allowance requested inherited world (.completed packet)
    returned.residual.purse.remaining = credit ∧ returned.residual.purse.spent = 0 ∧
      returned.residual.world = world ∧ returned.residual.trace = [] := by
  simp [nativeEntry, finite, decode, loadNative]

/-- No source suffix is recreated by splitting a finite worker's physical
allowance. Actual spent credit and committed world effects remain in it. -/
theorem finite_split_resume (maximum first later credit : Nat) (state : Compiled World) :
    (compiledCore maximum).runSlice (first + later) {state with purse := ⟨credit, 0⟩} =
      let earlier := (compiledCore maximum).runSlice first {state with purse := ⟨credit, 0⟩}
      let suffix := (compiledCore maximum).runSlice later earlier.1
      (suffix.1, earlier.2 + suffix.2) :=
  SourceAccounting.split_resume maximum first later _

theorem unbounded_split_resume (first later : Nat) (state : Compiled World) :
    unboundedNativeCore.runSlice (first + later) state =
      let earlier := unboundedNativeCore.runSlice first state
      let suffix := unboundedNativeCore.runSlice later earlier.1
      (suffix.1, earlier.2 + suffix.2) :=
  MachineCore.runSlice_add unboundedNativeCore first later state

namespace Controls

inductive Value where
  | data (value : Nat)
  | code (value : Nat)
  deriving DecidableEq, Repr

abbrev TestInput := Input (List Nat) Value

def effect (position debit event : Nat) : Instruction (List Nat) :=
  ⟨position, debit, fun world => world ++ [event]⟩

/-- Canonical entrance can comprise several visits. Their exact existing
prices belong here, not to a universal callback overhead. -/
def work : TestInput :=
  .computation 9 [effect 1 1 10, effect 2 1 20, effect 3 3 30]
    (fun world => .data world.length)

def run (source physical : Nat) : Observation (List Nat) Value :=
  nativeEntry 100 physical none (some source) [] work

theorem source_and_physical_prefixes_separate :
    (run 0 10).residual.world = [] ∧ (run 0 10).packet = none ∧
      (run 1 10).residual.world = [10] ∧ (run 1 10).residual.purse.spent = 1 ∧
      (run 2 10).residual.world = [10, 20] ∧ (run 2 10).packet = none ∧
      (run 5 0).residual.world = [] ∧ (run 5 0).residual.purse.spent = 0 ∧
      (run 5 1).residual.world = [10] ∧ (run 5 1).residual.purse.remaining = 4 ∧
      (run 5 2).residual.world = [10,20] ∧ (run 5 2).packet = none ∧
      (run 5 10).residual.world = [10,20,30] ∧ (run 5 10).packet = some (.data 3) := by
  decide +kernel

theorem computation_return_is_not_delivered_data :
    let scheduled : TestInput := .computation 9 [effect 1 2 10] (fun _ => .code 77)
    let pending := nativeEntry 100 8 none (some 1) [] scheduled
    let returned := nativeEntry 100 0 none (some 0) []
      (.completed (Value.code 77) : TestInput)
    pending.packet = none ∧ pending.residual.world = [] ∧
      returned.packet = some (.code 77) ∧ returned.residual.world = [] := by
  decide +kernel

/-- Skipping entry admission executes effects past the source prefix. -/
theorem omitting_source_admission_is_detected :
    (nativeEntry 100 8 none none [] work).residual.world = [10,20,30] ∧
      (run 1 8).residual.world = [10] ∧
      (nativeEntry 100 8 none none [] work).residual.world ≠ (run 1 8).residual.world := by
  decide +kernel

/-- An invented wrapper visit moves the exact effect threshold. -/
theorem extra_entry_charge_is_detected :
    let ordinary : TestInput := .computation 9 [effect 1 2 10] (fun _ => .data 1)
    let doubled : TestInput := .computation 9 [⟨0, 0, id⟩, effect 1 2 10] (fun _ => .data 1)
    (nativeEntry 100 8 none (some 2) [] ordinary).residual.world = [10] ∧
      (nativeEntry 100 8 none (some 2) [] ordinary).packet = some (.data 1) ∧
      (nativeEntry 100 8 none (some 2) [] doubled).packet = none ∧
      (nativeEntry 100 8 none (some 2) [] doubled).residual.world = [] ∧
      (nativeEntry 100 8 none (some 2) [] doubled).residual.purse.spent = 1 := by
  decide +kernel

theorem authored_zero_and_derived_unit_stay_distinct :
    let authored : TestInput := .computation 9 [effect 1 0 7] (fun _ => .data 7)
    let derived : TestInput := .computation 9 [effect 0 0 7] (fun _ => .data 7)
    (nativeEntry 100 0 none (some 0) [] authored).packet = none ∧
      (nativeEntry 100 1 none (some 0) [] authored).packet = some (.data 7) ∧
      (nativeEntry 100 1 none (some 0) [] derived).packet = none ∧
      (nativeEntry 100 1 none (some 1) [] derived).packet = some (.data 7) := by
  decide +kernel

theorem unbounded_entry_retains_order_and_occurrences :
    let repeated : TestInput := .computation 9 [effect 1 1 7, effect 2 1 7]
      (fun world => .data world.length)
    (nativeEntry 100 1 none none [] repeated).residual.world = [7] ∧
      (nativeEntry 100 1 none none [] repeated).packet = none ∧
      (nativeEntry 100 8 none none [] repeated).residual.world = [7,7] ∧
      (nativeEntry 100 8 none none [] repeated).packet = some (.data 2) := by
  decide +kernel

end Controls
end Mettapedia.Machines.CallbackSourceEntry

#print axioms Mettapedia.Machines.CallbackSourceEntry.unbounded_step_refines
#print axioms Mettapedia.Machines.CallbackSourceEntry.unbounded_slice_refines
#print axioms Mettapedia.Machines.CallbackSourceEntry.selected_schedule_refines
#print axioms Mettapedia.Machines.CallbackSourceEntry.inherited_finite_uses_canonical
#print axioms Mettapedia.Machines.CallbackSourceEntry.entry_refines
#print axioms Mettapedia.Machines.CallbackSourceEntry.delivered_packet_no_entry
#print axioms Mettapedia.Machines.CallbackSourceEntry.delivered_packet_keeps_unused_credit
#print axioms Mettapedia.Machines.CallbackSourceEntry.finite_split_resume
#print axioms Mettapedia.Machines.CallbackSourceEntry.unbounded_split_resume
#print axioms Mettapedia.Machines.CallbackSourceEntry.Controls.source_and_physical_prefixes_separate
#print axioms Mettapedia.Machines.CallbackSourceEntry.Controls.computation_return_is_not_delivered_data
#print axioms Mettapedia.Machines.CallbackSourceEntry.Controls.omitting_source_admission_is_detected
#print axioms Mettapedia.Machines.CallbackSourceEntry.Controls.extra_entry_charge_is_detected
#print axioms Mettapedia.Machines.CallbackSourceEntry.Controls.authored_zero_and_derived_unit_stay_distinct
#print axioms Mettapedia.Machines.CallbackSourceEntry.Controls.unbounded_entry_retains_order_and_occurrences
