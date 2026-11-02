import Mettapedia.Computability.StackMachinePortTime
import Mettapedia.Computability.StackMachineCompositionReflection

/-!
# Physical source calls retaining their original arguments

The caller copies an argument into two physical stacks, restores one copy for
the original source program, then returns a tagged argument/result packet.
Source labels and registers are embedded structurally. The original argument,
intermediate words and returned packet never live in finite control registers.
All copying, reversal, delimiter and reset transitions are counted.

This is a source-call component, not an IC reconstruction or shortening test.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.StackMachineContextCall

open Turing StateTransition Turing.TM2.Stmt

inductive Auxiliary where
  | input | saved | argument | output | result
  deriving DecidableEq, Fintype

inductive Phase (Label : Type) where
  | copy | restore | run (label : Label) | scan | emit | context
  deriving DecidableEq, Fintype

variable (source : FinTM2) [Inhabited (source.Γ source.k₀)]
  [Fintype (source.Γ source.k₁)] [Inhabited (source.Γ source.k₁)]

local instance : Fintype source.K := source.kFin
local instance : Fintype source.Λ := source.ΛFin
local instance : Fintype source.σ := source.σFin
local instance : Fintype (source.Γ source.k₀) := source.Γk₀Fin

abbrev Key := source.K ⊕ Auxiliary
abbrev Cell := Option (source.Γ source.k₀ ⊕ source.Γ source.k₁)

abbrev Alphabet : Key source → Type
  | .inl key => source.Γ key
  | .inr .input | .inr .saved | .inr .argument => source.Γ source.k₀
  | .inr .output => source.Γ source.k₁
  | .inr .result => Cell source

abbrev Control := source.σ × Option (source.Γ source.k₀) × Option (source.Γ source.k₁)

/-- The original halt returns to physical output collection. -/
def lift (statement : source.Stmt) :
    TM2.Stmt (Alphabet source) (Phase source.Λ) (Control source) :=
  StackMachineRegisters.embedStatement (Alphabet := source.Γ)
    (TargetAlphabet := Alphabet source) Sum.inl Phase.run
    (fun state => state.1) (fun state value => (value, state.2))
    (fun _ => rfl) (.goto (fun _ => .scan)) statement

def program : Phase source.Λ → TM2.Stmt (Alphabet source) (Phase source.Λ) (Control source)
  | .copy => pop (.inr .input) (fun state value => (state.1, value, state.2.2))
      (branch (fun state => state.2.1.isSome)
        (push (.inr .saved) (fun state => state.2.1.getD default)
          (push (.inr .argument) (fun state => state.2.1.getD default)
            (goto (fun _ => .copy))))
        (load (fun state => (state.1, none, none)) (goto (fun _ => .restore))))
  | .restore => pop (.inr .argument) (fun state value => (state.1, value, state.2.2))
      (branch (fun state => state.2.1.isSome)
        (push (.inl source.k₀) (fun state => state.2.1.getD default) (goto (fun _ => .restore)))
        (load (fun _ => (source.initialState, none, none)) (goto (fun _ => .run source.main))))
  | .run label => lift source (source.m label)
  | .scan => pop (.inl source.k₁) (fun state value => (state.1, state.2.1, value))
      (branch (fun state => state.2.2.isSome)
        (push (.inr .output) (fun state => state.2.2.getD default) (goto (fun _ => .scan)))
        (load (fun state => (state.1, none, none)) (goto (fun _ => .emit))))
  | .emit => pop (.inr .output) (fun state value => (state.1, state.2.1, value))
      (branch (fun state => state.2.2.isSome)
        (push (.inr .result) (fun state => some (.inr (state.2.2.getD default)))
          (goto (fun _ => .emit)))
        (push (.inr .result) (fun _ => none)
          (load (fun state => (state.1, none, none)) (goto (fun _ => .context)))))
  | .context => pop (.inr .saved) (fun state value => (state.1, value, state.2.2))
      (branch (fun state => state.2.1.isSome)
        (push (.inr .result) (fun state => some (.inl (state.2.1.getD default)))
          (goto (fun _ => .context)))
        (load (fun _ => (source.initialState, none, none)) halt))

def machine : FinTM2 where
  K := Key source
  k₀ := .inr .input
  k₁ := .inr .result
  Γ := Alphabet source
  Λ := Phase source.Λ
  main := .copy
  σ := Control source
  initialState := (source.initialState, none, none)
  m := program source

attribute [local implicit_reducible] machine

/-- A delimiter cannot be confused with a symbol from either alphabet. -/
def packet (input : List (source.Γ source.k₀)) (output : List (source.Γ source.k₁)) : List (Cell source) :=
  input.map (fun value => some (.inl value)) ++ none :: output.map (fun value => some (.inr value))

omit [Inhabited (source.Γ source.k₀)] [Fintype (source.Γ source.k₁)] [Inhabited (source.Γ source.k₁)] in
theorem packet_length (input : List (source.Γ source.k₀)) (output : List (source.Γ source.k₁)) :
    (packet source input output).length = input.length + output.length + 1 := by
  simp only [packet, List.length_append, List.length_cons, List.length_map]
  omega

theorem distinct_ports : (machine source).k₀ ≠ (machine source).k₁ := by
  intro same
  cases same

def storage (contents : ∀ key, List (source.Γ key))
    (input saved argument : List (source.Γ source.k₀)) (output : List (source.Γ source.k₁))
    (result : List (Cell source)) : ∀ key, List (Alphabet source key)
  | .inl key => contents key
  | .inr .input => input
  | .inr .saved => saved
  | .inr .argument => argument
  | .inr .output => output
  | .inr .result => result

def config (phase : Option (Phase source.Λ)) (state : Control source)
    (contents : ∀ key, List (source.Γ key))
    (input saved argument : List (source.Γ source.k₀)) (output : List (source.Γ source.k₁))
    (result : List (Cell source)) : (machine source).Cfg where
  l := phase
  var := state
  stk := storage source contents input saved argument output result

omit [Inhabited (source.Γ source.k₀)] [Fintype (source.Γ source.k₁)] [Inhabited (source.Γ source.k₁)] in
theorem storage_update (contents : ∀ key, List (source.Γ key))
    (input saved argument : List (source.Γ source.k₀)) (output : List (source.Γ source.k₁))
    (result : List (Cell source)) (key : source.K) (word : List (source.Γ key)) :
    storage source (Function.update contents key word) input saved argument output result =
      Function.update (storage source contents input saved argument output result) (.inl key) word := by
  funext target
  cases target with
  | inl target =>
      by_cases same : target = key
      · subst target; simp [storage, Function.update]
      · simp [storage, Function.update, same]
  | inr target => cases target <;> simp [storage, Function.update]

def sourceConfig (saved : List (source.Γ source.k₀)) (original : source.Cfg) : (machine source).Cfg :=
  config source (some (original.l.elim .scan Phase.run)) (original.var, none, none)
    original.stk [] saved [] [] []

theorem source_step (saved : List (source.Γ source.k₀)) (before after : source.Cfg)
    (advanced : source.step before = some after) :
    (machine source).step (sourceConfig source saved before) = some (sourceConfig source saved after) := by
  exact StackMachineRegisters.step_embedStatement
    (Alphabet := source.Γ) (TargetAlphabet := Alphabet source)
    Sum.inl Phase.run .scan
    (fun state : Control source => state.1) (fun state value => (value, state.2)) (fun _ => rfl)
    (fun registers => (registers, none, none))
    (fun contents => storage source contents [] saved [] [] [])
    (fun _ => rfl) (fun _ _ => rfl)
    (by intro contents key; change contents key = (contents key).map id; simp)
    (by
      intro contents key word
      change storage source (Function.update contents key word) [] saved [] [] [] =
        Function.update (storage source contents [] saved [] [] []) (.inl key) (word.map id)
      simpa only [List.map_id] using storage_update source contents [] saved [] [] [] key word)
    source.m (program source) before after (fun _ _ => rfl) advanced

def source_execution (saved : List (source.Γ source.k₀))
    {before after : source.Cfg} {time : Nat}
    (executed : EvalsToInTime source.step before (some after) time) :
    EvalsToInTime (machine source).step (sourceConfig source saved before)
      (some (sourceConfig source saved after)) time :=
  StackMachineComposition.lift_execution source.step (machine source).step
    (sourceConfig source saved) (source_step source saved) executed

local macro "call_step" : tactic => `(tactic| (
  simp [FinTM2.step, machine, program, config, storage, TM2.step, TM2.stepAux]
  all_goals funext key
  all_goals cases key with
    | inl key => simp [Function.update, storage]
    | inr key => cases key <;> simp [Function.update, storage]))

theorem copy_cons (state : Control source) (contents : ∀ key, List (source.Γ key))
    (head : source.Γ source.k₀) (input saved argument : List (source.Γ source.k₀))
    (output : List (source.Γ source.k₁)) (result : List (Cell source)) :
    (machine source).step (config source (some .copy) state contents (head :: input) saved argument output result) =
      some (config source (some .copy) (state.1, some head, state.2.2) contents
        input (head :: saved) (head :: argument) output result) := by call_step

theorem copy_nil (state : Control source) (contents : ∀ key, List (source.Γ key))
    (saved argument : List (source.Γ source.k₀)) (output : List (source.Γ source.k₁))
    (result : List (Cell source)) :
    (machine source).step (config source (some .copy) state contents [] saved argument output result) =
      some (config source (some .restore) (state.1, none, none) contents [] saved argument output result) := by call_step

def copy_run (state : Control source) (contents : ∀ key, List (source.Γ key))
    (input saved argument : List (source.Γ source.k₀)) (output : List (source.Γ source.k₁))
    (result : List (Cell source)) :
    EvalsToInTime (machine source).step
      (config source (some .copy) state contents input saved argument output result)
      (some (config source (some .restore) (state.1, none, none) contents []
        (input.reverse ++ saved) (input.reverse ++ argument) output result)) (input.length + 1) := by
  induction input generalizing state saved argument with
  | nil => simpa using StackMachineComposition.oneStep (copy_nil source state contents saved argument output result)
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep (copy_cons source state contents head tail saved argument output result)
      have rest := ih (state.1, some head, state.2.2) (head :: saved) (head :: argument)
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
        List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

omit [Inhabited (source.Γ source.k₀)] [Fintype (source.Γ source.k₁)] [Inhabited (source.Γ source.k₁)] in
theorem initial_contents_push (word : List (source.Γ source.k₀)) (head : source.Γ source.k₀) :
    Function.update (initList source word).stk source.k₀ (head :: word) = (initList source (head :: word)).stk := by
  funext key
  by_cases same : key = source.k₀
  · subst key; simp [initList]
  · simp [initList, same]

theorem restore_cons (state : Control source) (saved word : List (source.Γ source.k₀))
    (head : source.Γ source.k₀) (argument : List (source.Γ source.k₀)) :
    (machine source).step (config source (some .restore) state (initList source word).stk [] saved (head :: argument) [] []) =
      some (config source (some .restore) (state.1, some head, state.2.2)
        (initList source (head :: word)).stk [] saved argument [] []) := by
  simp [FinTM2.step, machine, program, config, storage, TM2.step, TM2.stepAux]
  funext key
  cases key with
  | inl key =>
      by_cases same : key = source.k₀
      · subst key; simp [Function.update, storage, initList]
      · simp [Function.update, storage, initList, same]
  | inr key => cases key <;> simp [Function.update, storage]

theorem restore_nil (state : Control source) (saved word : List (source.Γ source.k₀)) :
    (machine source).step (config source (some .restore) state (initList source word).stk [] saved [] [] []) =
      some (sourceConfig source saved (initList source word)) := by
  simp [sourceConfig, FinTM2.step, machine, program, config, storage, TM2.step, TM2.stepAux, initList]

def restore_run (state : Control source) (saved word argument : List (source.Γ source.k₀)) :
    EvalsToInTime (machine source).step
      (config source (some .restore) state (initList source word).stk [] saved argument [] [])
      (some (sourceConfig source saved (initList source (argument.reverse ++ word)))) (argument.length + 1) := by
  induction argument generalizing state word with
  | nil => simpa using StackMachineComposition.oneStep (restore_nil source state saved word)
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep (restore_cons source state saved word head tail)
      have rest := ih (state.1, some head, state.2.2) (head :: word)
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
        List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

/-- Preparing the call performs two physical passes over the argument. -/
def prepare_run (input : List (source.Γ source.k₀)) :
    EvalsToInTime (machine source).step (initList (machine source) input)
      (some (sourceConfig source input.reverse (initList source input))) (2 * input.length + 2) := by
  have copied := copy_run source (source.initialState, none, none) (initList source []).stk input [] [] [] []
  have restored := restore_run source (source.initialState, none, none) input.reverse [] input.reverse
  have begin : config source (some .copy) (source.initialState, none, none)
      (initList source []).stk input [] [] [] [] = initList (machine source) input := by
    simp only [config, initList, machine]
    congr 1
    funext key
    cases key with
    | inl key =>
        by_cases same : key = source.k₀
        · subst key; simp [storage]
        · simp [storage, same]
    | inr key => cases key <;> simp [storage]
  rw [begin] at copied
  simp only [List.append_nil] at copied
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at restored
  have joined := EvalsToInTime.trans _ (input.length + 1) (input.length + 1) _ _ _ copied restored
  exact ⟨joined.toEvalsTo, joined.steps_le_m.trans (by omega)⟩

theorem scan_cons (state : Control source) (saved : List (source.Γ source.k₀))
    (head : source.Γ source.k₁) (word output : List (source.Γ source.k₁)) (result : List (Cell source)) :
    (machine source).step (config source (some .scan) state (haltList source (head :: word)).stk
      [] saved [] output result) =
      some (config source (some .scan) (state.1, state.2.1, some head) (haltList source word).stk
        [] saved [] (head :: output) result) := by
  simp [FinTM2.step, machine, program, config, storage, TM2.step, TM2.stepAux, haltList]
  funext key
  cases key with
  | inl key =>
      by_cases same : key = source.k₁
      · subst key; simp [Function.update, storage]
      · simp [Function.update, storage, same]
  | inr key => cases key <;> simp [Function.update, storage]

theorem scan_nil (state : Control source) (saved : List (source.Γ source.k₀))
    (output : List (source.Γ source.k₁)) (result : List (Cell source)) :
    (machine source).step (config source (some .scan) state (haltList source []).stk [] saved [] output result) =
      some (config source (some .emit) (state.1, none, none) (fun _ => []) [] saved [] output result) := by
  simp [FinTM2.step, machine, program, config, storage, TM2.step, TM2.stepAux, haltList]
  funext key
  cases key with
  | inl key =>
      by_cases same : key = source.k₁
      · subst key; simp [Function.update, storage]
      · simp [Function.update, storage, same]
  | inr key => cases key <;> simp [Function.update, storage]

def scan_run (state : Control source) (saved : List (source.Γ source.k₀))
    (word output : List (source.Γ source.k₁)) (result : List (Cell source)) :
    EvalsToInTime (machine source).step
      (config source (some .scan) state (haltList source word).stk [] saved [] output result)
      (some (config source (some .emit) (state.1, none, none) (fun _ => []) [] saved []
        (word.reverse ++ output) result)) (word.length + 1) := by
  induction word generalizing state output with
  | nil => simpa using StackMachineComposition.oneStep (scan_nil source state saved output result)
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep (scan_cons source state saved head tail output result)
      have rest := ih (state.1, state.2.1, some head) (head :: output)
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append,
        List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

theorem emit_cons (state : Control source) (saved : List (source.Γ source.k₀))
    (head : source.Γ source.k₁) (output : List (source.Γ source.k₁)) (result : List (Cell source)) :
    (machine source).step (config source (some .emit) state (fun _ => []) [] saved [] (head :: output) result) =
      some (config source (some .emit) (state.1, state.2.1, some head) (fun _ => [])
        [] saved [] output (some (.inr head) :: result)) := by call_step

theorem emit_nil (state : Control source) (saved : List (source.Γ source.k₀)) (result : List (Cell source)) :
    (machine source).step (config source (some .emit) state (fun _ => []) [] saved [] [] result) =
      some (config source (some .context) (state.1, none, none) (fun _ => []) [] saved [] [] (none :: result)) := by call_step

def emit_run (state : Control source) (saved : List (source.Γ source.k₀))
    (output : List (source.Γ source.k₁)) (result : List (Cell source)) :
    EvalsToInTime (machine source).step
      (config source (some .emit) state (fun _ => []) [] saved [] output result)
      (some (config source (some .context) (state.1, none, none) (fun _ => []) [] saved [] []
        (none :: (output.reverse.map (fun value => some (.inr value)) ++ result)))) (output.length + 1) := by
  induction output generalizing state result with
  | nil => simpa using StackMachineComposition.oneStep (emit_nil source state saved result)
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep (emit_cons source state saved head tail result)
      have rest := ih (state.1, state.2.1, some head) (some (.inr head) :: result)
      simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

theorem context_cons (state : Control source) (head : source.Γ source.k₀)
    (saved : List (source.Γ source.k₀)) (result : List (Cell source)) :
    (machine source).step (config source (some .context) state (fun _ => []) [] (head :: saved) [] [] result) =
      some (config source (some .context) (state.1, some head, state.2.2) (fun _ => [])
        [] saved [] [] (some (.inl head) :: result)) := by call_step

theorem context_nil (state : Control source) (result : List (Cell source)) :
    (machine source).step (config source (some .context) state (fun _ => []) [] [] [] [] result) =
      some (haltList (machine source) result) := by
  simp [FinTM2.step, machine, program, config, storage, TM2.step, TM2.stepAux, haltList]
  funext key
  cases key with
  | inl key => simp [storage]
  | inr key => cases key <;> simp [storage]

def context_run (state : Control source) (saved : List (source.Γ source.k₀)) (result : List (Cell source)) :
    EvalsToInTime (machine source).step
      (config source (some .context) state (fun _ => []) [] saved [] [] result)
      (some (haltList (machine source) (saved.reverse.map (fun value => some (.inl value)) ++ result)))
      (saved.length + 1) := by
  induction saved generalizing state result with
  | nil => simpa using StackMachineComposition.oneStep (context_nil source state result)
  | cons head tail ih =>
      have first := StackMachineComposition.oneStep (context_cons source state head tail result)
      have rest := ih (state.1, some head, state.2.2) (some (.inl head) :: result)
      simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest

/-- Output collection, framing and restoration retain every original cell. -/
def finish_run (input : List (source.Γ source.k₀)) (output : List (source.Γ source.k₁)) :
    EvalsToInTime (machine source).step (sourceConfig source input.reverse (haltList source output))
      (some (haltList (machine source) (packet source input output)))
      (input.length + 2 * output.length + 3) := by
  have scanned := scan_run source (source.initialState, none, none) input.reverse output [] []
  have emitted := emit_run source (source.initialState, none, none) input.reverse output.reverse []
  have restored := context_run source (source.initialState, none, none) input.reverse
    (none :: output.map (fun value => some (.inr value)))
  simp only [List.append_nil] at scanned
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at emitted restored
  have front := EvalsToInTime.trans _ (output.length + 1) (output.length + 1) _ _ _ scanned emitted
  have joined := EvalsToInTime.trans _ ((output.length + 1) + (output.length + 1))
    (input.length + 1) _ _ _ front restored
  change EvalsToInTime _ (config source (some .scan) (source.initialState, none, none)
    (haltList source output).stk [] input.reverse [] [] []) _ _
  exact ⟨joined.toEvalsTo, joined.steps_le_m.trans (by omega)⟩

/-- A genuine source execution gives a physical context-preserving call.
The bound includes every argument and output transfer. -/
def outputs {input : List (source.Γ source.k₀)} {output : List (source.Γ source.k₁)} {time : Nat}
    (executed : TM2OutputsInTime source input (some output) time) :
    TM2OutputsInTime (machine source) input (some (packet source input output))
      (time + 3 * input.length + 2 * output.length + 5) := by
  have prepared := prepare_run source input
  have called := source_execution source input.reverse executed
  have finished := finish_run source input output
  have front := EvalsToInTime.trans _ (2 * input.length + 2) time _ _ _ prepared called
  have joined := EvalsToInTime.trans _ (time + (2 * input.length + 2))
    (input.length + 2 * output.length + 3) _ _ _ front finished
  exact ⟨joined.toEvalsTo, joined.steps_le_m.trans (by omega)⟩

def outputs_linear (distinct : source.k₀ ≠ source.k₁)
    {input : List (source.Γ source.k₀)} {output : List (source.Γ source.k₁)} {time : Nat}
    (executed : TM2OutputsInTime source input (some output) time) :
    TM2OutputsInTime (machine source) input (some (packet source input output))
      ((1 + 3 * StackMachinePortTime.machinePopBound source +
        2 * StackMachineSpaceGrowth.machinePushBound source) * time + 5) := by
  have called := outputs source executed
  have sizes := StackMachinePortTime.io_lengths_le source distinct executed
  exact ⟨called.toEvalsTo, called.steps_le_m.trans (by nlinarith)⟩

/-- In-place sources pay explicitly for retaining their original argument. -/
def outputs_with_input_charge
    {input : List (source.Γ source.k₀)} {output : List (source.Γ source.k₁)} {time : Nat}
    (executed : TM2OutputsInTime source input (some output) time) :
    TM2OutputsInTime (machine source) input (some (packet source input output))
      ((1 + 2 * StackMachineSpaceGrowth.machinePushBound source) * time + 5 * input.length + 5) := by
  have called := outputs source executed
  have size := StackMachineSpaceGrowth.output_length_le source executed
  exact ⟨called.toEvalsTo, called.steps_le_m.trans (by nlinarith)⟩

/-- A completed deterministic run cannot stop before a known successful
prefix. Removing that prefix retains a counted suffix in the full budget. -/
def terminal_tail {Cfg : Type} (step : Cfg → Option Cfg)
    {before middle final : Cfg} {prefixBound totalBound : Nat}
    (prefixRun : EvalsToInTime step before (some middle) prefixBound)
    (fullRun : EvalsToInTime step before (some final) totalBound) (stopped : step final = none) :
    EvalsToInTime step middle (some final) totalBound := by
  have shorter : prefixRun.steps ≤ fullRun.steps := by
    by_contra contrary
    let rest := prefixRun.steps - fullRun.steps - 1
    have lengths : prefixRun.steps = (rest + 1) + fullRun.steps := by dsimp only [rest]; omega
    have impossible := prefixRun.evals_in_steps
    rw [lengths, Function.iterate_add_apply, fullRun.evals_in_steps] at impossible
    simp only [Function.iterate_succ_apply, flip, Option.bind_eq_bind, Option.bind_some, stopped] at impossible
    have empty : (flip Option.bind step)^[rest] none = none := Function.iterate_fixed (by rfl) rest
    rw [empty] at impossible
    cases impossible
  have lengths : fullRun.steps = (fullRun.steps - prefixRun.steps) + prefixRun.steps := by omega
  refine ⟨⟨fullRun.steps - prefixRun.steps, ?_⟩,
    (Nat.sub_le fullRun.steps prefixRun.steps).trans fullRun.steps_le_m⟩
  have ran := fullRun.evals_in_steps
  rw [lengths, Function.iterate_add_apply, prefixRun.evals_in_steps] at ran
  exact ran

theorem sourceConfig_not_halted (saved : List (source.Γ source.k₀)) (state : source.Cfg) :
    (sourceConfig source saved state).l ≠ none := by
  simp only [sourceConfig, config, ne_eq, Option.some_ne_none, not_false_eq_true]

/-- A terminal caller trace contains a terminal original source prefix,
even when no successful source execution was supplied in advance. -/
theorem completed_source_prefix (saved : List (source.Γ source.k₀))
    (count : Nat) (before : source.Cfg) (final : (machine source).Cfg)
    (ran : (flip bind (machine source).step)^[count] (some (sourceConfig source saved before)) = some final)
    (stopped : final.l = none) :
    ∃ after : source.Cfg, after.l = none ∧ Nonempty (EvalsToInTime source.step before (some after) count) := by
  obtain ⟨after, halted, execution⟩ := StackMachineComposition.completed_source_prefix_generic
    source.step (machine source).step (sourceConfig source saved) (fun state => state.l = none)
    (sourceConfig_not_halted source saved) (source_step source saved) count before final ran stopped
  exact ⟨after, (StackMachineComposition.source_step_none_iff source after).mp halted, execution⟩

theorem terminal_source_halts
    {input : List (source.Γ source.k₀)} {final : (machine source).Cfg} {time : Nat}
    (executed : EvalsToInTime (machine source).step (initList (machine source) input) (some final) time)
    (halted : final.l = none) :
    ∃ after : source.Cfg, after.l = none ∧
      Nonempty (EvalsToInTime source.step (initList source input) (some after) time) := by
  have stopped : (machine source).step final = none := by
    cases final with
    | mk label registers contents =>
        dsimp only at halted
        subst label
        rfl
  have tail := terminal_tail (machine source).step (prepare_run source input) executed stopped
  obtain ⟨after, done, ⟨original⟩⟩ := completed_source_prefix source input.reverse
    tail.steps (initList source input) final tail.evals_in_steps halted
  exact ⟨after, done, ⟨{ original.toEvalsTo with
    steps_le_m := original.steps_le_m.trans tail.steps_le_m }⟩⟩

theorem clean_halts_at (input : List (source.Γ source.k₀))
    (clean : ∀ (state : source.Cfg),
      Reaches source.step (initList source input) state → state.l = none →
        ∃ output : List (source.Γ source.k₁), state = haltList source output)
    (state : (machine source).Cfg)
    (path : Reaches (machine source).step (initList (machine source) input) state) (stopped : state.l = none) :
    ∃ output : List (Cell source), state = haltList (machine source) output := by
  obtain ⟨actual⟩ := StackMachineComposition.reaches_has_execution path
  let counted : EvalsToInTime (machine source).step (initList (machine source) input) (some state) actual.steps :=
    ⟨actual, le_rfl⟩
  obtain ⟨firstHalt, halted, ⟨firstRun⟩⟩ := terminal_source_halts source counted stopped
  obtain ⟨output, same⟩ := clean firstHalt
    (StackMachineComposition.execution_reaches firstRun.toEvalsTo) halted
  have original : TM2OutputsInTime source input (some output) actual.steps := by
    simpa only [TM2OutputsInTime, Option.map_some, same] using firstRun
  have expected := outputs source original
  have stateStopped : (machine source).step state = none := by
    cases state with
    | mk label registers contents =>
        dsimp only at stopped
        subst label
        rfl
  have actualValue : state ∈ StateTransition.eval (machine source).step (initList (machine source) input) :=
    StateTransition.mem_eval.mpr ⟨path, stateStopped⟩
  have canonical : haltList (machine source) (packet source input output) ∈
      StateTransition.eval (machine source).step (initList (machine source) input) :=
    StateTransition.mem_eval.mpr ⟨StackMachineComposition.execution_reaches expected.toEvalsTo, by rfl⟩
  exact ⟨packet source input output, Part.mem_unique actualValue canonical⟩

theorem clean_halts
    (clean : ∀ (input : List (source.Γ source.k₀)) (state : source.Cfg),
      Reaches source.step (initList source input) state → state.l = none →
        ∃ output : List (source.Γ source.k₁), state = haltList source output)
    (input : List (source.Γ source.k₀)) (state : (machine source).Cfg)
    (path : Reaches (machine source).step (initList (machine source) input) state) (stopped : state.l = none) :
    ∃ output : List (Cell source), state = haltList (machine source) output :=
  clean_halts_at source input (clean input) state path stopped

/-- Every returned packet reflects an actual original run in the same
budget. Clean halting is required only at this admitted input. -/
theorem reflects_outputs_at {input : List (source.Γ source.k₀)}
    (clean : ∀ (state : source.Cfg),
      Reaches source.step (initList source input) state → state.l = none →
        ∃ output : List (source.Γ source.k₁), state = haltList source output)
    {returned : List (Cell source)} {time : Nat}
    (executed : TM2OutputsInTime (machine source) input (some returned) time) :
    ∃ output : List (source.Γ source.k₁), packet source input output = returned ∧
      Nonempty (TM2OutputsInTime source input (some output) time) := by
  obtain ⟨after, stopped, ⟨prefixRun⟩⟩ := terminal_source_halts source executed rfl
  obtain ⟨output, same⟩ := clean after
    (StackMachineComposition.execution_reaches prefixRun.toEvalsTo) stopped
  have original : TM2OutputsInTime source input (some output) time := by
    simpa only [TM2OutputsInTime, Option.map_some, same] using prefixRun
  exact ⟨output, StackMachineComposition.outputs_unique
    (outputs source original).toTM2Outputs executed.toTM2Outputs, ⟨original⟩⟩

theorem reflects_outputs
    (clean : ∀ (input : List (source.Γ source.k₀)) (state : source.Cfg),
      Reaches source.step (initList source input) state → state.l = none →
        ∃ output : List (source.Γ source.k₁), state = haltList source output)
    {input : List (source.Γ source.k₀)} {returned : List (Cell source)} {time : Nat}
    (executed : TM2OutputsInTime (machine source) input (some returned) time) :
    ∃ output : List (source.Γ source.k₁), packet source input output = returned ∧
      Nonempty (TM2OutputsInTime source input (some output) time) :=
  reflects_outputs_at source (clean input) executed

end Mettapedia.Computability.StackMachineContextCall
