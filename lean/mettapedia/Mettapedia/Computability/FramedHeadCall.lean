import Mettapedia.Computability.StackMachineContextCall

/-!
# One physical source call retaining the remaining framed fields

The first delimited word is transferred to an unchanged source machine. Its
output replaces that field; the remaining framed suffix is preserved in order.
Every input, output and suffix transfer is charged. A missing first delimiter
does not silently become an empty argument. Admitted input framing is explicit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.FramedHeadCall

open Turing StateTransition Turing.TM2.Stmt

inductive Auxiliary where
  | input | argument | output | suffix | result
  deriving DecidableEq, Fintype

inductive Phase (Label : Type) where
  | read | restore | run (label : Label) | collect | copySuffix | restoreSuffix | emit
  deriving DecidableEq, Fintype

variable (source : FinTM2) [Inhabited (source.Γ source.k₀)]
  [Fintype (source.Γ source.k₁)] [Inhabited (source.Γ source.k₁)]
  (bridge : source.Γ source.k₁ ≃ source.Γ source.k₀)

local instance : Fintype source.K := source.kFin
local instance : Fintype source.Λ := source.ΛFin
local instance : Fintype source.σ := source.σFin
local instance : Fintype (source.Γ source.k₀) := source.Γk₀Fin

abbrev Key := source.K ⊕ Auxiliary
abbrev Alphabet : Key source → Type
  | .inl key => source.Γ key
  | .inr .argument => source.Γ source.k₀
  | .inr .output => source.Γ source.k₁
  | .inr .input | .inr .suffix | .inr .result => Option (source.Γ source.k₀)

abbrev Control := source.σ × Option (Option (source.Γ source.k₀)) ×
  Option (source.Γ source.k₀) × Option (source.Γ source.k₁)

def initial : Control source := (source.initialState, none, none, none)

def lift (statement : source.Stmt) : TM2.Stmt (Alphabet source) (Phase source.Λ) (Control source) :=
  StackMachineRegisters.embedStatement (Alphabet := source.Γ) (TargetAlphabet := Alphabet source)
    Sum.inl Phase.run (fun state => state.1) (fun state value => (value, state.2))
    (fun _ => rfl) (.goto (fun _ => .collect)) statement

def program : Phase source.Λ → TM2.Stmt (Alphabet source) (Phase source.Λ) (Control source)
  | .read => pop (.inr .input) (fun state value => (state.1, value, state.2.2))
      (branch (fun state => state.2.1.isSome)
        (branch (fun state => state.2.1.join.isSome)
          (push (.inr .argument) (fun state => state.2.1.join.getD default) (goto (fun _ => .read)))
          (load (fun _ => initial source) (goto (fun _ => .restore))))
        (goto (fun _ => .read)))
  | .restore => pop (.inr .argument) (fun state value => (state.1, state.2.1, value, state.2.2.2))
      (branch (fun state => state.2.2.1.isSome)
        (push (.inl source.k₀) (fun state => state.2.2.1.getD default) (goto (fun _ => .restore)))
        (load (fun _ => initial source) (goto (fun _ => .run source.main))))
  | .run label => lift source (source.m label)
  | .collect => pop (.inl source.k₁) (fun state value => (state.1, state.2.1, state.2.2.1, value))
      (branch (fun state => state.2.2.2.isSome)
        (push (.inr .output) (fun state => state.2.2.2.getD default) (goto (fun _ => .collect)))
        (load (fun _ => initial source) (goto (fun _ => .copySuffix))))
  | .copySuffix => pop (.inr .input) (fun state value => (state.1, value, state.2.2))
      (branch (fun state => state.2.1.isSome)
        (push (.inr .suffix) (fun state => state.2.1.getD none) (goto (fun _ => .copySuffix)))
        (load (fun _ => initial source) (goto (fun _ => .restoreSuffix))))
  | .restoreSuffix => pop (.inr .suffix) (fun state value => (state.1, value, state.2.2))
      (branch (fun state => state.2.1.isSome)
        (push (.inr .result) (fun state => state.2.1.getD none) (goto (fun _ => .restoreSuffix)))
        (push (.inr .result) (fun _ => none)
          (load (fun _ => initial source) (goto (fun _ => .emit)))))
  | .emit => pop (.inr .output) (fun state value => (state.1, state.2.1, state.2.2.1, value))
      (branch (fun state => state.2.2.2.isSome)
        (push (.inr .result) (fun state => some (bridge (state.2.2.2.getD default))) (goto (fun _ => .emit)))
        (load (fun _ => initial source) halt))

def machine : FinTM2 where
  K := Key source
  k₀ := .inr .input
  k₁ := .inr .result
  Γ := Alphabet source
  Λ := Phase source.Λ
  main := .read
  σ := Control source
  initialState := initial source
  m := program source bridge

attribute [local implicit_reducible] machine

def storage (contents : ∀ key, List (source.Γ key))
    (input : List (Option (source.Γ source.k₀))) (argument : List (source.Γ source.k₀))
    (output : List (source.Γ source.k₁)) (suffix result : List (Option (source.Γ source.k₀))) :
    ∀ key, List (Alphabet source key)
  | .inl key => contents key
  | .inr .input => input
  | .inr .argument => argument
  | .inr .output => output
  | .inr .suffix => suffix
  | .inr .result => result

def config (phase : Option (Phase source.Λ)) (state : Control source)
    (contents : ∀ key, List (source.Γ key))
    (input : List (Option (source.Γ source.k₀))) (argument : List (source.Γ source.k₀))
    (output : List (source.Γ source.k₁)) (suffix result : List (Option (source.Γ source.k₀))) :
    (machine source bridge).Cfg where
  l := phase
  var := state
  stk := storage source contents input argument output suffix result

omit [Inhabited (source.Γ source.k₀)] [Fintype (source.Γ source.k₁)] [Inhabited (source.Γ source.k₁)] in
theorem storage_update (contents : ∀ key, List (source.Γ key))
    (input : List (Option (source.Γ source.k₀))) (argument : List (source.Γ source.k₀))
    (output : List (source.Γ source.k₁)) (suffix result : List (Option (source.Γ source.k₀)))
    (key : source.K) (word : List (source.Γ key)) :
    storage source (Function.update contents key word) input argument output suffix result =
      Function.update (storage source contents input argument output suffix result) (.inl key) word := by
  funext target
  cases target with
  | inl target =>
      by_cases same : target = key
      · subst target; simp [storage, Function.update]
      · simp [storage, Function.update, same]
  | inr target => cases target <;> simp [storage, Function.update]

def sourceConfig (tail : List (Option (source.Γ source.k₀))) (original : source.Cfg) : (machine source bridge).Cfg :=
  config source bridge (some (original.l.elim .collect Phase.run)) (original.var, none, none, none)
    original.stk tail [] [] [] []

theorem source_step (tail : List (Option (source.Γ source.k₀))) (before after : source.Cfg)
    (advanced : source.step before = some after) :
    (machine source bridge).step (sourceConfig source bridge tail before) =
      some (sourceConfig source bridge tail after) := by
  exact StackMachineRegisters.step_embedStatement (Alphabet := source.Γ) (TargetAlphabet := Alphabet source)
    Sum.inl Phase.run .collect
    (fun state : Control source => state.1) (fun state value => (value, state.2)) (fun _ => rfl)
    (fun registers => (registers, none, none, none))
    (fun contents => storage source contents tail [] [] [] [])
    (fun _ => rfl) (fun _ _ => rfl)
    (by intro contents key; change contents key = (contents key).map id; simp)
    (by
      intro contents key word
      change storage source (Function.update contents key word) tail [] [] [] [] =
        Function.update (storage source contents tail [] [] [] []) (.inl key) (word.map id)
      simpa only [List.map_id] using storage_update source contents tail [] [] [] [] key word)
    source.m (program source bridge) before after (fun _ _ => rfl) advanced

def source_execution (tail : List (Option (source.Γ source.k₀)))
    {before after : source.Cfg} {time : Nat}
    (executed : EvalsToInTime source.step before (some after) time) :
    EvalsToInTime (machine source bridge).step (sourceConfig source bridge tail before)
      (some (sourceConfig source bridge tail after)) time :=
  StackMachineComposition.lift_execution source.step (machine source bridge).step
    (sourceConfig source bridge tail) (source_step source bridge tail) executed

local macro "head_step" : tactic => `(tactic| (
  simp [FinTM2.step, machine, program, config, storage, initial, TM2.step, TM2.stepAux]
  all_goals funext key
  all_goals cases key with
    | inl key => simp [storage, Function.update]
    | inr key => cases key <;> simp [storage, Function.update]))

theorem read_cons (state : Control source) (contents : ∀ key, List (source.Γ key))
    (symbol : source.Γ source.k₀) (input : List (Option (source.Γ source.k₀)))
    (argument : List (source.Γ source.k₀)) (output : List (source.Γ source.k₁))
    (suffix result : List (Option (source.Γ source.k₀))) :
    (machine source bridge).step (config source bridge (some .read) state contents
      (some symbol :: input) argument output suffix result) =
      some (config source bridge (some .read) (state.1, some (some symbol), state.2.2) contents
        input (symbol :: argument) output suffix result) := by head_step

theorem read_delimiter (state : Control source) (contents : ∀ key, List (source.Γ key))
    (input : List (Option (source.Γ source.k₀))) (argument : List (source.Γ source.k₀))
    (output : List (source.Γ source.k₁)) (suffix result : List (Option (source.Γ source.k₀))) :
    (machine source bridge).step (config source bridge (some .read) state contents
      (none :: input) argument output suffix result) =
      some (config source bridge (some .restore) (initial source) contents input argument output suffix result) := by head_step

theorem read_missing (state : Control source) (contents : ∀ key, List (source.Γ key))
    (argument : List (source.Γ source.k₀)) (output : List (source.Γ source.k₁))
    (suffix result : List (Option (source.Γ source.k₀))) :
    (machine source bridge).step (config source bridge (some .read) state contents [] argument output suffix result) =
      some (config source bridge (some .read) (state.1, none, state.2.2) contents [] argument output suffix result) := by head_step

def read_run (state : Control source) (contents : ∀ key, List (source.Γ key))
    (word : List (source.Γ source.k₀)) (tail : List (Option (source.Γ source.k₀)))
    (argument : List (source.Γ source.k₀)) (output : List (source.Γ source.k₁))
    (suffix result : List (Option (source.Γ source.k₀))) :
    EvalsToInTime (machine source bridge).step
      (config source bridge (some .read) state contents (word.map some ++ none :: tail) argument output suffix result)
      (some (config source bridge (some .restore) (initial source) contents tail
        (word.reverse ++ argument) output suffix result)) (word.length + 1) := by
  induction word generalizing state argument with
  | nil => simpa using StackMachineComposition.oneStep (read_delimiter source bridge state contents tail argument output suffix result)
  | cons symbol rest ih =>
      have first := StackMachineComposition.oneStep (read_cons source bridge state contents symbol
        (rest.map some ++ none :: tail) argument output suffix result)
      have later := ih (state.1, some (some symbol), state.2.2) (symbol :: argument)
      simpa only [List.map_cons, List.cons_append, List.reverse_cons, List.append_assoc,
        List.singleton_append, List.nil_append, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first later

theorem restore_cons (state : Control source) (word : List (source.Γ source.k₀))
    (tail : List (Option (source.Γ source.k₀))) (symbol : source.Γ source.k₀)
    (argument : List (source.Γ source.k₀)) :
    (machine source bridge).step (config source bridge (some .restore) state (initList source word).stk
      tail (symbol :: argument) [] [] []) =
      some (config source bridge (some .restore) (state.1, state.2.1, some symbol, state.2.2.2)
        (initList source (symbol :: word)).stk tail argument [] [] []) := by
  simp [FinTM2.step, machine, program, config, storage, initial, TM2.step, TM2.stepAux]
  funext key
  cases key with
  | inl key =>
      by_cases same : key = source.k₀
      · subst key; simp [storage, Function.update, initList]
      · simp [storage, Function.update, initList, same]
  | inr key => cases key <;> simp [storage, Function.update]

theorem restore_nil (state : Control source) (word : List (source.Γ source.k₀))
    (tail : List (Option (source.Γ source.k₀))) :
    (machine source bridge).step (config source bridge (some .restore) state (initList source word).stk tail [] [] [] []) =
      some (sourceConfig source bridge tail (initList source word)) := by
  simp [sourceConfig, config, storage, initial, FinTM2.step, machine, program, TM2.step, TM2.stepAux, initList]

def restore_run (state : Control source) (word argument : List (source.Γ source.k₀))
    (tail : List (Option (source.Γ source.k₀))) :
    EvalsToInTime (machine source bridge).step
      (config source bridge (some .restore) state (initList source word).stk tail argument [] [] [])
      (some (sourceConfig source bridge tail (initList source (argument.reverse ++ word)))) (argument.length + 1) := by
  induction argument generalizing state word with
  | nil => simpa using StackMachineComposition.oneStep (restore_nil source bridge state word tail)
  | cons symbol rest ih =>
      have first := StackMachineComposition.oneStep (restore_cons source bridge state word tail symbol rest)
      have later := ih (state.1, state.2.1, some symbol, state.2.2.2) (symbol :: word)
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first later

def prepare_run (word : List (source.Γ source.k₀)) (tail : List (Option (source.Γ source.k₀))) :
    EvalsToInTime (machine source bridge).step
      (initList (machine source bridge) (word.map some ++ none :: tail))
      (some (sourceConfig source bridge tail (initList source word))) (2 * word.length + 2) := by
  have read := read_run source bridge (initial source) (initList source []).stk word tail [] [] [] []
  have restored := restore_run source bridge (initial source) [] word.reverse tail
  have begin : config source bridge (some .read) (initial source) (initList source []).stk
      (word.map some ++ none :: tail) [] [] [] [] =
        initList (machine source bridge) (word.map some ++ none :: tail) := by
    simp only [config, initList, machine, initial]
    congr 1
    funext key
    cases key with
    | inl key =>
        by_cases same : key = source.k₀
        · subst key; simp [storage]
        · simp [storage, same]
    | inr key => cases key <;> simp [storage]
  rw [begin] at read
  simp only [List.append_nil] at read
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at restored
  have joined := EvalsToInTime.trans _ (word.length + 1) (word.length + 1) _ _ _ read restored
  exact ⟨joined.toEvalsTo, joined.steps_le_m.trans (by omega)⟩

theorem collect_cons (state : Control source) (tail : List (Option (source.Γ source.k₀)))
    (symbol : source.Γ source.k₁) (word output : List (source.Γ source.k₁)) :
    (machine source bridge).step (config source bridge (some .collect) state (haltList source (symbol :: word)).stk
      tail [] output [] []) =
      some (config source bridge (some .collect) (state.1, state.2.1, state.2.2.1, some symbol)
        (haltList source word).stk tail [] (symbol :: output) [] []) := by
  simp [FinTM2.step, machine, program, config, storage, initial, TM2.step, TM2.stepAux, haltList]
  funext key
  cases key with
  | inl key =>
      by_cases same : key = source.k₁
      · subst key; simp [storage, Function.update]
      · simp [storage, Function.update, same]
  | inr key => cases key <;> simp [storage, Function.update]

theorem collect_nil (state : Control source) (tail : List (Option (source.Γ source.k₀)))
    (output : List (source.Γ source.k₁)) :
    (machine source bridge).step (config source bridge (some .collect) state (haltList source []).stk tail [] output [] []) =
      some (config source bridge (some .copySuffix) (initial source) (fun _ => []) tail [] output [] []) := by
  simp [FinTM2.step, machine, program, config, storage, initial, TM2.step, TM2.stepAux, haltList]
  funext key
  cases key with
  | inl key =>
      by_cases same : key = source.k₁
      · subst key; simp [storage, Function.update]
      · simp [storage, Function.update, same]
  | inr key => cases key <;> simp [storage, Function.update]

def collect_run (state : Control source) (tail : List (Option (source.Γ source.k₀)))
    (word output : List (source.Γ source.k₁)) :
    EvalsToInTime (machine source bridge).step
      (config source bridge (some .collect) state (haltList source word).stk tail [] output [] [])
      (some (config source bridge (some .copySuffix) (initial source) (fun _ => []) tail []
        (word.reverse ++ output) [] [])) (word.length + 1) := by
  induction word generalizing state output with
  | nil => simpa using StackMachineComposition.oneStep (collect_nil source bridge state tail output)
  | cons symbol rest ih =>
      have first := StackMachineComposition.oneStep (collect_cons source bridge state tail symbol rest output)
      have later := ih (state.1, state.2.1, state.2.2.1, some symbol) (symbol :: output)
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first later

theorem copySuffix_cons (state : Control source) (cell : Option (source.Γ source.k₀))
    (tail suffix result : List (Option (source.Γ source.k₀))) (output : List (source.Γ source.k₁)) :
    (machine source bridge).step (config source bridge (some .copySuffix) state (fun _ => [])
      (cell :: tail) [] output suffix result) =
      some (config source bridge (some .copySuffix) (state.1, some cell, state.2.2) (fun _ => [])
        tail [] output (cell :: suffix) result) := by head_step

theorem copySuffix_nil (state : Control source) (suffix result : List (Option (source.Γ source.k₀)))
    (output : List (source.Γ source.k₁)) :
    (machine source bridge).step (config source bridge (some .copySuffix) state (fun _ => []) [] [] output suffix result) =
      some (config source bridge (some .restoreSuffix) (initial source) (fun _ => []) [] [] output suffix result) := by head_step

def copySuffix_run (state : Control source) (tail suffix result : List (Option (source.Γ source.k₀)))
    (output : List (source.Γ source.k₁)) :
    EvalsToInTime (machine source bridge).step
      (config source bridge (some .copySuffix) state (fun _ => []) tail [] output suffix result)
      (some (config source bridge (some .restoreSuffix) (initial source) (fun _ => []) [] [] output
        (tail.reverse ++ suffix) result)) (tail.length + 1) := by
  induction tail generalizing state suffix with
  | nil => simpa using StackMachineComposition.oneStep (copySuffix_nil source bridge state suffix result output)
  | cons cell rest ih =>
      have first := StackMachineComposition.oneStep (copySuffix_cons source bridge state cell rest suffix result output)
      have later := ih (state.1, some cell, state.2.2) (cell :: suffix)
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first later

theorem restoreSuffix_cons (state : Control source) (cell : Option (source.Γ source.k₀))
    (suffix result : List (Option (source.Γ source.k₀))) (output : List (source.Γ source.k₁)) :
    (machine source bridge).step (config source bridge (some .restoreSuffix) state (fun _ => [])
      [] [] output (cell :: suffix) result) =
      some (config source bridge (some .restoreSuffix) (state.1, some cell, state.2.2) (fun _ => [])
        [] [] output suffix (cell :: result)) := by head_step

theorem restoreSuffix_nil (state : Control source) (result : List (Option (source.Γ source.k₀)))
    (output : List (source.Γ source.k₁)) :
    (machine source bridge).step (config source bridge (some .restoreSuffix) state (fun _ => []) [] [] output [] result) =
      some (config source bridge (some .emit) (initial source) (fun _ => []) [] [] output [] (none :: result)) := by head_step

def restoreSuffix_run (state : Control source) (suffix result : List (Option (source.Γ source.k₀)))
    (output : List (source.Γ source.k₁)) :
    EvalsToInTime (machine source bridge).step
      (config source bridge (some .restoreSuffix) state (fun _ => []) [] [] output suffix result)
      (some (config source bridge (some .emit) (initial source) (fun _ => []) [] [] output []
        (none :: (suffix.reverse ++ result)))) (suffix.length + 1) := by
  induction suffix generalizing state result with
  | nil => simpa using StackMachineComposition.oneStep (restoreSuffix_nil source bridge state result output)
  | cons cell rest ih =>
      have first := StackMachineComposition.oneStep (restoreSuffix_cons source bridge state cell rest result output)
      have later := ih (state.1, some cell, state.2.2) (cell :: result)
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first later

theorem emit_cons (state : Control source) (symbol : source.Γ source.k₁)
    (output : List (source.Γ source.k₁)) (result : List (Option (source.Γ source.k₀))) :
    (machine source bridge).step (config source bridge (some .emit) state (fun _ => []) [] [] (symbol :: output) [] result) =
      some (config source bridge (some .emit) (state.1, state.2.1, state.2.2.1, some symbol) (fun _ => [])
        [] [] output [] (some (bridge symbol) :: result)) := by head_step

theorem emit_nil (state : Control source) (result : List (Option (source.Γ source.k₀))) :
    (machine source bridge).step (config source bridge (some .emit) state (fun _ => []) [] [] [] [] result) =
      some (haltList (machine source bridge) result) := by
  simp [FinTM2.step, machine, program, config, storage, initial, TM2.step, TM2.stepAux, haltList]
  funext key
  cases key with
  | inl key => simp [storage]
  | inr key => cases key <;> simp [storage]

def emit_run (state : Control source) (output : List (source.Γ source.k₁))
    (result : List (Option (source.Γ source.k₀))) :
    EvalsToInTime (machine source bridge).step
      (config source bridge (some .emit) state (fun _ => []) [] [] output [] result)
      (some (haltList (machine source bridge) (output.reverse.map (fun value => some (bridge value)) ++ result)))
      (output.length + 1) := by
  induction output generalizing state result with
  | nil => simpa using StackMachineComposition.oneStep (emit_nil source bridge state result)
  | cons symbol rest ih =>
      have first := StackMachineComposition.oneStep (emit_cons source bridge state symbol rest result)
      have later := ih (state.1, state.2.1, state.2.2.1, some symbol) (some (bridge symbol) :: result)
      simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        List.singleton_append, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EvalsToInTime.trans _ 1 (rest.length + 1) _ _ _ first later

def finish_run (word : List (source.Γ source.k₁)) (tail : List (Option (source.Γ source.k₀))) :
    EvalsToInTime (machine source bridge).step (sourceConfig source bridge tail (haltList source word))
      (some (haltList (machine source bridge) (word.map (fun value => some (bridge value)) ++ none :: tail)))
      (2 * word.length + 2 * tail.length + 4) := by
  have collected := collect_run source bridge (initial source) tail word []
  simp only [List.append_nil] at collected
  have copied := copySuffix_run source bridge (initial source) tail [] [] word.reverse
  simp only [List.append_nil] at copied
  have restored := restoreSuffix_run source bridge (initial source) tail.reverse [] word.reverse
  simp only [List.reverse_reverse, List.length_reverse, List.append_nil] at restored
  have emitted := emit_run source bridge (initial source) word.reverse (none :: tail)
  simp only [List.reverse_reverse, List.length_reverse] at emitted
  have first := EvalsToInTime.trans _ (word.length + 1) (tail.length + 1) _ _ _ collected copied
  have second := EvalsToInTime.trans _ ((tail.length + 1) + (word.length + 1)) (tail.length + 1) _ _ _ first restored
  have joined := EvalsToInTime.trans _ ((tail.length + 1) + ((tail.length + 1) + (word.length + 1)))
    (word.length + 1) _ _ _ second emitted
  change EvalsToInTime _ (config source bridge (some .collect) (initial source)
    (haltList source word).stk tail [] [] [] []) _ _
  exact ⟨joined.toEvalsTo, joined.steps_le_m.trans (by omega)⟩

/-- One source invocation replaces only the first complete framed field.
The tail is copied in order, with every delimiter and duplicate retained. -/
def outputs {input : List (source.Γ source.k₀)} {output : List (source.Γ source.k₁)}
    (tail : List (Option (source.Γ source.k₀))) {time : Nat}
    (executed : TM2OutputsInTime source input (some output) time) :
    TM2OutputsInTime (machine source bridge) (input.map some ++ none :: tail)
      (some (output.map (fun value => some (bridge value)) ++ none :: tail))
      (time + 2 * input.length + 2 * output.length + 2 * tail.length + 6) := by
  have prepared := prepare_run source bridge input tail
  have called := source_execution source bridge tail executed
  have finished := finish_run source bridge output tail
  have front := EvalsToInTime.trans _ (2 * input.length + 2) time _ _ _ prepared called
  have joined := EvalsToInTime.trans _ (time + (2 * input.length + 2))
    (2 * output.length + 2 * tail.length + 4) _ _ _ front finished
  exact ⟨joined.toEvalsTo, joined.steps_le_m.trans (by omega)⟩

theorem terminal_source_halts {input : List (source.Γ source.k₀)}
    (tail : List (Option (source.Γ source.k₀))) {final : (machine source bridge).Cfg} {time : Nat}
    (executed : EvalsToInTime (machine source bridge).step
      (initList (machine source bridge) (input.map some ++ none :: tail)) (some final) time)
    (stopped : final.l = none) :
    ∃ after : source.Cfg, after.l = none ∧
      Nonempty (EvalsToInTime source.step (initList source input) (some after) time) := by
  have terminalStep : (machine source bridge).step final = none := by
    cases final with
    | mk label registers contents =>
        dsimp only at stopped
        subst label
        rfl
  have afterPreparation := StackMachineContextCall.terminal_tail (machine source bridge).step
    (prepare_run source bridge input tail) executed terminalStep
  obtain ⟨after, halted, ⟨original⟩⟩ := StackMachineComposition.completed_source_prefix_generic
    source.step (machine source bridge).step (sourceConfig source bridge tail) (fun state => state.l = none)
    (by intro state; simp [sourceConfig, config]) (source_step source bridge tail)
    afterPreparation.steps (initList source input) final afterPreparation.evals_in_steps stopped
  exact ⟨after, (StackMachineComposition.source_step_none_iff source after).mp halted, ⟨{ original.toEvalsTo with
    steps_le_m := original.steps_le_m.trans afterPreparation.steps_le_m }⟩⟩

/-- Reflection uses clean halting at this admitted head only; it does not
assume anything about unrelated or malformed inputs. -/
theorem reflects_outputs_at {input : List (source.Γ source.k₀)}
    (clean : ∀ state : source.Cfg, Reaches source.step (initList source input) state → state.l = none →
      ∃ output, state = haltList source output)
    (tail : List (Option (source.Γ source.k₀))) {returned : List (Option (source.Γ source.k₀))} {time : Nat}
    (executed : TM2OutputsInTime (machine source bridge) (input.map some ++ none :: tail) (some returned) time) :
    ∃ output : List (source.Γ source.k₁),
      output.map (fun value => some (bridge value)) ++ none :: tail = returned ∧
        Nonempty (TM2OutputsInTime source input (some output) time) := by
  obtain ⟨after, stopped, ⟨prefixRun⟩⟩ := terminal_source_halts source bridge tail executed rfl
  obtain ⟨output, same⟩ := clean after (StackMachineComposition.execution_reaches prefixRun.toEvalsTo) stopped
  have original : TM2OutputsInTime source input (some output) time := by
    simpa only [TM2OutputsInTime, Option.map_some, same] using prefixRun
  exact ⟨output, StackMachineComposition.outputs_unique (outputs source bridge tail original).toTM2Outputs
    executed.toTM2Outputs, ⟨original⟩⟩

end Mettapedia.Computability.FramedHeadCall
