import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Tactic
import Mettapedia.Computability.StackMachineRegisters

/-!
# Sequential composition of finite stack machines

The two programs retain separate stack arenas. A two-pass transfer moves the
first output to the second input through an alphabet equivalence, preserving
the physical word order. The transfer has its own finite control and temporary
stack; no intermediate word is stored in an internal machine variable.
`Dispatch` consumes a finite status symbol, executes the selected program on
the remaining physical input, and drains refused inputs before returning the
fixed failure output. All branch and cleanup transitions are counted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.StackMachineComposition

open Turing StateTransition
open Turing.TM2.Stmt

/-- A proved machine equality transports the existing counted run, including
its physical input and output. No execution or clock is replaced. -/
def outputs_of_machine_eq {first second : FinTM2} (same : first = second)
    {firstInput : List (first.Γ first.k₀)} {secondInput : List (second.Γ second.k₀)}
    {firstOutput : Option (List (first.Γ first.k₁))} {secondOutput : Option (List (second.Γ second.k₁))}
    {bound : Nat} (sameInput : HEq firstInput secondInput) (sameOutput : HEq firstOutput secondOutput)
    (executed : TM2OutputsInTime first firstInput firstOutput bound) :
    TM2OutputsInTime second secondInput secondOutput bound := by
  cases same
  cases sameInput
  cases sameOutput
  exact executed

private theorem reaches_of_iteration {S : Type} (step : S → Option S) :
    ∀ (count : Nat) (start finish : S),
      (fun state : Option S => state.bind step)^[count] (some start) = some finish →
        Reaches step start finish := by
  intro count
  induction count with
  | zero =>
      intro start finish ran
      simp only [Function.iterate_zero_apply, Option.some.injEq] at ran
      subst finish
      exact Relation.ReflTransGen.refl
  | succ count ih =>
      intro start finish ran
      rw [Function.iterate_succ_apply] at ran
      cases next : step start with
      | none =>
          simp only [Option.bind_some, next] at ran
          have empty : (fun state : Option S => state.bind step)^[count] none = none :=
            Function.iterate_fixed (by rfl) count
          rw [empty] at ran
          contradiction
      | some middle =>
          simp only [Option.bind_some, next] at ran
          exact Relation.ReflTransGen.head next (ih middle finish ran)

/-- Expose the path carried by a counted original execution. -/
theorem execution_reaches {S : Type} {step : S → Option S} {before after : S}
    (execution : EvalsTo step before (some after)) : Reaches step before after :=
  reaches_of_iteration step execution.steps before after execution.evals_in_steps

/-- Two halting executions of one deterministic finite stack machine return
the same physical output word. -/
theorem outputs_unique {machine : FinTM2} {input : List (machine.Γ machine.k₀)}
    {first second : List (machine.Γ machine.k₁)}
    (firstRun : TM2Outputs machine input (some first))
    (secondRun : TM2Outputs machine input (some second)) : first = second := by
  have firstReached := reaches_of_iteration machine.step firstRun.steps
    (initList machine input) (haltList machine first) firstRun.evals_in_steps
  have secondReached := reaches_of_iteration machine.step secondRun.steps
    (initList machine input) (haltList machine second) secondRun.evals_in_steps
  have same := Part.mem_unique
    (StateTransition.mem_eval.mpr ⟨firstReached, by rfl⟩)
    (StateTransition.mem_eval.mpr ⟨secondReached, by rfl⟩)
  have words := congrArg (fun state : machine.Cfg => state.stk machine.k₁) same
  simpa [haltList] using words


namespace Programs

variable {FirstKey SecondKey FirstLabel SecondLabel FirstState SecondState : Type}
  {FirstAlphabet : FirstKey → Type} {SecondAlphabet : SecondKey → Type}

abbrev Key (FirstKey SecondKey : Type) := Option (FirstKey ⊕ SecondKey)

abbrev Cells (outputKey : FirstKey) : Key FirstKey SecondKey → Type
  | none => FirstAlphabet outputKey
  | some (.inl key) => FirstAlphabet key
  | some (.inr key) => SecondAlphabet key

abbrev Labels (FirstLabel SecondLabel : Type) := FirstLabel ⊕ (Bool ⊕ SecondLabel)

abbrev Registers (outputKey : FirstKey) :=
  FirstState × SecondState × Option (FirstAlphabet outputKey)

/-- Execute sequential composition using only the original programs, physical
stack addresses and registers. Finiteness witnesses are absent from the
executable interface; both handoff passes still execute ordinary stack steps. -/
def body (outputKey : FirstKey) (inputKey : SecondKey) (secondMain : SecondLabel)
    (defaultSymbol : FirstAlphabet outputKey)
    (convert : FirstAlphabet outputKey → SecondAlphabet inputKey)
    (first : FirstLabel → TM2.Stmt FirstAlphabet FirstLabel FirstState)
    (second : SecondLabel → TM2.Stmt SecondAlphabet SecondLabel SecondState) :
    Labels FirstLabel SecondLabel → TM2.Stmt
      (Cells (FirstAlphabet := FirstAlphabet) (SecondAlphabet := SecondAlphabet) outputKey)
      (Labels FirstLabel SecondLabel) (Registers (FirstState := FirstState)
        (SecondState := SecondState) (FirstAlphabet := FirstAlphabet) outputKey)
  | .inl label => StackMachineRegisters.embedStatement (fun key => some (.inl key)) Sum.inl
      (fun state => state.1) (fun state value => (value, state.2)) (fun _ => rfl)
      (.goto (fun _ => .inr (.inl false))) (first label)
  | .inr (.inr label) => StackMachineRegisters.embedStatement (fun key => some (.inr key))
      (fun label => .inr (.inr label)) (fun state => state.2.1)
      (fun state value => (state.1, value, state.2.2)) (fun _ => rfl) .halt (second label)
  | .inr (.inl false) =>
      .pop (some (.inl outputKey)) (fun state value => (state.1, state.2.1, value))
        (.branch (fun state => state.2.2.isSome)
          (.push none (fun state => state.2.2.getD defaultSymbol)
            (.goto (fun _ => .inr (.inl false))))
          (.load (fun state => (state.1, state.2.1, none))
            (.goto (fun _ => .inr (.inl true)))))
  | .inr (.inl true) =>
      .pop none (fun state value => (state.1, state.2.1, value))
        (.branch (fun state => state.2.2.isSome)
          (.push (some (.inr inputKey))
            (fun state => convert (state.2.2.getD defaultSymbol))
            (.goto (fun _ => .inr (.inl true))))
          (.load (fun state => (state.1, state.2.1, none))
            (.goto (fun _ => .inr (.inr secondMain)))))

end Programs

variable (first second : FinTM2)

local instance : Fintype first.K := first.kFin
local instance : Fintype second.K := second.kFin
local instance : Fintype first.Λ := first.ΛFin
local instance : Fintype second.Λ := second.ΛFin
local instance : Fintype first.σ := first.σFin
local instance : Fintype second.σ := second.σFin

abbrev Key := Programs.Key first.K second.K
abbrev Label := Programs.Labels first.Λ second.Λ
abbrev Alphabet := Programs.Cells (FirstAlphabet := first.Γ) (SecondAlphabet := second.Γ) first.k₁
abbrev State := Programs.Registers (FirstState := first.σ) (SecondState := second.σ)
  (FirstAlphabet := first.Γ) first.k₁

def leftKey (key : first.K) : Key first second := some (.inl key)
def rightKey (key : second.K) : Key first second := some (.inr key)

/-- The first program's halt transfers control rather than terminating the
combined execution. All its other operations retain their original meaning. -/
def liftFirst : Turing.TM2.Stmt first.Γ first.Λ first.σ → Turing.TM2.Stmt (Alphabet first second)
    (Label first second) (State first second)
  | .push key value rest => .push (leftKey first second key)
      (fun state => value state.1) (liftFirst rest)
  | .peek key update rest => .peek (leftKey first second key)
      (fun state value => (update state.1 value, state.2)) (liftFirst rest)
  | .pop key update rest => .pop (leftKey first second key)
      (fun state value => (update state.1 value, state.2)) (liftFirst rest)
  | .load update rest => .load (fun state => (update state.1, state.2)) (liftFirst rest)
  | .branch condition yes no => .branch (fun state => condition state.1)
      (liftFirst yes) (liftFirst no)
  | .goto label => .goto (fun state => .inl (label state.1))
  | .halt => .goto (fun _ => .inr (.inl false))

/-- The second program operates only on its own contents and state component. -/
def liftSecond : Turing.TM2.Stmt second.Γ second.Λ second.σ → Turing.TM2.Stmt (Alphabet first second)
    (Label first second) (State first second)
  | .push key value rest => .push (rightKey first second key)
      (fun state => value state.2.1) (liftSecond rest)
  | .peek key update rest => .peek (rightKey first second key)
      (fun state value => (state.1, update state.2.1 value, state.2.2)) (liftSecond rest)
  | .pop key update rest => .pop (rightKey first second key)
      (fun state value => (state.1, update state.2.1 value, state.2.2)) (liftSecond rest)
  | .load update rest => .load (fun state => (state.1, update state.2.1, state.2.2)) (liftSecond rest)
  | .branch condition yes no => .branch (fun state => condition state.2.1)
      (liftSecond yes) (liftSecond no)
  | .goto label => .goto (fun state => .inr (.inr (label state.2.1)))
  | .halt => .halt

/-- The original first-program lift is the structural statement embedding. -/
theorem liftFirst_eq_embedStatement (statement : first.Stmt) :
    liftFirst first second statement =
      StackMachineRegisters.embedStatement (Alphabet := first.Γ)
        (TargetAlphabet := Alphabet first second) (TargetState := State first second)
        (Label' := Label first second)
        (leftKey first second) Sum.inl (fun state => state.1)
        (fun state value => (value, state.2)) (fun _ => rfl)
        (.goto (fun _ => .inr (.inl false))) statement := by
  induction statement <;>
    simp only [liftFirst, StackMachineRegisters.embedStatement, *]
  all_goals rfl

/-- The original second-program lift is the structural statement embedding. -/
theorem liftSecond_eq_embedStatement (statement : second.Stmt) :
    liftSecond first second statement =
      StackMachineRegisters.embedStatement (Alphabet := second.Γ)
        (TargetAlphabet := Alphabet first second) (TargetState := State first second)
        (Label' := Label first second)
        (rightKey first second) (fun label => .inr (.inr label))
        (fun state => state.2.1)
        (fun state value => (state.1, value, state.2.2)) (fun _ => rfl)
        .halt statement := by
  induction statement <;>
    simp only [liftSecond, StackMachineRegisters.embedStatement, *]
  all_goals rfl

variable [Fintype (first.Γ first.k₁)] [Inhabited (first.Γ first.k₁)]

/-- Two actual symbol passes perform the alphabet conversion and restore order. -/
def machine (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀) : FinTM2 where
  K := Key first second
  k₀ := leftKey first second first.k₀
  k₁ := rightKey first second second.k₁
  Γ := Alphabet first second
  Γk₀Fin := first.Γk₀Fin
  Λ := Label first second
  main := .inl first.main
  σ := State first second
  initialState := (first.initialState, second.initialState, none)
  m
    | .inl label => liftFirst first second (first.m label)
    | .inr (.inr label) => liftSecond first second (second.m label)
    | .inr (.inl false) =>
        .pop (leftKey first second first.k₁)
          (fun state value => (state.1, state.2.1, value))
          (.branch (fun state => state.2.2.isSome)
            (.push none (fun state => state.2.2.getD default)
              (.goto (fun _ => .inr (.inl false))))
            (.load (fun state => (state.1, state.2.1, none))
              (.goto (fun _ => .inr (.inl true)))))
    | .inr (.inl true) =>
        .pop none (fun state value => (state.1, state.2.1, value))
          (.branch (fun state => state.2.2.isSome)
            (.push (rightKey first second second.k₀)
              (fun state => bridge (state.2.2.getD default))
              (.goto (fun _ => .inr (.inl true))))
            (.load (fun state => (state.1, state.2.1, none))
              (.goto (fun _ => .inr (.inr second.main)))))

attribute [local implicit_reducible] machine

/-- The computational interface is exactly the existing composed transition
table. It changes no source step, continuation, stack operation or clock. -/
theorem body_eq (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀) :
    Programs.body (FirstAlphabet := first.Γ) (SecondAlphabet := second.Γ)
      first.k₁ second.k₀ second.main default bridge first.m second.m =
      (machine first second bridge).m := by
  funext phase
  cases phase with
  | inl phase =>
      exact (liftFirst_eq_embedStatement first second (first.m phase)).symm
  | inr phase =>
      cases phase with
      | inl flag => cases flag <;> rfl
      | inr phase =>
          exact (liftSecond_eq_embedStatement first second (second.m phase)).symm

def firstStacks (contents : ∀ key, List (first.Γ key)) :
    ∀ key, List (Alphabet first second key)
  | none => []
  | some (.inl key) => contents key
  | some (.inr _) => []

def secondStacks (contents : ∀ key, List (second.Γ key)) :
    ∀ key, List (Alphabet first second key)
  | none => []
  | some (.inl _) => []
  | some (.inr key) => contents key

def firstConfig (_bridge : first.Γ first.k₁ ≃ second.Γ second.k₀) (config : Turing.TM2.Cfg first.Γ first.Λ first.σ) : Turing.TM2.Cfg (Alphabet first second) (Label first second) (State first second) where
  l := match config.l with
    | some label => some (.inl label)
    | none => some (.inr (.inl false))
  var := (config.var, second.initialState, none)
  stk := firstStacks first second config.stk

def secondConfig (_bridge : first.Γ first.k₁ ≃ second.Γ second.k₀) (config : Turing.TM2.Cfg second.Γ second.Λ second.σ) : Turing.TM2.Cfg (Alphabet first second) (Label first second) (State first second) where
  l := config.l.map (fun label => .inr (.inr label))
  var := (first.initialState, config.var, none)
  stk := secondStacks first second config.stk

omit [Fintype (first.Γ first.k₁)] [Inhabited (first.Γ first.k₁)] in
theorem firstStacks_update (contents : ∀ key, List (first.Γ key))
    (key : first.K) (value : List (first.Γ key)) :
    firstStacks first second (Function.update contents key value) =
      Function.update (firstStacks first second contents) (leftKey first second key) value := by
  funext index
  cases index with
  | none => simp [firstStacks, leftKey, Function.update]
  | some index =>
      cases index with
      | inl index =>
          by_cases same : index = key
          · subst index; simp [firstStacks, leftKey, Function.update]
          · simp [firstStacks, leftKey, Function.update, same]
      | inr index => simp [firstStacks, leftKey, Function.update]

omit [Fintype (first.Γ first.k₁)] [Inhabited (first.Γ first.k₁)] in
theorem secondStacks_update (contents : ∀ key, List (second.Γ key))
    (key : second.K) (value : List (second.Γ key)) :
    secondStacks first second (Function.update contents key value) =
      Function.update (secondStacks first second contents) (rightKey first second key) value := by
  funext index
  cases index with
  | none => simp [secondStacks, rightKey, Function.update]
  | some index =>
      cases index with
      | inl index => simp [secondStacks, rightKey, Function.update]
      | inr index =>
          by_cases same : index = key
          · subst index; simp [secondStacks, rightKey, Function.update]
          · simp [secondStacks, rightKey, Function.update, same]

omit [Fintype (first.Γ first.k₁)] [Inhabited (first.Γ first.k₁)] in
/-- The first statement lift executes every original stack operation exactly. -/
theorem liftFirst_stepAux (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    (statement : first.Stmt) (state : first.σ) (contents : ∀ key, List (first.Γ key)) :
    Turing.TM2.stepAux (liftFirst first second statement) (state, second.initialState, none)
      (firstStacks first second contents) =
        firstConfig first second bridge (Turing.TM2.stepAux statement state contents) := by
  induction statement generalizing state contents with
  | push key value rest ih =>
      simp only [liftFirst, Turing.TM2.stepAux, firstStacks, leftKey]
      have lifted := ih state (Function.update contents key (value state :: contents key))
      rw [firstStacks_update] at lifted
      simpa only [leftKey] using lifted
  | peek key update rest ih =>
      simp only [liftFirst, Turing.TM2.stepAux, firstStacks, leftKey]
      exact ih _ _
  | pop key update rest ih =>
      simp only [liftFirst, Turing.TM2.stepAux, firstStacks, leftKey]
      have lifted := ih (update state (contents key).head?) (Function.update contents key (contents key).tail)
      rw [firstStacks_update] at lifted
      simpa only [leftKey] using lifted
  | load update rest ih =>
      simp only [liftFirst, Turing.TM2.stepAux]
      exact ih _ _
  | branch condition yes no ihYes ihNo =>
      simp only [liftFirst, Turing.TM2.stepAux]
      cases condition state <;> simp only [cond_false, cond_true]
      · exact ihNo _ _
      · exact ihYes _ _
  | goto label => rfl
  | halt => rfl

omit [Fintype (first.Γ first.k₁)] [Inhabited (first.Γ first.k₁)] in
theorem liftSecond_stepAux (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    (statement : second.Stmt) (state : second.σ) (contents : ∀ key, List (second.Γ key)) :
    Turing.TM2.stepAux (liftSecond first second statement) (first.initialState, state, none)
      (secondStacks first second contents) =
        secondConfig first second bridge (Turing.TM2.stepAux statement state contents) := by
  induction statement generalizing state contents with
  | push key value rest ih =>
      simp only [liftSecond, Turing.TM2.stepAux, secondStacks, rightKey]
      have lifted := ih state (Function.update contents key (value state :: contents key))
      rw [secondStacks_update] at lifted
      simpa only [rightKey] using lifted
  | peek key update rest ih =>
      simp only [liftSecond, Turing.TM2.stepAux, secondStacks, rightKey]
      exact ih _ _
  | pop key update rest ih =>
      simp only [liftSecond, Turing.TM2.stepAux, secondStacks, rightKey]
      have lifted := ih (update state (contents key).head?) (Function.update contents key (contents key).tail)
      rw [secondStacks_update] at lifted
      simpa only [rightKey] using lifted
  | load update rest ih =>
      simp only [liftSecond, Turing.TM2.stepAux]
      exact ih _ _
  | branch condition yes no ihYes ihNo =>
      simp only [liftSecond, Turing.TM2.stepAux]
      cases condition state <;> simp only [cond_false, cond_true]
      · exact ihNo _ _
      · exact ihYes _ _
  | goto label => rfl
  | halt => rfl

theorem first_step (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    (config : first.Cfg) (label : first.Λ) (active : config.l = some label) :
    (machine first second bridge).step (firstConfig first second bridge config) =
      (first.step config).map (firstConfig first second bridge) := by
  cases config with
  | mk current state contents =>
      dsimp at active
      subst current
      simp only [FinTM2.step, Turing.TM2.step, firstConfig, machine]
      exact congrArg some (liftFirst_stepAux first second bridge _ _ _)

theorem second_step (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀) (config : second.Cfg) :
    (machine first second bridge).step (secondConfig first second bridge config) =
      (second.step config).map (secondConfig first second bridge) := by
  cases config with
  | mk current state contents =>
      cases current with
      | none => rfl
      | some label =>
          simp only [FinTM2.step, Turing.TM2.step, secondConfig, machine, Option.map_some]
          exact congrArg some (liftSecond_stepAux first second bridge _ _ _)

/-- Transfer configurations retain only the first output, a temporary word
and the partially restored second input. -/
def transferConfig (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    (phase : Option Bool) (symbol : Option (first.Γ first.k₁))
    (input temporary : List (first.Γ first.k₁)) (output : List (second.Γ second.k₀)) :
    (machine first second bridge).Cfg where
  l := some (match phase with
    | some value => .inr (.inl value)
    | none => .inr (.inr second.main))
  var := (first.initialState, second.initialState, symbol)
  stk
    | none => temporary
    | some (.inl key) => if same : key = first.k₁ then same.symm ▸ input else []
    | some (.inr key) => if same : key = second.k₀ then same.symm ▸ output else []

theorem scan_cons (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    (symbol : Option (first.Γ first.k₁)) (head : first.Γ first.k₁)
    (tail temporary : List (first.Γ first.k₁)) (output : List (second.Γ second.k₀)) :
    (machine first second bridge).step (transferConfig first second bridge (some false)
      symbol (head :: tail) temporary output) =
        some (transferConfig first second bridge (some false) (some head) tail (head :: temporary) output) := by
  simp [FinTM2.step, machine, transferConfig, Turing.TM2.step, Turing.TM2.stepAux, leftKey]
  funext key
  cases key with
  | none => simp [Function.update]
  | some key =>
      cases key with
      | inl key =>
          by_cases same : key = first.k₁
          · subst key; simp [Function.update]
          · simp [Function.update, same]
      | inr key => simp [Function.update]

theorem scan_nil (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    (symbol : Option (first.Γ first.k₁)) (temporary : List (first.Γ first.k₁))
    (output : List (second.Γ second.k₀)) :
    (machine first second bridge).step (transferConfig first second bridge (some false) symbol [] temporary output) =
      some (transferConfig first second bridge (some true) none [] temporary output) := by
  simp [FinTM2.step, machine, transferConfig, Turing.TM2.step, Turing.TM2.stepAux, leftKey]

theorem restore_cons (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    (symbol : Option (first.Γ first.k₁)) (head : first.Γ first.k₁)
    (tail input : List (first.Γ first.k₁)) (output : List (second.Γ second.k₀)) :
    (machine first second bridge).step (transferConfig first second bridge (some true)
      symbol input (head :: tail) output) =
        some (transferConfig first second bridge (some true) (some head) input tail (bridge head :: output)) := by
  simp [FinTM2.step, machine, transferConfig, Turing.TM2.step, Turing.TM2.stepAux, rightKey]
  funext key
  cases key with
  | none => simp [Function.update]
  | some key =>
      cases key with
      | inl key => simp [Function.update]
      | inr key =>
          by_cases same : key = second.k₀
          · subst key; simp [Function.update]
          · simp [Function.update, same]

theorem restore_nil (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    (symbol : Option (first.Γ first.k₁)) (input : List (first.Γ first.k₁))
    (output : List (second.Γ second.k₀)) :
    (machine first second bridge).step (transferConfig first second bridge (some true) symbol input [] output) =
      some (transferConfig first second bridge none none input [] output) := by
  simp [FinTM2.step, machine, transferConfig, Turing.TM2.step, Turing.TM2.stepAux]

omit first second [Fintype (first.Γ first.k₁)] [Inhabited (first.Γ first.k₁)] in
theorem iterate_bind_none {Config : Type} (step : Config → Option Config) (count : ℕ) :
    (fun state => state.bind step)^[count] none = none := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply', ih, Option.bind_none]

omit first second [Fintype (first.Γ first.k₁)] [Inhabited (first.Γ first.k₁)] in
/-- Refinement of successful finite paths requires agreement on each actual
transition, without imposing a continuation on a halted source state. -/
theorem iterate_some_refinement {Source Target : Type}
    (source : Source → Option Source) (target : Target → Option Target)
    (embed : Source → Target)
    (preserves : ∀ before after, source before = some after →
      target (embed before) = some (embed after))
    (steps : ℕ) (before after : Source)
    (executes : (fun state => state.bind source)^[steps] (some before) = some after) :
    (fun state => state.bind target)^[steps] (some (embed before)) = some (embed after) := by
  induction steps generalizing before after with
  | zero =>
      have equal : before = after := Option.some.inj executes
      subst after
      rfl
  | succ steps ih =>
      rw [Function.iterate_succ_apply] at executes ⊢
      simp only [Option.bind_some] at executes ⊢
      cases next : source before with
      | none =>
          rw [next, iterate_bind_none] at executes
          contradiction
      | some middle =>
          rw [next] at executes
          rw [preserves before middle next]
          exact ih middle after executes

omit first second [Fintype (first.Γ first.k₁)] [Inhabited (first.Γ first.k₁)] in
/-- A lifted path retains the original number of transitions and its bound. -/
def lift_execution {Source Target : Type}
    (source : Source → Option Source) (target : Target → Option Target)
    (embed : Source → Target)
    (preserves : ∀ before after, source before = some after →
      target (embed before) = some (embed after))
    {before after : Source} {bound : ℕ}
    (execution : EvalsToInTime source before (some after) bound) :
    EvalsToInTime target (embed before) (some (embed after)) bound where
  steps := execution.steps
  evals_in_steps := iterate_some_refinement source target embed preserves
    execution.steps before after execution.evals_in_steps
  steps_le_m := execution.steps_le_m

def first_execution (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    {before after : first.Cfg} {bound : ℕ}
    (execution : EvalsToInTime first.step before (some after) bound) :
    EvalsToInTime (machine first second bridge).step
      (firstConfig first second bridge before) (some (firstConfig first second bridge after)) bound := by
  apply lift_execution first.step _ (firstConfig first second bridge) _ execution
  intro before after executes
  cases active : before.l with
  | none =>
      cases before with
      | mk label state contents =>
          dsimp at active
          subst label
          simp [FinTM2.step, Turing.TM2.step] at executes
  | some label => rw [first_step first second bridge before label active, executes]; rfl

def second_execution (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    {before after : second.Cfg} {bound : ℕ}
    (execution : EvalsToInTime second.step before (some after) bound) :
    EvalsToInTime (machine first second bridge).step
      (secondConfig first second bridge before) (some (secondConfig first second bridge after)) bound := by
  apply lift_execution second.step _ (secondConfig first second bridge) _ execution
  intro before after executes
  rw [second_step first second bridge before, executes]
  rfl

omit first second [Fintype (first.Γ first.k₁)] [Inhabited (first.Γ first.k₁)] in
/-- One transition witnessed in the machine's iteration semantics. -/
def oneStep {Config : Type} {step : Config → Option Config} {before after : Config}
    (executed : step before = some after) : EvalsToInTime step before (some after) 1 where
  steps := 1
  evals_in_steps := by simpa [flip, Option.bind] using executed
  steps_le_m := le_rfl

omit first second [Fintype (first.Γ first.k₁)] [Inhabited (first.Γ first.k₁)] in
/-- A finite original path has a counted execution witness. -/
theorem reaches_has_execution {Config : Type} {step : Config → Option Config} {before after : Config}
    (path : Reaches step before after) : Nonempty (EvalsTo step before (some after)) := by
  induction path with
  | refl => exact ⟨EvalsTo.refl step before⟩
  | @tail middle final previous advanced ih =>
      obtain ⟨run⟩ := ih
      exact ⟨EvalsTo.trans step _ _ _ run (oneStep (Option.mem_def.mp advanced)).toEvalsTo⟩

/-- The first pass consumes the entire first output and reverses it temporarily. -/
def scan_run (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    (word temporary : List (first.Γ first.k₁)) (output : List (second.Γ second.k₀))
    (symbol : Option (first.Γ first.k₁)) :
    EvalsToInTime (machine first second bridge).step
      (transferConfig first second bridge (some false) symbol word temporary output)
      (some (transferConfig first second bridge (some true) none [] (word.reverse ++ temporary) output))
      (word.length + 1) := by
  induction word generalizing temporary symbol with
  | nil => simpa using oneStep (scan_nil first second bridge symbol temporary output)
  | cons head tail ih =>
      have started := oneStep (scan_cons first second bridge symbol head tail temporary output)
      have continued := ih (head :: temporary) (some head)
      have joined := EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ started continued
      simpa using joined

/-- The second pass applies the alphabet equivalence and restores word order. -/
def restore_run (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    (temporary input : List (first.Γ first.k₁)) (output : List (second.Γ second.k₀))
    (symbol : Option (first.Γ first.k₁)) :
    EvalsToInTime (machine first second bridge).step
      (transferConfig first second bridge (some true) symbol input temporary output)
      (some (transferConfig first second bridge none none input [] (temporary.reverse.map bridge ++ output)))
      (temporary.length + 1) := by
  induction temporary generalizing output symbol with
  | nil => simpa using oneStep (restore_nil first second bridge symbol input output)
  | cons head tail ih =>
      have started := oneStep (restore_cons first second bridge symbol head tail input output)
      have continued := ih (bridge head :: output) (some head)
      have joined := EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ started continued
      simpa using joined

theorem init_eq (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    (word : List (first.Γ first.k₀)) :
    initList (machine first second bridge) word =
      firstConfig first second bridge (initList first word) := by
  simp only [initList, machine, firstConfig]
  congr 1
  funext key
  cases key with
  | none => simp [leftKey, firstStacks]
  | some key =>
      cases key with
      | inl key =>
          by_cases same : key = first.k₀
          · subst key; simp [leftKey, firstStacks]
          · simp [leftKey, firstStacks, same]
      | inr key => simp [leftKey, firstStacks]

theorem first_halt_eq (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    (word : List (first.Γ first.k₁)) :
    firstConfig first second bridge (haltList first word) =
      transferConfig first second bridge (some false) none word [] [] := by
  simp only [haltList, firstConfig, transferConfig]
  congr 1
  funext key
  cases key with
  | none => rfl
  | some key =>
      cases key with
      | inl key =>
          by_cases same : key = first.k₁
          · subst key; simp [firstStacks]
          · simp [firstStacks, same]
      | inr key =>
          by_cases same : key = second.k₀
          · subst key; simp [firstStacks]
          · simp [firstStacks, same]

theorem second_init_eq (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    (word : List (second.Γ second.k₀)) :
    transferConfig first second bridge none none [] [] word =
      secondConfig first second bridge (initList second word) := by
  simp only [initList, secondConfig, transferConfig]
  congr 1
  funext key
  cases key with
  | none => rfl
  | some key =>
      cases key with
      | inl key =>
          by_cases same : key = first.k₁
          · subst key; simp [secondStacks]
          · simp [secondStacks, same]
      | inr key =>
          by_cases same : key = second.k₀
          · subst key; simp [secondStacks]
          · simp [secondStacks, same]

theorem second_halt_eq (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    (word : List (second.Γ second.k₁)) :
    secondConfig first second bridge (haltList second word) =
      haltList (machine first second bridge) word := by
  simp only [haltList, machine, secondConfig]
  congr 1
  funext key
  cases key with
  | none => simp [rightKey, secondStacks]
  | some key =>
      cases key with
      | inl key => simp [rightKey, secondStacks]
      | inr key =>
          by_cases same : key = second.k₁
          · subst key; simp [rightKey, secondStacks]
          · simp [rightKey, secondStacks, same]

/-- The actual handoff consumes both transfer stacks and preserves every symbol,
including its position and repeated occurrences. -/
def transfer_run (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    (word : List (first.Γ first.k₁)) :
    EvalsToInTime (machine first second bridge).step
      (firstConfig first second bridge (haltList first word))
      (some (secondConfig first second bridge (initList second (word.map bridge))))
      (2 * word.length + 2) := by
  have scanned := scan_run first second bridge word [] [] none
  simp only [List.append_nil] at scanned
  have restored := restore_run first second bridge word.reverse [] [] none
  have joined := EvalsToInTime.trans _ (word.length + 1)
    (word.reverse.length + 1) _ _ _ scanned restored
  rw [first_halt_eq, ← second_init_eq]
  have timeEq : word.reverse.length + 1 + (word.length + 1) = 2 * word.length + 2 := by
    simp only [List.length_reverse]
    omega
  rw [timeEq] at joined
  simpa using joined

/-- Composition executes both original programs and the finite word handoff.
The time bound counts their actual transitions and both intermediate passes. -/
def outputs (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    (input : List (first.Γ first.k₀)) (middle : List (first.Γ first.k₁))
    (output : List (second.Γ second.k₁)) (firstTime secondTime : ℕ)
    (firstRun : TM2OutputsInTime first input (some middle) firstTime)
    (secondRun : TM2OutputsInTime second (middle.map bridge) (some output) secondTime) :
    TM2OutputsInTime (machine first second bridge) input (some output)
      (firstTime + 2 * middle.length + 2 + secondTime) := by
  have started := first_execution first second bridge firstRun
  have transferred := transfer_run first second bridge middle
  have finished := second_execution first second bridge secondRun
  have firstPart := EvalsToInTime.trans _ firstTime (2 * middle.length + 2)
    _ _ _ started transferred
  have joined := EvalsToInTime.trans _ ((2 * middle.length + 2) + firstTime) secondTime
    _ _ _ firstPart finished
  change EvalsToInTime _ (initList (machine first second bridge) input)
    (some (haltList (machine first second bridge) output)) _
  rw [init_eq, ← second_halt_eq]
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using joined

end Mettapedia.Computability.StackMachineComposition


namespace Mettapedia.Computability.StackMachineComposition.Dispatch

open Turing StateTransition
open Turing.TM2.Stmt

variable (program : FinTM2)

local instance : Fintype program.K := program.kFin
local instance : Fintype program.Λ := program.ΛFin
local instance : Fintype program.σ := program.σFin
local instance : Fintype (program.Γ program.k₀) := program.Γk₀Fin

inductive Phase (Label : Type) where
  | read | discard | run (label : Label)
  deriving Fintype, DecidableEq

abbrev State := program.σ × Option (program.Γ program.k₀)

def lift : program.Stmt → Turing.TM2.Stmt program.Γ (Phase program.Λ) (State program)
  | .push key value rest => .push key (fun state => value state.1) (lift rest)
  | .peek key update rest => .peek key (fun state value => (update state.1 value, state.2)) (lift rest)
  | .pop key update rest => .pop key (fun state value => (update state.1 value, state.2)) (lift rest)
  | .load update rest => .load (fun state => (update state.1, state.2)) (lift rest)
  | .branch condition yes no => .branch (fun state => condition state.1) (lift yes) (lift no)
  | .goto label => .goto (fun state => .run (label state.1))
  | .halt => .halt

def emit : List (program.Γ program.k₁) →
    Turing.TM2.Stmt program.Γ (Phase program.Λ) (State program) →
    Turing.TM2.Stmt program.Γ (Phase program.Λ) (State program)
  | [], rest => rest
  | head :: tail, rest => emit tail (.push program.k₁ (fun _ => head) rest)

def machine (accept : program.Γ program.k₀ → Bool) (refused : List (program.Γ program.k₁)) : FinTM2 where
  K := program.K
  k₀ := program.k₀
  k₁ := program.k₁
  Γ := program.Γ
  Γk₀Fin := program.Γk₀Fin
  Λ := Phase program.Λ
  main := .read
  σ := State program
  initialState := (program.initialState, none)
  m phase := match phase with
    | .run label => lift program (program.m label)
    | .read => .pop program.k₀ (fun state value => (state.1, value))
        (.branch (fun state => state.2.any accept)
          (.load (fun state => (state.1, none)) (.goto (fun _ => .run program.main)))
          (.goto (fun _ => .discard)))
    | .discard => .pop program.k₀ (fun state value => (state.1, value))
        (.branch (fun state => state.2.isSome) (.goto (fun _ => .discard))
          (emit program refused (.load (fun _ => (program.initialState, none)) .halt)))

def embed (config : program.Cfg) (status : Option (program.Γ program.k₀)) :
    Turing.TM2.Cfg program.Γ (Phase program.Λ) (State program) where
  l := config.l.map Phase.run
  var := (config.var, status)
  stk := config.stk

theorem lift_stepAux (statement : program.Stmt) (state : program.σ)
    (status : Option (program.Γ program.k₀)) (contents : ∀ key, List (program.Γ key)) :
    Turing.TM2.stepAux (lift program statement) (state, status) contents =
      embed program (Turing.TM2.stepAux statement state contents) status := by
  induction statement generalizing state contents with
  | push key value rest ih => exact ih _ _
  | peek key update rest ih => exact ih _ _
  | pop key update rest ih => exact ih _ _
  | load update rest ih => exact ih _ _
  | branch condition yes no yesIH noIH =>
      simp only [lift, Turing.TM2.stepAux]
      cases condition state <;> simp only [cond_false, cond_true]
      · exact noIH _ _
      · exact yesIH _ _
  | goto label => rfl
  | halt => rfl

theorem emit_stepAux (word : List (program.Γ program.k₁))
    (rest : Turing.TM2.Stmt program.Γ (Phase program.Λ) (State program))
    (state : State program) (contents : ∀ key, List (program.Γ key)) :
    Turing.TM2.stepAux (emit program word rest) state contents =
      Turing.TM2.stepAux rest state
        (Function.update contents program.k₁ (word ++ contents program.k₁)) := by
  induction word generalizing rest with
  | nil => simp [emit]
  | cons head tail ih =>
      rw [emit, ih]
      simp only [Turing.TM2.stepAux, Function.update_self, Function.update_idem, List.cons_append]

theorem run_step (accept : program.Γ program.k₀ → Bool) (refused : List (program.Γ program.k₁))
    (config : program.Cfg) (status : Option (program.Γ program.k₀)) :
    (machine program accept refused).step (embed program config status) =
      (program.step config).map (fun next => embed program next status) := by
  cases config with
  | mk label state contents =>
      cases label with
      | none => rfl
      | some label =>
          simp only [FinTM2.step, machine, embed, Turing.TM2.step, Option.map_some]
          exact congrArg some (lift_stepAux program _ state status contents)

def run_execution (accept : program.Γ program.k₀ → Bool) (refused : List (program.Γ program.k₁))
    (input : List (program.Γ program.k₀)) (output : List (program.Γ program.k₁))
    (time : Nat) (execution : TM2OutputsInTime program input (some output) time) :
    EvalsToInTime (machine program accept refused).step
      (embed program (initList program input) none)
      (some (embed program (haltList program output) none)) time := by
  refine { steps := execution.steps, steps_le_m := execution.steps_le_m, evals_in_steps := ?_ }
  apply iterate_some_refinement program.step (machine program accept refused).step
    (fun config => embed program config none)
  · intro before after next
    rw [run_step, next]
    rfl
  · exact execution.evals_in_steps

def inputConfig (phase : Phase program.Λ) (status : Option (program.Γ program.k₀))
    (word : List (program.Γ program.k₀)) :
    Turing.TM2.Cfg program.Γ (Phase program.Λ) (State program) where
  l := some phase
  var := (program.initialState, status)
  stk := (initList program word).stk

theorem pop_input_contents (word : List (program.Γ program.k₀)) :
    Function.update (initList program word).stk program.k₀ word.tail =
      (initList program word.tail).stk := by
  funext key
  by_cases same : key = program.k₀
  · subst key; simp [initList]
  · simp [initList, Function.update, same]

theorem input_empty_contents : (initList program []).stk = fun _ => [] := by
  funext key
  by_cases same : key = program.k₀
  · subst key; simp [initList]
  · simp [initList, same]

theorem empty_output_contents (word : List (program.Γ program.k₁)) :
    Function.update (fun key => ([] : List (program.Γ key))) program.k₁ word =
      (haltList program word).stk := by
  funext key
  by_cases same : key = program.k₁
  · subst key; simp [haltList]
  · simp [haltList, Function.update, same]

theorem read_success (accept : program.Γ program.k₀ → Bool) (refused : List (program.Γ program.k₁))
    (tag : program.Γ program.k₀) (word : List (program.Γ program.k₀)) (accepted : accept tag = true) :
    (machine program accept refused).step (inputConfig program .read none (tag :: word)) =
      some (embed program (initList program word) none) := by
  simp [FinTM2.step, machine, inputConfig, Turing.TM2.step, Turing.TM2.stepAux,
    initList, accepted, embed]
  funext key
  by_cases same : key = program.k₀
  · subst key; simp [Function.update]
  · simp [Function.update, same]


theorem read_refused (accept : program.Γ program.k₀ → Bool) (refused : List (program.Γ program.k₁))
    (tag : program.Γ program.k₀) (word : List (program.Γ program.k₀)) (rejected : accept tag = false) :
    (machine program accept refused).step (inputConfig program .read none (tag :: word)) =
      some (inputConfig program .discard (some tag) word) := by
  simp [FinTM2.step, machine, inputConfig, Turing.TM2.step, Turing.TM2.stepAux,
    initList, rejected]
  funext key
  by_cases same : key = program.k₀
  · subst key; simp [Function.update]
  · simp [Function.update, same]


theorem discard_cons (accept : program.Γ program.k₀ → Bool) (refused : List (program.Γ program.k₁))
    (status : Option (program.Γ program.k₀)) (head : program.Γ program.k₀) (word : List (program.Γ program.k₀)) :
    (machine program accept refused).step (inputConfig program .discard status (head :: word)) =
      some (inputConfig program .discard (some head) word) := by
  simp [FinTM2.step, machine, inputConfig, Turing.TM2.step, Turing.TM2.stepAux, initList]
  funext key
  by_cases same : key = program.k₀
  · subst key; simp [Function.update]
  · simp [Function.update, same]


theorem discard_empty (accept : program.Γ program.k₀ → Bool) (refused : List (program.Γ program.k₁))
    (status : Option (program.Γ program.k₀)) :
    (machine program accept refused).step (inputConfig program .discard status []) =
      some (embed program (haltList program refused) none) := by
  simp only [FinTM2.step, machine, inputConfig, Turing.TM2.step]
  have empty := input_empty_contents program
  rw [empty]
  simp only [Turing.TM2.stepAux, List.head?_nil, List.tail_nil, Option.isSome_none, cond_false,
    Function.update_eq_self, emit_stepAux, List.append_nil, empty_output_contents]
  rfl



def discard_run (accept : program.Γ program.k₀ → Bool) (refused : List (program.Γ program.k₁))
    (word : List (program.Γ program.k₀)) (status : Option (program.Γ program.k₀)) :
    EvalsToInTime (machine program accept refused).step
      (inputConfig program .discard status word)
      (some (embed program (haltList program refused) none)) (word.length + 1) := by
  induction word generalizing status with
  | nil =>
      exact oneStep (discard_empty program accept refused status)
  | cons head tail ih =>
      have first : EvalsToInTime (machine program accept refused).step
          (inputConfig program .discard status (head :: tail))
          (some (inputConfig program .discard (some head) tail)) 1 :=
        oneStep (discard_cons program accept refused status head tail)
      simpa only [List.length_cons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first (ih (some head))

theorem init_eq (accept : program.Γ program.k₀ → Bool) (refused : List (program.Γ program.k₁))
    (word : List (program.Γ program.k₀)) :
    initList (machine program accept refused) word = inputConfig program .read none word := rfl

theorem halt_eq (accept : program.Γ program.k₀ → Bool) (refused : List (program.Γ program.k₁))
    (word : List (program.Γ program.k₁)) :
    haltList (machine program accept refused) word = embed program (haltList program word) none := rfl

/-- Success reads exactly one status cell, then executes the original program
on the remaining physical input. No re-encoding or uncharged body extraction
occurs at the boundary. -/
def outputs_success (accept : program.Γ program.k₀ → Bool) (refused : List (program.Γ program.k₁))
    (tag : program.Γ program.k₀) (input : List (program.Γ program.k₀))
    (output : List (program.Γ program.k₁)) (time : Nat)
    (accepted : accept tag = true) (execution : TM2OutputsInTime program input (some output) time) :
    TM2OutputsInTime (machine program accept refused) (tag :: input) (some output) (time + 1) := by
  have first : EvalsToInTime (machine program accept refused).step
      (inputConfig program .read none (tag :: input))
      (some (embed program (initList program input) none)) 1 :=
    oneStep (read_success program accept refused tag input accepted)
  rw [show TM2OutputsInTime (machine program accept refused) (tag :: input) (some output) (time + 1) =
      EvalsToInTime (machine program accept refused).step
        (inputConfig program .read none (tag :: input))
        (some (embed program (haltList program output) none)) (time + 1) by rfl]
  exact EvalsToInTime.trans _ 1 time _ _ _ first
    (run_execution program accept refused input output time execution)

/-- A refused status drains every remaining input symbol, then returns the
fixed failure output with all scratch and register state cleared. -/
def outputs_refused (accept : program.Γ program.k₀ → Bool) (refused : List (program.Γ program.k₁))
    (tag : program.Γ program.k₀) (input : List (program.Γ program.k₀))
    (rejected : accept tag = false) :
    TM2OutputsInTime (machine program accept refused) (tag :: input) (some refused) (input.length + 2) := by
  have first : EvalsToInTime (machine program accept refused).step
      (inputConfig program .read none (tag :: input))
      (some (inputConfig program .discard (some tag) input)) 1 :=
    oneStep (read_refused program accept refused tag input rejected)
  change EvalsToInTime (machine program accept refused).step
    (inputConfig program .read none (tag :: input))
    (some (embed program (haltList program refused) none)) _
  have joined := EvalsToInTime.trans _ 1 (input.length + 1) _ _ _ first
    (discard_run program accept refused input (some tag))
  convert joined using 1


theorem read_empty (accept : program.Γ program.k₀ → Bool) (refused : List (program.Γ program.k₁)) :
    (machine program accept refused).step (inputConfig program .read none []) =
      some (inputConfig program .discard none []) := by
  simp [FinTM2.step, machine, inputConfig, Turing.TM2.step, Turing.TM2.stepAux, initList]

/-- A missing status is refused too, through the same counted cleanup path. -/
def outputs_empty (accept : program.Γ program.k₀ → Bool) (refused : List (program.Γ program.k₁)) :
    TM2OutputsInTime (machine program accept refused) [] (some refused) 2 := by
  change EvalsToInTime (machine program accept refused).step
    (inputConfig program .read none []) (some (embed program (haltList program refused) none)) 2
  exact EvalsToInTime.trans _ 1 1 _ _ _
    (oneStep (read_empty program accept refused))
    (oneStep (discard_empty program accept refused none))

end Mettapedia.Computability.StackMachineComposition.Dispatch


namespace Mettapedia.Computability.StackMachineComposition.Sweep

open Turing StateTransition
open Turing.TM2.Stmt
open Mettapedia.Computability.StackMachineComposition (oneStep)

variable {Key State : Type} [DecidableEq Key] {Cells : Key → Type}

def advance (limit : Nat) (index : Fin (limit+1)) : Fin (limit+1) :=
  if less : index.val < limit then ⟨index.val+1,by omega⟩ else index

/-- A fixed finite key schedule clears heterogeneous stacks. Only symbol
presence is retained; no stack word or element enters a register. -/
def program (keys : List Key) (initial : State) (index : Fin (keys.length+1)) :
    TM2.Stmt Cells (Fin (keys.length+1)) (State × Bool) :=
  match keys[index.val]? with
  | none => load (fun _ => (initial,false)) halt
  | some key => pop key (fun state value => (state.1,value.isSome))
      (branch Prod.snd (goto fun _ => index) (goto fun _ => advance keys.length index))

abbrev Cfg (keys : List Key) := TM2.Cfg Cells (Fin (keys.length+1)) (State × Bool)

def step (keys : List Key) (initial : State) : Cfg (Cells:=Cells) (State:=State) keys →
    Option (Cfg (Cells:=Cells) (State:=State) keys) := TM2.step (program keys initial)

def config (keys : List Key) (phase : Option (Fin (keys.length+1))) (state : State × Bool)
    (contents : ∀ key, List (Cells key)) : Cfg (Cells:=Cells) (State:=State) keys := ⟨phase,state,contents⟩

def clear (contents : ∀ key, List (Cells key)) : List Key → ∀ key, List (Cells key)
  | [] => contents
  | key :: rest => clear (Function.update contents key []) rest

def cost (contents : ∀ key, List (Cells key)) : List Key → Nat
  | [] => 1
  | key :: rest => (contents key).length + 1 + cost (Function.update contents key []) rest

theorem pop_cons (keys : List Key) (initial : State) (index : Fin (keys.length+1)) (key : Key)
    (selected : keys[index.val]? = some key) (state : State × Bool)
    (contents : ∀ key, List (Cells key)) (head : Cells key) (tail : List (Cells key))
    (stored : contents key = head :: tail) :
    step keys initial (config keys (some index) state contents) =
      some (config keys (some index) (state.1,true) (Function.update contents key tail)) := by
  simp [step,program,config,TM2.step,TM2.stepAux,selected,stored]

theorem pop_nil (keys : List Key) (initial : State) (index : Fin (keys.length+1)) (key : Key)
    (selected : keys[index.val]? = some key) (state : State × Bool)
    (contents : ∀ key, List (Cells key)) (empty : contents key = []) :
    step keys initial (config keys (some index) state contents) =
      some (config keys (some (advance keys.length index)) (state.1,false) contents) := by
  simp [step,program,config,TM2.step,TM2.stepAux,selected,empty]

def wordRun (keys : List Key) (initial : State) (index : Fin (keys.length+1)) (key : Key)
    (selected : keys[index.val]? = some key) (state : State × Bool)
    (word : List (Cells key)) (contents : ∀ key, List (Cells key)) :
    EvalsToInTime (step keys initial)
      (config keys (some index) state (Function.update contents key word))
      (some (config keys (some (advance keys.length index)) (state.1,false)
        (Function.update contents key []))) (word.length+1) := by
  induction word generalizing state with
  | nil => exact oneStep (pop_nil keys initial index key selected state (Function.update contents key []) (by simp))
  | cons head tail ih =>
      have popped := oneStep (pop_cons keys initial index key selected state
        (Function.update contents key (head::tail)) head tail (by simp))
      simp only [Function.update_idem] at popped
      have rest := ih (state.1,true)
      have joined := EvalsToInTime.trans _ _ _ _ _ _ popped rest
      convert joined using 1; simp only [List.length_cons]

omit [DecidableEq Key] in
theorem schedule_index (keys before : List Key) (key : Key) (rest : List Key)
    (split : keys = before ++ key :: rest) :
    keys[before.length]? = some key := by rw [split]; simp

/-- Every scheduled stack is physically consumed; unselected stacks retain
their original bytes. Repeated keys are permitted and incur another visit. -/
def run (keys : List Key) (initial : State) (before rest : List Key)
    (split : keys = before ++ rest) (state : State × Bool) (contents : ∀ key, List (Cells key)) :
    EvalsToInTime (step keys initial)
      (config keys (some ⟨before.length,by simp only [split,List.length_append]; omega⟩) state contents)
      (some (config keys none (initial,false) (clear contents rest))) (cost contents rest) := by
  induction rest generalizing before state contents with
  | nil =>
      have selected : keys[before.length]? = none := by simp [split]
      apply oneStep
      simp [step,program,config,selected,clear]
  | cons key rest ih =>
      let index : Fin (keys.length+1) := ⟨before.length,by simp only [split,List.length_append,List.length_cons]; omega⟩
      have selected : keys[index.val]? = some key := schedule_index keys before key rest split
      have first := wordRun keys initial index key selected state (contents key) contents
      simp only [Function.update_eq_self] at first
      have nextSplit : keys = (before++[key]) ++ rest := by simpa only [List.append_assoc,List.singleton_append] using split
      have next := ih (before++[key]) nextSplit (state.1,false) (Function.update contents key [])
      have nextIndex : advance keys.length index =
          ⟨(before++[key]).length,by simp only [nextSplit,List.length_append]; omega⟩ := by
        apply Fin.ext
        simp only [advance,index]
        have less : before.length < keys.length := by simp only [split,List.length_append,List.length_cons]; omega
        simp only [less,↓reduceDIte,List.length_append,List.length_singleton]
      rw [nextIndex] at first
      have joined := EvalsToInTime.trans _ _ _ _ _ _ first next
      simpa only [cost, clear, Nat.add_comm] using joined

theorem cost_le (contents : ∀ key, List (Cells key)) (keys : List Key) :
    cost contents keys ≤ (keys.map fun key => (contents key).length).sum + keys.length + 1 := by
  induction keys generalizing contents with
  | nil => simp [cost]
  | cons key rest ih =>
      have tail := ih (Function.update contents key [])
      have lengths :
          (rest.map fun selected => (Function.update contents key [] selected).length).sum ≤
          (rest.map fun selected => (contents selected).length).sum := by
        apply List.sum_le_sum
        intro selected member
        by_cases same : selected = key
        · subst selected; simp
        · simp [Function.update_of_ne same]
      simp only [cost,List.map_cons,List.sum_cons,List.length_cons]
      omega

end Mettapedia.Computability.StackMachineComposition.Sweep
