import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralLiveRunnerExecution
import Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRender

/-!
# Emitting a runnable MeTTa module for an admitted language

`emit?` takes an admitted plan and a module name and returns a MeTTa program with two entries:

- `name:begin source` returns the live machine at the source, to continue with
  `gslt:live:tick` and `gslt:live:advance`;
- `name:run source ticks quantum` returns the chronological trace after that page.

The plan is inlined in the entries as data. Loaded after the live runner's libraries, the
module needs nothing else. `emit?` refuses, with the reason, a plan that has admission
obligations, a plan with equations, a plan whose premises are not stratified, and a name whose
entries could collide with the runtime's own heads or with the plan's data.

`begin_returns` and `run_returns`: for every module that `emit?` returns, the actual PeTTa run
of its entries is the live runner's model. `emitted_run` collects what that gives: the trace is
a reduction sequence of the plan's GSLT from the source, every receipt is kept, and a normal
ending means the state has no step.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralLiveRunnerEmission

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open SpaceSemantics (Program)
open Eval
open GeneralLiveRunnerExecution

private abbrev a (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name
private abbrev encoded (term : Term) : Atom := CettaWireAtom.encode term
private abbrev number (value : Nat) : Atom := encoded (.natural value)
private abbrev patternValue (pattern : Pattern) : Atom := encoded (InferenceCettaWire.encodePattern pattern)

/-! ## The module -/

def beginHead (name : String) : String := name ++ ":begin"
def runHead (name : String) : String := name ++ ":run"

/-- The heads that are not the module's own entries. -/
def allowed (name : String) (head : String) : Bool := head != beginHead name && head != runHead name

/-- The plan as data, with the plan's own free types as its table. -/
def planAtom (spec : Spec) : Atom := encoded (planTerm spec spec.plan.snapshot.freeTypes)

def beginBody (spec : Spec) : Atom := a "gslt:live:begin" [planAtom spec, v "source"]

def runBody (spec : Spec) : Atom :=
  a "let" [v "machine", a "gslt:live:begin" [planAtom spec, v "source"],
    a "let" [v "paged", a "gslt:live:advance" [v "machine", v "ticks", v "quantum"],
      a "gslt:live:trace" [v "paged"]]]

/-- `(: head (-> Atom … Atom %Undefined%))`: every argument is passed as data. -/
def declaration (head : String) (arity : Nat) : Atom :=
  .expression [.symbol ":", .symbol head,
    .expression (.symbol "->" :: (List.replicate arity (.symbol "Atom") ++ [.symbol "%Undefined%"]))]

def beginEquation (spec : Spec) (name : String) : SpaceSemantics.Equation := ⟨beginHead name, [v "source"], beginBody spec⟩
def runEquation (spec : Spec) (name : String) : SpaceSemantics.Equation :=
  ⟨runHead name, [v "source", v "ticks", v "quantum"], runBody spec⟩

/-- The emitted program. -/
def program (spec : Spec) (name : String) : Program where
  equations := [beginEquation spec name, runEquation spec name]
  declarations := [declaration (beginHead name) 1, declaration (runHead name) 3]
  layout := [.declaration, .equation, .declaration, .equation]

/-- The runtime with the module loaded after it. -/
def emittedRuntime (spec : Spec) (name : String) : Program := runtime.append (program spec name)

private def specialHeads : List String := ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "match"]

private def declaredHeadAllowed (name : String) : Atom → Bool
  | .expression [.symbol ":", .symbol head, .expression (.symbol "->" :: _)] => allowed name head
  | _ => true

/-- The entries are fresh: they are ordinary authored functions, the runtime never defines,
declares or calls them, and the inlined plan never names them. -/
def namesFresh (spec : Spec) (name : String) : Bool :=
  (beginHead name != runHead name) &&
  !specialHeads.contains (beginHead name) && !specialHeads.contains (runHead name) &&
  !ioHead (beginHead name) && !ioHead (runHead name) &&
  !StdLib.known (beginHead name) && !StdLib.known (runHead name) &&
  allowed name "let" &&
  runtime.equations.all (fun equation => allowed name equation.head && codeWithin (allowed name) equation.body) &&
  runtime.declarations.all (declaredHeadAllowed name) &&
  codeWithin (allowed name) (beginBody spec) && codeWithin (allowed name) (runBody spec)

/-! ## Admission -/

/-- Why a language is not emitted. -/
inductive Refusal where
  | obligations (pending : List GeneralExecutionAdmission.Obligation)
  | equations (count : Nat)
  | dynamicProvider
  | unstratified
  | nameCollision (name : String)
  | unrenderable

/-- **The emitter.** -/
def emit? (spec : Spec) (name : String) : Except Refusal Program :=
  match spec.plan.obligations with
  | _ :: _ => .error (.obligations spec.plan.obligations)
  | [] =>
    if spec.plan.equations.isEmpty then
      if spec.plan.snapshot.provider.dynamicRelations.isEmpty then
        if GeneralPremise.checkStepStratification (GeneralPlanEnvironment.environment spec.plan).language then
          if namesFresh spec name then .ok (program spec name) else .error (.nameCollision name)
        else .error .unstratified
      else .error .dynamicProvider
    else .error (.equations spec.plan.equations.length)

/-- What an emitted module guarantees about its plan and name. -/
structure Emitted (spec : Spec) (name : String) : Prop where
  complete : spec.plan.obligations = []
  empty : spec.plan.equations = []
  finiteProvider : spec.plan.snapshot.provider.dynamicRelations = []
  stratified : GeneralPremise.checkStepStratification (GeneralPlanEnvironment.environment spec.plan).language = true
  fresh : namesFresh spec name = true

theorem emit?_ok {spec : Spec} {name : String} {emitted : Program} (ok : emit? spec name = .ok emitted) :
    emitted = program spec name ∧ Emitted spec name := by
  unfold emit? at ok
  split at ok
  · cases ok
  · rename_i none
    by_cases empty : spec.plan.equations.isEmpty = true
    · rw [if_pos empty] at ok
      by_cases finite : spec.plan.snapshot.provider.dynamicRelations.isEmpty = true
      · rw [if_pos finite] at ok
        by_cases stratified : GeneralPremise.checkStepStratification
            (GeneralPlanEnvironment.environment spec.plan).language = true
        · rw [if_pos stratified] at ok
          by_cases fresh : namesFresh spec name = true
          · rw [if_pos fresh] at ok
            cases ok
            exact ⟨rfl, none, List.isEmpty_iff.mp empty, List.isEmpty_iff.mp finite, stratified, fresh⟩
          · rw [if_neg fresh] at ok; cases ok
        · rw [if_neg stratified] at ok; cases ok
      · rw [if_neg finite] at ok; cases ok
    · rw [if_neg empty] at ok; cases ok

/-! ## The runtime runs unchanged beneath the module -/

section Transport

variable {spec : Spec} {name : String}

private theorem fresh_parts (fresh : namesFresh spec name = true) :
    (beginHead name != runHead name) = true ∧
    specialHeads.contains (beginHead name) = false ∧ specialHeads.contains (runHead name) = false ∧
    ioHead (beginHead name) = false ∧ ioHead (runHead name) = false ∧
    StdLib.known (beginHead name) = false ∧ StdLib.known (runHead name) = false ∧
    allowed name "let" = true ∧
    runtime.equations.all (fun equation => allowed name equation.head && codeWithin (allowed name) equation.body)
      = true ∧
    runtime.declarations.all (declaredHeadAllowed name) = true ∧
    codeWithin (allowed name) (beginBody spec) = true ∧ codeWithin (allowed name) (runBody spec) = true := by
  simp only [namesFresh, Bool.and_eq_true, Bool.not_eq_true'] at fresh
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨distinct, special₁⟩, special₂⟩, io₁⟩, io₂⟩, known₁⟩, known₂⟩, letAllowed⟩, bodies⟩,
    declarations⟩, beginCode⟩, runCode⟩ := fresh
  exact ⟨distinct, special₁, special₂, io₁, io₂, known₁, known₂, letAllowed, bodies, declarations, beginCode,
    runCode⟩

theorem runtime_closed (fresh : namesFresh spec name = true) : ProgramClosed (allowed name) runtime := by
  obtain ⟨_, _, _, _, _, _, _, letAllowed, bodies, _⟩ := fresh_parts fresh
  refine ⟨letAllowed, fun equation member _ => ?_⟩
  have row := List.all_eq_true.mp bodies equation member
  simp only [Bool.and_eq_true] at row
  exact row.2

private theorem own_heads_not_allowed : ∀ equation ∈ (program spec name).equations,
    allowed name equation.head = false := by
  intro equation member
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · simp [allowed, beginEquation]
  · simp [allowed, runEquation]

theorem runtime_agreement : ProgramAgreementOn (allowed name) runtime (emittedRuntime spec name) := by
  apply appended_program_agreement
  · exact own_heads_not_allowed
  · intro head types member
    simp only [program, declaration, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same <;>
      · simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at same
        obtain ⟨_, rfl, _⟩ := same
        simp [allowed]

/-- Runtime code runs unchanged in the runtime with the module. -/
theorem transport (fresh : namesFresh spec name = true) {caller : Subst} {before after : State}
    {code answer : Atom} (supported : codeWithin (allowed name) code = true)
    (returned : PureReturns runtime caller before code after answer) :
    PureReturns (emittedRuntime spec name) caller before code after answer :=
  path_of_closed_agreement (runtime_closed fresh) runtime_agreement ⟨supported, rfl⟩ returned

/-- Only the module defines its entries. -/
private theorem entry_rows (fresh : namesFresh spec name = true) :
    (emittedRuntime spec name).equations.filter (fun row => row.head == beginHead name) =
        [beginEquation spec name] ∧
      (emittedRuntime spec name).equations.filter (fun row => row.head == runHead name) =
        [runEquation spec name] := by
  obtain ⟨distinct, _, _, _, _, _, _, _, bodies, _⟩ := fresh_parts fresh
  have below (head : String) (notAllowed : allowed name head = false) :
      runtime.equations.filter (fun row => row.head == head) = [] := by
    rw [List.filter_eq_nil_iff]
    intro row member same
    have checked := List.all_eq_true.mp bodies row member
    simp only [Bool.and_eq_true] at checked
    rw [beq_iff_eq.mp same, notAllowed] at checked
    exact Bool.false_ne_true checked.1
  have different : (beginHead name == runHead name) = false := by simpa using distinct
  have different' : (runHead name == beginHead name) = false := by
    rw [Bool.eq_false_iff]
    intro same
    rw [beq_iff_eq.mp same] at distinct
    simp at distinct
  have split : (emittedRuntime spec name).equations =
      runtime.equations ++ [beginEquation spec name, runEquation spec name] := rfl
  refine ⟨?_, ?_⟩
  · rw [split, List.filter_append, below (beginHead name) (by simp [allowed]), List.nil_append]
    simp [beginEquation, runEquation, different']
  · rw [split, List.filter_append, below (runHead name) (by simp [allowed]), List.nil_append]
    simp [beginEquation, runEquation, different]

private theorem entry_raw (fresh : namesFresh spec name = true) :
    (∀ index < 1, argumentIsRaw (emittedRuntime spec name) (beginHead name) index = true) ∧
      ∀ index < 3, argumentIsRaw (emittedRuntime spec name) (runHead name) index = true := by
  obtain ⟨_, _, _, _, _, known₁, known₂, _⟩ := fresh_parts fresh
  refine ⟨fun index bounded => ?_, fun index bounded => ?_⟩
  · unfold argumentIsRaw
    rw [known₁]
    simp only [Bool.false_eq_true, if_false, emittedRuntime, SpaceSemantics.Program.append, List.any_append,
      Bool.or_eq_true]
    refine .inr ?_
    have zero : index = 0 := by omega
    subst zero
    simp [program, declaration]
  · unfold argumentIsRaw
    rw [known₂]
    simp only [Bool.false_eq_true, if_false, emittedRuntime, SpaceSemantics.Program.append, List.any_append,
      Bool.or_eq_true]
    refine .inr ?_
    interval_cases index <;> simp [program, declaration]

end Transport

/-! ## The entries run the model -/

private theorem closed_arguments (values : List Atom) : values.map (applySubst []) = values := by
  have unchanged : applySubst [] = id := by
    funext value
    exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
  simp only [unchanged, List.map_id]

private theorem live_raw (head : String) (count : Nat)
    (checked : (List.range count).all (fun index => argumentIsRaw runtime head index) = true) :
    ∀ index < count, argumentIsRaw runtime head index = true :=
  fun index bounded => List.all_eq_true.mp checked index (List.mem_range.mpr bounded)

/-- The begin call of an entry, in the runtime. -/
private theorem begin_call (spec : Spec) (finiteProvider : spec.plan.snapshot.provider.dynamicRelations = [])
    (caller : Subst) (state : State) (source : Pattern)
    (captured : applySubst caller (v "source") = patternValue source) :
    PureReturns runtime caller state (a "gslt:live:begin" [planAtom spec, v "source"]) state
      (encoded ((Machine.begin spec source).term spec spec.plan.snapshot.freeTypes)) := by
  apply PureData.raw_capture_returns runtime [] caller state state "gslt:live:begin"
    [planAtom spec, patternValue source] [planAtom spec, v "source"] _ (by decide +kernel)
    (live_raw "gslt:live:begin" 2 (by decide +kernel)) (by decide)
  · simp [captured, planAtom]
  · exact begin_returns spec (tabled_freeTypes spec) finiteProvider state source

/-- **The begin entry** returns the live machine at the source. -/
theorem begin_entry_returns {spec : Spec} {name : String} (fresh : namesFresh spec name = true)
    (finiteProvider : spec.plan.snapshot.provider.dynamicRelations = [])
    (state : State) (source : Pattern) :
    PureReturns (emittedRuntime spec name) [] state (a (beginHead name) [patternValue source]) state
      (encoded ((Machine.begin spec source).term spec spec.plan.snapshot.freeTypes)) := by
  obtain ⟨_, special₁, _, io₁, _, known₁, _, _, _, _, beginCode, _⟩ := fresh_parts fresh
  let callee : Subst := [("source", patternValue source)]
  apply PureData.raw_authored_call_return (emittedRuntime spec name) [] callee state state (beginHead name)
    [patternValue source] (beginBody spec) _
    (by simpa [specialHeads] using special₁) io₁ known₁
  · simp [emittedRuntime, SpaceSemantics.Program.append, program, beginEquation]
  · simpa using (entry_raw fresh).1
  · rw [closed_arguments]
    exact PureData.named_equation_clause (emittedRuntime spec name) (beginHead name) (beginEquation spec name)
      ["source"] [patternValue source] (entry_rows fresh).1 rfl (by decide) rfl
  · exact transport fresh beginCode (begin_call spec finiteProvider callee state source (by simp [callee, applySubst, Subst.lookup]))

/-- The run body, in the runtime. -/
private theorem run_body_returns (spec : Spec) (finiteProvider : spec.plan.snapshot.provider.dynamicRelations = [])
    (state : State) (source : Pattern) (ticks quantum : Nat) :
    PureReturns runtime [("quantum", number quantum), ("ticks", number ticks), ("source", patternValue source)]
      state (runBody spec) state
      (encoded (Machine.advance spec ticks quantum (Machine.begin spec source)).traceTerm) := by
  let table := spec.plan.snapshot.freeTypes
  let caller : Subst := [("quantum", number quantum), ("ticks", number ticks), ("source", patternValue source)]
  let begun := Machine.begin spec source
  let paged := Machine.advance spec ticks quantum begun
  let withMachine := ("machine", encoded (begun.term spec table)) :: caller
  let withPaged := ("paged", encoded (paged.term spec table)) :: withMachine
  unfold runBody
  apply let_returns runtime caller withMachine state state state (v "machine") _ _
    (encoded (begun.term spec table)) _ (begin_call spec finiteProvider caller state source (by simp [caller, applySubst, Subst.lookup]))
  · simp [withMachine, caller, SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
  · apply let_returns runtime withMachine withPaged state state state (v "paged") _ _
      (encoded (paged.term spec table))
    · apply PureData.raw_capture_returns runtime [] withMachine state state "gslt:live:advance"
        [encoded (begun.term spec table), number ticks, number quantum] [v "machine", v "ticks", v "quantum"] _
        (by decide +kernel) (live_raw "gslt:live:advance" 3 (by decide +kernel)) (by decide)
      · simp [withMachine, caller, applySubst, Subst.lookup]
      · exact advance_returns spec (tabled_freeTypes spec) finiteProvider state ticks begun (spec.begin_reached source)
          quantum
    · simp [withPaged, withMachine, caller, SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
        Subst.lookup]
    · apply PureData.raw_capture_returns runtime [] withPaged state state "gslt:live:trace"
        [encoded (paged.term spec table)] [v "paged"] _ (by decide +kernel)
        (live_raw "gslt:live:trace" 1 (by decide +kernel)) (by decide)
      · simp [withPaged, withMachine, caller, applySubst, Subst.lookup]
      · exact trace_returns spec table state paged

/-- **The run entry** returns the trace of the model's run from the source. -/
theorem run_entry_returns {spec : Spec} {name : String} (fresh : namesFresh spec name = true)
    (finiteProvider : spec.plan.snapshot.provider.dynamicRelations = [])
    (state : State) (source : Pattern) (ticks quantum : Nat) :
    PureReturns (emittedRuntime spec name) [] state
      (a (runHead name) [patternValue source, number ticks, number quantum]) state
      (encoded (Machine.advance spec ticks quantum (Machine.begin spec source)).traceTerm) := by
  obtain ⟨_, _, special₂, _, io₂, _, known₂, _, _, _, _, runCode⟩ := fresh_parts fresh
  apply PureData.raw_authored_call_return (emittedRuntime spec name) []
    [("quantum", number quantum), ("ticks", number ticks), ("source", patternValue source)] state state
    (runHead name) [patternValue source, number ticks, number quantum] (runBody spec) _
    (by simpa [specialHeads] using special₂) io₂ known₂
  · simp [emittedRuntime, SpaceSemantics.Program.append, program, runEquation]
  · simpa using (entry_raw fresh).2
  · rw [closed_arguments]
    exact PureData.named_equation_clause (emittedRuntime spec name) (runHead name) (runEquation spec name)
      ["source", "ticks", "quantum"] [patternValue source, number ticks, number quantum] (entry_rows fresh).2 rfl
      (by decide) rfl
  · exact transport fresh runCode (run_body_returns spec finiteProvider state source ticks quantum)

/-! ## What an emitted module gives -/

/-- **Emitted modules run their language.** For every module that `emit?` returns, the actual
PeTTa run of its run entry prints the trace of a machine whose chronological states start at
the source and form a reduction sequence of the plan's GSLT, with every committed receipt valid
at the state before it; a normal ending means the last state has no step. -/
theorem emitted_run {spec : Spec} {name : String} {emitted : Program} (ok : emit? spec name = .ok emitted)
    (state : State) (source : Pattern) (ticks quantum : Nat) :
    let machine := Machine.advance spec ticks quantum (Machine.begin spec source)
    emitted = program spec name ∧
      PureReturns (runtime.append emitted) [] state
        (a (runHead name) [patternValue source, number ticks, number quantum]) state
        (encoded machine.traceTerm) ∧
      machine.states.reverse.head? = some source ∧ machine.states.reverse.IsChain spec.Step ∧
      spec.History machine.states machine.receipts ∧
      (machine.phase = .done → ∀ target, ¬ spec.Step machine.state target) := by
  intro machine
  obtain ⟨rfl, admitted⟩ := emit?_ok ok
  have reached := spec.run_reached source ticks quantum
  obtain ⟨starts, chained⟩ := spec.run_chain admitted.empty admitted.stratified source ticks quantum
  exact ⟨rfl, run_entry_returns admitted.fresh admitted.finiteProvider state source ticks quantum, starts, chained, reached.history,
    spec.done_no_step admitted.empty admitted.stratified reached⟩

/-! ## The module as text -/

/-- **The emitter, as text.** -/
def emitText? (spec : Spec) (name : String) : Except Refusal String := do
  let emitted ← emit? spec name
  match ReadAfterRender.renderProgram? emitted with
  | some text => pure text
  | none => throw .unrenderable

private theorem loaded_program (spec : Spec) (name : String) :
    SpaceSemantics.loadedAtoms (program spec name) =
      [declaration (beginHead name) 1, (beginEquation spec name).toAtom,
       declaration (runHead name) 3, (runEquation spec name).toAtom] := rfl

/-- **Emitted text reads back as the emitted program.** The shared source reader, the one that
reads every pinned library, reads the emitted text as exactly the program the run theorems are
about. -/
theorem emitted_text_reads_back {spec : Spec} {name : String} {text : String}
    (emitted : emitText? spec name = .ok text) : SpaceSemantics.readProgram text = .ok (program spec name) := by
  unfold emitText? at emitted
  cases ok : emit? spec name with
  | error refusal => rw [ok] at emitted; cases emitted
  | ok produced =>
    rw [ok] at emitted
    simp only [bind, Except.bind] at emitted
    obtain ⟨rfl, _⟩ := emit?_ok ok
    cases rendered : ReadAfterRender.renderProgram? (program spec name) with
    | none => rw [rendered] at emitted; cases emitted
    | some rendering =>
      rw [rendered] at emitted
      cases emitted
      have expressionsOnly : ReadAfterRender.AllExpressions (SpaceSemantics.loadedAtoms (program spec name)) := by
        rw [loaded_program]
        intro atom member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
      rw [ReadAfterRender.read_render rendered expressionsOnly, loaded_program]
      rfl

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralLiveRunnerEmission
