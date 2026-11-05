import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.ClassGraph
import Mettapedia.OSLF.MeTTaIL.Complete.QuoteDropCoherence
import Mettapedia.OSLF.MeTTaIL.Complete.WrapperCoherence

/-!
# Emitted complete modules run their language

For a module emitted with the class search profile, loaded after the runner's runtime, the actual
PeTTa run of each entry is the model:

- `name:begin source` is the runner at the source;
- `name:run source ticks quantum` is the trace of `ResumableSearchRunner.Machine.advance` over
  the search modulo equations that commits targets in standard, canonical, reflective or model form
  (`Complete.Normalized.search`);
- `name:explore source work` is the states of `Complete.Explore.explore` after `work` rounds,
  computed by stopping as soon as the explorer is settled (`Complete.Settled`);
- `name:edges source work` is the transition graph of that explorer (`Complete.Graph.edges`).

The plan's free table is its own list of free types; on its declared footprint that is exactly
the table the bridge theorems are stated on (`Complete.Footprint.entriesOn_declared`).
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.MeTTaIL.Complete.Footprint (Scope declaredFootprint)
open Mettapedia.Machines.ResumableSearchRunner (Machine)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open SpaceSemantics (Program)
open Eval
open WireKit
open CompleteExecution (classMachineTerm classTraceTerm explorerTerm RunnerReady CommitReady)
open StandardWire (commitTerm)

private abbrev a (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
private abbrev v (name : String) : Atom := .var name

/-- The runtime with the module loaded after it. -/
def emittedRuntime (spec : Spec) (name : String) (profile : SearchProfile spec := .classes) : Program :=
  runtime.append (program spec name profile)

/-- What the bridge theorems need of an emitted plan: its search stays within its declared
footprint, and its free names are distinct. -/
structure Footprinted (spec : Spec) : Prop where
  scope : Scope spec.plan (declaredFootprint spec.plan)
  distinct : (spec.plan.snapshot.freeTypes.map Prod.fst).Nodup

theorem Footprinted.tabled {spec : Spec} (footprinted : Footprinted spec) :
    spec.plan.snapshot.freeTypes = spec.plan.snapshot.free.entriesOn (declaredFootprint spec.plan) :=
  (Complete.Footprint.entriesOn_declared footprinted.distinct).symm

/-- A compiled plan the emitter accepts is footprinted. -/
theorem footprinted_of_compiled {snapshot : GeneralExecutionAdmission.Snapshot}
    {permissions : GeneralExecutionAdmission.Permissions} {bound : List TypeExpr} {expected : TypeExpr}
    {mode : Complete.Normalized.Commit} {name : String}
    (emitted : Emitted ⟨GeneralExecutionAdmission.compile snapshot permissions, bound, expected, mode⟩ name) :
    Footprinted ⟨GeneralExecutionAdmission.compile snapshot permissions, bound, expected, mode⟩ :=
  ⟨(Complete.Footprint.compiled_scope emitted.complete emitted.finiteProvider).1,
    Complete.Footprint.compiled_distinct emitted.complete⟩

/-! ## The runtime runs unchanged beneath the module -/

section Transport

variable {spec : Spec} {name : String} {profile : SearchProfile spec}

theorem fresh_parts (fresh : namesFresh spec name profile = true) :
    (entries name).Nodup ∧
    (∀ head ∈ entries name, specialHeads.contains head = false ∧ ioHead head = false ∧ StdLib.known head = false) ∧
    allowed name "let" = true ∧
    runtime.equations.all (fun equation => allowed name equation.head && codeWithin (allowed name) equation.body)
      = true ∧
    runtime.declarations.all (declaredHeadAllowed name) = true ∧
    codeWithin (allowed name) (beginBody spec profile) = true ∧ codeWithin (allowed name) (runBody spec profile) = true ∧
    codeWithin (allowed name) (exploreBody spec profile) = true ∧ codeWithin (allowed name) (edgesBody spec profile) = true := by
  simp only [namesFresh, Bool.and_eq_true, decide_eq_true_eq] at fresh
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨distinct, heads⟩, letAllowed⟩, bodies⟩, declarations⟩, beginCode⟩, runCode⟩, exploreCode⟩,
    edgesCode⟩ := fresh
  refine ⟨distinct, fun head member => ?_, letAllowed, bodies, declarations, beginCode, runCode, exploreCode,
    edgesCode⟩
  have row := List.all_eq_true.mp heads head member
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at row
  exact ⟨row.1.1, row.1.2, row.2⟩

theorem entry_facts (fresh : namesFresh spec name profile = true) {head : String} (member : head ∈ entries name) :
    head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique", "match"] ∧ ioHead head = false ∧
      StdLib.known head = false := by
  obtain ⟨special, io, known⟩ := (fresh_parts fresh).2.1 head member
  exact ⟨by simpa [specialHeads] using special, io, known⟩

theorem runtime_closed (fresh : namesFresh spec name profile = true) : ProgramClosed (allowed name) runtime := by
  obtain ⟨_, _, letAllowed, bodies, _⟩ := fresh_parts fresh
  refine ⟨letAllowed, fun equation member _ => ?_⟩
  have row := List.all_eq_true.mp bodies equation member
  simp only [Bool.and_eq_true] at row
  exact row.2

private theorem own_heads_not_allowed : ∀ equation ∈ (program spec name profile).equations,
    allowed name equation.head = false := by
  intro equation member
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    simp [allowed, entries, beginEquation, runEquation, exploreEquation, edgesEquation]

theorem runtime_agreement : ProgramAgreementOn (allowed name) runtime (emittedRuntime spec name profile) := by
  apply appended_program_agreement
  · exact own_heads_not_allowed
  · intro head types member
    simp only [program, declaration, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same | same | same <;>
      · simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at same
        obtain ⟨_, rfl, _⟩ := same
        simp [allowed, entries]

/-- Runtime code runs unchanged in the runtime with the module. -/
theorem transport (fresh : namesFresh spec name profile = true) {caller : Subst} {before after : State}
    {code answer : Atom} (supported : codeWithin (allowed name) code = true)
    (returned : PureReturns runtime caller before code after answer) :
    PureReturns (emittedRuntime spec name profile) caller before code after answer :=
  path_of_closed_agreement (runtime_closed fresh) runtime_agreement ⟨supported, rfl⟩ returned

/-- Only the module defines its entries. -/
theorem entry_row (fresh : namesFresh spec name profile = true) (equation : SpaceSemantics.Equation)
    (listed : equation ∈ (program spec name profile).equations) :
    (emittedRuntime spec name profile).equations.filter (fun row => row.head == equation.head) = [equation] := by
  obtain ⟨distinct, _, _, bodies, _⟩ := fresh_parts fresh
  have below : runtime.equations.filter (fun row => row.head == equation.head) = [] := by
    rw [List.filter_eq_nil_iff]
    intro row member same
    have checked := List.all_eq_true.mp bodies row member
    simp only [Bool.and_eq_true] at checked
    rw [beq_iff_eq.mp same, own_heads_not_allowed equation listed] at checked
    exact Bool.false_ne_true checked.1
  have split : (emittedRuntime spec name profile).equations = runtime.equations ++ (program spec name profile).equations := rfl
  rw [split, List.filter_append, below, List.nil_append]
  simp only [entries, List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil,
    not_false_eq_true, List.nodup_nil, and_true] at distinct
  obtain ⟨⟨beginRun, beginExplore, beginEdges⟩, ⟨runExplore, runEdges⟩, exploreEdges⟩ := distinct
  simp only [program, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl <;>
    simp [program, beginEquation, runEquation, exploreEquation, edgesEquation, beginRun, beginExplore, runExplore,
      beginEdges, runEdges, exploreEdges, Ne.symm beginRun, Ne.symm beginExplore, Ne.symm runExplore,
      Ne.symm beginEdges, Ne.symm runEdges, Ne.symm exploreEdges]

theorem entry_raw (head : String) (arity : Nat) (known : StdLib.known head = false)
    (declared : declaration head arity ∈ (program spec name profile).declarations) :
    ∀ index < arity, argumentIsRaw (emittedRuntime spec name profile) head index = true := by
  intro index bounded
  unfold argumentIsRaw
  rw [known]
  simp only [Bool.false_eq_true, if_false, emittedRuntime, SpaceSemantics.Program.append, List.any_append,
    Bool.or_eq_true]
  refine .inr (List.any_eq_true.mpr ⟨declaration head arity, declared, ?_⟩)
  have inside : index < (List.replicate arity (Atom.symbol "Atom")).length := by simpa using bounded
  simp [declaration, List.getElem?_append_left inside, bounded]

end Transport

/-! ## The entries run the model -/

theorem closed_arguments (values : List Atom) : values.map (applySubst []) = values := by
  have unchanged : applySubst [] = id := by
    funext value
    exact Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil value
  simp only [unchanged, List.map_id]

theorem runtime_raw (head : String) (count : Nat)
    (checked : (List.range count).all (fun index => argumentIsRaw runtime head index) = true) :
    ∀ index < count, argumentIsRaw runtime head index = true :=
  fun index bounded => List.all_eq_true.mp checked index (List.mem_range.mpr bounded)

variable {spec : Spec}

/-- The machine at the source. -/
abbrev begun (spec : Spec) (source : Pattern) : CompleteExecution.ClassMachine spec.plan :=
  Machine.begin (Complete.Normalized.search spec.plan spec.bound spec.expected spec.mode)
    (Complete.Normalized.commit spec.plan spec.mode source)

/-- The machine after a page of ticks. -/
abbrev paged (spec : Spec) (source : Pattern) (ticks quantum : Nat) : CompleteExecution.ClassMachine spec.plan :=
  Machine.advance (Complete.Normalized.search spec.plan spec.bound spec.expected spec.mode) ticks quantum
    (begun spec source)

private theorem begin_call (footprinted : Footprinted spec) (caller : Subst) (state : State) (source : Pattern)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ declaredFootprint spec.plan)
    (ready : CommitReady spec.mode (table spec) source)
    (captured : applySubst caller (v "source") = CompleteExecution.patternValue source) :
    PureReturns runtime caller state (a "gslt:runner:begin" [CompleteExecution.classSearchBackend, planAtom spec, standardAtom spec, v "source"]) state
      (encoded (classMachineTerm spec.plan (begun spec source))) := by
  apply PureData.raw_capture_returns runtime [] caller state state "gslt:runner:begin"
    [CompleteExecution.classSearchBackend, planAtom spec, standardAtom spec, CompleteExecution.patternValue source]
    [CompleteExecution.classSearchBackend, planAtom spec, standardAtom spec, v "source"] _ (by decide +kernel)
    (runtime_raw "gslt:runner:begin" 4 (by decide +kernel)) (by decide)
  · simp [captured, planAtom, standardAtom]; rfl
  · exact CompleteExecution.runner_begin_returns spec.plan state spec.mode (table spec) (table_for spec) _ spec.bound
      spec.expected _ footprinted.tabled footprinted.scope.declared source inside ready

/-- **The begin entry** returns the runner at the source. -/
theorem begin_entry_returns {name : String} (fresh : namesFresh spec name = true) (footprinted : Footprinted spec)
    (state : State) (source : Pattern) (inside : ∀ name ∈ source.freeFvarNames, name ∈ declaredFootprint spec.plan)
    (ready : CommitReady spec.mode (table spec) source) :
    PureReturns (emittedRuntime spec name) [] state (a (beginHead name) [CompleteExecution.patternValue source]) state
      (encoded (classMachineTerm spec.plan (begun spec source))) := by
  obtain ⟨special, io, known⟩ := entry_facts fresh (head := beginHead name) (by simp [entries])
  let callee : Subst := [("source", CompleteExecution.patternValue source)]
  apply PureData.raw_authored_call_return (emittedRuntime spec name) [] callee state state (beginHead name)
    [CompleteExecution.patternValue source] (beginBody spec) _ special io known
  · simp [emittedRuntime, SpaceSemantics.Program.append, program, beginEquation]
  · simpa using entry_raw (spec := spec) (name := name) (beginHead name) 1 known (by simp [program])
  · rw [closed_arguments]
    exact PureData.named_equation_clause (emittedRuntime spec name) (beginHead name) (beginEquation spec name)
      ["source"] [CompleteExecution.patternValue source]
      (entry_row fresh (beginEquation spec name) (by simp [program])) rfl (by decide) rfl
  · exact transport fresh (fresh_parts fresh).2.2.2.2.2.1
      (begin_call footprinted callee state source inside ready (by simp [callee, applySubst, Subst.lookup]))

private theorem run_body_returns (footprinted : Footprinted spec) (state : State) (source : Pattern)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ declaredFootprint spec.plan)
    (ready : CommitReady spec.mode (table spec) source) (ticks quantum : Nat) :
    PureReturns runtime [("quantum", number quantum), ("ticks", number ticks),
        ("source", CompleteExecution.patternValue source)]
      state (runBody spec) state (encoded (classTraceTerm spec.plan (paged spec source ticks quantum))) := by
  let caller : Subst := [("quantum", number quantum), ("ticks", number ticks),
    ("source", CompleteExecution.patternValue source)]
  let withMachine := ("machine", encoded (classMachineTerm spec.plan (begun spec source))) :: caller
  let withPaged := ("paged", encoded (classMachineTerm spec.plan (paged spec source ticks quantum))) :: withMachine
  have searchReady : RunnerReady spec.bound spec.expected (declaredFootprint spec.plan) (begun spec source) :=
    CompleteExecution.searchReady_begin footprinted.scope
      (Complete.Normalized.commit_within spec.plan spec.mode source _ inside)
  unfold runBody
  apply let_returns runtime caller withMachine state state state (v "machine") _ _
    (encoded (classMachineTerm spec.plan (begun spec source))) _
    (begin_call footprinted caller state source inside ready (by simp [caller, applySubst, Subst.lookup]))
  · simp [withMachine, caller, SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
  · apply let_returns runtime withMachine withPaged state state state (v "paged") _ _
      (encoded (classMachineTerm spec.plan (paged spec source ticks quantum)))
    · apply PureData.raw_capture_returns runtime [] withMachine state state "gslt:runner:advance"
        [CompleteExecution.classSearchBackend, CompleteExecution.planValue spec.plan spec.plan.snapshot.freeTypes spec.bound spec.expected,
          encoded (commitTerm spec.plan spec.mode (table spec)), number ticks, number quantum,
          encoded (classMachineTerm spec.plan (begun spec source))]
        [CompleteExecution.classSearchBackend, planAtom spec, standardAtom spec, v "ticks", v "quantum", v "machine"] _
        (by decide +kernel) (runtime_raw "gslt:runner:advance" 6 (by decide +kernel)) (by decide)
      · simp [withMachine, caller, planAtom, standardAtom, applySubst, Subst.lookup]
      · exact CompleteExecution.runner_advance_returns spec.plan state spec.mode (table spec) (table_for spec) _
          spec.bound spec.expected _ footprinted.tabled footprinted.scope quantum ticks (begun spec source) searchReady
    · simp [withPaged, withMachine, caller, SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
        Subst.lookup]
    · apply PureData.raw_capture_returns runtime [] withPaged state state "gslt:runner:trace"
        [encoded (classMachineTerm spec.plan (paged spec source ticks quantum))] [v "paged"] _ (by decide +kernel)
        (runtime_raw "gslt:runner:trace" 1 (by decide +kernel)) (by decide)
      · simp [withPaged, withMachine, caller, applySubst, Subst.lookup]
      · exact CompleteExecution.runner_trace_returns spec.plan state (paged spec source ticks quantum)

/-- **The run entry** returns the trace of the model's run from the source. -/
theorem run_entry_returns {name : String} (fresh : namesFresh spec name = true) (footprinted : Footprinted spec)
    (state : State) (source : Pattern) (inside : ∀ name ∈ source.freeFvarNames, name ∈ declaredFootprint spec.plan)
    (ready : CommitReady spec.mode (table spec) source)
    (ticks quantum : Nat) :
    PureReturns (emittedRuntime spec name) [] state
      (a (runHead name) [CompleteExecution.patternValue source, number ticks, number quantum]) state
      (encoded (classTraceTerm spec.plan (paged spec source ticks quantum))) := by
  obtain ⟨special, io, known⟩ := entry_facts fresh (head := runHead name) (by simp [entries])
  apply PureData.raw_authored_call_return (emittedRuntime spec name) []
    [("quantum", number quantum), ("ticks", number ticks), ("source", CompleteExecution.patternValue source)]
    state state (runHead name) [CompleteExecution.patternValue source, number ticks, number quantum] (runBody spec) _
    special io known
  · simp [emittedRuntime, SpaceSemantics.Program.append, program, runEquation]
  · simpa using entry_raw (spec := spec) (name := name) (runHead name) 3 known (by simp [program])
  · rw [closed_arguments]
    exact PureData.named_equation_clause (emittedRuntime spec name) (runHead name) (runEquation spec name)
      ["source", "ticks", "quantum"] [CompleteExecution.patternValue source, number ticks, number quantum]
      (entry_row fresh (runEquation spec name) (by simp [program])) rfl (by decide) rfl
  · exact transport fresh (fresh_parts fresh).2.2.2.2.2.2.1
      (run_body_returns footprinted state source inside ready ticks quantum)

/-- The explorer after `work` rounds. -/
abbrev explored (spec : Spec) (source : Pattern) (work : Nat) : CompleteExecution.ClassExplorer spec.plan :=
  Complete.Explore.explore (Complete.Normalized.search spec.plan spec.bound spec.expected spec.mode)
    (Complete.Normalized.commit spec.plan spec.mode source) work

private theorem explore_body_returns (footprinted : Footprinted spec) (state : State) (source : Pattern)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ declaredFootprint spec.plan)
    (ready : CommitReady spec.mode (table spec) source) (work : Nat) :
    PureReturns runtime [("work", number work), ("source", CompleteExecution.patternValue source)]
      state (exploreBody spec) state
      (CompleteExecution.patternsValue ((explored spec source work).nodes.map (·.state))) := by
  let search := Complete.Normalized.search spec.plan spec.bound spec.expected spec.mode
  let start := Complete.Explore.begin search (Complete.Normalized.commit spec.plan spec.mode source)
  let caller : Subst := [("work", number work), ("source", CompleteExecution.patternValue source)]
  let withExplorer := ("explorer", encoded (explorerTerm spec.plan start)) :: caller
  let final := Complete.Settled.roundsUntilSettled search work start
  let withExplored := ("explored", encoded (explorerTerm spec.plan final)) :: withExplorer
  have nodesReady : ∀ node ∈ start.nodes,
      CompleteExecution.NodeReady spec.bound spec.expected (declaredFootprint spec.plan) node := by
    intro node member
    simp only [start, Complete.Explore.begin, List.mem_singleton] at member
    subst member
    exact CompleteExecution.searchReady_begin footprinted.scope
      (Complete.Normalized.commit_within spec.plan spec.mode source _ inside)
  have rounds := CompleteExecution.explore_rounds_returns spec.plan state spec.mode (table spec) (table_for spec) _
    spec.bound spec.expected _ footprinted.tabled footprinted.scope work start nodesReady
  have sameStates : final.nodes.map (·.state) = (explored spec source work).nodes.map (·.state) := by
    rw [Complete.Settled.roundsUntilSettled_states
        (Complete.Settled.normalized_stable spec.plan spec.bound spec.expected spec.mode),
      CompleteExecution.iterate_begin]
  unfold exploreBody
  apply let_returns runtime caller withExplorer state state state (v "explorer") _ _
    (encoded (explorerTerm spec.plan start))
  · apply PureData.raw_capture_returns runtime [] caller state state "gslt:explore:begin"
      [CompleteExecution.classSearchBackend, CompleteExecution.planValue spec.plan spec.plan.snapshot.freeTypes spec.bound spec.expected,
        encoded (commitTerm spec.plan spec.mode (table spec)), CompleteExecution.patternValue source]
      [CompleteExecution.classSearchBackend, planAtom spec, standardAtom spec, v "source"] _ (by decide +kernel)
      (runtime_raw "gslt:explore:begin" 4 (by decide +kernel)) (by decide)
    · simp [caller, planAtom, standardAtom, applySubst, Subst.lookup]
    · exact CompleteExecution.explore_begin_returns spec.plan state spec.mode (table spec) (table_for spec) _
        spec.bound spec.expected _ footprinted.tabled footprinted.scope.declared source inside ready
  · simp [withExplorer, caller, SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
  · apply let_returns runtime withExplorer withExplored state state state (v "explored") _ _
      (encoded (explorerTerm spec.plan final))
    · apply PureData.raw_capture_returns runtime [] withExplorer state state "gslt:explore:rounds"
        [CompleteExecution.classSearchBackend, CompleteExecution.planValue spec.plan spec.plan.snapshot.freeTypes spec.bound spec.expected,
          encoded (commitTerm spec.plan spec.mode (table spec)), number work, encoded (explorerTerm spec.plan start)]
        [CompleteExecution.classSearchBackend, planAtom spec, standardAtom spec, v "work", v "explorer"] _
        (by decide +kernel) (runtime_raw "gslt:explore:rounds" 5 (by decide +kernel)) (by decide)
      · simp [withExplorer, caller, planAtom, standardAtom, applySubst, Subst.lookup]
      · exact rounds
    · simp [withExplored, withExplorer, caller, SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
        Subst.lookup]
    · rw [← sameStates]
      apply PureData.raw_capture_returns runtime [] withExplored state state "gslt:explore:states"
        [encoded (explorerTerm spec.plan final)] [v "explored"] _ (by decide +kernel)
        (runtime_raw "gslt:explore:states" 1 (by decide +kernel)) (by decide)
      · simp [withExplored, withExplorer, caller, applySubst, Subst.lookup]
      · exact CompleteExecution.explore_states_returns spec.plan state final

/-- **The explore entry** returns the states of the model's exploration after `work` rounds. -/
theorem explore_entry_returns {name : String} (fresh : namesFresh spec name = true)
    (footprinted : Footprinted spec) (state : State) (source : Pattern)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ declaredFootprint spec.plan)
    (ready : CommitReady spec.mode (table spec) source) (work : Nat) :
    PureReturns (emittedRuntime spec name) [] state
      (a (exploreHead name) [CompleteExecution.patternValue source, number work]) state
      (CompleteExecution.patternsValue ((explored spec source work).nodes.map (·.state))) := by
  obtain ⟨special, io, known⟩ := entry_facts fresh (head := exploreHead name) (by simp [entries])
  apply PureData.raw_authored_call_return (emittedRuntime spec name) []
    [("work", number work), ("source", CompleteExecution.patternValue source)]
    state state (exploreHead name) [CompleteExecution.patternValue source, number work] (exploreBody spec) _
    special io known
  · simp [emittedRuntime, SpaceSemantics.Program.append, program, exploreEquation]
  · simpa using entry_raw (spec := spec) (name := name) (exploreHead name) 2 known (by simp [program])
  · rw [closed_arguments]
    exact PureData.named_equation_clause (emittedRuntime spec name) (exploreHead name) (exploreEquation spec name)
      ["source", "work"] [CompleteExecution.patternValue source, number work]
      (entry_row fresh (exploreEquation spec name) (by simp [program])) rfl (by decide) rfl
  · exact transport fresh (fresh_parts fresh).2.2.2.2.2.2.2.1
      (explore_body_returns footprinted state source inside ready work)

/-- The explorer after up to `work` rounds, stopped as soon as it is settled. -/
abbrev settledExplorer (spec : Spec) (source : Pattern) (work : Nat) : CompleteExecution.ClassExplorer spec.plan :=
  Complete.Settled.roundsUntilSettled (Complete.Normalized.search spec.plan spec.bound spec.expected spec.mode) work
    (Complete.Explore.begin (Complete.Normalized.search spec.plan spec.bound spec.expected spec.mode)
      (Complete.Normalized.commit spec.plan spec.mode source))

/-- The transitions of that explorer. -/
abbrev graph (spec : Spec) (source : Pattern) (work : Nat) :
    List (Pattern × GeneralOccurrenceSemantics.Receipt × Pattern) :=
  Complete.Graph.edges (Complete.Normalized.search spec.plan spec.bound spec.expected spec.mode)
    (settledExplorer spec source work)

private theorem edges_body_returns (footprinted : Footprinted spec) (state : State) (source : Pattern)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ declaredFootprint spec.plan)
    (ready : CommitReady spec.mode (table spec) source) (work : Nat) :
    PureReturns runtime [("work", number work), ("source", CompleteExecution.patternValue source)]
      state (edgesBody spec) state (encoded (encodeList CompleteExecution.edgeTerm (graph spec source work))) := by
  let search := Complete.Normalized.search spec.plan spec.bound spec.expected spec.mode
  let start := Complete.Explore.begin search (Complete.Normalized.commit spec.plan spec.mode source)
  let caller : Subst := [("work", number work), ("source", CompleteExecution.patternValue source)]
  let withExplorer := ("explorer", encoded (explorerTerm spec.plan start)) :: caller
  let final := Complete.Settled.roundsUntilSettled search work start
  let withExplored := ("explored", encoded (explorerTerm spec.plan final)) :: withExplorer
  have nodesReady : ∀ node ∈ start.nodes,
      CompleteExecution.NodeReady spec.bound spec.expected (declaredFootprint spec.plan) node := by
    intro node member
    simp only [start, Complete.Explore.begin, List.mem_singleton] at member
    subst member
    exact CompleteExecution.searchReady_begin footprinted.scope
      (Complete.Normalized.commit_within spec.plan spec.mode source _ inside)
  have rounds := CompleteExecution.explore_rounds_returns spec.plan state spec.mode (table spec) (table_for spec) _
    spec.bound spec.expected _ footprinted.tabled footprinted.scope work start nodesReady
  unfold edgesBody
  apply let_returns runtime caller withExplorer state state state (v "explorer") _ _
    (encoded (explorerTerm spec.plan start))
  · apply PureData.raw_capture_returns runtime [] caller state state "gslt:explore:begin"
      [CompleteExecution.classSearchBackend, CompleteExecution.planValue spec.plan spec.plan.snapshot.freeTypes spec.bound spec.expected,
        encoded (commitTerm spec.plan spec.mode (table spec)), CompleteExecution.patternValue source]
      [CompleteExecution.classSearchBackend, planAtom spec, standardAtom spec, v "source"] _ (by decide +kernel)
      (runtime_raw "gslt:explore:begin" 4 (by decide +kernel)) (by decide)
    · simp [caller, planAtom, standardAtom, applySubst, Subst.lookup]
    · exact CompleteExecution.explore_begin_returns spec.plan state spec.mode (table spec) (table_for spec) _
        spec.bound spec.expected _ footprinted.tabled footprinted.scope.declared source inside ready
  · simp [withExplorer, caller, SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom, Subst.lookup]
  · apply let_returns runtime withExplorer withExplored state state state (v "explored") _ _
      (encoded (explorerTerm spec.plan final))
    · apply PureData.raw_capture_returns runtime [] withExplorer state state "gslt:explore:rounds"
        [CompleteExecution.classSearchBackend, CompleteExecution.planValue spec.plan spec.plan.snapshot.freeTypes spec.bound spec.expected,
          encoded (commitTerm spec.plan spec.mode (table spec)), number work, encoded (explorerTerm spec.plan start)]
        [CompleteExecution.classSearchBackend, planAtom spec, standardAtom spec, v "work", v "explorer"] _
        (by decide +kernel) (runtime_raw "gslt:explore:rounds" 5 (by decide +kernel)) (by decide)
      · simp [withExplorer, caller, planAtom, standardAtom, applySubst, Subst.lookup]
      · exact rounds
    · simp [withExplored, withExplorer, caller, SpaceSemantics.matchBinding, SpaceSemantics.matchValue, matchAtom,
        Subst.lookup]
    · apply PureData.raw_capture_returns runtime [] withExplored state state "gslt:explore:edges"
        [CompleteExecution.classSearchBackend, encoded (commitTerm spec.plan spec.mode (table spec)), encoded (explorerTerm spec.plan final)]
        [CompleteExecution.classSearchBackend, standardAtom spec, v "explored"] _
        (by decide +kernel) (runtime_raw "gslt:explore:edges" 3 (by decide +kernel)) (by decide)
      · simp [withExplored, withExplorer, caller, standardAtom, applySubst, Subst.lookup]
      · exact CompleteExecution.explore_edges_returns spec.plan state spec.mode (table spec) (table_for spec)
          spec.bound spec.expected final fun node member =>
            (CompleteExecution.rounds_ready footprinted.scope spec.mode work start nodesReady node member).2

/-- **The edges entry** returns the transition graph of the model's exploration. -/
theorem edges_entry_returns {name : String} (fresh : namesFresh spec name = true)
    (footprinted : Footprinted spec) (state : State) (source : Pattern)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ declaredFootprint spec.plan)
    (ready : CommitReady spec.mode (table spec) source) (work : Nat) :
    PureReturns (emittedRuntime spec name) [] state
      (a (edgesHead name) [CompleteExecution.patternValue source, number work]) state
      (encoded (encodeList CompleteExecution.edgeTerm (graph spec source work))) := by
  obtain ⟨special, io, known⟩ := entry_facts fresh (head := edgesHead name) (by simp [entries])
  apply PureData.raw_authored_call_return (emittedRuntime spec name) []
    [("work", number work), ("source", CompleteExecution.patternValue source)]
    state state (edgesHead name) [CompleteExecution.patternValue source, number work] (edgesBody spec) _
    special io known
  · simp [emittedRuntime, SpaceSemantics.Program.append, program, edgesEquation]
  · simpa using entry_raw (spec := spec) (name := name) (edgesHead name) 2 known (by simp [program])
  · rw [closed_arguments]
    exact PureData.named_equation_clause (emittedRuntime spec name) (edgesHead name) (edgesEquation spec name)
      ["source", "work"] [CompleteExecution.patternValue source, number work]
      (entry_row fresh (edgesEquation spec name) (by simp [program])) rfl (by decide) rfl
  · exact transport fresh (fresh_parts fresh).2.2.2.2.2.2.2.2
      (edges_body_returns footprinted state source inside ready work)

/-! ## What an emitted module gives -/

/-- **Emitted complete modules run their language.** For every class-profile module that `emit?` returns
for a footprinted plan, and every source whose free names are declared, the actual PeTTa runs of
its entries print the model: the run entry prints the trace of the runner over the search
modulo equations after any page of ticks, and the explore entry prints the states every path
has reached after any number of fair rounds. -/
theorem emitted_complete {name : String} {emitted : Program} (ok : emit? spec name .classes = .ok emitted)
    (footprinted : Footprinted spec) (state : State) (source : Pattern)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ declaredFootprint spec.plan)
    (ready : CommitReady spec.mode (table spec) source) :
    emitted = program spec name ∧
      (∀ ticks quantum : Nat, PureReturns (runtime.append emitted) [] state
        (a (runHead name) [CompleteExecution.patternValue source, number ticks, number quantum]) state
        (encoded (classTraceTerm spec.plan (paged spec source ticks quantum)))) ∧
      ∀ work : Nat, PureReturns (runtime.append emitted) [] state
        (a (exploreHead name) [CompleteExecution.patternValue source, number work]) state
        (CompleteExecution.patternsValue ((explored spec source work).nodes.map (·.state))) := by
  obtain ⟨rfl, admitted⟩ := emit?_ok ok
  exact ⟨rfl, fun ticks quantum => run_entry_returns admitted.fresh footprinted state source inside ready ticks quantum,
    fun work => explore_entry_returns admitted.fresh footprinted state source inside ready work⟩

/-- **Emitted complete modules run their language, modulo its equations, in committed form.**
For every class-profile module that `emit?` returns for a footprinted plan, and every source whose free names
are declared and which its commit mode can commit:

- after any page of ticks, the PeTTa run of the run entry prints the trace of a machine whose
  states start at the source's committed form and each reach the next by a step of the plan's GSLT
  modulo its equations followed by the committed form, and a normal ending means the last state has
  no step;
- for a module committing standard forms of a language that declares no collection or
  scope-extrusion laws, every state reachable from the source by finitely many GSLT steps is, up
  to the equations, among the states the PeTTa run of the explore entry prints after some number
  of rounds. -/
theorem emitted_runs_language {name : String} {emitted : Program} (ok : emit? spec name .classes = .ok emitted)
    (footprinted : Footprinted spec) (state : State) (source : Pattern)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ declaredFootprint spec.plan)
    (ready : CommitReady spec.mode (table spec) source) :
    emitted = program spec name ∧
      (∀ ticks quantum : Nat,
        PureReturns (runtime.append emitted) [] state
          (a (runHead name) [CompleteExecution.patternValue source, number ticks, number quantum]) state
          (encoded (classTraceTerm spec.plan (paged spec source ticks quantum))) ∧
        (paged spec source ticks quantum).states.reverse.head? =
          some (Complete.Normalized.commit spec.plan spec.mode source) ∧
        (paged spec source ticks quantum).states.reverse.IsChain
          (Complete.Normalized.NormalizedStep spec.plan spec.bound spec.expected spec.mode) ∧
        ((paged spec source ticks quantum).phase = .done → ∀ target,
          ¬ (GeneralOccurrenceSemantics.gslt spec.plan spec.bound spec.expected).Step
            (paged spec source ticks quantum).state target)) ∧
      (spec.mode = .standard → Complete.Normalized.laws spec.plan = [] ∧ Complete.Normalized.extrusions spec.plan = [] →
        ∀ target, (GeneralOccurrenceSemantics.gslt spec.plan spec.bound spec.expected).MultiStep source target →
          ∃ work, ∃ reached ∈ (explored spec source work).nodes.map (·.state),
            Relation.EqvGen (GeneralOccurrenceSemantics.Equation spec.plan spec.bound spec.expected) reached target ∧
            PureReturns (runtime.append emitted) [] state
              (a (exploreHead name) [CompleteExecution.patternValue source, number work]) state
              (CompleteExecution.patternsValue ((explored spec source work).nodes.map (·.state)))) := by
  obtain ⟨rfl, admitted⟩ := emit?_ok ok
  refine ⟨rfl, fun ticks quantum => ?_, fun standard free target reaches => ?_⟩
  · obtain ⟨starts, chained⟩ := Complete.Normalized.run_chain spec.plan spec.bound spec.expected
      (Complete.Normalized.commit spec.plan spec.mode source) ticks quantum spec.mode
    exact ⟨run_entry_returns admitted.fresh footprinted state source inside ready ticks quantum, starts, chained,
      Complete.Normalized.done_no_step spec.plan spec.bound spec.expected admitted.balanced
        (Mettapedia.Machines.ResumableSearchRunner.run_reached
          (Complete.Normalized.search_lawful spec.plan spec.bound spec.expected spec.mode)
          (Complete.Normalized.commit spec.plan spec.mode source) ticks quantum)⟩
  · obtain ⟨reached, ⟨work, node, member, rfl⟩, related⟩ :=
      Complete.Explore.explores_multistep spec.plan spec.bound spec.expected admitted.balanced source reaches
    have same : explored spec source work =
        Complete.Explore.explore (Complete.Classes.search spec.plan spec.bound spec.expected) source work := by
      simp only [explored, standard, Complete.Normalized.commit,
        Complete.Normalized.search_lawFree spec.plan spec.bound spec.expected free,
        Complete.Normalized.standard_lawFree spec.plan free]
    exact ⟨work, node.state, List.mem_map.mpr ⟨node, same ▸ member, rfl⟩, related,
      explore_entry_returns admitted.fresh footprinted state source inside ready work⟩

/-- **Emitted modules committing canonical forms explore the presented GSLT.** For every class-profile module
that `emit?` returns for a footprinted plan committing canonical forms, without scope extrusion,
whose canonical explorer is complete for the presented GSLT at the source (`explores`, which
`CanonicalCoherence` and `DescentCoherence` prove for admitted plans), every state reachable from
the source by the presented GSLT (steps modulo equality in the model) is, up to that equality,
among the states the PeTTa run of the explore entry prints after some number of rounds. -/
theorem emitted_explores_presented {name : String} {emitted : Program} (ok : emit? spec name .classes = .ok emitted)
    (footprinted : Footprinted spec) (state : State) (source : Pattern)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ declaredFootprint spec.plan)
    (ready : CommitReady spec.mode (table spec) source)
    (canonical : spec.mode = .canonical) (noExtrusions : Complete.Normalized.extrusions spec.plan = [])
    (explores : ∀ target, (Complete.Presented.gslt spec.plan spec.bound spec.expected).MultiStep source target →
      ∃ reached, Complete.Explore.Explored (S := Complete.CanonicalCoherence.search spec.plan spec.bound spec.expected)
          (CanonicalBags.lawNormal (Complete.Normalized.laws spec.plan) source) reached ∧
        Complete.Presented.ModelEquiv spec.plan spec.bound spec.expected reached target) :
    ∀ target, (Complete.Presented.gslt spec.plan spec.bound spec.expected).MultiStep source target →
      ∃ work, ∃ reached ∈ (explored spec source work).nodes.map (·.state),
        Complete.Presented.ModelEquiv spec.plan spec.bound spec.expected reached target ∧
        PureReturns (runtime.append emitted) [] state
          (a (exploreHead name) [CompleteExecution.patternValue source, number work]) state
          (CompleteExecution.patternsValue ((explored spec source work).nodes.map (·.state))) := by
  obtain ⟨rfl, admitted⟩ := emit?_ok ok
  intro target reaches
  obtain ⟨reached, ⟨work, node, member, rfl⟩, related⟩ := explores target reaches
  have same : explored spec source work = Complete.Explore.explore
      (Complete.CanonicalCoherence.search spec.plan spec.bound spec.expected)
      (CanonicalBags.lawNormal (Complete.Normalized.laws spec.plan) source) work := by
    simp only [explored, canonical, Complete.CanonicalCoherence.search_canonical spec.plan spec.bound spec.expected
      noExtrusions, Complete.CanonicalCoherence.commit_canonical noExtrusions]
  exact ⟨work, node.state, List.mem_map.mpr ⟨node, same ▸ member, rfl⟩, related,
    explore_entry_returns admitted.fresh footprinted state source inside ready work⟩

/-- **Emitted modules committing quote-drop normal forms explore the model with the name
equation.** For every class-profile module that `emit?` returns for a footprinted plan committing the canonical
form of the quote-drop normal form of a reflective presentation, without scope extrusion, whose
explorer is complete modulo that model at the source (`explores`, which
`QuoteDropCoherence.presented_explores_quoteDrop` proves for admitted plans), every state reachable
from the source by steps modulo the model is, up to that model, among the states the PeTTa run of the
explore entry prints after some number of rounds. -/
theorem emitted_explores_quoteDrop {name : String} {emitted : Program} (ok : emit? spec name .classes = .ok emitted)
    (footprinted : Footprinted spec) (state : State) (source : Pattern)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ declaredFootprint spec.plan)
    (ready : CommitReady spec.mode (table spec) source) {declaration : ReflectivePresentationDecl}
    (reflective : spec.mode = .reflective declaration) (noExtrusions : Complete.Normalized.extrusions spec.plan = [])
    (explores : ∀ target,
      (Complete.QuoteDropCoherence.gslt spec.plan spec.bound spec.expected declaration).MultiStep source target →
      ∃ reached, Complete.Explore.Explored
          (S := Complete.QuoteDropCoherence.search spec.plan spec.bound spec.expected declaration)
          (Complete.QuoteDropCoherence.commit spec.plan declaration source) reached ∧
        Complete.QuoteDropCoherence.ModelEquiv spec.plan spec.bound spec.expected declaration reached target) :
    ∀ target, (Complete.QuoteDropCoherence.gslt spec.plan spec.bound spec.expected declaration).MultiStep source target →
      ∃ work, ∃ reached ∈ (explored spec source work).nodes.map (·.state),
        Complete.QuoteDropCoherence.ModelEquiv spec.plan spec.bound spec.expected declaration reached target ∧
        PureReturns (runtime.append emitted) [] state
          (a (exploreHead name) [CompleteExecution.patternValue source, number work]) state
          (CompleteExecution.patternsValue ((explored spec source work).nodes.map (·.state))) := by
  obtain ⟨rfl, admitted⟩ := emit?_ok ok
  intro target reaches
  obtain ⟨reached, ⟨work, node, member, rfl⟩, related⟩ := explores target reaches
  have same : explored spec source work = Complete.Explore.explore
      (Complete.QuoteDropCoherence.search spec.plan spec.bound spec.expected declaration)
      (Complete.QuoteDropCoherence.commit spec.plan declaration source) work := by
    simp only [explored, reflective, Complete.QuoteDropCoherence.search_reflective spec.plan spec.bound spec.expected
      declaration noExtrusions, Complete.QuoteDropCoherence.commit_reflective noExtrusions]
  exact ⟨work, node.state, List.mem_map.mpr ⟨node, same ▸ member, rfl⟩, related,
    explore_entry_returns admitted.fresh footprinted state source inside ready work⟩

/-- **Emitted modules committing model normal forms explore the model of the declared collection
algebra.** For every class-profile module that `emit?` returns for a footprinted plan committing the canonical form of
the model normal form of a reflective presentation, without scope extrusion, whose explorer is complete
modulo that model at the source (`explores`, which `WrapperCoherence.presented_explores_wrappers` proves
for admitted plans), every state reachable from the source by steps modulo the declared collection
algebra, its wrapper laws and the name equation is, up to that model, among the states the PeTTa run of
the explore entry prints after some number of rounds. -/
theorem emitted_explores_model {name : String} {emitted : Program} (ok : emit? spec name .classes = .ok emitted)
    (footprinted : Footprinted spec) (state : State) (source : Pattern)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ declaredFootprint spec.plan)
    (ready : CommitReady spec.mode (table spec) source) {declaration : ReflectivePresentationDecl}
    (model : spec.mode = .model declaration) (noExtrusions : Complete.Normalized.extrusions spec.plan = [])
    (explores : ∀ target,
      (Complete.WrapperCoherence.gslt spec.plan spec.bound spec.expected declaration).MultiStep source target →
      ∃ reached, Complete.Explore.Explored
          (S := Complete.WrapperCoherence.search spec.plan spec.bound spec.expected declaration)
          (Complete.WrapperCoherence.commit spec.plan declaration source) reached ∧
        Complete.WrapperCoherence.ModelEquiv spec.plan spec.bound spec.expected declaration reached target) :
    ∀ target, (Complete.WrapperCoherence.gslt spec.plan spec.bound spec.expected declaration).MultiStep source target →
      ∃ work, ∃ reached ∈ (explored spec source work).nodes.map (·.state),
        Complete.WrapperCoherence.ModelEquiv spec.plan spec.bound spec.expected declaration reached target ∧
        PureReturns (runtime.append emitted) [] state
          (a (exploreHead name) [CompleteExecution.patternValue source, number work]) state
          (CompleteExecution.patternsValue ((explored spec source work).nodes.map (·.state))) := by
  obtain ⟨rfl, admitted⟩ := emit?_ok ok
  intro target reaches
  obtain ⟨reached, ⟨work, node, member, rfl⟩, related⟩ := explores target reaches
  have same : explored spec source work = Complete.Explore.explore
      (Complete.WrapperCoherence.search spec.plan spec.bound spec.expected declaration)
      (Complete.WrapperCoherence.commit spec.plan declaration source) work := by
    simp only [explored, model, Complete.WrapperCoherence.search_model spec.plan spec.bound spec.expected
      declaration noExtrusions, Complete.WrapperCoherence.commit_model noExtrusions]
  exact ⟨work, node.state, List.mem_map.mpr ⟨node, same ▸ member, rfl⟩, related,
    explore_entry_returns admitted.fresh footprinted state source inside ready work⟩

/-- **Emitted complete modules print their transition graph.** For every module that `emit?`
returns for a footprinted plan, and every source whose free names are declared, the PeTTa run of
the edges entry prints the transitions of the exploration stopped once settled, and:

- every printed transition is a valid receipt of its source state, ending at its target;
- once the exploration is settled, every transition ends at an explored state, and every receipt
  that the search of an explored state ever publishes is printed;
- for a module committing standard forms of a language that declares no collection or
  scope-extrusion laws, once settled, every GSLT step out of an explored state is printed, up to
  the equations. -/
theorem emitted_graph {name : String} {emitted : Program} (ok : emit? spec name .classes = .ok emitted)
    (footprinted : Footprinted spec) (state : State) (source : Pattern)
    (inside : ∀ name ∈ source.freeFvarNames, name ∈ declaredFootprint spec.plan)
    (ready : CommitReady spec.mode (table spec) source) (work : Nat) :
    PureReturns (runtime.append emitted) [] state
        (a (edgesHead name) [CompleteExecution.patternValue source, number work]) state
        (encoded (encodeList CompleteExecution.edgeTerm (graph spec source work))) ∧
      (∀ edge ∈ graph spec source work,
        (Complete.Normalized.search spec.plan spec.bound spec.expected spec.mode).Valid edge.1 edge.2.1 ∧
          edge.2.2 = (Complete.Normalized.search spec.plan spec.bound spec.expected spec.mode).target edge.2.1) ∧
      (Complete.Settled.settled (Complete.Normalized.search spec.plan spec.bound spec.expected spec.mode)
          (settledExplorer spec source work) = true →
        (∀ edge ∈ graph spec source work, ∃ node ∈ (settledExplorer spec source work).nodes, node.state = edge.2.2) ∧
        ∀ node ∈ (settledExplorer spec source work).nodes, ∀ (rounds : Nat) receipt,
          receipt ∈ (Complete.Normalized.search spec.plan spec.bound spec.expected spec.mode).publication
              ((Complete.Normalized.search spec.plan spec.bound spec.expected spec.mode).run node.state rounds) →
            (node.state, receipt, (Complete.Normalized.search spec.plan spec.bound spec.expected spec.mode).target receipt) ∈
              graph spec source work) ∧
      (spec.mode = .standard → Complete.Normalized.laws spec.plan = [] ∧ Complete.Normalized.extrusions spec.plan = [] →
        Complete.Settled.settled (Complete.Normalized.search spec.plan spec.bound spec.expected spec.mode)
          (settledExplorer spec source work) = true →
        ∀ node ∈ (settledExplorer spec source work).nodes, ∀ target,
          (GeneralOccurrenceSemantics.gslt spec.plan spec.bound spec.expected).Step node.state target →
            ∃ receipt, (node.state, receipt, receipt.target) ∈ graph spec source work ∧
              Relation.EqvGen (GeneralOccurrenceSemantics.Equation spec.plan spec.bound spec.expected)
                receipt.target target) := by
  obtain ⟨rfl, admitted⟩ := emit?_ok ok
  let search := Complete.Normalized.search spec.plan spec.bound spec.expected spec.mode
  let start := Complete.Normalized.commit spec.plan spec.mode source
  obtain ⟨more, _, same⟩ := Complete.Graph.roundsUntilSettled_explore (S := search) start work 0
  have final : settledExplorer spec source work = Complete.Explore.explore search start more := by
    simpa only [settledExplorer, search, start, Complete.Explore.explore, Nat.zero_add] using same
  have lawful := Complete.Normalized.search_lawful spec.plan spec.bound spec.expected spec.mode
  have stable := Complete.Settled.normalized_stable spec.plan spec.bound spec.expected spec.mode
  refine ⟨edges_entry_returns admitted.fresh footprinted state source inside ready work, ?_, ?_, ?_⟩
  · intro edge member
    simp only [graph, final] at member
    exact Complete.Graph.edge_valid lawful start more edge member
  · intro done
    simp only [graph, final] at done ⊢
    exact ⟨Complete.Graph.edge_target lawful start more done,
      Complete.Graph.edges_complete lawful stable start more done⟩
  · intro standard free done node present target stepped
    have classes : search = Complete.Classes.search spec.plan spec.bound spec.expected := by
      simp only [search, standard]
      exact Complete.Normalized.search_lawFree spec.plan spec.bound spec.expected free
    simp only [graph, final] at done present ⊢
    rw [classes] at done present ⊢
    simpa only [standard, Complete.Normalized.search_lawFree spec.plan spec.bound spec.expected free] using
      Complete.Graph.edges_cover_steps spec.plan spec.bound spec.expected admitted.balanced start more done
        present stepped

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
