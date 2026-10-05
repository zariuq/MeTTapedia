import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaItemsExecution

/-!
# Completed generated calls

The loaded dispatcher, materialized body segment and function return compose
in the existing MeTTa interpreter. Recursive calls retain their actual caller,
queued work and prior answers. The body premise is the recursive induction
obligation, rather than an assumption that the complete call returns correctly.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlExecution
open Mettapedia.Languages.MeTTa.HE.CanonAbsorbsFreshening
open Mettapedia.Languages.MeTTa.HE.LeaTTaSpecConformance
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge
open Metta.Minimal

namespace Execution

private theorem lookup_unassigned_of_private (bindings : Metta.Bindings) (name : String)
    (privateName : name ∉ bindings.vars) : Metta.Bindings.lookupVal bindings name = none := by
  induction bindings with
  | nil => rfl
  | cons relation rest ih =>
    cases relation with
    | val key value =>
      have different : name ≠ key := by
        intro equal
        apply privateName
        simp [Metta.Bindings.vars, equal]
      have absent : name ∉ Metta.Bindings.vars rest := by
        intro member
        apply privateName
        simpa only [Metta.Bindings.vars, List.mem_eraseDups, List.flatMap_cons,
          List.mem_append] using Or.inr (by
            simpa only [Metta.Bindings.vars, List.mem_eraseDups] using member)
      simp only [Metta.Bindings.lookupVal, beq_eq_false_iff_ne.mpr different, Bool.false_eq_true,
        if_false]
      exact ih absent
    | eq left right =>
      apply ih
      intro member
      apply privateName
      simpa only [Metta.Bindings.vars, List.mem_eraseDups, List.flatMap_cons,
        List.mem_append] using Or.inr (by
          simpa only [Metta.Bindings.vars, List.mem_eraseDups] using member)

/-- The selected generated body returns to a real caller. All new bindings
are private to the callee; its invocation cannot assign an unassigned caller
name. Source and target budgets remain independent. -/
theorem loaded_selected_to_caller (program : Program) (head : String)
    (present : head ∈ program.map Equation.head)
    (environment : MinEnv) (loaded : LoadedProgram program environment)
    (sourceFuel : Nat) (arguments : List Term) (row : OrderedDispatch.CaseRow)
    (sourceBindings : Env)
    (selected : OrderedDispatch.selectCase (OrderedDispatch.compileHead program head)
      arguments = some (row, sourceBindings))
    (result : Outcome)
    (bodyRun : ExpressionExecutes program
      environment
      sourceFuel sourceBindings row.equation.body result)
    (state : St) (noExtra : state.world.selfExtra = [])
    (noImports : state.world.selfImports = [])
    (incoming : Metta.Bindings) (stored : ClosedValueBindings incoming)
    (invariant : LeaRuntimeBindingInvariant incoming) (caller : Frame) (continuation : Stack) :
    let query := toLeaTTaAtom (call (dispatchName head)
      [.grounded (.int sourceFuel), MeTTaData.encodeItems arguments])
    ∃ nextState output cost threshold,
      nextState.world = state.world ∧ ClosedValueBindings output ∧
      LeaRuntimeBindingInvariant output ∧
      (∀ key ∈ liveStackVars (caller :: continuation),
        Metta.Bindings.lookupVal incoming key = none →
          Metta.Bindings.lookupVal output key = none) ∧
      ∀ fuel, threshold ≤ fuel → ∀ rest done,
        interpretFuel environment (fuel + cost) state
          (⟨atomToStack (.expr [.sym "eval", query]) (caller :: continuation), incoming⟩ :: rest) done =
        interpretFuel environment fuel nextState
          (finItem (caller :: continuation) (toLeaTTaAtom (observation result)) output :: rest) done := by
  intro query
  obtain ⟨first, rawBody, emitted, registered⟩ := loaded.dispatch head present sourceFuel
    arguments state.world noExtra noImports
  obtain ⟨rename, start, counter, skipped, parentBody, matched, injective, matchedClosed,
      matchedInvariant, privateNames, callerPrivate, callerPreserved, entry⟩ :=
    loaded_dispatcher_enters_body program head first sourceFuel arguments row sourceBindings
      selected rawBody emitted environment state (caller :: continuation) incoming stored invariant
      (by rw [loaded.groundings]; exact dispatchName_native_miss _ _)
      (dispatchName_not_embedded _ _) registered
  let body := renBy rename (toLeaTTaAtom
    (expression program (sourceBindings.map fun pair => (pair.1, MeTTaData.encode pair.2))
      (.grounded (.int sourceFuel)) row.equation.body (patterns row.equation.params start).2).1)
  obtain ⟨nextState, output, bodyCost, threshold, world, outputClosed, outputInvariant,
      preserves, execution⟩ := bodyRun (patterns row.equation.params start).2 rename injective
    { state with counter := counter } noExtra noImports matched matchedClosed matchedInvariant
    parentBody (varsCopy (caller :: continuation)) (caller :: continuation)
    (fun key member => lookup_unassigned_of_private matched key (privateNames key member))
  refine ⟨nextState, output, bodyCost + 7 + 2 * skipped, threshold, world,
    outputClosed, outputInvariant, ?_, ?_⟩
  · intro key live unassigned
    apply preserves key (List.mem_append_right _ live)
      (fun member => callerPrivate key member live)
    exact callerPreserved key live unassigned
  · intro fuel enough rest done
    have entered := entry (fuel + 1 + bodyCost) rest done
    have ran := execution (fuel + 1) (by omega) rest done
    have returned := selected_return_to_caller environment nextState output parentBody
      (toLeaTTaAtom (observation result)) (varsCopy (caller :: continuation)) caller continuation
      fuel rest done
    rw [Metta.instantiate_of_closed output _ (observation_closed result)] at returned
    simpa only [show fuel + 1 + bodyCost + 6 + 2 * skipped =
      fuel + (bodyCost + 7 + 2 * skipped) by omega] using entered.trans (ran.trans returned)

/-- The public entry composes the same selected body with its outermost
function return. Exactly one tagged outcome is observed; the source outcome
is not identified with physical target-budget exhaustion. -/
theorem loaded_selected_execution (program : Program) (head : String)
    (present : head ∈ program.map Equation.head)
    (environment : MinEnv) (loaded : LoadedProgram program environment)
    (sourceFuel : Nat) (arguments : List Term) (row : OrderedDispatch.CaseRow)
    (sourceBindings : Env)
    (selected : OrderedDispatch.selectCase (OrderedDispatch.compileHead program head)
      arguments = some (row, sourceBindings)) (result : Outcome)
    (bodyRun : ExpressionExecutes program
      environment
      sourceFuel sourceBindings row.equation.body result)
    (state : St) (noExtra : state.world.selfExtra = [])
    (noImports : state.world.selfImports = [])
    (incoming : Metta.Bindings) (stored : ClosedValueBindings incoming)
    (invariant : LeaRuntimeBindingInvariant incoming) :
    let query := toLeaTTaAtom (requestAtom program sourceFuel head arguments)
    ∃ nextState output cost threshold,
      nextState.world = state.world ∧ ClosedValueBindings output ∧
      LeaRuntimeBindingInvariant output ∧
      ∀ fuel, threshold ≤ fuel →
        interpretFuel environment (fuel + cost) state
          [⟨atomToStack (.expr [.sym "eval", query]) [], incoming⟩] [] =
        ([(toLeaTTaAtom (observation result), output)], nextState) := by
  intro query
  obtain ⟨first, rawBody, emitted, registered⟩ := loaded.dispatch head present sourceFuel
    arguments state.world noExtra noImports
  obtain ⟨rename, start, counter, skipped, parentBody, matched, injective, matchedClosed,
      matchedInvariant, privateNames, _, _, entry⟩ :=
    loaded_dispatcher_enters_body program head first sourceFuel arguments row sourceBindings
      selected rawBody emitted environment state [] incoming stored invariant
      (by rw [loaded.groundings]; exact dispatchName_native_miss _ _)
      (dispatchName_not_embedded _ _) registered
  obtain ⟨nextState, output, bodyCost, threshold, world, outputClosed, outputInvariant,
      _, execution⟩ := bodyRun (patterns row.equation.params start).2 rename injective
    { state with counter := counter } noExtra noImports matched matchedClosed matchedInvariant
    parentBody (varsCopy []) []
    (fun key member => lookup_unassigned_of_private matched key (privateNames key member))
  refine ⟨nextState, output, bodyCost + 7 + 2 * skipped, threshold, world,
    outputClosed, outputInvariant, ?_⟩
  intro fuel enough
  have entered := entry (fuel + 1 + bodyCost) [] []
  have ran := execution (fuel + 1) (by omega) [] []
  have visible : (toLeaTTaAtom (observation result) != emptyA) = true := by
    cases result <;> rfl
  have returned := selected_closed_return_finishes environment nextState output parentBody
    (toLeaTTaAtom (observation result)) [] fuel (observation_closed result) visible
  have defined : program.defines head = true := by simpa [Program.defines] using present
  simpa only [query, requestAtom, invoke, defined, if_true, sequenceAtom_encode, varsCopy,
    show fuel + 1 + bodyCost + 6 + 2 * skipped = fuel + (bodyCost + 7 + 2 * skipped) by omega]
    using entered.trans (ran.trans returned)

/-- A missing authored row refuses inside a caller, without evaluating any
body. Header matching remains capture avoiding even on this negative path. -/
theorem loaded_refused_to_caller (program : Program) (head : String)
    (present : head ∈ program.map Equation.head)
    (environment : MinEnv) (loaded : LoadedProgram program environment)
    (sourceFuel : Nat) (arguments : List Term)
    (refused : OrderedDispatch.selectCase (OrderedDispatch.compileHead program head)
      arguments = none)
    (state : St) (noExtra : state.world.selfExtra = [])
    (noImports : state.world.selfImports = [])
    (incoming : Metta.Bindings) (stored : ClosedValueBindings incoming)
    (invariant : LeaRuntimeBindingInvariant incoming) (caller : Frame) (continuation : Stack) :
    let query := toLeaTTaAtom (call (dispatchName head)
      [.grounded (.int sourceFuel), MeTTaData.encodeItems arguments])
    ∃ nextState output cost threshold,
      nextState.world = state.world ∧ ClosedValueBindings output ∧
      LeaRuntimeBindingInvariant output ∧
      (∀ key ∈ liveStackVars (caller :: continuation),
        Metta.Bindings.lookupVal incoming key = none →
          Metta.Bindings.lookupVal output key = none) ∧
      ∀ fuel, threshold ≤ fuel → ∀ rest done,
        interpretFuel environment (fuel + cost) state
          (⟨atomToStack (.expr [.sym "eval", query]) (caller :: continuation), incoming⟩ :: rest) done =
        interpretFuel environment fuel nextState
          (finItem (caller :: continuation) (.sym "nik:Failure") output :: rest) done := by
  intro query
  obtain ⟨first, rawBody, emitted, registered⟩ := loaded.dispatch head present sourceFuel
    arguments state.world noExtra noImports
  obtain ⟨refusalBody, refusalEmitted, refuses⟩ := dispatcher_refused_execution program head
    first sourceFuel state.counter arguments refused environment (caller :: continuation)
      incoming stored invariant
  have same : refusalBody = rawBody := by
    simpa only [call, Atom.expression.injEq, List.cons.injEq, true_and, and_true]
      using refusalEmitted.symm.trans emitted
  subst refusalBody
  obtain ⟨matched, output, matching, merging, outputClosed, enters⟩ := loaded_dispatcher_entry
    program head first sourceFuel arguments rawBody emitted environment state (caller :: continuation)
      incoming stored (by rw [loaded.groundings]; exact dispatchName_native_miss _ _)
      (dispatchName_not_embedded _ _) registered
  obtain ⟨scanCost, scanning⟩ := refuses matched output matching merging
  obtain ⟨materializedBody, branches, checked, rename, materializedEmitted, _, _, _, _, _, materializes⟩ :=
    dispatcher_query_materialization program head first sourceFuel state.counter arguments
      (caller :: continuation) incoming stored invariant
  have same : materializedBody = rawBody := by
    simpa only [call, Atom.expression.injEq, List.cons.injEq, true_and, and_true]
      using materializedEmitted.symm.trans emitted
  subst materializedBody
  have outputInvariant := (materializes matched output matching merging).2.1
  let lhs := toLeaTTaAtom (call (dispatchName head)
    [.var (freshName first), .var (freshName (first + 1))])
  let fresh := freshenRuleAvoiding state.counter
    (Metta.Minimal.queryOpAvoid (caller :: continuation) query incoming) lhs
    (toLeaTTaAtom (call "function" [rawBody]))
  refine ⟨{ state with counter := fresh.2 }, output, scanCost + 2, 0,
    rfl, outputClosed, outputInvariant, ?_, ?_⟩
  · intro key live unassigned
    exact query_preserves_unassigned_caller (caller :: continuation) query lhs
      (toLeaTTaAtom (call "function" [rawBody])) incoming matched output state.counter key
      stored (by simp [query, call, toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.vars,
        data_atom_runtime_closed (MeTTaData.encodeItems_data arguments)])
      live unassigned matching merging
  · intro fuel _ rest done
    have entered := enters (fuel + 1 + scanCost) rest done
    have scanned := scanning { state with counter := fresh.2 } (fuel + 1) rest done
    have returned := selected_return_to_caller environment { state with counter := fresh.2 }
      output (Metta.instantiate output fresh.1.2) (.sym "nik:Failure")
      (varsCopy (caller :: continuation)) caller continuation fuel rest done
    rw [Metta.instantiate_of_closed output (.sym "nik:Failure")
      (by simp only [Metta.Atom.vars])] at returned
    simpa only [show fuel + 1 + scanCost + 1 = fuel + (scanCost + 2) by omega]
      using entered.trans (scanned.trans returned)

private theorem dispatchName_is_call (head : String) :
    dispatchName head ≠ "nik:Value" ∧ dispatchName head ≠ "nik:primitive" := by
  have leading : (dispatchName head).toList.take 9 = ['n', 'i', 'k', ':', 'c', 'a', 'l', 'l', ':'] := by
    unfold dispatchName
    rw [String.toList_append]
    rfl
  constructor <;> intro equal <;> rw [equal] at leading <;> cases leading

/-- A closed callee segment composes with the compiler's actual call/return
continuation. This shared control lemma has no guest-specific checking logic. -/
private theorem compiled_invocation_of_callee (environment : MinEnv) (head : String)
    (inputs : List Atom) (notValue : head ≠ "nik:Value") (notPrimitive : head ≠ "nik:primitive")
    (sourceClosed : (toLeaTTaAtom (call "eval" [call head inputs])).vars = [])
    (result : Outcome)
    (callee : ∀ state : St, state.world.selfExtra = [] → state.world.selfImports = [] →
      ∀ incoming : Metta.Bindings, ClosedValueBindings incoming → LeaRuntimeBindingInvariant incoming →
      ∀ caller continuation,
      ∃ nextState output cost threshold,
        nextState.world = state.world ∧ ClosedValueBindings output ∧
        LeaRuntimeBindingInvariant output ∧
        (∀ key ∈ liveStackVars (caller :: continuation),
          Metta.Bindings.lookupVal incoming key = none →
            Metta.Bindings.lookupVal output key = none) ∧
        ∀ fuel, threshold ≤ fuel → ∀ rest done,
          interpretFuel environment (fuel + cost) state
            (⟨atomToStack (toLeaTTaAtom (call "eval" [call head inputs]))
              (caller :: continuation), incoming⟩ :: rest) done =
          interpretFuel environment fuel nextState
            (finItem (caller :: continuation) (toLeaTTaAtom (observation result)) output :: rest) done) :
    CompiledExecutes environment (returnInvocation (call head inputs)) result := by
  intro first rename injective state noExtra noImports incoming stored invariant
    parentBody scope continuation code _
  let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
  let source := renBy rename (toLeaTTaAtom (call "eval" [call head inputs]))
  let template := renBy rename (toLeaTTaAtom (returned (.var (freshName first))))
  let recipient : Frame :=
    { atom := .expr [.sym "chain", source, .var (rename (freshName first)), template],
      ret := .chain, vars := chainFrameVars (parent :: continuation) source template }
  have sourceSame : source = toLeaTTaAtom (call "eval" [call head inputs]) :=
    renBy_eq_self_of_vars_nil rename _ sourceClosed
  obtain ⟨nextState, output, cost, threshold, world, outputClosed, outputInvariant,
      preserves, execution⟩ := callee state noExtra noImports incoming stored
    invariant recipient (parent :: continuation)
  refine ⟨nextState, output, cost + 3, threshold, world, outputClosed, outputInvariant, ?_, ?_⟩
  · intro key live _ unassigned
    exact preserves key (List.mem_append_right _ live) unassigned
  · intro fuel enough rest done
    have called := execution (fuel + 3) (by omega) rest done
    have returned := renamed_returnInvocation_enters_handler environment state nextState incoming
      output rename head inputs (toLeaTTaAtom (observation result)) first cost fuel
      parentBody scope continuation rest done notValue
      notPrimitive (observation_closed result)
    have completed := returned (by
      change interpretFuel environment (fuel + 3 + cost) state
        (⟨atomToStack source (recipient :: parent :: continuation), incoming⟩ :: rest) done = _
      rw [sourceSame]
      exact called)
    simpa only [code,
      show fuel + 3 + cost = fuel + (cost + 3) by omega] using completed


/-- A selected call satisfies the same body-segment interface as literals,
lets and evaluated arguments. This closes the recursive-call continuation:
the returned result is substituted by the actual MeTTa chain instruction. -/
theorem compiled_selected_invocation (program : Program) (head : String)
    (present : head ∈ program.map Equation.head)
    (environment : MinEnv) (loaded : LoadedProgram program environment)
    (sourceFuel : Nat) (arguments : List Term) (row : OrderedDispatch.CaseRow)
    (sourceBindings : Env)
    (selected : OrderedDispatch.selectCase (OrderedDispatch.compileHead program head)
      arguments = some (row, sourceBindings)) (result : Outcome)
    (bodyRun : ExpressionExecutes program
      environment
      sourceFuel sourceBindings row.equation.body result) :
    CompiledExecutes
      environment
      (returnInvocation (call (dispatchName head)
        [.grounded (.int sourceFuel), MeTTaData.encodeItems arguments])) result := by
  apply compiled_invocation_of_callee environment (dispatchName head)
    [.grounded (.int sourceFuel), MeTTaData.encodeItems arguments]
    (dispatchName_is_call head).1 (dispatchName_is_call head).2
  · simp [call, toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.vars,
      data_atom_runtime_closed (MeTTaData.encodeItems_data arguments)]
  · exact loaded_selected_to_caller program head present environment loaded sourceFuel
      arguments row sourceBindings selected result bodyRun

/-- If no authored row matches, the same continuation returns logical refusal.
It does not retry a different row or invoke an unlisted host operation. -/
theorem compiled_refused_invocation (program : Program) (head : String)
    (present : head ∈ program.map Equation.head)
    (environment : MinEnv) (loaded : LoadedProgram program environment)
    (sourceFuel : Nat) (arguments : List Term)
    (refused : OrderedDispatch.selectCase (OrderedDispatch.compileHead program head)
      arguments = none) :
    CompiledExecutes environment
      (returnInvocation (call (dispatchName head)
        [.grounded (.int sourceFuel), MeTTaData.encodeItems arguments])) .failure := by
  apply compiled_invocation_of_callee environment (dispatchName head)
    [.grounded (.int sourceFuel), MeTTaData.encodeItems arguments]
    (dispatchName_is_call head).1 (dispatchName_is_call head).2
  · simp [call, toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.vars,
      data_atom_runtime_closed (MeTTaData.encodeItems_data arguments)]
  · exact loaded_refused_to_caller program head present environment loaded sourceFuel arguments refused

/-- The only host-execution premise concerns the finite, named primitive
interface. It contains no guest checking operation or rule application. -/
def NamedPrimitivesExecute (host : Host) (environment : MinEnv) : Prop :=
  ∀ head ∈ primitiveHeads, ∀ arguments : List Term,
    CompiledExecutes environment
      (returnInvocation (call "nik:primitive"
        [.grounded (.string head), MeTTaData.encodeItems arguments]))
      (match host.primitive head arguments with
       | .fault => .failure
       | .value payload => .value payload
       | .unhandled => .value (.expr (.sym head :: arguments)))

/-- All source calls compose through one interface: declared equations,
named primitives, and uninterpreted data constructors. The recursive premise
is at the smaller source budget and will be supplied by fuel induction. -/
theorem compiled_apply (program : Program) (host : Host) (environment : MinEnv)
    (loaded : LoadedProgram program environment)
    (primitives : NamedPrimitivesExecute host environment)
    (unlisted : ∀ head, head ∉ primitiveHeads → ∀ arguments,
      host.primitive head arguments = .unhandled)
    (sourceFuel : Nat)
    (recursive : ∀ sourceBindings term,
      ExpressionExecutes program environment sourceFuel sourceBindings term
        (eval program host sourceFuel sourceBindings term))
    (head : String) (arguments : List Term) :
    CompiledExecutes environment
      (returnInvocation (invoke program (.grounded (.int sourceFuel)) head
        (arguments.map MeTTaData.encode)))
      (apply program host sourceFuel head arguments) := by
  cases declared : program.defines head with
  | true =>
    have present : head ∈ program.map Equation.head := by
      simpa [Program.defines] using declared
    have agrees := OrderedDispatch.compileHead_dispatch_eq program host
      (eval program host sourceFuel) head arguments declared
    simp only [invoke, declared, if_true, sequenceAtom_encode, apply]
    rw [← agrees]
    cases selected : OrderedDispatch.selectCase (OrderedDispatch.compileHead program head)
      arguments with
    | none =>
      simpa only [OrderedDispatch.dispatchCaseWith, selected] using
        compiled_refused_invocation program head present environment loaded sourceFuel arguments selected
    | some hit =>
      rcases hit with ⟨row, sourceBindings⟩
      simpa only [OrderedDispatch.dispatchCaseWith, selected] using
        compiled_selected_invocation program head present environment loaded sourceFuel arguments
          row sourceBindings selected _ (recursive sourceBindings row.equation.body)
  | false =>
    have absentArity : program.definesAt head arguments.length = false := by
      have absent : ∀ equation ∈ program, equation.head ≠ head := by
        simpa [Program.defines, beq_iff_eq] using declared
      simp only [Program.definesAt, List.any_eq_false]
      intro equation member
      simp [absent equation member]
    simp only [apply, applyWith, absentArity, declared, Bool.false_eq_true, if_false]
    by_cases named : head ∈ primitiveHeads
    · have native := primitives head named arguments
      cases primitive : host.primitive head arguments <;>
        simpa only [primitive, invoke, declared, Bool.false_eq_true, if_false, named, if_pos,
          sequenceAtom_encode] using native
    · rw [unlisted head named arguments]
      simpa only [invoke, declared, Bool.false_eq_true, if_false, named, sequenceAtom_encode,
        MeTTaData.encodeItems, sequenceAtom, MeTTaData.encode, observation, value, returnInvocation, returned,
        call, pure, StateT.pure] using
        compiled_return environment (.value (.expr (.sym head :: arguments)))

/-- Every emitted invocation has a control form accepted by the independent
interpreter. A data result returns directly; calls use their ordinary chains. -/
private theorem returnInvocation_controlled (invocation : Atom) (first : Nat)
    (rename : String → String) :
    isEmbeddedOp (renBy rename (toLeaTTaAtom (returnInvocation invocation first).1)) = true ∨
      ∃ payload, renBy rename (toLeaTTaAtom (returnInvocation invocation first).1) =
        .expr [.sym "return", payload] := by
  unfold returnInvocation
  split
  · apply Or.inr
    simp only [pure, StateT.pure, returned, call, toLeaTTaAtom, toLeaTTaAtoms,
      renBy, List.map_cons, List.map_nil]
    exact ⟨_, rfl⟩
  · apply Or.inl
    change isEmbeddedOp (renBy rename (toLeaTTaAtom (call "chain" [_, _, _]))) = true
    simp only [call, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil, isEmbeddedOp]
    rfl
  · apply Or.inl
    change isEmbeddedOp (renBy rename (toLeaTTaAtom (call "chain" [_, _, _]))) = true
    simp only [call, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil, isEmbeddedOp]
    rfl

/-- Invocation continuations obey the same allocation and substitution laws
used by the already proved left-to-right argument evaluator. -/
theorem invocation_continuation_syntax (program : Program) (sourceFuel : Nat) (head : String) :
    ContinuationSyntax (fun arguments =>
      returnInvocation (invoke program (.grounded (.int sourceFuel)) head arguments)) where
  scope first arguments bounded := returnInvocation_scope _ first
    (invoke_scope program _ head arguments first (usesBefore_grounded first _) bounded)
  substitute index first before replacement arguments _ := by
    simpa only [Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal.substituteName] using
      Control.substituteName_returnInvoke replacement (.grounded (.int sourceFuel))
        program head arguments index first before
  controlled first arguments rename := returnInvocation_controlled _ first rename

end Execution
end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
