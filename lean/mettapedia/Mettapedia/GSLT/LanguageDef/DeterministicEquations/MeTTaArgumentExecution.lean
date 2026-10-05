import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaReturnExecution
import Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlUnify

/-!
# Generated argument outcomes in the independent interpreter

The result branches used by `bindResult` inspect the returned constructor.
Values bind the continuation's operand; refusal and exhaustion return through
the surrounding function without evaluating the successful continuation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlExecution
open Mettapedia.Languages.MeTTa.HE.CanonAbsorbsFreshening
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge
open Metta.Minimal

/-- Binding a previously unassigned name to closed data preserves the
runtime invariant needed by subsequent calls and branch matches. -/
theorem fresh_closed_value_preserves_runtime (bindings : Metta.Bindings)
    (name : String) (payload : Metta.Atom)
    (stored : ClosedValueBindings bindings)
    (invariant : Mettapedia.Languages.MeTTa.HE.LeaTTaSpecConformance.LeaRuntimeBindingInvariant bindings)
    (closed : payload.vars = [])
    (noFloat : MettaAtomNoFloat payload)
    (fresh : Metta.Bindings.lookupVal bindings name = none) :
    Mettapedia.Languages.MeTTa.HE.LeaTTaSpecConformance.LeaRuntimeBindingInvariant
      (Metta.Bindings.addValRaw bindings name payload) := by
  have notVariable : ∀ other, payload ≠ .var other := by
    intro other same
    simp [same, Metta.Atom.vars] at closed
  have merged : Metta.Bindings.merge bindings [.val name payload] =
      [Metta.Bindings.addValRaw bindings name payload] := by
    simpa [Metta.Bindings.merge, Metta.Bindings.mergeOne] using
      Metta.Bindings.addVarBinding_fresh
        ((stored.toValueBindings.classValues_lookupVal name).1 fresh) notVariable
  apply invariant.merge (right := [.val name payload])
  · intro key atom member
    cases List.mem_singleton.mp member
    exact noFloat
  · simp only [merged, List.mem_singleton]
  · exact (addValRaw_closed closed stored).hasLoop_false


/-- The sequencing variable is private to the outcome test, so substituting
the returned atom cannot capture the successful continuation's variables. -/
theorem substitute_resultBranches (marker : String) (result name body : Atom)
    (nameFresh : marker ∉ (toLeaTTaAtom name).vars)
    (bodyFresh : marker ∉ (toLeaTTaAtom body).vars) :
    Metta.Subst.apply [(marker, toLeaTTaAtom result)]
        (toLeaTTaAtom (resultBranches (.var marker) name body)) =
      toLeaTTaAtom (resultBranches result name body) := by
  have nameSame := substitute_fresh marker (toLeaTTaAtom result) (toLeaTTaAtom name) nameFresh
  have bodySame := substitute_fresh marker (toLeaTTaAtom result) (toLeaTTaAtom body) bodyFresh
  simp only [resultBranches, selectBranches, List.foldr_cons, List.foldr_nil, value,
    returned, call, toLeaTTaAtom, toLeaTTaAtoms, Metta.Subst.apply, List.map_cons,
    List.map_nil, Metta.Subst.lookup, beq_self_eq_true, if_true, Option.getD_some,
    nameSame, bodySame]

/-- The emitter's allocation bound discharges runtime non-capture. -/
theorem UsesBefore.runtime_fresh {first : Nat} {atom : Atom}
    (bounded : UsesBefore first atom) : freshName first ∉ (toLeaTTaAtom atom).vars := by
  intro occurrence
  exact bounded.excludes first le_rfl
    (Mettapedia.Languages.MeTTa.HE.LeaTTaSpecConformance.atomOccurs_of_mem_translated_vars
      occurrence)

/-- Fresh names stay fresh after the equation's injective renaming. -/
theorem UsesBefore.renamed_runtime_fresh {first : Nat} {atom : Atom}
    (bounded : UsesBefore first atom) (rename : String → String)
    (injective : Function.Injective rename) :
    rename (freshName first) ∉ (renBy rename (toLeaTTaAtom atom)).vars := by
  rw [renBy_vars]
  rintro member
  obtain ⟨name, occurrence, same⟩ := List.mem_map.mp member
  rw [injective same] at occurrence
  exact bounded.runtime_fresh occurrence

/-- The returned data can be substituted into a freshly renamed outcome
test without capturing the successful continuation's names. -/
theorem substitute_renamed_resultBranches (marker : String) (result name body : Atom)
    (rename : String → String) (injective : Function.Injective rename)
    (closed : (toLeaTTaAtom result).vars = [])
    (nameFresh : marker ∉ (toLeaTTaAtom name).vars)
    (bodyFresh : marker ∉ (toLeaTTaAtom body).vars) :
    Metta.Subst.apply [(rename marker, toLeaTTaAtom result)]
        (renBy rename (toLeaTTaAtom (resultBranches (.var marker) name body))) =
      renBy rename (toLeaTTaAtom (resultBranches result name body)) := by
  have freshAfter (atom : Metta.Atom) (fresh : marker ∉ atom.vars) :
      rename marker ∉ (renBy rename atom).vars := by
    rw [renBy_vars]
    rintro member
    obtain ⟨name, occurrence, same⟩ := List.mem_map.mp member
    rw [injective same] at occurrence
    exact fresh occurrence
  have nameSame := substitute_fresh (rename marker) (toLeaTTaAtom result)
    (renBy rename (toLeaTTaAtom name)) (freshAfter _ nameFresh)
  have bodySame := substitute_fresh (rename marker) (toLeaTTaAtom result)
    (renBy rename (toLeaTTaAtom body)) (freshAfter _ bodyFresh)
  have resultSame := renBy_eq_self_of_vars_nil rename (toLeaTTaAtom result) closed
  simp only [resultBranches, selectBranches, List.foldr_cons, List.foldr_nil, value,
    returned, call, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil,
    Metta.Subst.apply, Metta.Subst.lookup, beq_self_eq_true, if_true, Option.getD_some,
    nameSame, bodySame, resultSame]

/-- Completed operands compose with argument sequencing after the equation
has been freshly renamed. No capture-free naming convention is imposed on
the runtime beyond the injective renaming and the emitter's allocation bound. -/
theorem renamed_bindResult_of_operand_execution (environment : MinEnv)
    (state nextState : St) (incoming output : Metta.Bindings)
    (rename : String → String) (injective : Function.Injective rename)
    (source result name body : Atom) (first cost fuel : Nat)
    (parent : Frame) (continuation : Stack) (rest : List Item)
    (done : List (Metta.Atom × Metta.Bindings))
    (closed : (toLeaTTaAtom result).vars = [])
    (nameBound : UsesBefore first name) (bodyBound : UsesBefore first body) :
    let sourceCall := renBy rename (toLeaTTaAtom (call "function" [source]))
    let template := renBy rename (toLeaTTaAtom (resultBranches (.var (freshName first)) name body))
    let caller : Frame :=
      { atom := .expr [.sym "chain", sourceCall, .var (rename (freshName first)), template],
        ret := .chain, vars := chainFrameVars (parent :: continuation) sourceCall template }
    (interpretFuel environment (fuel + 2 + cost) state
          (⟨atomToStack sourceCall (caller :: parent :: continuation), incoming⟩ :: rest) done =
        interpretFuel environment (fuel + 2) nextState
          (finItem (caller :: parent :: continuation) (toLeaTTaAtom result) output :: rest) done) →
    interpretFuel environment (fuel + 2 + cost) state
        (⟨atomToStack (renBy rename (toLeaTTaAtom (bindResult source name body first).1))
          (parent :: continuation), incoming⟩ :: rest) done =
      interpretFuel environment fuel nextState
        (⟨atomToStack (renBy rename (toLeaTTaAtom (resultBranches result name body)))
          (parent :: continuation), output⟩ :: rest) done := by
  intro sourceCall template caller operandExecution
  have shape : renBy rename (toLeaTTaAtom (bindResult source name body first).1) =
      .expr [.sym "chain", sourceCall, .var (rename (freshName first)), template] := by
    change renBy rename (.expr [.sym "chain", toLeaTTaAtom (call "function" [source]),
      .var (freshName first), toLeaTTaAtom (resultBranches (.var (freshName first)) name body)]) = _
    simp only [renBy, List.map_cons, List.map_nil, sourceCall, template]
  rw [shape]
  change interpretFuel environment (fuel + 2 + cost) state
    (⟨atomToStack sourceCall (caller :: parent :: continuation), incoming⟩ :: rest) done = _
  rw [operandExecution,
    chain_result_enters environment nextState output sourceCall (toLeaTTaAtom result)
      template (rename (freshName first)) _ parent continuation fuel rest done,
    Metta.instantiate_of_closed output (toLeaTTaAtom result) closed]
  rw [show Metta.Subst.apply [(rename (freshName first), toLeaTTaAtom result)] template =
      renBy rename (toLeaTTaAtom (resultBranches result name body)) from
    substitute_renamed_resultBranches _ _ _ _ rename injective closed
      nameBound.runtime_fresh bodyBound.runtime_fresh]

/-- A completed operand run composes with the generated argument binder.
The operand may make recursive calls and extend the runtime bindings. The
premise is its interpreter segment; the conclusion adds the real sequencing
steps and the emitter's capture-free substitution. The callee segment is
required only at the actual remaining budget, not at every smaller budget. -/
theorem bindResult_of_operand_execution (environment : MinEnv)
    (state nextState : St) (incoming output : Metta.Bindings)
    (source result name body : Atom) (first cost fuel : Nat)
    (parent : Frame) (continuation : Stack) (rest : List Item)
    (done : List (Metta.Atom × Metta.Bindings))
    (closed : (toLeaTTaAtom result).vars = [])
    (nameBound : UsesBefore first name) (bodyBound : UsesBefore first body) :
    let sourceCall := toLeaTTaAtom (call "function" [source])
    let template := toLeaTTaAtom (resultBranches (.var (freshName first)) name body)
    let caller : Frame :=
      { atom := .expr [.sym "chain", sourceCall, .var (freshName first), template],
        ret := .chain, vars := chainFrameVars (parent :: continuation) sourceCall template }
    (interpretFuel environment (fuel + 2 + cost) state
          (⟨atomToStack sourceCall (caller :: parent :: continuation), incoming⟩ :: rest) done =
        interpretFuel environment (fuel + 2) nextState
          (finItem (caller :: parent :: continuation) (toLeaTTaAtom result) output :: rest) done) →
    interpretFuel environment (fuel + 2 + cost) state
        (⟨atomToStack (toLeaTTaAtom (bindResult source name body first).1)
          (parent :: continuation), incoming⟩ :: rest) done =
      interpretFuel environment fuel nextState
        (⟨atomToStack (toLeaTTaAtom (resultBranches result name body))
          (parent :: continuation), output⟩ :: rest) done := by
  have identity (atom : Metta.Atom) : renBy id atom = atom := by
    change renBy (applyRen []) atom = atom
    rw [← renameVars_eq_renBy]
    exact Metta.renameVars_nil atom
  simpa only [identity, id_eq] using
    renamed_bindResult_of_operand_execution environment state nextState incoming output
      id (fun _ _ same => same) source result name body first cost fuel parent continuation
      rest done closed nameBound bodyBound

/-- Executing a returned operand enters the emitter's own outcome branches.
The temporary is allocated after the continuation and cannot capture it. -/
theorem bindResult_return_enters (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (result name body : Atom) (first fuel : Nat)
    (parent : Frame) (continuation : Stack) (rest : List Item)
    (done : List (Metta.Atom × Metta.Bindings))
    (closed : (toLeaTTaAtom result).vars = [])
    (nameBound : UsesBefore first name) (bodyBound : UsesBefore first body) :
    interpretFuel environment (fuel + 4) state
        (⟨atomToStack (toLeaTTaAtom (bindResult (returned result) name body first).1)
          (parent :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (⟨atomToStack (toLeaTTaAtom (resultBranches result name body))
          (parent :: continuation), bindings⟩ :: rest) done := by
  rw [show fuel + 4 = fuel + 2 + 2 by omega]
  apply bindResult_of_operand_execution environment state state bindings bindings
    (returned result) result name body first 2 fuel parent continuation rest done
    closed nameBound bodyBound
  let source := toLeaTTaAtom (call "function" [returned result])
  let template := toLeaTTaAtom (resultBranches (.var (freshName first)) name body)
  let caller : Frame :=
    { atom := .expr [.sym "chain", source, .var (freshName first), template],
      ret := .chain, vars := chainFrameVars (parent :: continuation) source template }
  simpa only [source, caller, template, call, returned, toLeaTTaAtom, toLeaTTaAtoms,
    atomToStack, Metta.instantiate_of_closed bindings (toLeaTTaAtom result) closed] using
    return_to_caller environment state bindings source (toLeaTTaAtom result)
      (varsCopy (caller :: parent :: continuation)) caller (parent :: continuation)
      (fuel + 2) rest done

/-- A fuel-guarded operand is materialized in its incoming frame, then
delivered to the same generated branches. This composes the native fuel
operations with nested function return and argument sequencing. -/
theorem bindResult_withFuel_return_enters (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (operand result name body : Atom)
    (first branchIndex remaining fuel : Nat) (parent : Frame) (continuation : Stack)
    (rest : List Item) (done : List (Metta.Atom × Metta.Bindings))
    (groundings : environment.gt = Metta.Builtins.table)
    (privateRemaining : Metta.instantiate bindings (.var (freshName first)) =
      .var (freshName first))
    (bounded : UsesBefore (first + 1) operand)
    (materialized : Metta.instantiate bindings (toLeaTTaAtom operand) = toLeaTTaAtom result)
    (closed : (toLeaTTaAtom result).vars = [])
    (nameBound : UsesBefore branchIndex name) (bodyBound : UsesBefore branchIndex body) :
    interpretFuel environment (fuel + 12) state
        (⟨atomToStack (toLeaTTaAtom
          (bindResult (withFuel (.grounded (.int (remaining + 1)))
            (fun _ => pure (returned operand)) first).1 name body branchIndex).1)
          (parent :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (⟨atomToStack (toLeaTTaAtom (resultBranches result name body))
          (parent :: continuation), bindings⟩ :: rest) done := by
  let source := toLeaTTaAtom (call "function"
    [(withFuel (.grounded (.int (remaining + 1)))
      (fun _ => pure (returned operand)) first).1])
  let template := toLeaTTaAtom (resultBranches (.var (freshName branchIndex)) name body)
  let scope := chainFrameVars (parent :: continuation) source template
  have execution := withFuel_return_chain_enters environment state bindings operand
    (toLeaTTaAtom result) source template (freshName branchIndex) scope first remaining fuel
    parent continuation rest done groundings privateRemaining bounded materialized closed
  rw [show Metta.Subst.apply [(freshName branchIndex, toLeaTTaAtom result)] template =
      toLeaTTaAtom (resultBranches result name body) from
    substitute_resultBranches _ _ _ _ nameBound.runtime_fresh bodyBound.runtime_fresh] at execution
  exact execution

/-- The successful argument branch extends the actual caller bindings. -/
theorem resultBranches_value_selects (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (payload body : Atom) (name : String)
    (parent : Frame) (continuation : Stack) (fuel : Nat)
    (rest : List Item) (done : List (Metta.Atom × Metta.Bindings))
    (closed : (toLeaTTaAtom payload).vars = [])
    (fresh : Metta.Bindings.classValues bindings name = [])
    (acyclic : (Metta.Bindings.addValRaw bindings name (toLeaTTaAtom payload)).hasLoop = false) :
    interpretFuel environment (fuel + 1) state
        (⟨atomToStack (toLeaTTaAtom (resultBranches (value payload) (.var name) body))
          (parent :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (parent :: continuation)
          (Metta.instantiate (Metta.Bindings.addValRaw bindings name (toLeaTTaAtom payload))
            (toLeaTTaAtom body))
          (Metta.Bindings.addValRaw bindings name (toLeaTTaAtom payload)) :: rest) done := by
  exact unify_tagged_selects environment state bindings "nik:Value"
    (toLeaTTaAtom payload) (toLeaTTaAtom body) _ name parent continuation fuel rest done
    closed fresh acyclic

/-- A successful argument match enters its renamed continuation with exactly
one closed-value substitution. The resulting store retains the complete
runtime invariant, and unrelated keys keep their previous values. -/
theorem renamed_resultBranches_value_enters (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (rename : String → String)
    (payload body : Atom) (name : String) (parentBody : Metta.Atom)
    (scope : List Metta.VarName) (continuation : Stack) (fuel : Nat)
    (rest : List Item) (done : List (Metta.Atom × Metta.Bindings))
    (stored : ClosedValueBindings bindings)
    (closed : (toLeaTTaAtom payload).vars = [])
    (fresh : Metta.Bindings.lookupVal bindings (rename name) = none)
    (fixed : Metta.instantiate bindings (renBy rename (toLeaTTaAtom body)) =
      renBy rename (toLeaTTaAtom body))
    (embedded : isEmbeddedOp (Metta.Subst.apply [(rename name, toLeaTTaAtom payload)]
      (renBy rename (toLeaTTaAtom body))) = true) :
    let output := Metta.Bindings.addValRaw bindings (rename name) (toLeaTTaAtom payload)
    let entered := Metta.Subst.apply [(rename name, toLeaTTaAtom payload)]
      (renBy rename (toLeaTTaAtom body))
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    ClosedValueBindings output ∧
      (Mettapedia.Languages.MeTTa.HE.LeaTTaSpecConformance.LeaRuntimeBindingInvariant bindings →
        Mettapedia.Languages.MeTTa.HE.LeaTTaSpecConformance.LeaRuntimeBindingInvariant output) ∧
      (∀ other, other ≠ rename name → Metta.Bindings.lookupVal output other =
        Metta.Bindings.lookupVal bindings other) ∧
      interpretFuel environment (fuel + 2) state
        (⟨atomToStack (renBy rename (toLeaTTaAtom
          (resultBranches (value payload) (.var name) body)))
          (parent :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (⟨atomToStack entered (parent :: continuation), output⟩ :: rest) done := by
  intro output entered parent
  have outputClosed : ClosedValueBindings output := addValRaw_closed closed stored
  have materialized : Metta.instantiate output (renBy rename (toLeaTTaAtom body)) = entered := by
    rw [instantiate_add_closed_value bindings (rename name) (toLeaTTaAtom payload)
      _ stored closed fresh, fixed]
  have stable : Metta.instantiate output entered = entered := by
    rw [← materialized, instantiate_closed_value_bindings_idempotent outputClosed]
  refine ⟨outputClosed, fun invariant => fresh_closed_value_preserves_runtime bindings (rename name)
    (toLeaTTaAtom payload) stored invariant closed (toLeaTTaAtom_noFloat payload) fresh,
    fun other different => lookup_add_other bindings _ other _ different, ?_⟩
  have shape : renBy rename (toLeaTTaAtom (resultBranches (value payload) (.var name) body)) =
      .expr [.sym "unify", .expr [.sym "nik:Value", toLeaTTaAtom payload],
        .expr [.sym "nik:Value", .var (rename name)], renBy rename (toLeaTTaAtom body),
        renBy rename (toLeaTTaAtom
          (selectBranches (value payload)
            [(.symbol "nik:Failure", returned (.symbol "nik:Failure")),
             (.symbol "nik:Exhausted", returned (.symbol "nik:Exhausted"))]
            (returned (.symbol "nik:Malformed"))))] := by
    simp only [resultBranches, selectBranches, List.foldr_cons, List.foldr_nil,
      value, call, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil]
    rw [renBy_eq_self_of_vars_nil rename (toLeaTTaAtom payload) closed]
  rw [shape]
  have selected := unify_tagged_selects environment state bindings "nik:Value"
    (toLeaTTaAtom payload) (renBy rename (toLeaTTaAtom body))
    (renBy rename (toLeaTTaAtom (selectBranches (value payload)
      [(.symbol "nik:Failure", returned (.symbol "nik:Failure")),
       (.symbol "nik:Exhausted", returned (.symbol "nik:Exhausted"))]
      (returned (.symbol "nik:Malformed"))))) (rename name)
    parent continuation (fuel + 1) rest done closed
    ((stored.toValueBindings.classValues_lookupVal _).1 fresh) outputClosed.hasLoop_false
  rw [show fuel + 2 = (fuel + 1) + 1 by omega, selected, materialized]
  simpa only [stable] using function_embedded_enters environment state output parentBody
    entered scope continuation fuel rest done (by simpa only [stable] using embedded)

private theorem symbol_branch_enters_handler (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (parentBody fallback : Metta.Atom) (symbol : String)
    (scope : List Metta.VarName) (continuation : Stack) (fuel : Nat)
    (rest : List Item) (done : List (Metta.Atom × Metta.Bindings))
    (acyclic : bindings.hasLoop = false) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretFuel environment (fuel + 1) state
        (⟨atomToStack (.expr [.sym "unify", .sym symbol, .sym symbol,
          .expr [.sym "return", .sym symbol], fallback])
          (parent :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (parent :: continuation) (.expr [.sym "return", .sym symbol]) bindings :: rest) done := by
  intro parent
  let middle := finItem (parent :: continuation)
    (.expr [.sym "return", .sym symbol]) bindings
  have step (budget : Nat) :
      interpretStack1 environment budget state
          ⟨atomToStack (.expr [.sym "unify", .sym symbol, .sym symbol,
            .expr [.sym "return", .sym symbol], fallback])
            (parent :: continuation), bindings⟩ = ([middle], state) := by
    simp only [atomToStack, step_unify]
    rw [unify_same_symbol _ symbol _ _ bindings acyclic]
    simp [middle, Metta.instantiate, Metta.Bindings.resolveAtom]
  exact driver_singleton_step environment fuel state state _ middle rest done (step fuel) (by rfl)

/-- Refusal selects a return without evaluating the value continuation. -/
theorem resultBranches_failure_enters_handler (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (name body : Atom) (parentBody : Metta.Atom)
    (scope : List Metta.VarName) (continuation : Stack) (fuel : Nat)
    (rest : List Item) (done : List (Metta.Atom × Metta.Bindings))
    (acyclic : bindings.hasLoop = false) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretFuel environment (fuel + 3) state
        (⟨atomToStack (toLeaTTaAtom (resultBranches (.symbol "nik:Failure") name body))
          (parent :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (parent :: continuation) (.expr [.sym "return", .sym "nik:Failure"]) bindings :: rest) done := by
  intro parent
  let fallback : Metta.Atom := .expr [.sym "unify", .sym "nik:Failure", .sym "nik:Exhausted",
    .expr [.sym "return", .sym "nik:Exhausted"], .expr [.sym "return", .sym "nik:Malformed"]]
  change interpretFuel environment (fuel + 3) state
    (⟨atomToStack (.expr [.sym "unify", .sym "nik:Failure",
      .expr [.sym "nik:Value", toLeaTTaAtom name], toLeaTTaAtom body,
      .expr [.sym "unify", .sym "nik:Failure", .sym "nik:Failure",
        .expr [.sym "return", .sym "nik:Failure"], fallback]])
      (parent :: continuation), bindings⟩ :: rest) done = _
  rw [show fuel + 3 = (fuel + 2) + 1 by omega,
    unify_unmatched_selects environment state bindings _ _ _ _ parent
      (continuation) (fuel + 2) rest done
      (match_symbol_tagged "nik:Failure" "nik:Value" (toLeaTTaAtom name))]
  rw [show fuel + 2 = (fuel + 1) + 1 by omega,
    function_unify_enters environment state bindings parentBody _ _ _ _ scope
      (continuation) (fuel + 1) rest done]
  have fixed : Metta.instantiate bindings fallback = fallback := by
    apply Metta.instantiate_of_closed
    simp [fallback, Metta.Atom.vars]
  simpa only [Metta.instantiate, Metta.Bindings.resolveAtom, List.map_cons, List.map_nil,
    show Metta.Bindings.resolveAtom bindings fallback = fallback from fixed] using
    symbol_branch_enters_handler environment state bindings parentBody fallback "nik:Failure"
      scope continuation fuel rest done acyclic


/-- Source exhaustion selects its distinct return in any function context. -/
theorem resultBranches_exhausted_enters_handler (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (name body : Atom) (parentBody : Metta.Atom)
    (scope : List Metta.VarName) (continuation : Stack) (fuel : Nat)
    (rest : List Item) (done : List (Metta.Atom × Metta.Bindings))
    (acyclic : bindings.hasLoop = false) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretFuel environment (fuel + 5) state
        (⟨atomToStack (toLeaTTaAtom (resultBranches (.symbol "nik:Exhausted") name body))
          (parent :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (parent :: continuation) (.expr [.sym "return", .sym "nik:Exhausted"]) bindings :: rest) done := by
  intro parent
  change interpretFuel environment (fuel + 5) state
    (⟨atomToStack (.expr [.sym "unify", .sym "nik:Exhausted",
      .expr [.sym "nik:Value", toLeaTTaAtom name], toLeaTTaAtom body,
      .expr [.sym "unify", .sym "nik:Exhausted", .sym "nik:Failure",
        .expr [.sym "return", .sym "nik:Failure"],
        .expr [.sym "unify", .sym "nik:Exhausted", .sym "nik:Exhausted",
          .expr [.sym "return", .sym "nik:Exhausted"],
          .expr [.sym "return", .sym "nik:Malformed"]]]])
      (parent :: continuation), bindings⟩ :: rest) done = _
  rw [show fuel + 5 = (fuel + 4) + 1 by omega,
    unify_unmatched_selects environment state bindings _ _ _ _ parent
      (continuation) (fuel + 4) rest done
      (match_symbol_tagged "nik:Exhausted" "nik:Value" (toLeaTTaAtom name))]
  rw [show fuel + 4 = (fuel + 3) + 1 by omega,
    function_unify_enters environment state bindings parentBody _ _ _ _ scope
      (continuation) (fuel + 3) rest done]
  simp only [Metta.instantiate, Metta.Bindings.resolveAtom, List.map_cons, List.map_nil]
  rw [show fuel + 3 = (fuel + 2) + 1 by omega,
    unify_unmatched_selects environment state bindings _ _ _ _ parent
      (continuation) (fuel + 2) rest done (by decide)]
  rw [show fuel + 2 = (fuel + 1) + 1 by omega,
    function_unify_enters environment state bindings parentBody _ _ _ _ scope
      (continuation) (fuel + 1) rest done]
  simpa only [Metta.instantiate, Metta.Bindings.resolveAtom, List.map_cons, List.map_nil] using
    symbol_branch_enters_handler environment state bindings parentBody
      (.expr [.sym "return", .sym "nik:Malformed"]) "nik:Exhausted"
      scope continuation fuel rest done acyclic

/-- Logical refusal propagates; the value continuation is never evaluated. -/
theorem resultBranches_failure (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (name body : Atom) (parentBody : Metta.Atom)
    (scope : List Metta.VarName) (caller : Frame) (continuation : Stack) (fuel : Nat)
    (rest : List Item) (done : List (Metta.Atom × Metta.Bindings))
    (acyclic : bindings.hasLoop = false) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretFuel environment (fuel + 4) state
        (⟨atomToStack (toLeaTTaAtom (resultBranches (.symbol "nik:Failure") name body))
          (parent :: caller :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (caller :: continuation) (.sym "nik:Failure") bindings :: rest) done := by
  intro parent
  have prefixRun := resultBranches_failure_enters_handler environment state bindings name body
    parentBody scope (caller :: continuation) (fuel + 1) rest done acyclic
  simp only [Nat.add_assoc] at prefixRun
  rw [prefixRun]
  simpa only [Metta.instantiate, Metta.Bindings.resolveAtom] using
    selected_return_to_caller environment state bindings parentBody (.sym "nik:Failure") scope
      caller continuation fuel rest done

/-- Exhaustion stays distinct from logical refusal, including inside a call. -/
theorem resultBranches_exhausted (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (name body : Atom) (parentBody : Metta.Atom)
    (scope : List Metta.VarName) (caller : Frame) (continuation : Stack) (fuel : Nat)
    (rest : List Item) (done : List (Metta.Atom × Metta.Bindings))
    (acyclic : bindings.hasLoop = false) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretFuel environment (fuel + 6) state
        (⟨atomToStack (toLeaTTaAtom (resultBranches (.symbol "nik:Exhausted") name body))
          (parent :: caller :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (caller :: continuation) (.sym "nik:Exhausted") bindings :: rest) done := by
  intro parent
  have prefixRun := resultBranches_exhausted_enters_handler environment state bindings name body
    parentBody scope (caller :: continuation) (fuel + 1) rest done acyclic
  simp only [Nat.add_assoc] at prefixRun
  rw [prefixRun]
  simpa only [Metta.instantiate, Metta.Bindings.resolveAtom] using
    selected_return_to_caller environment state bindings parentBody (.sym "nik:Exhausted") scope
      caller continuation fuel rest done

/-- A returned value passes through function return, sequencing and matching
to the actual continuation with its payload bound. -/
theorem bindResult_return_value (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (payload body : Atom) (name : String) (first fuel : Nat)
    (parent : Frame) (continuation : Stack) (rest : List Item)
    (done : List (Metta.Atom × Metta.Bindings))
    (closed : (toLeaTTaAtom payload).vars = [])
    (nameBound : UsesBefore first (.var name)) (bodyBound : UsesBefore first body)
    (fresh : Metta.Bindings.classValues bindings name = [])
    (acyclic : (Metta.Bindings.addValRaw bindings name (toLeaTTaAtom payload)).hasLoop = false) :
    interpretFuel environment (fuel + 5) state
        (⟨atomToStack (toLeaTTaAtom
          (bindResult (returned (value payload)) (.var name) body first).1)
          (parent :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (parent :: continuation)
          (Metta.instantiate (Metta.Bindings.addValRaw bindings name (toLeaTTaAtom payload))
            (toLeaTTaAtom body))
          (Metta.Bindings.addValRaw bindings name (toLeaTTaAtom payload)) :: rest) done := by
  rw [show fuel + 5 = (fuel + 1) + 4 by omega,
    bindResult_return_enters environment state bindings (value payload) (.var name) body
      first (fuel + 1) parent continuation rest done
      (by simp [value, call, toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.vars, closed])
      nameBound bodyBound]
  exact resultBranches_value_selects environment state bindings payload body name parent
    continuation fuel rest done closed fresh acyclic

/-- A guarded value read from the incoming frame reaches the next operand
binding after the actual native comparison and subtraction have executed. -/
theorem bindResult_withFuel_value_selects (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (operand payload body : Atom) (name : String)
    (first branchIndex remaining fuel : Nat) (parent : Frame) (continuation : Stack)
    (rest : List Item) (done : List (Metta.Atom × Metta.Bindings))
    (groundings : environment.gt = Metta.Builtins.table)
    (privateRemaining : Metta.instantiate bindings (.var (freshName first)) =
      .var (freshName first))
    (bounded : UsesBefore (first + 1) operand)
    (materialized : Metta.instantiate bindings (toLeaTTaAtom operand) = toLeaTTaAtom payload)
    (closed : (toLeaTTaAtom payload).vars = [])
    (nameBound : UsesBefore branchIndex (.var name)) (bodyBound : UsesBefore branchIndex body)
    (fresh : Metta.Bindings.classValues bindings name = [])
    (acyclic : (Metta.Bindings.addValRaw bindings name (toLeaTTaAtom payload)).hasLoop = false) :
    interpretFuel environment (fuel + 13) state
        (⟨atomToStack (toLeaTTaAtom
          (bindResult (withFuel (.grounded (.int (remaining + 1)))
            (fun _ => pure (returned (value operand))) first).1
            (.var name) body branchIndex).1)
          (parent :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (parent :: continuation)
          (Metta.instantiate (Metta.Bindings.addValRaw bindings name (toLeaTTaAtom payload))
            (toLeaTTaAtom body))
          (Metta.Bindings.addValRaw bindings name (toLeaTTaAtom payload)) :: rest) done := by
  have valueBound : UsesBefore (first + 1) (value operand) := by
    simpa [value] using bounded
  have valueMaterialized : Metta.instantiate bindings (toLeaTTaAtom (value operand)) =
      toLeaTTaAtom (value payload) := by
    simpa only [value, call, toLeaTTaAtom, toLeaTTaAtoms, Metta.instantiate,
      Metta.Bindings.resolveAtom, List.map_cons, List.map_nil, Metta.Atom.expr.injEq,
      List.cons.injEq, true_and, and_true] using materialized
  rw [show fuel + 13 = (fuel + 1) + 12 by omega,
    bindResult_withFuel_return_enters environment state bindings (value operand) (value payload)
      (.var name) body first branchIndex remaining (fuel + 1) parent continuation rest done
      groundings privateRemaining valueBound valueMaterialized
      (by simp [value, call, toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.vars, closed])
      nameBound bodyBound]
  exact resultBranches_value_selects environment state bindings payload body name parent
    continuation fuel rest done closed fresh acyclic

/-- A refused operand propagates through the entire generated binding form. -/
theorem bindResult_return_failure (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (name body : Atom) (parentBody : Metta.Atom)
    (scope : List Metta.VarName) (first fuel : Nat)
    (caller : Frame) (continuation : Stack) (rest : List Item)
    (done : List (Metta.Atom × Metta.Bindings))
    (nameBound : UsesBefore first name) (bodyBound : UsesBefore first body)
    (acyclic : bindings.hasLoop = false) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretFuel environment (fuel + 8) state
        (⟨atomToStack (toLeaTTaAtom
          (bindResult (returned (.symbol "nik:Failure")) name body first).1)
          (parent :: caller :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (caller :: continuation) (.sym "nik:Failure") bindings :: rest) done := by
  intro parent
  rw [show fuel + 8 = (fuel + 4) + 4 by omega,
    bindResult_return_enters environment state bindings (.symbol "nik:Failure") name body
      first (fuel + 4) parent (caller :: continuation) rest done
      (by simp [toLeaTTaAtom, Metta.Atom.vars]) nameBound bodyBound]
  exact resultBranches_failure environment state bindings name body parentBody scope caller
    continuation fuel rest done acyclic

/-- An exhausted operand cannot turn into a completed refusal or a value. -/
theorem bindResult_return_exhausted (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (name body : Atom) (parentBody : Metta.Atom)
    (scope : List Metta.VarName) (first fuel : Nat)
    (caller : Frame) (continuation : Stack) (rest : List Item)
    (done : List (Metta.Atom × Metta.Bindings))
    (nameBound : UsesBefore first name) (bodyBound : UsesBefore first body)
    (acyclic : bindings.hasLoop = false) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretFuel environment (fuel + 10) state
        (⟨atomToStack (toLeaTTaAtom
          (bindResult (returned (.symbol "nik:Exhausted")) name body first).1)
          (parent :: caller :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (caller :: continuation) (.sym "nik:Exhausted") bindings :: rest) done := by
  intro parent
  rw [show fuel + 10 = (fuel + 6) + 4 by omega,
    bindResult_return_enters environment state bindings (.symbol "nik:Exhausted") name body
      first (fuel + 6) parent (caller :: continuation) rest done
      (by simp [toLeaTTaAtom, Metta.Atom.vars]) nameBound bodyBound]
  exact resultBranches_exhausted environment state bindings name body parentBody scope caller
    continuation fuel rest done acyclic

/-- Positive control for every encoded guest term, including guest variables:
the target variable receives data, with no freshness or merge premise left. -/
theorem bindResult_encoded_payload (environment : MinEnv) (state : St)
    (payload : Term) (parent : Frame) (continuation : Stack) (fuel : Nat)
    (rest : List Item) (done : List (Metta.Atom × Metta.Bindings)) :
    let encoded := MeTTaData.encode payload
    let name := freshName 0
    interpretFuel environment (fuel + 5) state
        (⟨atomToStack (toLeaTTaAtom
          (bindResult (returned (value encoded)) (.var name) (returned (.var name)) 1).1)
          (parent :: continuation), []⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (parent :: continuation) (.expr [.sym "return", toLeaTTaAtom encoded])
          [.val name (toLeaTTaAtom encoded)] :: rest) done := by
  intro encoded name
  have closed := data_atom_runtime_closed (MeTTaData.encode_data payload)
  have absent : name ∉ (toLeaTTaAtom encoded).vars := by simp [encoded, closed]
  have bound : UsesBefore 1 (.var name) := by simp [name]
  have acyclic : (Metta.Bindings.addValRaw [] name (toLeaTTaAtom encoded)).hasLoop = false := by
    simpa [Metta.Bindings.addValRaw, Metta.Bindings.removeVal] using
      Metta.Bindings.hasLoop_singleton_val_of_not_mem name (toLeaTTaAtom encoded) absent
  have execution := bindResult_return_value environment state [] encoded (returned (.var name))
    name 1 fuel parent continuation rest done closed bound
    (by simpa [returned] using bound) (by rfl) acyclic
  have read := Metta.instantiate_singleton_val_var_of_not_mem name (toLeaTTaAtom encoded) absent
  simpa only [Metta.Bindings.addValRaw, Metta.Bindings.removeVal, List.filter_nil,
    instantiate_returned, toLeaTTaAtom, read] using execution

/-- An unrecognized result symbol cannot enter the value continuation. -/
theorem resultBranches_unrecognized_symbol (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (symbol : String) (name body : Atom) (parentBody : Metta.Atom)
    (scope : List Metta.VarName) (caller : Frame) (continuation : Stack) (fuel : Nat)
    (rest : List Item) (done : List (Metta.Atom × Metta.Bindings))
    (notFailure : symbol ≠ "nik:Failure") (notExhausted : symbol ≠ "nik:Exhausted") :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretFuel environment (fuel + 6) state
        (⟨atomToStack (toLeaTTaAtom (resultBranches (.symbol symbol) name body))
          (parent :: caller :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (caller :: continuation) (.sym "nik:Malformed") bindings :: rest) done := by
  intro parent
  change interpretFuel environment (fuel + 6) state
    (⟨atomToStack (.expr [.sym "unify", .sym symbol,
      .expr [.sym "nik:Value", toLeaTTaAtom name], toLeaTTaAtom body,
      .expr [.sym "unify", .sym symbol, .sym "nik:Failure",
        .expr [.sym "return", .sym "nik:Failure"],
        .expr [.sym "unify", .sym symbol, .sym "nik:Exhausted",
          .expr [.sym "return", .sym "nik:Exhausted"],
          .expr [.sym "return", .sym "nik:Malformed"]]]])
      (parent :: caller :: continuation), bindings⟩ :: rest) done = _
  rw [show fuel + 6 = (fuel + 5) + 1 by omega,
    unify_unmatched_selects environment state bindings _ _ _ _ parent
      (caller :: continuation) (fuel + 5) rest done
      (match_symbol_tagged symbol "nik:Value" (toLeaTTaAtom name))]
  rw [show fuel + 5 = (fuel + 4) + 1 by omega,
    function_unify_enters environment state bindings parentBody _ _ _ _ scope
      (caller :: continuation) (fuel + 4) rest done]
  simp only [Metta.instantiate, Metta.Bindings.resolveAtom, List.map_cons, List.map_nil]
  rw [show fuel + 4 = (fuel + 3) + 1 by omega,
    unify_unmatched_selects environment state bindings _ _ _ _ parent
      (caller :: continuation) (fuel + 3) rest done
      (by simp [Metta.matchAtoms, Metta.matchAtomsWith, notFailure])]
  rw [show fuel + 3 = (fuel + 2) + 1 by omega,
    function_unify_enters environment state bindings parentBody _ _ _ _ scope
      (caller :: continuation) (fuel + 2) rest done]
  simp only [Metta.instantiate, Metta.Bindings.resolveAtom, List.map_cons, List.map_nil]
  rw [show fuel + 2 = (fuel + 1) + 1 by omega,
    unify_unmatched_selects environment state bindings _ _ _ _ parent
      (caller :: continuation) (fuel + 1) rest done
      (by simp [Metta.matchAtoms, Metta.matchAtomsWith, notExhausted])]
  simpa only [Metta.instantiate, Metta.Bindings.resolveAtom] using
    selected_return_to_caller environment state bindings parentBody (.sym "nik:Malformed")
      scope caller continuation fuel rest done

/-- In a closed-value frame, sequencing preserves that invariant and enters
the next embedded instruction with its operand materialized. Loop freedom
follows from the actual binding update, rather than being a caller premise. -/
theorem bindResult_withFuel_enters_closed (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (operand payload body : Atom) (name : String)
    (first branchIndex remaining fuel : Nat) (parentBody : Metta.Atom)
    (scope : List Metta.VarName) (continuation : Stack)
    (rest : List Item) (done : List (Metta.Atom × Metta.Bindings))
    (groundings : environment.gt = Metta.Builtins.table)
    (stored : ClosedValueBindings bindings)
    (privateRemaining : Metta.instantiate bindings (.var (freshName first)) =
      .var (freshName first))
    (bounded : UsesBefore (first + 1) operand)
    (materialized : Metta.instantiate bindings (toLeaTTaAtom operand) = toLeaTTaAtom payload)
    (closed : (toLeaTTaAtom payload).vars = [])
    (nameBound : UsesBefore branchIndex (.var name)) (bodyBound : UsesBefore branchIndex body)
    (fresh : Metta.Bindings.lookupVal bindings name = none)
    (embedded : isEmbeddedOp
      (Metta.instantiate (Metta.Bindings.addValRaw bindings name (toLeaTTaAtom payload))
        (toLeaTTaAtom body)) = true) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    let output := Metta.Bindings.addValRaw bindings name (toLeaTTaAtom payload)
    ClosedValueBindings output ∧
    interpretFuel environment (fuel + 14) state
        (⟨atomToStack (toLeaTTaAtom
          (bindResult (withFuel (.grounded (.int (remaining + 1)))
            (fun _ => pure (returned (value operand))) first).1
            (.var name) body branchIndex).1)
          (parent :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (⟨atomToStack (Metta.instantiate output (toLeaTTaAtom body))
          (parent :: continuation), output⟩ :: rest) done := by
  intro parent output
  have outputClosed : ClosedValueBindings output := addValRaw_closed closed stored
  refine ⟨outputClosed, ?_⟩
  have freshClass := (stored.toValueBindings.classValues_lookupVal name).1 fresh
  rw [show fuel + 14 = (fuel + 1) + 13 by omega,
    bindResult_withFuel_value_selects environment state bindings operand payload body name
      first branchIndex remaining (fuel + 1) parent continuation rest done groundings
      privateRemaining bounded materialized closed nameBound bodyBound freshClass
      outputClosed.hasLoop_false]
  have stable := instantiate_closed_value_bindings_idempotent outputClosed (toLeaTTaAtom body)
  have step := function_embedded_enters environment state output parentBody
    (Metta.instantiate output (toLeaTTaAtom body)) scope continuation fuel rest done
    (by simpa only [stable] using embedded)
  simpa only [stable] using step

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
