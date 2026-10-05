import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaInvocationExecution
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.DataEquality

/-!
# Execution of the emitted deterministic fragment

Source fuel induction composes the actual loader, argument evaluator, lexical
bindings and call returns. Host assumptions are restricted to named data and
arithmetic operations. Target instruction budgets remain independent of the
source evaluation budget.
-/

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.HE.CanonAbsorbsFreshening
open Mettapedia.Languages.MeTTa.HE.LeaTTaSpecConformance
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal (substituteName)
open Metta.Minimal

namespace Execution

private theorem guarded_arguments (program : Program) (host : Host) (environment : MinEnv)
    (groundings : environment.gt = Metta.Builtins.table)
    (sourceBindings : Env) (remaining : Nat) (terms : List Term)
    (next : Atom → List Atom → Emit Atom)
    (formed : ContinuationSyntax (next (.grounded (.int remaining))))
    (scope : ∀ index first, index < first → ∀ arguments,
      (∀ atom ∈ arguments, UsesBefore first atom) →
      first ≤ (next (.var (freshName index)) arguments first).2 ∧
        UsesBefore (next (.var (freshName index)) arguments first).2
          (next (.var (freshName index)) arguments first).1)
    (fill : ∀ index first, index < first → ∀ arguments,
      (∀ atom ∈ arguments, UsesBefore first atom) →
      (substituteName (freshName index) (.grounded (.int remaining))
          (next (.var (freshName index)) arguments first).1,
        (next (.var (freshName index)) arguments first).2) =
      next (.grounded (.int remaining))
        (arguments.map (substituteName (freshName index) (.grounded (.int remaining)))) first)
    (finish : List Term → Outcome)
    (elements : ∀ term ∈ terms, ExpressionExecutes program environment remaining sourceBindings term
      (eval program host remaining sourceBindings term))
    (nextRun : ∀ values, CompiledExecutes environment
      (next (.grounded (.int remaining)) (values.map MeTTaData.encode)) (finish values)) :
    CompiledExecutes environment
      (withFuel (.grounded (.int (remaining + 1))) (fun fuel =>
        expressions program (sourceBindings.map fun row => (row.1, MeTTaData.encode row.2))
          fuel terms (next fuel)))
      (match evalItems program host remaining sourceBindings terms with
       | .values values => finish values
       | .stop result => result) := by
  let names := sourceBindings.map (fun row => (row.1, MeTTaData.encode row.2))
  have namesBound (first : Nat) : ∀ entry ∈ names, UsesBefore first entry.2 := by
    intro entry member
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp member
    exact usesBefore_data first row.2
  apply withFuel_executes environment groundings
    (fun fuel => expressions program names fuel terms (next fuel)) remaining
  · intro first
    exact expressions_scope program names (.var (freshName first)) terms _ (first + 1)
      (namesBound _) ((usesBefore_freshName _ _).mpr (by omega))
      (fun start later arguments bounded => scope first start (by omega) arguments bounded)
  · intro first
    have transported := congrArg Prod.fst (Control.expressions_substitution program names
      (.var (freshName first)) (.grounded (.int remaining)) terms
      (next (.var (freshName first))) (next (.grounded (.int remaining))) first (first + 1)
      (by omega) (namesBound _) ((usesBefore_freshName _ _).mpr (by omega))
      (fun start later arguments bounded => scope first start (by omega) arguments bounded)
      (fun start later arguments bounded => fill first start (by omega) arguments bounded))
    have namesSame : names.map (fun entry =>
        (entry.1, substituteName (freshName first) (.grounded (.int remaining)) entry.2)) = names := by
      simp only [names, List.map_map, Function.comp_def, Control.substituteName_encoded]
    simpa only [namesSame, substituteName, if_true] using transported
  · exact expressions_executes program environment sourceBindings remaining terms
      (eval program host remaining) _ formed finish elements nextRun

private theorem expression_call (program : Program) (host : Host) (environment : MinEnv)
    (loaded : LoadedProgram program environment)
    (primitives : NamedPrimitivesExecute host environment)
    (unlisted : ∀ head, head ∉ primitiveHeads → ∀ arguments,
      host.primitive head arguments = .unhandled)
    (sourceBindings : Env) (remaining : Nat) (head : String) (arguments : List Term)
    (notLet : ∀ a b c, arguments = [a, b, c] → head = "let" → False)
    (notNullary : ∀ a, arguments = [a] → head = "metta-nullary" → False)
    (recursive : ∀ sourceBindings term,
      ExpressionExecutes program environment remaining sourceBindings term
        (eval program host remaining sourceBindings term)) :
    ExpressionExecutes program environment (remaining + 1) sourceBindings
      (.expr (.sym head :: arguments))
      (eval program host (remaining + 1) sourceBindings (.expr (.sym head :: arguments))) := by
  let names := sourceBindings.map (fun row => (row.1, MeTTaData.encode row.2))
  have emitted : expression program names (.grounded (.int (remaining + 1)))
      (.expr (.sym head :: arguments)) =
      withFuel (.grounded (.int (remaining + 1))) (fun fuel =>
        expressions program names fuel arguments (fun values =>
          returnInvocation (invoke program fuel head values))) := by
    rw [expression]
    congr 1
    funext fuel
    split <;> simp_all
    all_goals aesop
  have evaluated : eval program host (remaining + 1) sourceBindings
      (.expr (.sym head :: arguments)) =
      (match evalItems program host remaining sourceBindings arguments with
       | .values values => apply program host remaining head values
       | .stop result => result) := by
    rw [eval]
    unfold evalStep
    split <;> simp_all [evalItems, apply]
    all_goals aesop
  change CompiledExecutes environment (expression program names _ _) _
  simp only [Nat.cast_add, Nat.cast_one]
  rw [emitted, evaluated]
  apply guarded_arguments program host environment loaded.groundings sourceBindings remaining arguments
    (fun fuel values => returnInvocation (invoke program fuel head values))
    (invocation_continuation_syntax program remaining head)
  · intro index first before arguments bounded
    exact returnInvocation_scope _ first (invoke_scope program _ head arguments first
      ((usesBefore_freshName first index).mpr before) bounded)
  · intro index first before arguments _
    simpa only [substituteName, if_true] using
      Control.substituteName_returnInvoke (.grounded (.int remaining)) (.var (freshName index))
        program head arguments index first before
  · intro term _
    exact recursive sourceBindings term
  · exact compiled_apply program host environment loaded primitives unlisted remaining recursive head

private theorem expression_data (program : Program) (host : Host) (environment : MinEnv)
    (groundings : environment.gt = Metta.Builtins.table)
    (sourceBindings : Env) (remaining : Nat) (items : List Term)
    (nonempty : items = [] → False)
    (notLet : ∀ a b c, items = [.sym "let", a, b, c] → False)
    (notNullary : ∀ a, items = [.sym "metta-nullary", a] → False)
    (notCall : ∀ head arguments, items = .sym head :: arguments → False)
    (recursive : ∀ sourceBindings term,
      ExpressionExecutes program environment remaining sourceBindings term
        (eval program host remaining sourceBindings term)) :
    ExpressionExecutes program environment (remaining + 1) sourceBindings (.expr items)
      (eval program host (remaining + 1) sourceBindings (.expr items)) := by
  let names := sourceBindings.map (fun row => (row.1, MeTTaData.encode row.2))
  let next : Atom → List Atom → Emit Atom := fun _ values =>
    pure (returned (value (call "nik:Expr" [sequenceAtom values])))
  have formed : ContinuationSyntax (next (.grounded (.int remaining))) :=
    data_continuation_syntax "nik:Expr"
  have emitted : expression program names (.grounded (.int (remaining + 1))) (.expr items) =
      withFuel (.grounded (.int (remaining + 1))) (fun fuel =>
        expressions program names fuel items (next fuel)) := by
    rw [expression]
    congr 1
    funext fuel
    split <;> simp_all [next]
  have evaluated : eval program host (remaining + 1) sourceBindings (.expr items) =
      (match evalItems program host remaining sourceBindings items with
       | .values values => .value (.expr values)
       | .stop result => result) := by
    rw [eval]
    unfold evalStep
    split <;> simp_all [evalItems]
    all_goals aesop
  change CompiledExecutes environment (expression program names _ _) _
  simp only [Nat.cast_add, Nat.cast_one]
  rw [emitted, evaluated]
  apply guarded_arguments program host environment groundings sourceBindings remaining items next formed
  · intro index first _ arguments bounded
    exact formed.scope first arguments bounded
  · intro index first before arguments bounded
    exact formed.substitute index first before (.grounded (.int remaining)) arguments bounded
  · intro term _
    exact recursive sourceBindings term
  · intro values
    simpa only [next, sequenceAtom_encode, observation, MeTTaData.encode, call] using
      compiled_return environment (.value (.expr values))

/-- Every source expression executes in the independent MeTTa interpreter.
The proof is by source fuel, not by assuming execution of the guest checker.
In particular, substitution, recursive calls and failure propagation use the
actual generated instructions and closed-binding invariant. -/
theorem expression_execution (program : Program) (host : Host) (environment : MinEnv)
    (loaded : LoadedProgram program environment)
    (primitives : NamedPrimitivesExecute host environment)
    (unlisted : ∀ head, head ∉ primitiveHeads → ∀ arguments,
      host.primitive head arguments = .unhandled) (sourceFuel : Nat) :
    ∀ sourceBindings term,
      ExpressionExecutes program environment sourceFuel sourceBindings term
        (eval program host sourceFuel sourceBindings term) := by
  induction sourceFuel with
  | zero =>
    intro sourceBindings term
    exact expression_zero program environment loaded.groundings sourceBindings term
  | succ remaining recursive =>
    intro sourceBindings term
    fun_cases evalStep (eval program host remaining) (apply program host remaining) sourceBindings term
    case case1 name payload lookup | case2 name lookup =>
      simpa only [eval, evalStep, lookup] using
        expression_variable program environment loaded.groundings sourceBindings name remaining
    case case3 name =>
      exact expression_symbol program environment loaded.groundings sourceBindings name remaining
    case case4 text =>
      exact expression_literal program environment loaded.groundings sourceBindings text remaining
    case case5 items values outcome | case6 items result outcome =>
      exact expression_list program host environment loaded.groundings sourceBindings remaining items
        (fun term _ => recursive sourceBindings term)
    case case7 =>
      exact expression_empty program environment loaded.groundings sourceBindings remaining
    case case8 name bound body payload outcome | case9 name bound body noValue =>
      exact expression_let program host environment loaded.groundings sourceBindings name bound body remaining
        (recursive sourceBindings bound) (fun payload => recursive ((name, payload) :: sourceBindings) body)
    case case10 target bound body notVariable =>
      have failed : eval program host (remaining + 1) sourceBindings
          (.expr [.sym "let", target, bound, body]) = .failure := by
        rw [eval]
        unfold evalStep
        split <;> simp_all
        all_goals aesop
      rw [failed]
      apply expression_of_return program environment loaded.groundings sourceBindings _ remaining .failure
      intro first
      apply congrArg (fun compiler : Emit Atom => (compiler first).1)
      rw [expression]
      congr 1
      funext fuel
      split <;> simp_all [observation]
      all_goals aesop
    case case11 name =>
      exact expression_nullary program environment loaded.groundings sourceBindings name remaining
    case case12 target notSymbol =>
      have failed : eval program host (remaining + 1) sourceBindings
          (.expr [.sym "metta-nullary", target]) = .failure := by
        rw [eval]
        unfold evalStep
        split <;> simp_all
        all_goals aesop
      rw [failed]
      apply expression_of_return program environment loaded.groundings sourceBindings _ remaining .failure
      intro first
      apply congrArg (fun compiler : Emit Atom => (compiler first).1)
      rw [expression]
      congr 1
      funext fuel
      split <;> simp_all [observation]
      all_goals aesop
    case case13 head arguments notLetVar notLet notNullarySym notNullary values outcome |
        case14 head arguments notLetVar notLet notNullarySym notNullary result outcome =>
      exact expression_call program host environment loaded primitives unlisted sourceBindings remaining
        head arguments notLet notNullary recursive
    case case15 items nonempty notLetVar notLet notNullarySym notNullary notCall values outcome |
        case16 items nonempty notLetVar notLet notNullarySym notNullary notCall result outcome =>
      exact expression_data program host environment loaded.groundings sourceBindings remaining items
        nonempty notLet notNullary notCall recursive

/-- The complete application contract no longer assumes any recursive body
execution. Those runs are supplied by the source-fuel induction above. -/
theorem invocation_execution (program : Program) (host : Host) (environment : MinEnv)
    (loaded : LoadedProgram program environment)
    (primitives : NamedPrimitivesExecute host environment)
    (unlisted : ∀ head, head ∉ primitiveHeads → ∀ arguments,
      host.primitive head arguments = .unhandled)
    (sourceFuel : Nat) (head : String) (arguments : List Term) :
    CompiledExecutes environment
      (returnInvocation (invoke program (.grounded (.int sourceFuel)) head
        (arguments.map MeTTaData.encode)))
      (apply program host sourceFuel head arguments) :=
  compiled_apply program host environment loaded primitives unlisted sourceFuel
    (expression_execution program host environment loaded primitives unlisted sourceFuel) head arguments

/-- Finish any generated body using the actual outer function-return frame. -/
theorem compiled_public_execution (environment : MinEnv) (compiler : Emit Atom)
    (result : Outcome) (execution : CompiledExecutes environment compiler result)
    (shaped : ∀ first rename, ∃ items,
      renBy rename (toLeaTTaAtom (compiler first).1) = .expr items)
    (first : Nat) (rename : String → String) (injective : Function.Injective rename)
    (state : St) (noExtra : state.world.selfExtra = []) (noImports : state.world.selfImports = [])
    (incoming : Metta.Bindings) (stored : ClosedValueBindings incoming)
    (invariant : LeaRuntimeBindingInvariant incoming) :
    let body := renBy rename (toLeaTTaAtom (compiler first).1)
    (∀ key ∈ body.vars, Metta.Bindings.lookupVal incoming key = none) →
    ∃ nextState output cost threshold,
      nextState.world = state.world ∧ ClosedValueBindings output ∧
      LeaRuntimeBindingInvariant output ∧
      ∀ fuel, threshold ≤ fuel →
        interpretFuel environment (fuel + cost) state
          [⟨atomToStack (.expr [.sym "function", body]) [], incoming⟩] [] =
        ([(toLeaTTaAtom (observation result), output)],
          nextState) := by
  intro body fresh
  let sourceCall := Metta.Atom.expr [.sym "function", body]
  obtain ⟨nextState, output, cost, threshold, world, outputClosed, outputInvariant,
      _, run⟩ := execution first rename injective state noExtra noImports incoming stored
      invariant sourceCall [] [] fresh
  have shape : ∃ items, body = .expr items := shaped first rename
  refine ⟨nextState, output, cost + 1, threshold, world, outputClosed, outputInvariant, ?_⟩
  intro fuel enough
  obtain ⟨items, shape⟩ := shape
  have opener : atomToStack sourceCall [] = atomToStack body
      [{ atom := sourceCall, ret := .function, vars := [] }] := by
    simp only [sourceCall, shape, atomToStack, varsCopy]
  have ran := run (fuel + 1) (by omega) [] []
  have visible : (toLeaTTaAtom (observation result) != emptyA) = true := by
    cases result <;> rfl
  have returned := Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlExecution.selected_closed_return_finishes
    environment nextState output sourceCall (toLeaTTaAtom (observation result)) [] fuel
      (observation_closed result) visible
  rw [show fuel + (cost + 1) = fuel + 1 + cost by omega]
  change interpretFuel environment (fuel + 1 + cost) state
    [⟨atomToStack sourceCall [], incoming⟩] [] = _
  rw [opener]
  exact ran.trans returned

/-- A public generated function returns exactly one closed tagged outcome.
The result is observed by the actual outer function-return instruction. -/
theorem expression_public_execution (program : Program) (host : Host) (environment : MinEnv)
    (loaded : LoadedProgram program environment)
    (primitives : NamedPrimitivesExecute host environment)
    (unlisted : ∀ head, head ∉ primitiveHeads → ∀ arguments,
      host.primitive head arguments = .unhandled)
    (sourceFuel : Nat) (sourceBindings : Env) (term : Term)
    (first : Nat) (rename : String → String) (injective : Function.Injective rename)
    (state : St) (noExtra : state.world.selfExtra = []) (noImports : state.world.selfImports = [])
    (incoming : Metta.Bindings) (stored : ClosedValueBindings incoming)
    (invariant : LeaRuntimeBindingInvariant incoming) :
    let body := renBy rename (toLeaTTaAtom (expression program
      (sourceBindings.map (fun row => (row.1, MeTTaData.encode row.2)))
      (.grounded (.int sourceFuel)) term first).1)
    (∀ key ∈ body.vars, Metta.Bindings.lookupVal incoming key = none) →
    ∃ nextState output cost threshold,
      nextState.world = state.world ∧ ClosedValueBindings output ∧
      LeaRuntimeBindingInvariant output ∧
      ∀ fuel, threshold ≤ fuel →
        interpretFuel environment (fuel + cost) state
          [⟨atomToStack (.expr [.sym "function", body]) [], incoming⟩] [] =
        ([(toLeaTTaAtom (observation (eval program host sourceFuel sourceBindings term)), output)],
          nextState) := by
  refine compiled_public_execution environment _ _
    (expression_execution program host environment loaded primitives unlisted
      sourceFuel sourceBindings term) ?_
    first rename injective state noExtra noImports incoming stored invariant
  intro first rename
  have embedded := expression_runtime_embedded program
    (sourceBindings.map (fun row => (row.1, MeTTaData.encode row.2)))
    (.grounded (.int sourceFuel)) term first rename
  cases shaped : renBy rename (toLeaTTaAtom (expression program
      (sourceBindings.map (fun row => (row.1, MeTTaData.encode row.2)))
      (.grounded (.int sourceFuel)) term first).1) with
  | sym => simp [shaped, isEmbeddedOp] at embedded
  | var => simp [shaped, isEmbeddedOp] at embedded
  | gnd => simp [shaped, isEmbeddedOp] at embedded
  | expr items => exact ⟨items, rfl⟩

/-- Public execution of the same request interface used by the emitted service.
Input data is encoded before invocation and is never re-evaluated as source. -/
theorem invocation_public_execution (program : Program) (host : Host) (environment : MinEnv)
    (loaded : LoadedProgram program environment)
    (primitives : NamedPrimitivesExecute host environment)
    (unlisted : ∀ head, head ∉ primitiveHeads → ∀ arguments,
      host.primitive head arguments = .unhandled)
    (sourceFuel : Nat) (head : String) (arguments : List Term)
    (first : Nat) (rename : String → String) (injective : Function.Injective rename)
    (state : St) (noExtra : state.world.selfExtra = []) (noImports : state.world.selfImports = [])
    (incoming : Metta.Bindings) (stored : ClosedValueBindings incoming)
    (invariant : LeaRuntimeBindingInvariant incoming) :
    let body := renBy rename (toLeaTTaAtom
      (returnInvocation (requestAtom program sourceFuel head arguments) first).1)
    (∀ key ∈ body.vars, Metta.Bindings.lookupVal incoming key = none) →
    ∃ nextState output cost threshold,
      nextState.world = state.world ∧ ClosedValueBindings output ∧
      LeaRuntimeBindingInvariant output ∧
      ∀ fuel, threshold ≤ fuel →
        interpretFuel environment (fuel + cost) state
          [⟨atomToStack (.expr [.sym "function", body]) [], incoming⟩] [] =
        ([(toLeaTTaAtom (observation (apply program host sourceFuel head arguments)), output)],
          nextState) := by
  refine compiled_public_execution environment _ _
    (invocation_execution program host environment loaded primitives unlisted
      sourceFuel head arguments) ?_
    first rename injective state noExtra noImports incoming stored invariant
  intro first rename
  unfold invoke
  split
  · unfold returnInvocation
    change ∃ items, renBy rename (toLeaTTaAtom (call "chain" [_, _, _])) = .expr items
    simp only [call, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil]
    exact ⟨_, rfl⟩
  · split
    · unfold returnInvocation
      change ∃ items, renBy rename (toLeaTTaAtom (call "chain" [_, _, _])) = .expr items
      simp only [call, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil]
      exact ⟨_, rfl⟩
    · simp only [value, call, returnInvocation, pure, StateT.pure]
      simp only [returned, call, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil]
      exact ⟨_, rfl⟩

/-- The public observation of a generated invocation after the target budget
is sufficient. This concerns the independent interpreter, not source replay.
Private result bindings and the freshening counter are not public observations. -/
def StableReturns (environment : MinEnv) (compiler : Emit Atom) (result : Outcome) : Prop :=
  ∃ threshold, ∀ budget, threshold ≤ budget →
    (interpretFuel environment budget St.init
      [⟨atomToStack (.expr [.sym "function", toLeaTTaAtom (compiler 0).1]) [], []⟩] []).1.map
        Prod.fst = [toLeaTTaAtom (observation result)]

theorem StableReturns.unique {environment : MinEnv} {compiler : Emit Atom}
    {first second : Outcome} (left : StableReturns environment compiler first)
    (right : StableReturns environment compiler second) : first = second := by
  obtain ⟨before, left⟩ := left
  obtain ⟨after, right⟩ := right
  have same := (left (max before after) (Nat.le_max_left _ _)).symm.trans
    (right (max before after) (Nat.le_max_right _ _))
  have atomSame : toLeaTTaAtom (observation first) = toLeaTTaAtom (observation second) :=
    List.cons.inj same |>.1
  exact observation_injective (toLeaTTaAtom_injective atomSame)

/-- Execution preservation for the real public request, at independently
sufficient target fuel. Every source outcome, including exhaustion, is covered. -/
theorem invocation_stable_returns (program : Program) (host : Host) (environment : MinEnv)
    (loaded : LoadedProgram program environment)
    (primitives : NamedPrimitivesExecute host environment)
    (unlisted : ∀ head, head ∉ primitiveHeads → ∀ arguments,
      host.primitive head arguments = .unhandled)
    (sourceFuel : Nat) (head : String) (arguments : List Term) :
    StableReturns environment (returnInvocation (requestAtom program sourceFuel head arguments))
      (apply program host sourceFuel head arguments) := by
  have invariant : LeaRuntimeBindingInvariant ([] : Metta.Bindings) :=
    leaRuntimeBindingInvariant_empty
  have fresh : ∀ key ∈ (renBy id (toLeaTTaAtom
      (returnInvocation (requestAtom program sourceFuel head arguments) 0).1)).vars,
      Metta.Bindings.lookupVal [] key = none := by
    intro key _
    rfl
  obtain ⟨nextState, output, cost, threshold, _, _, _, run⟩ :=
    invocation_public_execution program host environment loaded primitives unlisted
      sourceFuel head arguments 0 id Function.injective_id St.init rfl rfl [] .nil invariant fresh
  refine ⟨threshold + cost, ?_⟩
  intro budget enough
  have ready : threshold ≤ budget - cost := by omega
  have executed := run (budget - cost) ready
  have sameBudget : budget - cost + cost = budget := by omega
  rw [sameBudget] at executed
  have renamed : renBy id (toLeaTTaAtom
      (returnInvocation (requestAtom program sourceFuel head arguments) 0).1) =
      toLeaTTaAtom (returnInvocation (requestAtom program sourceFuel head arguments) 0).1 := by
    exact renBy_id _
  rw [renamed] at executed
  simpa only [List.map_cons, List.map_nil] using
    congrArg (fun execution => execution.1.map Prod.fst) executed

/-- Reflection of stable public outcomes. Arbitrarily small target budgets
remain a separate physical-exhaustion obligation. -/
theorem invocation_stable_iff (program : Program) (host : Host) (environment : MinEnv)
    (loaded : LoadedProgram program environment)
    (primitives : NamedPrimitivesExecute host environment)
    (unlisted : ∀ head, head ∉ primitiveHeads → ∀ arguments,
      host.primitive head arguments = .unhandled)
    (sourceFuel : Nat) (head : String) (arguments : List Term) (result : Outcome) :
    StableReturns environment (returnInvocation (requestAtom program sourceFuel head arguments)) result ↔
      apply program host sourceFuel head arguments = result := by
  have actual := invocation_stable_returns program host environment loaded primitives unlisted
    sourceFuel head arguments
  constructor
  · intro returned
    exact actual.unique returned
  · rintro rfl
    exact actual

/-- The authored MM0 host handles precisely the emitter's finite catalogue.
Unlisted source heads therefore remain data, with no hidden native operation. -/
theorem dataEqualityHost_unlisted (head : String) (absent : head ∉ primitiveHeads)
    (arguments : List Term) : dataEqualityHost.primitive head arguments = .unhandled := by
  simp only [primitiveHeads, List.mem_cons, List.not_mem_nil, or_false, not_or] at absent
  rcases absent with ⟨notZero, notPred, notAdd, notMonus, notMax, notLe, notLt, notEq,
    notMul, notDiv, notMod, notView, notCons, notData⟩
  have notProduct : naturalProduct? head = none := by
    unfold naturalProduct?
    split <;> simp_all
  have notBinary : naturalBinary? head = none := by
    unfold naturalBinary?
    split <;> simp_all
  rw [dataEqualityHost_prior head arguments notData,
    productDivisionHost_prior head arguments notProduct]
  exact computationalHost_unhandled head arguments notView notCons notBinary notZero notPred

end Execution
end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
