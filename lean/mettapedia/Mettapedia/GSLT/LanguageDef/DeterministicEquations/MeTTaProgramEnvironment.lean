import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaDispatcherExecution
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaNameEncoding
import MettaHyperonFull.Proofs.IndexingComplete
import Mettapedia.Util.LinearHash

/-!
# Loading emitted computational programs

The actual stateful emitter contributes one indexed equation per source head.
Loading its annotations and equations into the independent interpreter selects
that equation, without native or embedded-instruction interception. The result
composes with call entry and preserves the source-selected body. Execution of
that body is a separate obligation.
-/

set_option autoImplicit false
namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Metta.Minimal
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.LeaTTaSpecConformance
open Mettapedia.Languages.MeTTa.HE.CanonAbsorbsFreshening
open Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlExecution
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge

private theorem dispatcher_annotation (program : Program) (head : String) (first : Nat) :
    (dispatcher program head first).1.1 =
      call ":" [.symbol (dispatchName head),
        call "->" [.symbol "Number", .symbol "Atom", .symbol "%Undefined%"]] := rfl

private theorem dispatcher_batch (program : Program) (heads : List String) (first : Nat) :
    List.Forall₂ (fun head pair => ∃ start, pair = (dispatcher program head start).1)
      heads ((heads.mapM (dispatcher program)).run first).1 := by
  induction heads generalizing first with
  | nil => exact .nil
  | cons head heads ih =>
    rcases he : dispatcher program head first with ⟨pair, next⟩
    rcases ht : heads.mapM (dispatcher program) next with ⟨pairs, last⟩
    have tail := ih next
    simp only [StateT.run, ht] at tail
    have one : ∃ start, pair = (dispatcher program head start).1 := ⟨first, by rw [he]⟩
    simpa only [List.mapM_cons, StateT.run, bind, StateT.bind, pure, StateT.pure,
      he, ht] using List.Forall₂.cons one tail

private theorem emitted_dispatcher_rules (program : Program) (head : String) (first : Nat) :
    ∃ body,
      (dispatcher program head first).1.2 = call "="
        [call (dispatchName head) [.var (freshName first), .var (freshName (first + 1))],
          call "function" [body]] ∧
      extractRules [toLeaTTaAtom (dispatcher program head first).1.1,
          toLeaTTaAtom (dispatcher program head first).1.2] =
        [(toLeaTTaAtom (call (dispatchName head)
            [.var (freshName first), .var (freshName (first + 1))]),
          toLeaTTaAtom (call "function" [body]))] := by
  obtain ⟨body, rule⟩ := dispatcher_input_interface program head first
  refine ⟨body, rule, ?_⟩
  rw [dispatcher_annotation, rule]
  simp [extractRules, call, toLeaTTaAtom, toLeaTTaAtoms]

private theorem batch_no_headless (program : Program)
    {heads : List String} {pairs : List (Atom × Atom)}
    (generated : List.Forall₂
      (fun head pair => ∃ first, pair = (dispatcher program head first).1) heads pairs) :
    (extractRules (pairs.flatMap fun pair => [toLeaTTaAtom pair.1, toLeaTTaAtom pair.2])).filter
      (fun rule => (headKey rule.1).isNone) = [] := by
  induction generated with
  | nil => rfl
  | @cons head pair heads pairs generated related ih =>
    obtain ⟨first, rfl⟩ := generated
    obtain ⟨body, _, rules⟩ := emitted_dispatcher_rules program head first
    simp only [List.flatMap_cons, extractRules, List.filterMap_append, List.filter_append]
      at rules ⊢
    rw [rules]
    simpa only [extractRules, List.filter_cons, List.filter_nil, call, toLeaTTaAtom, toLeaTTaAtoms,
      headKey, Option.isNone_some, Bool.false_eq_true, if_false, List.nil_append] using ih

private theorem batch_filter_absent (program : Program)
    {heads : List String} {pairs : List (Atom × Atom)}
    (generated : List.Forall₂
      (fun head pair => ∃ first, pair = (dispatcher program head first).1) heads pairs)
    (key : String) (absent : ∀ head ∈ heads, dispatchName head ≠ key) :
    (extractRules (pairs.flatMap fun pair => [toLeaTTaAtom pair.1, toLeaTTaAtom pair.2])).filter
      (fun rule => headKey rule.1 == some key) = [] := by
  induction generated with
  | nil => rfl
  | @cons head pair heads pairs generated related ih =>
    obtain ⟨first, rfl⟩ := generated
    obtain ⟨body, _, rules⟩ := emitted_dispatcher_rules program head first
    have different := absent head (by simp)
    have emptyTail := ih (fun other member => absent other (by simp [member]))
    simp only [List.flatMap_cons, extractRules, List.filterMap_append, List.filter_append]
      at rules ⊢
    rw [rules]
    simpa only [extractRules, List.filter_cons, List.filter_nil, call, toLeaTTaAtom, toLeaTTaAtoms,
      headKey, beq_iff_eq, Option.some.injEq, different, if_false, List.nil_append] using emptyTail

private theorem batch_filter_present (program : Program)
    {heads : List String} {pairs : List (Atom × Atom)}
    (generated : List.Forall₂
      (fun head pair => ∃ first, pair = (dispatcher program head first).1) heads pairs)
    (distinct : heads.Nodup) (target : String) (present : target ∈ heads)
    (unique : ∀ head ∈ heads, dispatchName head = dispatchName target → head = target) :
    ∃ first body,
      (dispatcher program target first).1.2 = call "="
        [call (dispatchName target) [.var (freshName first), .var (freshName (first + 1))],
          call "function" [body]] ∧
      (extractRules (pairs.flatMap fun pair => [toLeaTTaAtom pair.1, toLeaTTaAtom pair.2])).filter
        (fun rule => headKey rule.1 == some (dispatchName target)) =
        [(toLeaTTaAtom (call (dispatchName target)
            [.var (freshName first), .var (freshName (first + 1))]),
          toLeaTTaAtom (call "function" [body]))] := by
  induction generated with
  | nil => simp at present
  | @cons head pair heads pairs generated related ih =>
    obtain ⟨first, rfl⟩ := generated
    obtain ⟨body, rule, rules⟩ := emitted_dispatcher_rules program head first
    obtain ⟨headAbsent, tailDistinct⟩ := List.nodup_cons.mp distinct
    by_cases same : head = target
    · subst head
      have tailEmpty := batch_filter_absent program related (dispatchName target)
        (fun other member equal => headAbsent ((unique other (by simp [member]) equal) ▸ member))
      refine ⟨first, body, rule, ?_⟩
      simp only [List.flatMap_cons, extractRules, List.filterMap_append, List.filter_append]
        at rules tailEmpty ⊢
      rw [rules, tailEmpty]
      simp [call, toLeaTTaAtom, toLeaTTaAtoms, headKey]
    · have headDifferent : dispatchName head ≠ dispatchName target :=
        fun equal => same (unique head (by simp) equal)
      have inTail : target ∈ heads := (List.mem_cons.mp present).resolve_left
        (fun equal => same equal.symm)
      obtain ⟨start, targetBody, targetRule, found⟩ := ih tailDistinct inTail
        (fun other member => unique other (by simp [member]))
      refine ⟨start, targetBody, targetRule, ?_⟩
      simp only [List.flatMap_cons, extractRules, List.filterMap_append, List.filter_append]
        at rules found ⊢
      rw [rules]
      simpa only [List.filter_cons, List.filter_nil, call, toLeaTTaAtom, toLeaTTaAtoms,
        headKey, beq_iff_eq, Option.some.injEq, headDifferent, if_false, List.nil_append] using found

/-- Loading the actual emitted program exposes exactly its generated equation
for each source head. The finite name-separation condition concerns only the
compiler's symbol encoding; no runtime match or evaluation is assumed. -/
theorem programAtoms_candidates (program : Program) (head : String)
    (present : head ∈ program.map Equation.head)
    (unique : ∀ other ∈ program.map Equation.head,
      dispatchName other = dispatchName head → other = head)
    (arguments : List Atom) (groundings : Metta.GroundingTable) :
    ∃ first body,
      (dispatcher program head first).1.2 = call "="
        [call (dispatchName head) [.var (freshName first), .var (freshName (first + 1))],
          call "function" [body]] ∧
      (MinEnv.ofAtomsGT
        ((programAtoms program).flatMap fun pair => [toLeaTTaAtom pair.1, toLeaTTaAtom pair.2])
        groundings).candidates (toLeaTTaAtom (call (dispatchName head) arguments)) =
        [(toLeaTTaAtom (call (dispatchName head)
            [.var (freshName first), .var (freshName (first + 1))]),
          toLeaTTaAtom (call "function" [body]))] := by
  let heads := (program.map Equation.head).eraseDups
  have generated : List.Forall₂
      (fun label pair => ∃ first, pair = (dispatcher program label first).1)
      heads (programAtoms program) := dispatcher_batch program heads 0
  obtain ⟨first, body, rule, found⟩ := batch_filter_present program generated
    (Mettapedia.Util.LinearHash.eraseDups_nodup _) head (by simpa only [heads, List.mem_eraseDups] using present)
    (fun other member => unique other (by simpa only [heads, List.mem_eraseDups] using member))
  refine ⟨first, body, rule, ?_⟩
  have keyed : headKey (toLeaTTaAtom (call (dispatchName head) arguments)) =
      some (dispatchName head) := by simp [call, toLeaTTaAtom, toLeaTTaAtoms, headKey]
  simp only [MinEnv.candidates, keyed, Metta.ruleIndex_getD, Metta.ofAtomsGT_varRules]
  rw [batch_no_headless program generated, List.append_nil]
  exact found

/-- Generated dispatchers use a reserved compiler prefix, independently of
source names and supplied arguments. -/
private theorem dispatchName_not_reserved (head reserved : String)
    (different : reserved.toList.take 4 ≠ ['n', 'i', 'k', ':']) :
    dispatchName head ≠ reserved := by
  have marked : (dispatchName head).toList.take 4 = ['n', 'i', 'k', ':'] := by
    unfold dispatchName
    rw [String.toList_append]
    rfl
  intro equal
  have observed := congrArg (fun name : String => name.toList.take 4) equal
  rw [marked] at observed
  exact different observed.symm

/-- A generated dispatcher is never intercepted by a built-in native operation. -/
theorem dispatchName_native_miss (head : String) (arguments : List Metta.Atom) :
    Metta.callGrounded Metta.Builtins.table (dispatchName head) arguments = .noReduce := by
  have different : ∀ builtin ∈ Metta.Builtins.table, builtin.name ≠ dispatchName head := by
    simp only [Metta.Builtins.table, Metta.Builtins.mathTable, List.forall_mem_append,
      List.forall_mem_cons]
    repeat' constructor
    all_goals first
      | solve | simp
      | apply Ne.symm; apply dispatchName_not_reserved; decide
  have absent : Metta.GroundingTable.lookup Metta.Builtins.table (dispatchName head) = none := by
    unfold Metta.GroundingTable.lookup
    apply List.find?_eq_none.mpr
    intro builtin member
    simpa only [beq_iff_eq] using different builtin member
  simp only [Metta.callGrounded, absent]

/-- Generated dispatcher calls are ordinary queries, not embedded instructions. -/
theorem dispatchName_not_embedded (head : String) (arguments : List Atom) :
    isEmbeddedOp (toLeaTTaAtom (call (dispatchName head) arguments)) = false := by
  simp only [call, toLeaTTaAtom, toLeaTTaAtoms, isEmbeddedOp,
    List.contains_cons, List.contains_nil, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  repeat' constructor
  all_goals
    apply dispatchName_not_reserved
    decide

/-- With no dynamically added rules, loading the emitted declarations yields
that same singleton candidate in every world and at every fresh-name counter. -/
theorem programAtoms_candidates_world (program : Program) (head : String)
    (present : head ∈ program.map Equation.head)
    (unique : ∀ other ∈ program.map Equation.head,
      dispatchName other = dispatchName head → other = head)
    (arguments : List Atom) (groundings : Metta.GroundingTable) (world : Metta.Minimal.World)
    (noExtra : world.selfExtra = []) (noImports : world.selfImports = []) :
    ∃ first body,
      (dispatcher program head first).1.2 = call "="
        [call (dispatchName head) [.var (freshName first), .var (freshName (first + 1))],
          call "function" [body]] ∧
      candidatesW (MinEnv.ofAtomsGT
        ((programAtoms program).flatMap fun pair => [toLeaTTaAtom pair.1, toLeaTTaAtom pair.2])
        groundings) world (toLeaTTaAtom (call (dispatchName head) arguments)) =
        [(toLeaTTaAtom (call (dispatchName head)
            [.var (freshName first), .var (freshName (first + 1))]),
          toLeaTTaAtom (call "function" [body]))] := by
  obtain ⟨first, body, rule, loaded⟩ :=
    programAtoms_candidates program head present unique arguments groundings
  exact ⟨first, body, rule, by simpa only [candidatesW, noExtra, noImports, List.nil_append,
    List.filterMap_nil, List.append_nil] using loaded⟩

/-- Loader obligations for generated calls. They concern only indexed rule
selection and native dispatch; they do not assume any call's result. Auxiliary
library equations may coexist with the generated dispatchers. -/
structure LoadedProgram (program : Program) (environment : MinEnv) : Prop where
  groundings : environment.gt = Metta.Builtins.table
  dispatch : ∀ head ∈ program.map Equation.head,
    ∀ (sourceFuel : Nat) (arguments : List Term) (world : Metta.Minimal.World),
    world.selfExtra = [] → world.selfImports = [] →
    ∃ first body,
      (dispatcher program head first).1.2 = call "="
        [call (dispatchName head) [.var (freshName first), .var (freshName (first + 1))],
          call "function" [body]] ∧
      candidatesW environment world (toLeaTTaAtom (call (dispatchName head)
        [.grounded (.int sourceFuel), MeTTaData.encodeItems arguments])) =
        [(toLeaTTaAtom (call (dispatchName head)
            [.var (freshName first), .var (freshName (first + 1))]),
          toLeaTTaAtom (call "function" [body]))]

/-- Loading additional equations preserves each generated dispatcher when
those equations have explicit heads disjoint from the compiler's names.
This is an indexing law, independent of the auxiliary library's computations. -/
theorem programAtoms_loaded (program : Program)
    (library : List Metta.Atom)
    (noHeadless : (extractRules library).filter (fun rule => (headKey rule.1).isNone) = [])
    (disjoint : ∀ head ∈ program.map Equation.head,
      (extractRules library).filter (fun rule => headKey rule.1 == some (dispatchName head)) = []) :
    LoadedProgram program (MinEnv.ofAtomsGT
      (((programAtoms program).flatMap fun pair => [toLeaTTaAtom pair.1, toLeaTTaAtom pair.2]) ++
        library) Metta.Builtins.table) where
  groundings := rfl
  dispatch head present sourceFuel arguments world noExtra noImports := by
    obtain ⟨first, body, emitted, loaded⟩ := programAtoms_candidates program head present
      (fun _ _ equal => dispatchName_injective equal)
      [.grounded (.int sourceFuel), MeTTaData.encodeItems arguments]
      Metta.Builtins.table
    refine ⟨first, body, emitted, ?_⟩
    have keyed : headKey (toLeaTTaAtom (call (dispatchName head)
        [.grounded (.int sourceFuel), MeTTaData.encodeItems arguments])) =
        some (dispatchName head) := by simp [call, toLeaTTaAtom, toLeaTTaAtoms, headKey]
    simp only [MinEnv.candidates, keyed, Metta.ruleIndex_getD, Metta.ofAtomsGT_varRules] at loaded
    simp only [candidatesW, noExtra, noImports, List.filterMap_nil,
      List.append_nil, MinEnv.candidates, keyed, Metta.ruleIndex_getD,
      Metta.ofAtomsGT_varRules, extractRules, List.filterMap_append, List.filter_append]
    simp only [extractRules] at noHeadless
    have unrelated := disjoint head present
    simp only [extractRules] at unrelated
    rw [noHeadless, unrelated]
    simpa only [extractRules, List.append_nil] using loaded

/-- The actual emitted program enters its source-selected body. The runtime
index, native dispatch and embedded-instruction premises are discharged from
the loader and generated names; the world contains no added rules. -/
theorem programAtoms_selection (program : Program) (head : String)
    (present : head ∈ program.map Equation.head)
    (unique : ∀ other ∈ program.map Equation.head,
      dispatchName other = dispatchName head → other = head)
    (sourceFuel : Nat) (arguments : List Term) (row : OrderedDispatch.CaseRow)
    (sourceBindings : Env)
    (selected : OrderedDispatch.selectCase (OrderedDispatch.compileHead program head)
      arguments = some (row, sourceBindings))
    (state : St) (noExtra : state.world.selfExtra = [])
    (noImports : state.world.selfImports = []) (previous : Stack)
    (incoming : Metta.Bindings)
    (stored : ClosedValueBindings incoming)
    (invariant : LeaRuntimeBindingInvariant incoming) :
    let environment := MinEnv.ofAtomsGT
      ((programAtoms program).flatMap fun pair => [toLeaTTaAtom pair.1, toLeaTTaAtom pair.2])
      Metta.Builtins.table
    let query := toLeaTTaAtom (call (dispatchName head)
      [.grounded (.int sourceFuel), MeTTaData.encodeItems arguments])
    ∃ first rawBody, ∃ rename : String → String, ∃ headerBindings output skipped start body,
      (dispatcher program head first).1.2 = call "="
        [call (dispatchName head) [.var (freshName first), .var (freshName (first + 1))],
          call "function" [rawBody]] ∧
      Function.Injective rename ∧
      AlphaRenameAtomRel rename
        (expression program (patterns row.equation.params start).1.2
          (.grounded (.int sourceFuel)) row.equation.body
          (patterns row.equation.params start).2).1 body ∧
      ClosedValueBindings output ∧
      LeaRuntimeBindingInvariant output ∧
      ValuationFor
        (leaClassSolution output ∘ rename)
        start sourceBindings ∧
      Metta.instantiate output (toLeaTTaAtom body) = renBy rename (toLeaTTaAtom
        (expression program (sourceBindings.map (fun entry =>
          (entry.1, MeTTaData.encode entry.2))) (.grounded (.int sourceFuel))
          row.equation.body (patterns row.equation.params start).2).1) ∧
      (∀ name ∈ liveStackVars previous,
        Metta.Bindings.lookupVal incoming name = none →
          Metta.Bindings.lookupVal output name = none) ∧
      (∀ name ∈ (Metta.instantiate output (toLeaTTaAtom body)).vars,
        name ∉ liveStackVars previous) ∧
      let fresh := freshenRuleAvoiding state.counter
        (Metta.Minimal.queryOpAvoid previous query incoming)
        (toLeaTTaAtom (call (dispatchName head)
          [.var (freshName first), .var (freshName (first + 1))]))
        (toLeaTTaAtom (call "function" [rawBody]))
      let function := Metta.instantiate headerBindings fresh.1.2
      let parent : Frame := { atom := function, ret := .function, vars := varsCopy previous }
      ∀ fuel rest done,
        interpretFuel environment (fuel + 5 + 2 * skipped) state
          (⟨atomToStack (.expr [.sym "eval", query]) previous, incoming⟩ :: rest) done =
        interpretFuel environment fuel { state with counter := fresh.2 }
          (finItem (parent :: previous) (Metta.instantiate output (toLeaTTaAtom body)) output :: rest) done := by
  intro environment query
  obtain ⟨first, rawBody, emitted, loaded⟩ := programAtoms_candidates_world program head
    present unique [.grounded (.int sourceFuel), MeTTaData.encodeItems arguments]
    Metta.Builtins.table state.world noExtra noImports
  refine ⟨first, ?_⟩
  apply loaded_dispatcher_selection program head first sourceFuel arguments row sourceBindings
    selected environment state previous incoming stored invariant
  · exact dispatchName_native_miss _ _
  · exact dispatchName_not_embedded _ _
  · intro otherBody otherEmitted
    have same : otherBody = rawBody := by
      simpa only [call, Atom.expression.injEq, List.cons.injEq, true_and, and_true]
        using otherEmitted.symm.trans emitted
    rw [same]
    exact loaded

/-- A loaded request enters the actual compiled body with its source inputs
already filled. Every remaining variable is private to that body. The
enclosing dispatcher frame, caller and scheduler state remain explicit. -/
theorem loaded_dispatcher_enters_body (program : Program) (head : String)
    (first sourceFuel : Nat) (arguments : List Term) (row : OrderedDispatch.CaseRow)
    (sourceBindings : Env)
    (selected : OrderedDispatch.selectCase (OrderedDispatch.compileHead program head)
      arguments = some (row, sourceBindings))
    (rawBody : Atom)
    (emitted : (dispatcher program head first).1.2 = call "="
      [call (dispatchName head) [.var (freshName first), .var (freshName (first + 1))],
        call "function" [rawBody]])
    (environment : MinEnv) (state : St) (previous : Stack)
    (incoming : Metta.Bindings) (stored : ClosedValueBindings incoming)
    (invariant : LeaRuntimeBindingInvariant incoming)
    (nativeMiss : Metta.callGrounded environment.gt (dispatchName head)
      ([toLeaTTaAtom (.grounded (.int sourceFuel)),
        toLeaTTaAtom (MeTTaData.encodeItems arguments)].map
          (fun atom => resolveStates state.world (subTokens state.world atom))) = .noReduce)
    (notEmbedded : isEmbeddedOp (toLeaTTaAtom (call (dispatchName head)
      [.grounded (.int sourceFuel), MeTTaData.encodeItems arguments])) = false)
    (loaded : candidatesW environment state.world (toLeaTTaAtom (call (dispatchName head)
      [.grounded (.int sourceFuel), MeTTaData.encodeItems arguments])) =
      [(toLeaTTaAtom (call (dispatchName head)
          [.var (freshName first), .var (freshName (first + 1))]),
        toLeaTTaAtom (call "function" [rawBody]))]) :
    let query := toLeaTTaAtom (call (dispatchName head)
      [.grounded (.int sourceFuel), MeTTaData.encodeItems arguments])
    ∃ rename : String → String, ∃ start counter skipped parentBody output,
      Function.Injective rename ∧ ClosedValueBindings output ∧ LeaRuntimeBindingInvariant output ∧
      let body := renBy rename (toLeaTTaAtom
        (expression program (sourceBindings.map (fun entry =>
          (entry.1, MeTTaData.encode entry.2))) (.grounded (.int sourceFuel))
          row.equation.body (patterns row.equation.params start).2).1)
      let parent : Frame := { atom := parentBody, ret := .function, vars := varsCopy previous }
      (∀ name ∈ body.vars, name ∉ output.vars) ∧
      (∀ name ∈ body.vars, name ∉ liveStackVars previous) ∧
      (∀ name ∈ liveStackVars previous, Metta.Bindings.lookupVal incoming name = none →
        Metta.Bindings.lookupVal output name = none) ∧
      ∀ fuel rest done,
        interpretFuel environment (fuel + 6 + 2 * skipped) state
          (⟨atomToStack (.expr [.sym "eval", query]) previous, incoming⟩ :: rest) done =
        interpretFuel environment fuel { state with counter := counter }
          (⟨atomToStack body (parent :: previous), output⟩ :: rest) done := by
  intro query
  obtain ⟨selectedBody, rename, headerBindings, output, skipped, start, rawSelected,
      _, injective, _, outputClosed, outputInvariant, _, materialized, callerPreserved, bodyPrivate, entry⟩ :=
    loaded_dispatcher_selection program head first sourceFuel arguments row sourceBindings
      selected environment state previous incoming stored invariant nativeMiss notEmbedded (by
        intro otherBody otherEmitted
        have same : otherBody = rawBody := by
          simpa only [call, Atom.expression.injEq, List.cons.injEq, true_and, and_true]
            using otherEmitted.symm.trans emitted
        rw [same]
        exact loaded)
  let fresh := freshenRuleAvoiding state.counter
    (Metta.Minimal.queryOpAvoid previous query incoming)
    (toLeaTTaAtom (call (dispatchName head)
      [.var (freshName first), .var (freshName (first + 1))]))
    (toLeaTTaAtom (call "function" [selectedBody]))
  let parentBody := Metta.instantiate headerBindings fresh.1.2
  refine ⟨rename, start, fresh.2, skipped, parentBody, output, injective,
    outputClosed, outputInvariant, ?_⟩
  intro body parent
  change Metta.instantiate output (toLeaTTaAtom rawSelected) = body at materialized
  have fixed : Metta.instantiate output body = body := by
    rw [← materialized, instantiate_closed_value_bindings_idempotent outputClosed]
  rw [materialized] at bodyPrivate
  refine ⟨fixed_closed_bindings_private output outputClosed body fixed,
    bodyPrivate, callerPreserved, ?_⟩
  intro fuel rest done
  have selectedBody := entry (fuel + 1) rest done
  change interpretFuel environment _ state _ done =
    interpretFuel environment (fuel + 1) { state with counter := fresh.2 }
      (finItem (parent :: previous) (Metta.instantiate output (toLeaTTaAtom rawSelected))
        output :: rest) done at selectedBody
  rw [materialized] at selectedBody
  have enters := function_embedded_enters environment { state with counter := fresh.2 }
    output parentBody body (varsCopy previous) previous fuel rest done
    (by rw [fixed]; exact expression_runtime_embedded _ _ _ _ _ _)
  rw [fixed] at enters
  simpa only [show fuel + 1 + 5 + 2 * skipped = fuel + 6 + 2 * skipped by omega]
    using selectedBody.trans enters

/-- The emitted-program-only loader is an instance of the same entry law.
The general law also supports additional, separately qualified primitive
equations without changing guest dispatch. -/
theorem programAtoms_enters_body (program : Program) (head : String)
    (present : head ∈ program.map Equation.head)
    (unique : ∀ other ∈ program.map Equation.head,
      dispatchName other = dispatchName head → other = head)
    (sourceFuel : Nat) (arguments : List Term) (row : OrderedDispatch.CaseRow)
    (sourceBindings : Env)
    (selected : OrderedDispatch.selectCase (OrderedDispatch.compileHead program head)
      arguments = some (row, sourceBindings))
    (state : St) (noExtra : state.world.selfExtra = [])
    (noImports : state.world.selfImports = []) (previous : Stack)
    (incoming : Metta.Bindings) (stored : ClosedValueBindings incoming)
    (invariant : LeaRuntimeBindingInvariant incoming) :
    let environment := MinEnv.ofAtomsGT
      ((programAtoms program).flatMap fun pair => [toLeaTTaAtom pair.1, toLeaTTaAtom pair.2])
      Metta.Builtins.table
    let query := toLeaTTaAtom (call (dispatchName head)
      [.grounded (.int sourceFuel), MeTTaData.encodeItems arguments])
    ∃ rename : String → String, ∃ start counter skipped parentBody output,
      Function.Injective rename ∧ ClosedValueBindings output ∧ LeaRuntimeBindingInvariant output ∧
      let body := renBy rename (toLeaTTaAtom
        (expression program (sourceBindings.map (fun entry =>
          (entry.1, MeTTaData.encode entry.2))) (.grounded (.int sourceFuel))
          row.equation.body (patterns row.equation.params start).2).1)
      let parent : Frame := { atom := parentBody, ret := .function, vars := varsCopy previous }
      (∀ name ∈ body.vars, name ∉ output.vars) ∧
      (∀ name ∈ body.vars, name ∉ liveStackVars previous) ∧
      (∀ name ∈ liveStackVars previous, Metta.Bindings.lookupVal incoming name = none →
        Metta.Bindings.lookupVal output name = none) ∧
      ∀ fuel rest done,
        interpretFuel environment (fuel + 6 + 2 * skipped) state
          (⟨atomToStack (.expr [.sym "eval", query]) previous, incoming⟩ :: rest) done =
        interpretFuel environment fuel { state with counter := counter }
          (⟨atomToStack body (parent :: previous), output⟩ :: rest) done := by
  intro environment query
  obtain ⟨first, rawBody, emitted, loaded⟩ := programAtoms_candidates_world program head
    present unique [.grounded (.int sourceFuel), MeTTaData.encodeItems arguments]
    Metta.Builtins.table state.world noExtra noImports
  exact loaded_dispatcher_enters_body program head first sourceFuel arguments row sourceBindings
    selected rawBody emitted environment state previous incoming stored invariant
    (dispatchName_native_miss _ _) (dispatchName_not_embedded _ _) loaded

@[simp] theorem sequenceAtom_encode (terms : List Term) :
    sequenceAtom (terms.map MeTTaData.encode) = MeTTaData.encodeItems terms := by
  induction terms with
  | nil => rfl
  | cons term rest ih => simp [sequenceAtom, MeTTaData.encodeItems, call, ih]

/-- A selected public request with no source budget returns exhaustion,
without executing the selected computation. -/
theorem programAtoms_zero_source_fuel (program : Program) (head : String)
    (present : head ∈ program.map Equation.head)
    (unique : ∀ other ∈ program.map Equation.head,
      dispatchName other = dispatchName head → other = head)
    (arguments : List Term) (row : OrderedDispatch.CaseRow) (sourceBindings : Env)
    (selected : OrderedDispatch.selectCase (OrderedDispatch.compileHead program head)
      arguments = some (row, sourceBindings))
    (state : St) (noExtra : state.world.selfExtra = [])
    (noImports : state.world.selfImports = [])
    (incoming : Metta.Bindings) (stored : ClosedValueBindings incoming)
    (invariant : LeaRuntimeBindingInvariant incoming) :
    let environment := MinEnv.ofAtomsGT
      ((programAtoms program).flatMap fun pair => [toLeaTTaAtom pair.1, toLeaTTaAtom pair.2])
      Metta.Builtins.table
    let query := toLeaTTaAtom (requestAtom program 0 head arguments)
    ∃ counter skipped output, ClosedValueBindings output ∧ LeaRuntimeBindingInvariant output ∧
      ∀ fuel,
        interpretFuel environment (fuel + 11 + 2 * skipped) state
          [⟨atomToStack (.expr [.sym "eval", query]) [], incoming⟩] [] =
        ([(.sym "nik:Exhausted", output)], { state with counter := counter }) := by
  intro environment query
  obtain ⟨rename, start, counter, skipped, parentBody, output, _, storedOutput, invariantOutput,
      _, _, _, enters⟩ := programAtoms_enters_body program head present unique 0 arguments row
    sourceBindings selected state noExtra noImports [] incoming stored invariant
  refine ⟨counter, skipped, output, storedOutput, invariantOutput, ?_⟩
  intro fuel
  have body := enters (fuel + 5) [] []
  simp only [varsCopy, Nat.cast_zero] at body
  have done := selected_closed_return_finishes environment { state with counter := counter }
    output parentBody (.sym "nik:Exhausted") [] fuel (by simp [Metta.Atom.vars]) (by decide)
  have completed := body.trans (by
    rw [expression, show fuel + 5 = fuel + 1 + 4 by omega,
      renamed_withFuel_zero_enters_handler environment { state with counter := counter }
        output rename _ (patterns row.equation.params start).2 (fuel + 1) parentBody [] [] [] []
        rfl storedOutput.hasLoop_false])
  have defined : program.defines head := by simpa [Program.defines] using present
  simpa only [query, requestAtom, invoke, defined, if_true, sequenceAtom_encode,
    Nat.cast_zero, show fuel + 5 + 6 + 2 * skipped = fuel + 11 + 2 * skipped by omega]
    using completed.trans done

/-- End-to-end execution of a selected variable body, including missing-input
refusal. This uses the emitted loader, query, matcher and public return. -/
theorem programAtoms_variable_execution (program : Program) (head name : String)
    (present : head ∈ program.map Equation.head)
    (unique : ∀ other ∈ program.map Equation.head,
      dispatchName other = dispatchName head → other = head)
    (sourceFuel : Nat) (arguments : List Term) (row : OrderedDispatch.CaseRow)
    (sourceBindings : Env)
    (selected : OrderedDispatch.selectCase (OrderedDispatch.compileHead program head)
      arguments = some (row, sourceBindings)) (variableBody : row.equation.body = .var name)
    (state : St) (noExtra : state.world.selfExtra = [])
    (noImports : state.world.selfImports = [])
    (incoming : Metta.Bindings) (stored : ClosedValueBindings incoming)
    (invariant : LeaRuntimeBindingInvariant incoming) :
    let environment := MinEnv.ofAtomsGT
      ((programAtoms program).flatMap fun pair => [toLeaTTaAtom pair.1, toLeaTTaAtom pair.2])
      Metta.Builtins.table
    let query := toLeaTTaAtom (requestAtom program (sourceFuel + 1) head arguments)
    let result := ((sourceBindings.lookup name).map fun term => value (MeTTaData.encode term)).getD
      (.symbol "nik:Failure")
    ∃ counter skipped output, ClosedValueBindings output ∧ LeaRuntimeBindingInvariant output ∧
      ∀ fuel,
        interpretFuel environment (fuel + 16 + 2 * skipped) state
          [⟨atomToStack (.expr [.sym "eval", query]) [], incoming⟩] [] =
        ([(toLeaTTaAtom result, output)], { state with counter := counter }) := by
  intro environment query result
  obtain ⟨rename, start, counter, skipped, parentBody, output, injective, storedOutput,
      invariantOutput, privateNames, _, _, enters⟩ := programAtoms_enters_body program head present
    unique (sourceFuel + 1) arguments row sourceBindings selected state noExtra noImports []
      incoming stored invariant
  refine ⟨counter, skipped, output, storedOutput, invariantOutput, ?_⟩
  intro fuel
  have body := enters (fuel + 10) [] []
  rw [variableBody] at body privateNames
  have variableRun := expression_encoded_variable_enters_handler program sourceBindings name
    (patterns row.equation.params start).2 sourceFuel (fuel + 1) rename injective
    environment { state with counter := counter } output storedOutput parentBody [] [] [] []
    rfl privateNames
  have closed : (toLeaTTaAtom result).vars = [] := by
    cases found : sourceBindings.lookup name with
    | none => simp [result, found, toLeaTTaAtom, Metta.Atom.vars]
    | some term => simp [result, found, value, call, toLeaTTaAtom, toLeaTTaAtoms,
        Metta.Atom.vars, data_atom_runtime_closed (MeTTaData.encode_data term)]
  have visible : (toLeaTTaAtom result != emptyA) = true := by
    cases found : sourceBindings.lookup name <;>
      simp only [result, found, Option.map_none, Option.getD_none, Option.map_some,
        Option.getD_some, value, call, toLeaTTaAtom, toLeaTTaAtoms, emptyA] <;> rfl
  have done := selected_closed_return_finishes environment { state with counter := counter }
    output parentBody (toLeaTTaAtom result) [] fuel closed visible
  have defined : program.defines head := by simpa [Program.defines] using present
  simpa only [query, requestAtom, invoke, defined, if_true, sequenceAtom_encode,
    show fuel + 10 + 6 + 2 * skipped = fuel + 16 + 2 * skipped by omega,
    show fuel + 10 = fuel + 1 + 9 by omega] using body.trans (variableRun.trans done)

/-- A declared head with no matching row returns logical failure through the
actual public request path, including at zero source fuel. No row body runs. -/
theorem programAtoms_refused_execution (program : Program) (head : String)
    (present : head ∈ program.map Equation.head)
    (unique : ∀ other ∈ program.map Equation.head,
      dispatchName other = dispatchName head → other = head)
    (sourceFuel : Nat) (arguments : List Term)
    (refused : OrderedDispatch.selectCase (OrderedDispatch.compileHead program head)
      arguments = none)
    (state : St) (noExtra : state.world.selfExtra = [])
    (noImports : state.world.selfImports = [])
    (incoming : Metta.Bindings) (stored : ClosedValueBindings incoming)
    (invariant : LeaRuntimeBindingInvariant incoming) :
    let environment := MinEnv.ofAtomsGT
      ((programAtoms program).flatMap fun pair => [toLeaTTaAtom pair.1, toLeaTTaAtom pair.2])
      Metta.Builtins.table
    let query := toLeaTTaAtom (requestAtom program sourceFuel head arguments)
    ∃ counter cost output, ClosedValueBindings output ∧ ∀ fuel,
      interpretFuel environment (fuel + cost) state
        [⟨atomToStack (.expr [.sym "eval", query]) [], incoming⟩] [] =
      ([(.sym "nik:Failure", output)], { state with counter := counter }) := by
  intro environment query
  obtain ⟨first, rawBody, emitted, loaded⟩ := programAtoms_candidates_world program head
    present unique [.grounded (.int sourceFuel), MeTTaData.encodeItems arguments]
    Metta.Builtins.table state.world noExtra noImports
  obtain ⟨refusalBody, refusalEmitted, refuses⟩ := dispatcher_refused_execution program head
    first sourceFuel state.counter arguments refused environment [] incoming stored invariant
  have same : refusalBody = rawBody := by
    simpa only [call, Atom.expression.injEq, List.cons.injEq, true_and, and_true]
      using refusalEmitted.symm.trans emitted
  subst refusalBody
  obtain ⟨matched, output, matching, merging, outputClosed, enters⟩ := loaded_dispatcher_entry
    program head first sourceFuel arguments rawBody emitted environment state [] incoming
      stored (dispatchName_native_miss _ _) (dispatchName_not_embedded _ _) loaded
  obtain ⟨scanCost, scanning⟩ := refuses matched output matching merging
  let lhs := toLeaTTaAtom (call (dispatchName head)
    [.var (freshName first), .var (freshName (first + 1))])
  let rawQuery := toLeaTTaAtom (call (dispatchName head)
    [.grounded (.int sourceFuel), MeTTaData.encodeItems arguments])
  let fresh := freshenRuleAvoiding state.counter
    (Metta.Minimal.queryOpAvoid [] rawQuery incoming) lhs
    (toLeaTTaAtom (call "function" [rawBody]))
  refine ⟨fresh.2, scanCost + 2, output, outputClosed, ?_⟩
  intro fuel
  have entry := enters (fuel + 1 + scanCost) [] []
  have scanned := scanning { state with counter := fresh.2 } (fuel + 1) [] []
  have finished := selected_closed_return_finishes environment { state with counter := fresh.2 }
    output (Metta.instantiate output fresh.1.2) (.sym "nik:Failure") [] fuel
    (by simp [Metta.Atom.vars]) (by decide)
  have defined : program.defines head := by simpa [Program.defines] using present
  simpa only [query, requestAtom, invoke, defined, if_true, sequenceAtom_encode,
    show fuel + 1 + scanCost + 1 = fuel + (scanCost + 2) by omega] using
    entry.trans (scanned.trans finished)

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
