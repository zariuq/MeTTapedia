import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.TypedConditionFinishes

/-!
# A named difference on the scoped lookup, every run finishing: an uncovered condition

`IfUncovered` proved, on the historical lookup, that for `(if (isZero 1) yes no)` with only
`(= (isZero 0) True)` every complete HE run publishes the call itself, while PeTTa yields no value.
Here the same holds on the scoped lookup at every frame, and **every run finishes**:

* `UncoveredCall`: a call of a defined function on data whose region is empty;
* `uncovered_call_source`, `fine_uncovered_call`: under `Bool`, at every frame, every derivation
  returns the call itself and every run finishes with it (no row matches, so the query returns the
  call);
* `if_source_uncovered`, `fine_if_uncovered`: `(if c y n)` with such a condition, at every frame:
  the call value `(if c y n)` matches no row of `if` either, so every derivation publishes it and
  every run finishes with it;
* `uncovered_finishes`: on HE's `if` with `(= (isZero 0) True)`, a complete run of
  `(if (isZero 1) yes no)` exists, every complete run publishes it, every run finishes, and PeTTa's
  run ends with no value (`IfUncovered.petta_uncovered`).

## Controls

* `Controls.isZero_condition` (positive): `(isZero 0)` is a condition with `True`
  (`IfConditions.call_condition`).
* `Controls.uncovered_not_condition` (negative): `(isZero 1)` is a condition for neither Boolean, so
  the condition interface of `IfConditions` has content.
* `Controls.covered_contrast` (positive): with the covered condition `(isZero 0)` the same program's
  `if` publishes `yes` on every run, which finishes, as PeTTa does.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace UncoveredFinishes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation (specBindingVars)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (AtomOccurs)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open HEOnTheStep (HEConfig)
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun NestedValues NestedCalls MarkedValues CompoundBindings DeclaredHeads
  DeclaredEveryRun TypedEveryRun AtomDemands IfEveryRun IfBranches EveryRunFinishes IfFinishes
  IfComputed ScopedTransfer ScopedIf IfConditions
open AnswerBags.Controls (sym app)

variable {dispatch : GroundedDispatch} {policy : Policy}

/-! ## An uncovered call under `Bool` -/

/-- **An uncovered call**: a defined function on data whose region on these arguments is empty. -/
structure UncoveredCall (dispatch : GroundedDispatch) (atoms : List Atom) (g : String)
    (args : List Atom) : Prop where
  ordinary : Ordinary dispatch atoms g args
  head : NodeHead dispatch atoms g
  region : regionInstances atoms g args = []
  undeclared : StorageTypesRel (Space.ofList atoms) (.expression (.symbol g :: args))
    [Atom.undefinedType]

/-- **Every derivation of an uncovered call under `Bool`, at every frame, returns the call.** -/
theorem uncovered_call_source {atoms : List Atom} (program : ScopedProgram atoms) {g : String}
    {args : List Atom} (call : UncoveredCall dispatch atoms g args) {live : List Atom}
    {scope : List String} {frame : Frame} {results : List Result}
    (derived : Completed.AtomRel (Space.ofList atoms) dispatch Completed.scopedLookup live scope
      (Entry.Value.ofAtom (.expression (.symbol g :: args))) (sym "Bool") frame results
      (policy := policy)) :
    results.map (fun r => r.1.erase) = [.expression (.symbol g :: args)] := by
  have ordinary := call.ordinary
  have answerable := call_answerable ordinary.head ordinary.arguments
  have closed := answerable.closed
  have readCall := HERuns.read_closed policy frame closed
  have entry := call_bool_entry policy ordinary.head args frame closed
  have shape : frame.read policy (Entry.Value.ofAtom (.expression (.symbol g :: args))) =
      .expression .active (Entry.Value.ofAtom (.symbol g) :: args.map Entry.Value.ofAtom) := by
    rw [readCall]
    simp only [Entry.Value.ofAtom, List.map_cons]
  have storage : StorageTypesRel (Space.ofList atoms) (.symbol g) [Atom.undefinedType] :=
    (Mettapedia.Languages.MeTTa.HE.Spec.Type.StorageTypesRel.undefined_iff_occurrences _ _).mpr
      (untyped_occurrences ordinary.untyped)
  have data := HERuns.ordinary_data ordinary
  have selectionExact : ∀ {outcome : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList atoms) Completed.scopedLookup policy live scope
        (frame.read policy (Entry.Value.ofAtom (.expression (.symbol g :: args)))).erase
        (.symbol g) (sym "Bool") frame outcome → outcome = .exhausted [] true :=
    fun chosen => chosen.undefined_exact_of_query fun _ queried =>
      scoped_contract.undeclared _ _ _ _ _ storage queried
  have query : ∀ {after : Frame} {children : List Result},
      Completed.CallRel (Space.ofList atoms) dispatch Completed.scopedLookup live scope
        (callValue g args) (sym "Bool") after children (policy := policy) →
      children.map (fun r => r.1.erase) = [.expression (.symbol g :: args)] := by
    intro after children called
    cases called with
    | error failed => exact absurd failed (call_not_error ordinary.head args)
    | embedded _ _ instruction _ _ =>
        rw [callValue_erase, ordinary.notInstruction] at instruction
        cases instruction
    | absent _ _ _ => simp [callValue_erase]
    | equations _ _ frontier nonempty _ =>
        rw [callValue_erase] at frontier
        have instances := works_instances (policy := policy) ordinary.arguments program
          after.certified.satisfiable frontier
        rw [call.region] at instances
        exact absurd (List.forall₂_nil_right_iff.mp instances) nonempty
  have publish : ∀ {raw selected : List Result},
      raw.map (fun r => r.1.erase) = [.expression (.symbol g :: args)] →
      Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
        (fun result : Result => isErrorAtom result.1.erase)
        (raw.map (Completed.readResult policy)) selected →
      (selected.map (Completed.publishResult policy
        (.expression (.symbol g :: args)))).map (fun r => r.1.erase) =
          [.expression (.symbol g :: args)] := by
    intro raw selected erased chosen
    exact publish_answers erased (fun a member => by
      rw [List.mem_singleton] at member
      subst member
      exact answerable) chosen
  have rows : ∀ {operator : Entry.Value} {arguments : List Entry.Value} {rows raw : List Result},
      Entry.Value.ofAtom (.symbol g) = operator → args.map Entry.Value.ofAtom = arguments →
      Completed.TupleRel (Space.ofList atoms) dispatch Completed.scopedLookup
        (sym "Bool" :: live) scope (operator :: arguments) frame rows (policy := policy) →
      Completed.CallsRel (Space.ofList atoms) dispatch Completed.scopedLookup live scope
        (sym "Bool") rows raw (policy := policy) →
      raw.map (fun r => r.1.erase) = [.expression (.symbol g :: args)] := by
    intro operator arguments rows raw sameOperator sameArguments tuples calls
    subst sameOperator sameArguments
    obtain ⟨after, rfl⟩ := tuple_source scoped_contract (Atom.symbol g :: args)
      (List.cons_ne_nil _ _) data _ _ _ tuples
    cases calls with
    | cons called rest =>
        cases rest
        rw [List.append_nil]
        exact query called
  cases derived with
  | delivered entered => cases Entry.functional entered entry
  | cast entered => cases Entry.functional entered entry
  | tuple _ shaped _ tuples calls chosen =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, sameOperator, sameArguments⟩ := shaped
      rw [readCall, Entry.Value.erase_ofAtom]
      exact publish (rows sameOperator sameArguments tuples calls) chosen
  | function _ shaped chosen =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      rw [Entry.Value.erase_ofAtom] at chosen
      cases selectionExact chosen
  | fallback _ shaped chosen tuples calls selected =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, sameOperator, sameArguments⟩ := shaped
      have operatorErase := congrArg Entry.Value.erase sameOperator
      rw [Entry.Value.erase_ofAtom] at operatorErase
      rw [← operatorErase] at chosen
      have exhausted := selectionExact chosen
      simp only [Completed.InvocationSelection.exhausted.injEq, and_true] at exhausted
      subst exhausted
      have chosenRaw := selected
      simp only [Completed.diagnosticResults, List.map_nil, List.append_nil] at chosenRaw
      rw [readCall, Entry.Value.erase_ofAtom]
      exact publish (rows sameOperator sameArguments tuples calls) chosenRaw
  | selectionFailed _ shaped chosen =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      rw [Entry.Value.erase_ofAtom] at chosen
      have exhausted := selectionExact chosen
      simp at exhausted

/-- **A query that no row matches, under any demand, finishes with the call value**: the frontier is
empty on every run, and `callAbsent` returns the call. -/
theorem fine_query_absent_any {atoms : List Atom} {E : Atom} {query : Atom} {live : List Atom}
    {scope : List String} {value : Entry.Value} (erased : value.erase = query)
    (notError : ¬ IsErrorRel value.erase) (nonGrounded : NonGroundedCallRel dispatch value.erase)
    (notInstruction : Minimal.embeddedInstruction value.erase = false)
    (empty : ∀ (live' : List Atom) (incoming : Bindings) (works : List EquationWork),
      (∃ model : String → Atom,
        Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied model incoming) →
      EquationFrontierRel (Space.ofList atoms) live' query incoming works → works = [])
    (activation : Frame) (stack : List Continuation) (emitted : List Result)
    (cont : ∀ R : List Result, R.map (fun r => r.1.erase) = [query] →
      Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms,
      .work (.call live scope value E activation), stack, emitted⟩ := by
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms) (E :: live) query
    activation.bindings
  have none := empty _ _ _ activation.certified.satisfiable frontier
  subst none
  have frontier' : EquationFrontierRel (Space.ofList atoms) (E :: live) value.erase
      activation.bindings [] := by
    rw [erased]
    exact frontier
  refine .step ⟨_, .internal (.callAbsent notError nonGrounded frontier')⟩ ?_
  intro z step
  cases step with
  | internal l =>
      cases l with
      | callError failed => exact absurd failed notError
      | callEmbedded _ _ instruction =>
          rw [notInstruction] at instruction
          cases instruction
      | callAbsent _ _ _ =>
          apply cont
          simp [erased]
      | callEquations _ _ frontierW nonempty =>
          rw [erased] at frontierW
          exact absurd (empty _ _ _ activation.certified.satisfiable frontierW) nonempty

/-- The frontier of an uncovered call is empty. -/
theorem uncovered_frontier_empty {atoms : List Atom} (program : ScopedProgram atoms) {g : String}
    {args : List Atom} (call : UncoveredCall dispatch atoms g args) (live : List Atom)
    (incoming : Bindings) (works : List EquationWork)
    (satisfiable : ∃ model : String → Atom,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied model incoming)
    (frontier : EquationFrontierRel (Space.ofList atoms) live (.expression (.symbol g :: args))
      incoming works) : works = [] := by
  have instances := works_instances (policy := Policy.unmarked) call.ordinary.arguments program
    satisfiable frontier
  rw [call.region] at instances
  exact List.forall₂_nil_right_iff.mp instances

/-- **Every run of an uncovered call under `Bool`, at every frame, finishes with the call.** -/
theorem fine_uncovered_call {atoms : List Atom} (program : ScopedProgram atoms) {g : String}
    {args : List Atom} (call : UncoveredCall dispatch atoms g args) {live : List Atom}
    {scope : List String} {frame : Frame} {stack : List Continuation} {emitted : List Result}
    (cont : ∀ R : List Result, R.map (fun r => r.1.erase) = [.expression (.symbol g :: args)] →
      Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms,
      .work (.atom live scope (Entry.Value.ofAtom (.expression (.symbol g :: args))) (sym "Bool")
        frame), stack, emitted⟩ := by
  have ordinary := call.ordinary
  have answerable := call_answerable ordinary.head ordinary.arguments
  have closed := answerable.closed
  have readV := HERuns.read_closed policy frame closed
  have entry := call_bool_entry policy ordinary.head args frame closed
  have readShape : frame.read policy (Entry.Value.ofAtom (.expression (.symbol g :: args))) =
      .expression .active (Entry.Value.symbol g :: args.map Entry.Value.ofAtom) := by
    rw [readV]
    simp only [Entry.Value.ofAtom, List.map_cons]
  have occurrences : Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel
      ((Space.ofList atoms).atoms : Multiset Atom) (Entry.Value.symbol g).erase
      {Atom.undefinedType} := by
    simp only [Entry.Value.erase]
    exact untyped_occurrences ordinary.untyped
  have storage : StorageTypesRel (Space.ofList atoms) (.symbol g) [Atom.undefinedType] :=
    (Mettapedia.Languages.MeTTa.HE.Spec.Type.StorageTypesRel.undefined_iff_occurrences _ _).mpr
      (untyped_occurrences ordinary.untyped)
  have operatorErase : (Entry.Value.symbol g).erase = Atom.symbol g := by
    simp only [Entry.Value.erase]
  have selectionExact : ∀ {outcome : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList atoms) Completed.scopedLookup policy live scope
        (frame.read policy (Entry.Value.ofAtom (.expression (.symbol g :: args)))).erase
        (.symbol g) (sym "Bool") frame outcome → outcome = .exhausted [] true :=
    fun chosen => chosen.undefined_exact_of_query fun _ queried =>
      scoped_contract.undeclared _ _ _ _ _ storage queried
  have published : (frame.read policy (Entry.Value.ofAtom (.expression (.symbol g :: args)))).erase =
      .expression (.symbol g :: args) := by
    rw [readV, Entry.Value.erase_ofAtom]
  have afterPublish : ∀ R : List Result, R.map (fun r => r.1.erase) =
        [.expression (.symbol g :: args)] →
      Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms, .returning R,
        .publish (.expression (.symbol g :: args)) :: stack, emitted⟩ := by
    intro R eraseR
    apply fine_publish (HENested.clean_of_erase eraseR (fun a member => by
      rw [List.mem_singleton] at member
      subst member
      exact answerable))
    apply cont
    rw [publish_erase, eraseR]
  have afterRows : ∀ (rest : List Continuation),
      (∀ R : List Result, R.map (fun r => r.1.erase) = [.expression (.symbol g :: args)] →
        Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms, .returning R, rest, emitted⟩) →
      ∀ rows : List Result, rows.map (fun r => r.1.erase) =
          (combos ([.symbol g] :: args.map fun a => [a])).map Atom.expression →
        Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms, .returning rows,
          .calls live scope (sym "Bool") :: rest, emitted⟩ := by
    intro rest restFine rows eraseRows
    have single : (combos ([.symbol g] :: args.map fun a => [a])).map Atom.expression =
        [.expression (.symbol g :: args)] := by
      rw [show ([.symbol g] :: args.map fun a => [a]) = ((.symbol g :: args).map fun a => [a]) from
        rfl, combos_singletons]
      rfl
    rw [single] at eraseRows
    obtain ⟨r, rfl, rErase⟩ := List.map_eq_singleton_iff.mp eraseRows
    apply fine_calls_frame
    apply fine_calls_cons
    refine fine_query_absent_any rErase
      (HERuns.value_not_error ordinary.head rErase)
      (HERuns.value_nonGrounded call.head.notHost (call.head.instruction args) rErase)
      (by rw [rErase]; exact call.head.instruction args)
      (fun live' incoming works sat frontier =>
        uncovered_frontier_empty program call live' incoming works sat frontier)
      r.2 _ _ ?_
    intro Q eraseQ
    apply fine_append
    apply fine_calls_nil
    apply fine_prepend
    apply restFine
    simpa using eraseQ
  have argsAll : List.Forall₂ (fun v L => FineRuns dispatch Completed.scopedLookup policy atoms v L ∧
      ∀ a ∈ L, Answerable a) (Entry.Value.symbol g :: args.map Entry.Value.ofAtom)
      ([.symbol g] :: args.map fun a => [a]) := by
    refine .cons ⟨fine_data scoped_answers scoped_contract atoms ordinary.head (.symbol g)
        (by simp only [Entry.Value.erase]) (.symbol g), fun a member => by
          rw [List.mem_singleton] at member
          subst member
          exact answerable_of_data ordinary.head⟩ ?_
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    apply List.forall₂_same.mpr
    intro a member
    refine ⟨fine_data scoped_answers scoped_contract atoms (ordinary.arguments a member) _
      (Entry.Value.erase_ofAtom a) (marked_ofAtom a), fun x inside => ?_⟩
    rw [List.mem_singleton] at inside
    subst inside
    exact answerable_of_data (ordinary.arguments x member)
  refine .step ⟨_, .internal (LocalStepWith.atomTuple entry readShape occurrences)⟩ ?_
  intro y step
  cases step with
  | internal l =>
      cases l with
      | delivered entered => cases Entry.functional entered entry
      | cast entered => cases Entry.functional entered entry
      | atomTuple _ shaped _ =>
          rw [readShape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, rfl⟩ := shaped
          rw [published]
          exact fine_tuple atoms (.symbol g :: args.map Entry.Value.ofAtom)
            ([.symbol g] :: args.map fun a => [a]) (List.cons_ne_nil _ _) argsAll _ scope frame _
            emitted (afterRows _ afterPublish)
      | atomFunction _ shaped chosen =>
          rw [readShape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          rw [operatorErase] at chosen
          cases selectionExact chosen
      | atomFallback _ shaped chosen =>
          rw [readShape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, rfl⟩ := shaped
          rw [operatorErase] at chosen
          have exhausted := selectionExact chosen
          simp only [Completed.InvocationSelection.exhausted.injEq, and_true] at exhausted
          subst exhausted
          rw [published]
          refine fine_tuple atoms (.symbol g :: args.map Entry.Value.ofAtom)
            ([.symbol g] :: args.map fun a => [a]) (List.cons_ne_nil _ _) argsAll _ scope frame _
            emitted (afterRows _ ?_)
          intro R eraseR
          apply fine_diagnostics
          simp only [Completed.diagnosticResults, List.map_nil, List.append_nil]
          exact afterPublish R eraseR
      | atomSelectionFailed _ shaped chosen =>
          rw [readShape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          rw [operatorErase] at chosen
          have exhausted := selectionExact chosen
          simp at exhausted

/-! ## `if` with an uncovered condition -/

/-- **The data of `(if c y n)` with an uncovered condition**: data branches with closed stored types,
and no row of `if` for `(if c y n)`. -/
structure UncoveredIf (atoms : List Atom) (c y n : Atom) : Prop where
  dataYes : DataAtom y
  dataNo : DataAtom n
  typedYes : ∃ T, StorageTypesRel (Space.ofList atoms) y [T] ∧ TypeSubst.typeVars T = []
  typedNo : ∃ T, StorageTypesRel (Space.ofList atoms) n [T] ∧ TypeSubst.typeVars T = []
  region : regionInstances atoms "if" [c, y, n] = []

theorem uncovered_answerable {atoms : List Atom} {g : String} {args : List Atom} {y n : Atom}
    (call : UncoveredCall dispatch atoms g args) (dataY : DataAtom y) (dataN : DataAtom n) :
    Answerable (callC (.expression (.symbol g :: args)) y n) :=
  app_answerable if_data fun a member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact call_answerable call.ordinary.head call.ordinary.arguments
    · exact answerable_of_data dataY
    · exact answerable_of_data dataN

/-- The frontier of `(if c y n)` is empty. -/
theorem if_frontier_empty {atoms : List Atom} (program : IfProgram atoms) {g : String}
    {args : List Atom} {y n : Atom} (call : UncoveredCall dispatch atoms g args)
    (shape : UncoveredIf atoms (.expression (.symbol g :: args)) y n) (live : List Atom)
    (incoming : Bindings) (works : List EquationWork)
    (satisfiable : ∃ model : String → Atom,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied model incoming)
    (frontier : EquationFrontierRel (Space.ofList atoms) live
      (callC (.expression (.symbol g :: args)) y n) incoming works) : works = [] := by
  have ground : ∀ a ∈ [Atom.expression (.symbol g :: args), y, n], TypeSubst.typeVars a = [] := by
    intro a member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact HERuns.ground_typeVars (call_answerable call.ordinary.head call.ordinary.arguments)
    · exact HERuns.ground_typeVars (answerable_of_data shape.dataYes)
    · exact HERuns.ground_typeVars (answerable_of_data shape.dataNo)
  have instances := works_instances_ground Policy.unmarked ground program.rows satisfiable frontier
  rw [shape.region] at instances
  exact List.forall₂_nil_right_iff.mp instances

/-- **Every derivation of `(if c y n)` with an uncovered condition, at every frame, publishes the
call itself**, on the scoped lookup: the condition returns itself under `Bool`, and `(if c y n)`
matches no row of `if`. -/
theorem if_source_uncovered {atoms : List Atom} (program : IfProgram atoms) {g : String}
    {args : List Atom} {y n : Atom} (call : UncoveredCall dispatch atoms g args)
    (shape : UncoveredIf atoms (.expression (.symbol g :: args)) y n) {live : List Atom}
    {scope : List String} {frame : Frame} {results : List Result}
    (derived : Completed.AtomRel (Space.ofList atoms) dispatch Completed.scopedLookup live scope
      (Entry.Value.ofAtom (callC (.expression (.symbol g :: args)) y n)) Atom.undefinedType frame
      results (policy := policy)) :
    results.map (fun r => r.1.erase) = [callC (.expression (.symbol g :: args)) y n] := by
  obtain ⟨Ty, typesY, closedY⟩ := shape.typedYes
  obtain ⟨Tn, typesN, closedN⟩ := shape.typedNo
  have closedC := (call_answerable call.ordinary.head call.ordinary.arguments).closed
  have closedYes := (answerable_of_data shape.dataYes).closed
  have closedNo := (answerable_of_data shape.dataNo).closed
  have readC : frame.read policy (Entry.Value.ofAtom (callC (.expression (.symbol g :: args)) y n)) =
      Entry.Value.ofAtom (callC (.expression (.symbol g :: args)) y n) :=
    HERuns.read_closed policy frame (callC_closed closedC closedYes closedNo)
  have entry : Entry.Rel policy.reentry
      (frame.read policy (Entry.Value.ofAtom (callC (.expression (.symbol g :: args)) y n))).status
      (frame.read policy (Entry.Value.ofAtom (callC (.expression (.symbol g :: args)) y n))).erase
      Atom.undefinedType .interpret := by
    have atEmpty := call_entry policy if_data [.expression (.symbol g :: args), y, n]
    rw [Completed.Frame.read_empty] at atEmpty
    rw [readC]
    exact atEmpty
  have shapeV : frame.read policy (Entry.Value.ofAtom (callC (.expression (.symbol g :: args)) y n)) =
      .expression .active (Entry.Value.ofAtom (.symbol "if") ::
        [Atom.expression (.symbol g :: args), y, n].map Entry.Value.ofAtom) := by
    rw [readC]
    simp only [callC, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  have outcome : ∀ {result : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList atoms) Completed.scopedLookup policy live scope
        (frame.read policy (Entry.Value.ofAtom (callC (.expression (.symbol g :: args)) y n))).erase
        (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType frame result →
      ∃ (u : String) (signature : SelectedTypePolicy) (after : Frame),
        u ∉ specBindingVars frame.bindings ∧ signature.functionType = ifArrowV u ∧
        after.bindings = frame.bindings ∧ result = .selected signature [after] := by
    intro result chosenRel
    rw [readC, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosenRel
    exact if_selection_c program call.undeclared (Or.inr rfl) typesY closedY typesN closedN chosenRel
  have readY : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom y) = Entry.Value.ofAtom y :=
    fun frame => HERuns.read_closed policy frame closedYes
  have readN : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom n) = Entry.Value.ofAtom n :=
    fun frame => HERuns.read_closed policy frame closedNo
  cases derived with
  | delivered entered => cases Entry.functional entered entry
  | cast entered => cases Entry.functional entered entry
  | tuple _ shaped occurs _ _ _ =>
      rw [shapeV] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      rw [Entry.Value.erase_ofAtom] at occurs
      have same := Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel.unique occurs
        program.types.occurrences
      simp [Atom.undefinedType] at same
  | fallback _ shaped chosenRel _ _ _ =>
      rw [shapeV] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      obtain ⟨_, _, _, _, _, _, impossible⟩ := outcome chosenRel
      cases impossible
  | selectionFailed _ shaped chosenRel _ =>
      rw [shapeV] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      obtain ⟨_, _, _, _, _, _, impossible⟩ := outcome chosenRel
      cases impossible
  | function _ shaped chosenRel invoked priority =>
      rw [shapeV] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, rfl⟩ := shaped
      obtain ⟨u, signature, after, freshU, functionType, afterBindings, selected⟩ :=
        outcome chosenRel
      simp only [Completed.InvocationSelection.selected.injEq] at selected
      obtain ⟨rfl, rfl⟩ := selected
      have freshAfter : u ∉ specBindingVars after.bindings := by
        rw [afterBindings]
        exact freshU
      have projections := if_projections_v functionType
      have returnType := returnType_v functionType
      cases invoked with
      | cons function calls rest =>
          cases rest
          cases function with
          | evaluated _ operatorRel branchesRel =>
              rw [functionType] at operatorRel
              obtain ⟨frF, rfl⟩ := cast_source_any if_data
                (symbol_cast_entry (by decide) (by decide) (arrowV_not_raw u))
                (operator_cast_accepts program freshAfter) operatorRel
              rw [projections.1] at branchesRel
              simp only [List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_right]
                at branchesRel
              cases branchesRel with
              | stopped stopped _ =>
                  rw [Entry.Value.erase_ofAtom] at stopped
                  exact absurd stopped if_data.not_stopped
              | continuing _ arguments restBranches =>
                  cases restBranches
                  cases arguments with
                  | cons conditionRel conditionBranches =>
                      obtain ⟨r, sameR, rErase⟩ := List.map_eq_singleton_iff.mp
                        (uncovered_call_source program.rows call conditionRel)
                      subst sameR
                      cases conditionBranches with
                      | stopped stopped _ =>
                          obtain ⟨stoppedCondition, _⟩ := stopped
                          rw [rErase] at stoppedCondition
                          exact absurd stoppedCondition (call_not_stopped call.ordinary.head)
                      | continuing _ yesArguments restCondition =>
                          cases restCondition
                          cases yesArguments with
                          | cons yesRel yesBranches =>
                              have yesDelivered := atom_demand_source yesRel
                              subst yesDelivered
                              rw [readY] at yesBranches
                              cases yesBranches with
                              | stopped stopped _ =>
                                  obtain ⟨_, different⟩ := stopped
                                  exact absurd rfl different
                              | continuing _ noArguments restYes =>
                                  cases restYes
                                  cases noArguments with
                                  | cons noRel noBranches =>
                                      have noDelivered := atom_demand_source noRel
                                      subst noDelivered
                                      rw [readN] at noBranches
                                      cases noBranches with
                                      | stopped stopped _ =>
                                          obtain ⟨_, different⟩ := stopped
                                          exact absurd rfl different
                                      | continuing _ packets restNo =>
                                          cases restNo
                                          cases packets
                                          rw [returnType] at calls
                                          simp only [List.map_cons, List.map_nil, List.append_nil,
                                            Completed.argumentPrepend_packet] at calls
                                          cases calls with
                                          | cons callRel restCalls =>
                                              cases restCalls
                                              have assembled : ∀ frame : Frame,
                                                  (Completed.functionAssemble
                                                    (Entry.Value.ofAtom (.symbol "if"))
                                                    (Entry.Value.argumentPacket
                                                      [r.1, Entry.Value.ofAtom y,
                                                        Entry.Value.ofAtom n], frame)).1.erase =
                                                    callC (.expression (.symbol g :: args)) y n :=
                                                fun frame => by
                                                  simp [Completed.functionAssemble,
                                                    Entry.Value.erase, Entry.Value.erase_ofAtom,
                                                    rErase, callC, app]
                                              have answered : ∀ {value : Entry.Value}
                                                  {frame' : Frame} {children : List Result},
                                                  value.erase =
                                                    callC (.expression (.symbol g :: args)) y n →
                                                  Completed.CallRel (Space.ofList atoms) dispatch
                                                    Completed.scopedLookup live scope value (.var u)
                                                    frame' children (policy := policy) →
                                                  children.map (fun r => r.1.erase) =
                                                    [callC (.expression (.symbol g :: args)) y n] := by
                                                intro value frame' children erased called
                                                cases called with
                                                | error failed =>
                                                    exact absurd failed
                                                      (HERuns.value_not_error if_data erased)
                                                | embedded _ _ instruction _ _ =>
                                                    rw [erased] at instruction
                                                    simp [Minimal.embeddedInstruction] at instruction
                                                | absent _ _ _ => simp [erased]
                                                | equations _ _ frontier nonempty _ =>
                                                    rw [erased] at frontier
                                                    exact absurd (if_frontier_empty program call
                                                      shape _ _ _ frame'.certified.satisfiable
                                                      frontier) nonempty
                                              exact publish_answers
                                                (by simp only [List.append_nil]
                                                    exact answered (assembled _) callRel)
                                                (fun a member => by
                                                  rw [List.mem_singleton] at member
                                                  subst member
                                                  exact uncovered_answerable call shape.dataYes
                                                    shape.dataNo)
                                                priority

/-- **Every run of `(if c y n)` with an uncovered condition, at every frame, finishes with the call
itself**, on the scoped lookup. -/
theorem fine_if_uncovered (notHost : ¬ dispatch.executable (.symbol "if")) (policy : Policy)
    {atoms : List Atom} (program : IfProgram atoms) {g : String} {args : List Atom} {y n : Atom}
    (call : UncoveredCall dispatch atoms g args)
    (shape : UncoveredIf atoms (.expression (.symbol g :: args)) y n) {live : List Atom}
    {scope : List String} {frame : Frame} (stack : List Continuation) (emitted : List Result)
    (cont : ∀ R : List Result,
      R.map (fun r => r.1.erase) = [callC (.expression (.symbol g :: args)) y n] →
      Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms,
      .work (.atom live scope (Entry.Value.ofAtom (callC (.expression (.symbol g :: args)) y n))
        Atom.undefinedType frame), stack, emitted⟩ := by
  obtain ⟨Ty, typesY, closedY⟩ := shape.typedYes
  obtain ⟨Tn, typesN, closedN⟩ := shape.typedNo
  have closedC := (call_answerable call.ordinary.head call.ordinary.arguments).closed
  have closedYes := (answerable_of_data shape.dataYes).closed
  have closedNo := (answerable_of_data shape.dataNo).closed
  have readC : frame.read policy (Entry.Value.ofAtom (callC (.expression (.symbol g :: args)) y n)) =
      Entry.Value.ofAtom (callC (.expression (.symbol g :: args)) y n) :=
    HERuns.read_closed policy frame (callC_closed closedC closedYes closedNo)
  have entry : Entry.Rel policy.reentry
      (frame.read policy (Entry.Value.ofAtom (callC (.expression (.symbol g :: args)) y n))).status
      (frame.read policy (Entry.Value.ofAtom (callC (.expression (.symbol g :: args)) y n))).erase
      Atom.undefinedType .interpret := by
    have atEmpty := call_entry policy if_data [.expression (.symbol g :: args), y, n]
    rw [Completed.Frame.read_empty] at atEmpty
    rw [readC]
    exact atEmpty
  have shapeV : frame.read policy (Entry.Value.ofAtom (callC (.expression (.symbol g :: args)) y n)) =
      .expression .active (Entry.Value.ofAtom (.symbol "if") ::
        [Atom.expression (.symbol g :: args), y, n].map Entry.Value.ofAtom) := by
    rw [readC]
    simp only [callC, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  obtain ⟨target, rename, injective, renamed, fresh⟩ :=
    Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact.TypeCandidateAlphaVariantRel.exists
      (invocationTypeScope (invocationTypeScope scope live (callC (.expression (.symbol g :: args)) y n)
        Atom.undefinedType frame.bindings) [] (.symbol "if") Atom.undefinedType frame.bindings) ifArrow
  have freshU := fresh "t" (by rw [ifArrow_vars]; exact List.mem_singleton_self _)
  have selection : Completed.ArgumentService.historical.selection (Space.ofList atoms)
      Completed.scopedLookup policy live scope
      (frame.read policy (Entry.Value.ofAtom (callC (.expression (.symbol g :: args)) y n))).erase
      (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType frame
      (.selected (ifPolicyV (rename "t")) [frame]) := by
    rw [readC, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom]
    exact if_selection_succeeds_c policy program call.undeclared (Or.inr rfl) typesY closedY typesN
      closedN live scope frame freshU
  have clean : ∀ R : List Result,
      R.map (fun r => r.1.erase) = [callC (.expression (.symbol g :: args)) y n] →
      ∀ r ∈ R, Answerable r.1.erase := by
    intro R eraseR r member
    have inR : r.1.erase ∈ [callC (.expression (.symbol g :: args)) y n] := by
      rw [← eraseR]
      exact List.mem_map.mpr ⟨r, member, rfl⟩
    rw [List.mem_singleton] at inR
    rw [inR]
    exact uncovered_answerable call shape.dataYes shape.dataNo
  refine .step ⟨_, .internal (LocalStepWith.atomFunction (admission := .historical) entry shapeV
    selection)⟩ ?_
  intro z moved
  cases moved with
  | internal l =>
      cases l with
      | delivered entered => cases Entry.functional entered entry
      | cast entered => cases Entry.functional entered entry
      | atomTuple _ shaped occurs =>
          rw [shapeV] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          rw [Entry.Value.erase_ofAtom] at occurs
          have same := Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel.unique occurs
            program.types.occurrences
          simp [Atom.undefinedType] at same
      | atomFallback _ shaped chosen =>
          rw [shapeV] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          rw [readC, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosen
          obtain ⟨_, _, _, _, _, _, impossible⟩ :=
            if_selection_c program call.undeclared (Or.inr rfl) typesY closedY typesN closedN chosen
          cases impossible
      | atomSelectionFailed _ shaped chosen =>
          rw [shapeV] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          rw [readC, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosen
          obtain ⟨_, _, _, _, _, _, impossible⟩ :=
            if_selection_c program call.undeclared (Or.inr rfl) typesY closedY typesN closedN chosen
          cases impossible
      | atomFunction _ shaped chosen =>
          rw [shapeV] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, rfl⟩ := shaped
          rw [readC, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosen
          obtain ⟨u, signature, after, freshFrame, functionType, afterBindings, selected⟩ :=
            if_selection_c program call.undeclared (Or.inr rfl) typesY closedY typesN closedN chosen
          simp only [Completed.InvocationSelection.selected.injEq] at selected
          obtain ⟨rfl, rfl⟩ := selected
          have freshAfter : u ∉ specBindingVars after.bindings := by
            rw [afterBindings]
            exact freshFrame
          have projections := if_projections_v functionType
          apply fine_invocations_cons
          rw [returnType_v functionType]
          simp only [List.map_cons, List.map_nil]
          refine fine_functionStart (by simp [projections.1]) ?_
          rw [projections.1, functionType]
          simp only [List.zip_cons_cons, List.zip_nil_right]
          refine fine_data_cast_any if_data
            (symbol_cast_entry (by decide) (by decide) (arrowV_not_raw u))
            (operator_step program freshAfter) (operator_cast_accepts program freshAfter) ?_
          intro frF
          apply fine_functionHeads_frame
          refine fine_functionBranches_continue ?_ ?_
          · simpa using if_data.not_stopped
          apply fine_argumentsCons
          refine fine_uncovered_call program.rows call ?_
          intro R eraseR
          obtain ⟨r, rfl, rErase⟩ := List.map_eq_singleton_iff.mp eraseR
          apply fine_arguments_frame
          refine fine_argumentBranches_continue ?_ ?_
          · rintro ⟨stopped, _⟩
            rw [rErase] at stopped
            exact call_not_stopped call.ordinary.head stopped
          apply fine_argumentsCons
          refine fine_deliver_closed closedYes ?_
          apply fine_arguments_frame
          refine fine_argumentBranches_continue ?_ ?_
          · rintro ⟨_, different⟩
            exact different rfl
          apply fine_argumentsCons
          refine fine_deliver_closed closedNo ?_
          apply fine_arguments_frame
          refine fine_argumentBranches_continue ?_ ?_
          · rintro ⟨_, different⟩
            exact different rfl
          apply fine_argumentsNil
          apply fine_argumentTail
          apply fine_append
          apply fine_argumentBranches_nil
          apply fine_prepend
          apply fine_argumentTail
          apply fine_append
          apply fine_argumentBranches_nil
          apply fine_prepend
          apply fine_argumentTail
          apply fine_append
          apply fine_argumentBranches_nil
          apply fine_prepend
          apply fine_functionAssemble
          apply fine_append
          apply fine_functionBranches_nil
          apply fine_prepend
          apply fine_calls_frame
          apply fine_calls_cons
          have assembledErase : (Completed.functionAssemble (Entry.Value.ofAtom (.symbol "if"))
              (Entry.Value.argumentPacket [r.1, Entry.Value.ofAtom y, Entry.Value.ofAtom n],
                r.2)).1.erase = callC (.expression (.symbol g :: args)) y n := by
            simp [Completed.functionAssemble, Entry.Value.erase,
              Entry.Value.erase_ofAtom, rErase, callC, app]
          refine fine_query_absent_any assembledErase
            (HERuns.value_not_error if_data assembledErase)
            (HERuns.value_nonGrounded notHost (by simp [Minimal.embeddedInstruction])
              assembledErase)
            (by rw [assembledErase]; simp [Minimal.embeddedInstruction])
            (fun live' incoming works sat frontier =>
              if_frontier_empty program call shape live' incoming works sat frontier) _ _ _ ?_
          intro Q eraseQ
          apply fine_append
          apply fine_calls_nil
          apply fine_prepend
          apply fine_append
          apply fine_invocations_nil
          apply fine_prepend
          refine fine_publish (clean _ (by simpa using eraseQ)) ?_
          apply cont
          rw [publish_erase]
          simpa using eraseQ

/-! ## The named difference -/

open IfUncovered (uncoveredRows condition uncoveredCall uncovered_program condition_untyped
  condition_types petta_uncovered isZero_data)
open WholeRunWords.Double (noHost)

theorem isZero_one_uncovered : UncoveredCall noHost uncoveredRows "isZero" [.grounded (.int 1)] where
  ordinary := ⟨isZero_data, (fun a member => by
      rw [List.mem_singleton] at member
      subst member
      exact .grounded _), condition_untyped, (fun impossible => impossible), (by decide),
    (by decide), (by decide), (by decide), (by decide), (by decide)⟩
  head := ⟨isZero_data, condition_untyped, (fun impossible => impossible), (by decide), (by decide),
    (by decide), (by decide)⟩
  region := by decide +kernel
  undeclared := condition_types

theorem uncovered_if_shape : UncoveredIf uncoveredRows condition (sym "yes") (sym "no") where
  dataYes := .symbol (by decide) (by decide)
  dataNo := .symbol (by decide) (by decide)
  typedYes := ⟨_, IfUncovered.symbol_undeclared "yes" (by decide), rfl⟩
  typedNo := ⟨_, IfUncovered.symbol_undeclared "no" (by decide), rfl⟩
  region := by decide +kernel

/-- **The named difference on the scoped lookup, every run finishing.** On HE's `if` with
`(= (isZero 0) True)`, for `(if (isZero 1) yes no)`: a complete HE run exists and every complete run
publishes the call itself; no run is infinite and every reachable configuration steps or is final with
it; PeTTa's run ends with no value from fuel `8` on. -/
theorem uncovered_finishes (policy : Policy) :
    Publishes noHost Completed.scopedLookup policy (Space.ofList uncoveredRows) uncoveredCall
        [uncoveredCall] ∧
      Finishes noHost Completed.scopedLookup policy (Space.ofList uncoveredRows) uncoveredCall
        [uncoveredCall] ∧
      ∀ k, 8 ≤ k → Streaming.values (Streaming.advance (translate uncoveredRows) k
        (Streaming.enter { state := store uncoveredRows } uncoveredCall)) = [] := by
  have fine : Fine noHost Completed.scopedLookup policy
      (load (Space.ofList uncoveredRows) uncoveredCall Atom.undefinedType) :=
    fine_if_uncovered (fun impossible => impossible) policy uncovered_program isZero_one_uncovered
      uncovered_if_shape [] [] (fun R _ => fine_top R [])
  have every : ∀ emitted : List Result,
      Relation.ReflTransGen (HEStep noHost Completed.scopedLookup policy)
        (load (Space.ofList uncoveredRows) uncoveredCall Atom.undefinedType)
        (final (Space.ofList uncoveredRows) emitted) →
      emitted.map (fun r => r.1.erase) = [uncoveredCall] :=
    fun emitted run => if_source_uncovered uncovered_program isZero_one_uncovered uncovered_if_shape
      (complete_source run)
  refine ⟨⟨?_, every⟩, ⟨fine.acc, fun y path => ?_⟩, petta_uncovered⟩
  · obtain ⟨space, emitted, path⟩ := IfAtFrames.Fine.exists_final fine
    have same : space = Space.ofList uncoveredRows := space_fixed path
    subst same
    exact ⟨emitted, path⟩
  · rcases (fine.reaches path).progress with moves | ⟨space, emitted, rfl⟩
    · exact Or.inl moves
    · have same : space = Space.ofList uncoveredRows := space_fixed path
      subst same
      exact Or.inr ⟨emitted, rfl, every emitted path⟩

/-! ## Controls -/

namespace Controls

/-- `(isZero 0)` is a Boolean call in the same program. -/
theorem isZero_zero_call : BoolCall noHost uncoveredRows "isZero" [.grounded (.int 0)] true where
  ordinary := ⟨isZero_data, (fun a member => by
      rw [List.mem_singleton] at member
      subst member
      exact .grounded _), condition_untyped, (fun impossible => impossible), (by decide),
    (by decide), (by decide), (by decide), (by decide), (by decide)⟩
  head := ⟨isZero_data, condition_untyped, (fun impossible => impossible), (by decide), (by decide),
    (by decide), (by decide)⟩
  region := by decide +kernel
  bodies := by decide +kernel
  undeclared := IfInBodies.Controls.expression_undeclared_of (by decide)

/-- **Positive control of the condition interface**: `(isZero 0)` is a condition with `True`. -/
theorem isZero_condition (policy : Policy) :
    ScopedCondition noHost policy uncoveredRows (app "isZero" [.grounded (.int 0)]) true :=
  call_condition uncovered_program.rows isZero_zero_call

/-- A complete run from the entry of `c` under a demand `T` is a source derivation under `T`. -/
theorem complete_source_at {lookup : CastLookup} {space : Space} {c T : Atom} {E : List Result}
    (run : Relation.ReflTransGen (HEStep noHost lookup policy)
      (load space c T) ⟨space, .returning [], [], E⟩) :
    Completed.AtomRel space noHost lookup [] [] (Entry.Value.ofAtom c) T Completed.Frame.empty E
      (policy := policy) := by
  have final : Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual.Configuration.SourceRel
      noHost lookup policy ⟨space, .returning [], [], E⟩ E :=
    ⟨[], [], .returning [], .nil [], (List.append_nil E).symm⟩
  have initial := Mettapedia.Languages.MeTTa.HE.RecursiveCorrectness.Contextual.steps_source_back
    run final
  exact (Mettapedia.Languages.MeTTa.HE.RecursiveCorrectness.Contextual.initial_source_iff space
    noHost lookup policy (.atom [] [] (Entry.Value.ofAtom c) T Completed.Frame.empty) E).mp initial

/-- **Negative control of the condition interface**: `(isZero 1)` is a condition for neither
Boolean. A condition's runs under `Bool` reach a final configuration whose source derivation returns
the Boolean, while every derivation of `(isZero 1)` under `Bool` returns the call itself. -/
theorem uncovered_not_condition (policy : Policy) (b : Bool) :
    ¬ ScopedCondition noHost policy uncoveredRows condition b := by
  intro isCondition
  have fine : Fine noHost Completed.scopedLookup policy
      (load (Space.ofList uncoveredRows) condition (sym "Bool")) :=
    isCondition.fine [] [] Completed.Frame.empty [] [] (fun R _ => fine_top R [])
  obtain ⟨space, emitted, path⟩ := IfAtFrames.Fine.exists_final fine
  have same : space = Space.ofList uncoveredRows := space_fixed path
  subst same
  have derived := complete_source_at path
  have boolean := isCondition.determined [] [] Completed.Frame.empty emitted derived
  have itself := uncovered_call_source uncovered_program.rows isZero_one_uncovered derived
  rw [boolean] at itself
  simp at itself

/-- **Positive control, the covered condition**: in the same program `(if (isZero 0) yes no)`
publishes `yes` on every run, which finishes, as PeTTa does. -/
theorem covered_contrast (policy : Policy) :
    Publishes noHost Completed.scopedLookup policy (Space.ofList uncoveredRows)
        (callC (app "isZero" [.grounded (.int 0)]) (sym "yes") (sym "no")) [sym "yes"] ∧
      Finishes noHost Completed.scopedLookup policy (Space.ofList uncoveredRows)
        (callC (app "isZero" [.grounded (.int 0)]) (sym "yes") (sym "no")) [sym "yes"] ∧
      ∃ N : Nat, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate uncoveredRows) n
        (Streaming.enter { state := store uncoveredRows }
          (callC (app "isZero" [.grounded (.int 0)]) (sym "yes") (sym "no")))) = [sym "yes"] := by
  have node : IfInBodies.IfNode noHost uncoveredRows (app "isZero" [.grounded (.int 0)]) true
      (sym "yes") (sym "no") :=
    { condition := isZero_condition
      branches :=
        { branches :=
            { takenData := .symbol (by decide) (by decide)
              takenNotRefused := by simp [pick, Atom.notReducible]
              takenUndeclared := IfUncovered.symbol_undeclared "yes" (by decide)
              closedYes := data_closed (.symbol (by decide) (by decide))
              closedNo := data_closed (.symbol (by decide) (by decide))
              groundYes := rfl
              groundNo := rfl
              typedYes := ⟨_, IfUncovered.symbol_undeclared "yes" (by decide)⟩
              typedNo := ⟨_, IfUncovered.symbol_undeclared "no" (by decide)⟩
              region := by decide +kernel }
          typedYes := ⟨_, IfUncovered.symbol_undeclared "yes" (by decide), rfl⟩
          typedNo := ⟨_, IfUncovered.symbol_undeclared "no" (by decide), rfl⟩ }
      dataYes := .symbol (by decide) (by decide)
      dataNo := .symbol (by decide) (by decide) }
  exact IfInBodies.if_bodies_every_run noHost (fun impossible => impossible) policy
    uncovered_program (.ifNode node)

end Controls

#print axioms uncovered_call_source
#print axioms fine_query_absent_any
#print axioms fine_uncovered_call
#print axioms if_source_uncovered
#print axioms fine_if_uncovered
#print axioms uncovered_finishes
#print axioms Controls.isZero_condition
#print axioms Controls.uncovered_not_condition
#print axioms Controls.covered_contrast

end UncoveredFinishes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
