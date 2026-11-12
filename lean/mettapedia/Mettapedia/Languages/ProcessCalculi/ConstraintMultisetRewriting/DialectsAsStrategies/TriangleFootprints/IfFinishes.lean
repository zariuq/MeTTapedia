import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.IfSharedType

/-!
# Every run of `(if b y n)` finishes: the branch left never runs

`IfBranches.branch_every_run` shows that a complete HE run of `(if b y n)` exists and that every
complete run publishes the taken branch. Here **every run finishes**: from the entry configuration
HE's machine has no infinite run, and every configuration it reaches either steps or is final. With
`y` or `n` a divergent call such as `(loop)`, this is the precise sense in which the branch left
never runs: it is only delivered under the `Atom` demand, and nothing ever evaluates it.

The proof is `EveryRunFinishes.Fine` (H6's continuation-passing logical relation) carried along
`if`'s function path:

* frame lemmas for the function-application continuations (`invocations`, `function`,
  `functionHeads`, `functionBranches`, `arguments`, `argumentBranches`, `argumentTail`,
  `functionAssemble`), each the only step of its configuration;
* `fine_data_cast`: a data atom whose one stored type the demand accepts at every frame is cast,
  and every cast result is the atom (whatever frame the renewal reaches);
* `fine_branch_query`: the query of `if` under `$t`, for every frontier and every unifier output;
* `branch_fine`, `branch_every_run_finishes`.

## Controls

* `Controls.loop_left_finishes` (`(if True yes (loop))` with `(= (loop) (loop))`): every run
  finishes and every final configuration publishes `yes`, while `(loop)` alone has an infinite run
  in the same program (`IfBranches.Controls.loop_diverges_alone`).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace IfFinishes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel rawTypeLookupRel
  FunctionTypeRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (AtomOccurs)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open HEOnTheStep (HEConfig)
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun NestedValues NestedCalls MarkedValues CompoundBindings DeclaredHeads
  DeclaredEveryRun TypedEveryRun AtomDemands IfEveryRun IfBranches EveryRunFinishes
open AnswerBags.Controls (sym app rule rule_consFree)

variable {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy}

/-! ## Function-application frames -/

section Frames

variable {space : Space} {stack : List Continuation} {emitted : List Result} {live : List Atom}
  {scope : List String}

theorem fine_invocations_nil {expected : Atom} {signature : SelectedTypePolicy}
    {operator : Entry.Value} {arguments : List Entry.Value}
    (next : Fine dispatch lookup policy ⟨space, .returning [], stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space,
      .work (.invocations live scope expected signature operator arguments []), stack, emitted⟩ :=
  fine_det (.internal .invocationsNil) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_invocations_cons {expected : Atom} {signature : SelectedTypePolicy}
    {operator : Entry.Value} {arguments : List Entry.Value} {activation : Frame}
    {activations : List Frame}
    (next : Fine dispatch lookup policy ⟨space,
      .work (.function (Completed.invocationReturnType signature :: live) scope expected signature
        operator arguments activation),
      .calls live scope (Completed.invocationReturnType signature) ::
        .append (.invocations live scope expected signature operator arguments activations) ::
          stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space,
      .work (.invocations live scope expected signature operator arguments
        (activation :: activations)), stack, emitted⟩ :=
  fine_det (.internal .invocationsCons) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_functionStart {expected : Atom} {signature : SelectedTypePolicy}
    {operator : Entry.Value} {arguments : List Entry.Value} {activation : Frame}
    (arity : arguments.length = signature.argumentTypes.length)
    (next : Fine dispatch lookup policy ⟨space,
      .work (.atom (signature.functionType :: arguments.map Entry.Value.erase ++ live)
        (scope ++ expectedApplicationScope
          (.expression ((operator :: arguments).map Entry.Value.erase)) expected)
        operator signature.functionType activation),
      .functionHeads live scope (arguments.zip signature.argumentTypes) :: stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space,
      .work (.function live scope expected signature operator arguments activation), stack,
      emitted⟩ :=
  fine_det (.internal (.functionStart arity)) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_functionHeads_frame {requests : List Completed.ArgumentRequest} {heads : List Result}
    (next : Fine dispatch lookup policy ⟨space, .work (.functionBranches live scope requests heads),
      stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space, .returning heads,
      .functionHeads live scope requests :: stack, emitted⟩ :=
  fine_det (.internal .functionHeads) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_functionBranches_nil {requests : List Completed.ArgumentRequest}
    (next : Fine dispatch lookup policy ⟨space, .returning [], stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space, .work (.functionBranches live scope requests []), stack,
      emitted⟩ :=
  fine_det (.internal .functionBranchesNil) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_functionBranches_continue {requests : List Completed.ArgumentRequest}
    {head : Result} {heads : List Result} (notStopped : ¬ IsEmptyOrErrorRel head.1.erase)
    (next : Fine dispatch lookup policy ⟨space,
      .work (.arguments (head.1.erase :: live) scope requests head.2),
      .functionAssemble head.1 :: .append (.functionBranches live scope requests heads) :: stack,
      emitted⟩) :
    Fine dispatch lookup policy ⟨space,
      .work (.functionBranches live scope requests (head :: heads)), stack, emitted⟩ :=
  fine_det (.internal (.functionBranchesContinue notStopped)) (fun z step => by
    cases step with
    | internal l =>
        cases l with
        | functionBranchesStopped stopped => exact absurd stopped notStopped
        | functionBranchesContinue _ => rfl) next

theorem fine_functionAssemble {head : Entry.Value} {R : List Result}
    (next : Fine dispatch lookup policy ⟨space,
      .returning (R.map (Completed.functionAssemble head)), stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space, .returning R, .functionAssemble head :: stack, emitted⟩ :=
  fine_det (.internal .functionAssemble) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_argumentsNil {activation : Frame}
    (next : Fine dispatch lookup policy ⟨space,
      .returning [(Entry.Value.argumentPacket [], activation)], stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space, .work (.arguments live scope [] activation), stack, emitted⟩ :=
  fine_det (.internal .argumentsNil) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_argumentsCons {request : Completed.ArgumentRequest}
    {requests : List Completed.ArgumentRequest} {activation : Frame}
    (next : Fine dispatch lookup policy ⟨space,
      .work (.atom (Completed.argumentScope requests ++ live) scope request.1 request.2 activation),
      .arguments live scope request.1 requests :: stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space,
      .work (.arguments live scope (request :: requests) activation), stack, emitted⟩ :=
  fine_det (.internal .argumentsCons) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_arguments_frame {original : Entry.Value} {requests : List Completed.ArgumentRequest}
    {heads : List Result}
    (next : Fine dispatch lookup policy ⟨space,
      .work (.argumentBranches live scope original requests heads), stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space, .returning heads,
      .arguments live scope original requests :: stack, emitted⟩ :=
  fine_det (.internal .arguments) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_argumentBranches_nil {original : Entry.Value}
    {requests : List Completed.ArgumentRequest}
    (next : Fine dispatch lookup policy ⟨space, .returning [], stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space,
      .work (.argumentBranches live scope original requests []), stack, emitted⟩ :=
  fine_det (.internal .argumentBranchesNil) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

theorem fine_argumentBranches_continue {original : Entry.Value}
    {requests : List Completed.ArgumentRequest} {head : Result} {heads : List Result}
    (notStopped : ¬ Completed.ArgumentStopped original head)
    (next : Fine dispatch lookup policy ⟨space,
      .work (.arguments (head.1.erase :: live) scope requests head.2),
      .argumentTail head.1 :: .append (.argumentBranches live scope original requests heads) ::
        stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space,
      .work (.argumentBranches live scope original requests (head :: heads)), stack, emitted⟩ :=
  fine_det (.internal (.argumentBranchesContinue notStopped)) (fun z step => by
    cases step with
    | internal l =>
        cases l with
        | argumentBranchesStopped stopped => exact absurd stopped notStopped
        | argumentBranchesContinue _ => rfl) next

theorem fine_argumentTail {head : Entry.Value} {R : List Result}
    (next : Fine dispatch lookup policy ⟨space,
      .returning (R.map (Completed.argumentPrepend head)), stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space, .returning R, .argumentTail head :: stack, emitted⟩ :=
  fine_det (.internal .argumentTail) (fun z step => by
    cases step with
    | internal l => cases l; rfl) next

end Frames

/-! ## Casts and deliveries -/

/-- **A data atom cast under a demand that accepts its one stored type at the frame**: the cast is
the only kind of step, and every cast result is the atom, at whatever frame the renewal reaches. -/
theorem fine_data_cast {atoms : List Atom} {live : List Atom} {scope : List String}
    {stack : List Continuation} {emitted : List Result} {d E T : Atom} (data : DataAtom d)
    (entry : Entry.Rel policy.reentry .active d E .cast)
    (stored : StorageTypesRel (Space.ofList atoms) d [T]) {frame : Frame}
    (renewal : ∃ after, Completed.Frame.TypeRenewRel policy E T frame after)
    (accepts : ∃ output, policy.matching.Rel E T frame.bindings output)
    (next : ∀ after : Frame, Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms,
      .returning [(Entry.Value.ofAtom d, after)], stack, emitted⟩) :
    Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms,
      .work (.atom live scope (Entry.Value.ofAtom d) E frame), stack, emitted⟩ := by
  obtain ⟨after, renewed⟩ := renewal
  refine .step ⟨_, renewed_cast_step dispatch policy (answerable_of_data data).closed entry stored
    frame after renewed live scope stack emitted⟩ ?_
  have entry' : Entry.Rel policy.reentry (frame.read policy (Entry.Value.ofAtom d)).status
      (frame.read policy (Entry.Value.ofAtom d)).erase E .cast := by
    simp only [CompleteRun.read_data policy frame data, Entry.Value.erase_ofAtom, data.status]
    exact entry
  intro y step
  cases step with
  | internal l =>
      cases l with
      | delivered entered => cases Entry.functional entered entry'
      | cast _ batch related =>
          rw [CompleteRun.read_data policy frame data, Entry.Value.erase_ofAtom] at batch related
          cases batch with
          | success _ _ _ _ =>
              obtain ⟨r, rs, first, rest, rfl⟩ := List.forall₂_cons_left_iff.mp related
              obtain rfl := List.forall₂_nil_left_iff.mp rest
              have value : r.1 = Entry.Value.ofAtom d := by
                have payload := first.payload
                split at payload <;> exact payload
              obtain ⟨rv, rf⟩ := r
              simp only at value
              subst value
              exact next rf
          | failure queried rejected =>
              have same := StorageTypesRel.unique
                (show StorageTypesRel (Space.ofList atoms) d _ from queried) stored
              subst same
              obtain ⟨output, matched⟩ := accepts
              exact (rejected T List.mem_cons_self output matched).elim
      | atomTuple entered => cases Entry.functional entered entry'
      | atomFunction entered => cases Entry.functional entered entry'
      | atomFallback entered => cases Entry.functional entered entry'
      | atomSelectionFailed entered => cases Entry.functional entered entry'

/-- A demand whose match keeps the frame's bindings renews the frame unchanged. -/
theorem keeping_renewal {E T : Atom} {frame : Frame}
    (keeps : TypeMatchRel E T frame.bindings frame.bindings) :
    ∃ after, Completed.Frame.TypeRenewRel policy E T frame after :=
  ⟨frame, .unchanged (Completed.Frame.preserved_type_match policy frame keeps)⟩

/-- **The renewal of `if`'s operator at a frame without bindings**, under either matching policy. -/
theorem if_renewal_at (policy : Policy) {frame : Frame} (empty : frame.bindings = Bindings.empty) :
    ∃ after, Completed.Frame.TypeRenewRel policy ifArrow ifArrow frame after := by
  have model : ∃ valuation : String → Atom,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation tEq :=
    ⟨fun _ => Atom.undefinedType, by
      simp [Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied, tEq,
        Bindings.addEquality, Bindings.empty]⟩
  have matched : policy.matching.Rel ifArrow ifArrow frame.bindings tEq := by
    rw [empty]
    cases policy.matching with
    | raw => exact ifArrow_matches
    | finite => exact ⟨ifArrow_matches, model⟩
  obtain ⟨after, _, renewal⟩ := Completed.Frame.TypeRenewRel.of_modelled_match frame matched model
  exact ⟨after, renewal⟩

/-- **A closed atom under the `Atom` demand is delivered as it is**; nothing else can happen. -/
theorem fine_deliver_closed {space : Space} {live : List Atom} {scope : List String}
    {stack : List Continuation} {emitted : List Result} {a : Atom}
    (closed : ∀ name, ¬ AtomOccurs a name) {frame : Frame}
    (next : Fine dispatch lookup policy ⟨space, .returning [(Entry.Value.ofAtom a, frame)], stack,
      emitted⟩) :
    Fine dispatch lookup policy ⟨space,
      .work (.atom live scope (Entry.Value.ofAtom a) Atom.atomType frame), stack, emitted⟩ := by
  have entry : Entry.Rel policy.reentry (frame.read policy (Entry.Value.ofAtom a)).status
      (frame.read policy (Entry.Value.ofAtom a)).erase Atom.atomType .deliver :=
    atom_demand_deliver _
  refine fine_det (.internal (.delivered entry)) (fun z step => ?_)
    (by rw [HERuns.read_closed policy frame closed]; exact next)
  cases step with
  | internal l =>
      cases l with
      | delivered _ => rfl
      | cast entered => cases Entry.functional entered entry
      | atomTuple entered => cases Entry.functional entered entry
      | atomFunction entered => cases Entry.functional entered entry
      | atomFallback entered => cases Entry.functional entered entry
      | atomSelectionFailed entered => cases Entry.functional entered entry

/-! ## The query of `(if b y n)` under `$t` -/

/-- **Every run of the typed query of `(if b y n)` finishes with the taken branch**: whatever
frontier the machine takes (each has one work, the equation of `b`) and whatever unifier output, the
body is read as the taken branch, which meets `$t` by a cast whose every result is that branch. -/
theorem fine_branch_query (notHost : ¬ dispatch.executable (.symbol "if")) {atoms : List Atom}
    (program : IfProgram atoms) {b : Bool} {y n : Atom} (branches : Branches atoms b y n)
    {live : List Atom} {scope : List String} {value : Entry.Value}
    (erased : value.erase = callOf b y n) (activation : Frame) (stack : List Continuation)
    (emitted : List Result)
    (cont : ∀ R : List Result, R.map (fun r => r.1.erase) = [pick b y n] →
      Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms,
      .work (.call live scope value (.var "t") activation), stack, emitted⟩ := by
  have ground := call_ground (b := b) branches.closedYes branches.closedNo
  have notError : ¬ IsErrorRel value.erase := by
    rw [erased]
    rintro ⟨tail, same⟩
    simp at same
  have nonGrounded : NonGroundedCallRel dispatch value.erase := by
    rw [erased]
    refine And.intro ?_ (by simp [Minimal.embeddedInstruction])
    rintro ⟨operator, arguments, same, executable⟩
    simp only [callOf, app, Atom.expression.injEq, List.cons.injEq] at same
    rw [← same.1] at executable
    exact notHost executable
  have notPending : ¬ Completed.FunctionPending policy (Entry.Value.ofAtom (pick b y n)) := by
    rintro ⟨⟨inner, same⟩, _⟩
    rw [Entry.Value.erase_ofAtom] at same
    have data := branches.takenData
    rw [same] at data
    cases data
  have fromFrontier : ∀ works : List EquationWork,
      EquationFrontierRel (Space.ofList atoms) (.var "t" :: live) (callOf b y n)
        activation.bindings works →
      Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms,
        .work (.equations live scope value (.var "t") activation works), stack, emitted⟩ := by
    intro works frontier
    have instances := works_instances_ground policy ground program.rows
      activation.certified.satisfiable frontier
    rw [branches.region] at instances
    obtain ⟨w, ws, ⟨_, reads⟩, rest, rfl⟩ := List.forall₂_cons_right_iff.mp instances
    obtain rfl := List.forall₂_nil_right_iff.mp rest
    have frontier' : EquationFrontierRel (Space.ofList atoms) (.var "t" :: live) value.erase
        activation.bindings [w] := by
      rw [erased]
      exact frontier
    obtain ⟨environments, paired⟩ := Entry.Value.UnifyRel.equation_frontier
      (policy := policy.rebuilding) activation.certified frontier'
    obtain ⟨after, unified, certificate⟩ := forall₂_left_exists paired w List.mem_cons_self
    refine .step ⟨_, .internal (.equationsCons (output := ⟨w.bindings, after, certificate⟩) rfl
      unified)⟩ ?_
    intro z step
    cases step with
    | internal l =>
        cases l with
        | equationsCons sameBindings _ =>
            have readValue := value_of_data branches.takenData (reads _ sameBindings)
            rw [readValue]
            refine fine_boundary_producer notPending ?_
            apply fine_boundaryBatch_frame
            apply fine_boundaryBatch_cons
            apply fine_boundary_returned
            refine fine_returned_evaluate ?_ ?_ ?_
            · simpa [Entry.Value.erase_ofAtom] using branches.takenNotRefused
            · simpa [Entry.Value.erase_ofAtom] using branches.takenData.not_stopped
            refine fine_data_cast branches.takenData (data_var_entry branches.takenData "t")
              branches.takenUndeclared (keeping_renewal (.undefinedRight _ _))
              (variable_meets_undefined "t" _) ?_
            intro final
            apply fine_append
            apply fine_boundaryBatch_nil
            apply fine_prepend
            apply fine_append
            apply fine_equations_nil
            apply fine_prepend
            apply cont
            simp
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms) (.var "t" :: live) (callOf b y n)
    activation.bindings
  have instances := works_instances_ground policy ground program.rows
    activation.certified.satisfiable frontier
  have worksNonempty : works ≠ [] := by
    intro none
    subst none
    rw [branches.region] at instances
    cases instances
  have frontier' : EquationFrontierRel (Space.ofList atoms) (.var "t" :: live) value.erase
      activation.bindings works := by
    rw [erased]
    exact frontier
  refine .step ⟨_, .internal (.callEquations notError nonGrounded frontier' worksNonempty)⟩ ?_
  intro z step
  cases step with
  | internal l =>
      cases l with
      | callError failed => exact absurd failed notError
      | callEmbedded _ _ instruction =>
          rw [erased] at instruction
          simp [Minimal.embeddedInstruction] at instruction
      | callAbsent _ _ frontierEmpty =>
          rw [erased] at frontierEmpty
          have none := works_instances_ground policy ground program.rows
            activation.certified.satisfiable frontierEmpty
          rw [branches.region] at none
          cases none
      | callEquations _ _ frontierW _ =>
          rw [erased] at frontierW
          exact fromFrontier _ frontierW

/-! ## The function application of `(if b y n)` -/

/-- **Every run of the function application of `(if b y n)` finishes with the call value**: the
operator is cast against its arrow, the condition against `Bool`, both branches are delivered under
`Atom` as they are (the branch left is never evaluated), and the call value is assembled. -/
theorem fine_branch_function {atoms : List Atom} (program : IfProgram atoms) {b : Bool}
    {y n : Atom} (closedY : ∀ name, ¬ AtomOccurs y name) (closedN : ∀ name, ¬ AtomOccurs n name)
    {live : List Atom} {scope : List String} {expected : Atom} {signature : SelectedTypePolicy}
    (functionType : signature.functionType = ifArrow) {activation : Frame}
    (empty : activation.bindings = Bindings.empty) (stack : List Continuation)
    (emitted : List Result)
    (cont : ∀ R : List Result, R.map (fun r => r.1.erase) = [callOf b y n] →
      Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms,
      .work (.function live scope expected signature (Entry.Value.ofAtom (.symbol "if"))
        [Entry.Value.ofAtom (.grounded (.bool b)), Entry.Value.ofAtom y, Entry.Value.ofAtom n]
        activation), stack, emitted⟩ := by
  have projections := if_projections functionType
  refine fine_functionStart (by simp [projections.1]) ?_
  rw [projections.1, functionType]
  simp only [List.zip_cons_cons, List.zip_nil_right]
  refine fine_data_cast if_data (symbol_cast_entry (by decide) (by decide) (by decide +kernel))
    program.types (if_renewal_at policy empty) (ifArrow_accepts empty) ?_
  intro frF
  apply fine_functionHeads_frame
  refine fine_functionBranches_continue ?_ ?_
  · simpa using if_data.not_stopped
  apply fine_argumentsCons
  refine fine_data_cast (DataAtom.grounded (.bool b)) (bool_cast_entry b) (bool_types_in _ b)
    (keeping_renewal (bool_matches _)) (bool_accepts _) ?_
  intro fr1
  apply fine_arguments_frame
  refine fine_argumentBranches_continue ?_ ?_
  · rintro ⟨stopped, _⟩
    exact (DataAtom.grounded (.bool b)).not_stopped (by simpa using stopped)
  apply fine_argumentsCons
  refine fine_deliver_closed closedY ?_
  apply fine_arguments_frame
  refine fine_argumentBranches_continue ?_ ?_
  · rintro ⟨_, different⟩
    exact different rfl
  apply fine_argumentsCons
  refine fine_deliver_closed closedN ?_
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
  apply cont
  simp [Completed.functionAssemble, Completed.argumentPrepend, Entry.Value.erase,
    Entry.Value.erase_ofAtom, callOf, app]

/-! ## Every run of `(if b y n)` -/

/-- **Every run of `(if b y n)` from HE's entry finishes**: the admission selects `if`'s arrow (no
other entry rule applies), the function application and the typed query follow. -/
theorem branch_fine (notHost : ¬ dispatch.executable (.symbol "if")) (policy : Policy)
    {atoms : List Atom} (program : IfProgram atoms) {b : Bool} {y n : Atom}
    (branches : Branches atoms b y n) :
    Fine dispatch Completed.rawLookup policy
      (load (Space.ofList atoms) (callOf b y n) Atom.undefinedType) := by
  obtain ⟨Ty, typesY⟩ := branches.typedYes
  obtain ⟨Tn, typesN⟩ := branches.typedNo
  have entry := call_entry policy if_data [.grounded (.bool b), y, n]
  have shape : Completed.Frame.empty.read policy (Entry.Value.ofAtom (callOf b y n)) =
      .expression .active (Entry.Value.ofAtom (.symbol "if") ::
        [Atom.grounded (.bool b), y, n].map Entry.Value.ofAtom) := by
    rw [Completed.Frame.read_empty]
    simp only [callOf, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  have selection : Completed.ArgumentService.historical.selection (Space.ofList atoms)
      Completed.rawLookup policy [] []
      (Completed.Frame.empty.read policy (Entry.Value.ofAtom (callOf b y n))).erase
      (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType Completed.Frame.empty
      (.selected ifPolicy [Completed.Frame.empty]) := by
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom]
    exact branch_selection_succeeds policy program b typesY typesN
  have clean : ∀ R : List Result, R.map (fun r => r.1.erase) = [pick b y n] →
      ∀ r ∈ R, Answerable r.1.erase := by
    intro R eraseR r member
    have inR : r.1.erase ∈ [pick b y n] := by
      rw [← eraseR]
      exact List.mem_map.mpr ⟨r, member, rfl⟩
    rw [List.mem_singleton] at inR
    rw [inR]
    exact answerable_of_data branches.takenData
  show Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms,
    .work (.atom [] [] (Entry.Value.ofAtom (callOf b y n)) Atom.undefinedType Completed.Frame.empty),
    [], []⟩
  refine .step ⟨_, .internal (LocalStepWith.atomFunction (admission := .historical) entry shape
    selection)⟩ ?_
  intro z moved
  cases moved with
  | internal l =>
      cases l with
      | delivered entered => cases Entry.functional entered entry
      | cast entered => cases Entry.functional entered entry
      | atomTuple _ shaped occurs =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          rw [Entry.Value.erase_ofAtom] at occurs
          have same := Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel.unique occurs
            program.types.occurrences
          simp [Atom.undefinedType] at same
      | atomFallback _ shaped chosen =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom]
            at chosen
          obtain ⟨_, _, _, _, impossible⟩ := branch_selection program b typesY typesN chosen
          cases impossible
      | atomSelectionFailed _ shaped chosen =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom]
            at chosen
          obtain ⟨_, _, _, _, impossible⟩ := branch_selection program b typesY typesN chosen
          cases impossible
      | atomFunction _ shaped chosen =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, rfl⟩ := shaped
          rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom]
            at chosen
          obtain ⟨signature, after, functionType, afterBindings, selected⟩ :=
            branch_selection program b typesY typesN chosen
          simp only [Completed.InvocationSelection.selected.injEq] at selected
          obtain ⟨rfl, rfl⟩ := selected
          have returnTypeOf : ∀ {s : SelectedTypePolicy}, s.returnType = .var "t" →
              Completed.invocationReturnType s = .var "t" := by
            intro s same
            simp [Completed.invocationReturnType, same, Atom.expressionType]
          apply fine_invocations_cons
          rw [returnTypeOf (if_projections functionType).2]
          simp only [List.map_cons, List.map_nil]
          refine fine_branch_function program branches.closedYes branches.closedNo functionType
            afterBindings _ _ ?_
          intro R eraseR
          obtain ⟨r, rfl, rErase⟩ : ∃ r, R = [r] ∧ r.1.erase = callOf b y n := by
            obtain ⟨r, sameR, rErase⟩ := List.map_eq_singleton_iff.mp eraseR
            exact ⟨r, sameR, rErase⟩
          apply fine_calls_frame
          apply fine_calls_cons
          refine fine_branch_query notHost program branches rErase r.2 _ _ ?_
          intro Q eraseQ
          apply fine_append
          apply fine_calls_nil
          apply fine_prepend
          apply fine_append
          apply fine_invocations_nil
          apply fine_prepend
          refine fine_publish (clean _ (by simpa using eraseQ)) ?_
          exact fine_top _ _

/-- **Every run of `(if b y n)` finishes, and every finished run publishes the taken branch.** Under
the hypotheses of `IfBranches.branch_every_run`: HE's step relation is well founded from the entry
(no infinite run; the branch left, even a divergent call, never runs), every configuration reachable
from the entry steps or is final, a final one publishes exactly the taken branch, and PeTTa's special
form yields the same from fuel `10` on. -/
theorem branch_every_run_finishes (dispatch : GroundedDispatch)
    (notHost : ¬ dispatch.executable (.symbol "if")) (policy : Policy) {atoms : List Atom}
    (program : IfProgram atoms) {b : Bool} {y n : Atom} (branches : Branches atoms b y n) :
    Acc (fun later earlier => HEStep dispatch Completed.rawLookup policy earlier later)
        (load (Space.ofList atoms) (callOf b y n) Atom.undefinedType) ∧
      (∀ c, Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList atoms) (callOf b y n) Atom.undefinedType) c →
        (∃ z, HEStep dispatch Completed.rawLookup policy c z) ∨
          ∃ emitted : List Result, c = ⟨Space.ofList atoms, .returning [], [], emitted⟩ ∧
            emitted.map (fun r => r.1.erase) = [pick b y n]) ∧
      ∀ k, 10 ≤ k → Streaming.values (Streaming.advance (translate atoms) k
        (Streaming.enter { state := store atoms } (callOf b y n))) = [pick b y n] := by
  have fine := branch_fine notHost policy program branches
  refine ⟨fine.acc, fun c path => ?_, petta_branch atoms branches.groundYes branches.groundNo
    branches.takenData⟩
  rcases (fine.reaches path).progress with moves | ⟨space, emitted, rfl⟩
  · exact Or.inl moves
  · have sameSpace := space_fixed path
    simp only [load, Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual.Configuration.initial]
      at sameSpace
    subst sameSpace
    exact Or.inr ⟨emitted, rfl, branch_source program branches (complete_source path)⟩

/-! ## Controls -/

namespace Controls

open IfBranches.Controls (loopIfRows loop_if_program loop_branches loop_branches_false)
open WholeRunWords.Double (noHost)

/-- **The test `(if True yes (loop))`, every run**: with `(= (loop) (loop))` in the program, HE's
machine has no infinite run from the entry, and every final configuration publishes `yes`. -/
theorem loop_left_finishes (policy : Policy) :
    Acc (fun later earlier => HEStep noHost Completed.rawLookup policy earlier later)
        (load (Space.ofList loopIfRows) (callOf true (sym "yes") (app "loop" []))
          Atom.undefinedType) ∧
      ∀ c, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList loopIfRows) (callOf true (sym "yes") (app "loop" []))
            Atom.undefinedType) c →
        (∃ z, HEStep noHost Completed.rawLookup policy c z) ∨
          ∃ emitted : List Result, c = ⟨Space.ofList loopIfRows, .returning [], [], emitted⟩ ∧
            emitted.map (fun r => r.1.erase) = [sym "yes"] := by
  obtain ⟨acc, every, -⟩ := branch_every_run_finishes noHost (fun impossible => impossible) policy
    loop_if_program loop_branches
  exact ⟨acc, every⟩

/-- The mirror `(if False (loop) no)`: no infinite run, every final configuration publishes `no`. -/
theorem loop_left_false_finishes (policy : Policy) :
    Acc (fun later earlier => HEStep noHost Completed.rawLookup policy earlier later)
      (load (Space.ofList loopIfRows) (callOf false (app "loop" []) (sym "no"))
        Atom.undefinedType) :=
  (branch_every_run_finishes noHost (fun impossible => impossible) policy loop_if_program
    loop_branches_false).1

/-- **Negative control**: the same program and the same `(loop)`, loaded alone, has no such
well-foundedness (`IfBranches.Controls.loop_diverges_alone`); the two facts together say that `if`
is what keeps the left branch from running. -/
theorem loop_contrast (policy : Policy) :
    Acc (fun later earlier => HEStep noHost Completed.rawLookup policy earlier later)
        (load (Space.ofList loopIfRows) (callOf true (sym "yes") (app "loop" []))
          Atom.undefinedType) ∧
      ¬ Acc (fun later earlier => HEStep noHost Completed.rawLookup policy earlier later)
        (load (Space.ofList loopIfRows) (app "loop" []) Atom.undefinedType) :=
  ⟨(loop_left_finishes policy).1, IfBranches.Controls.loop_diverges_alone policy⟩

end Controls

#print axioms fine_data_cast
#print axioms fine_deliver_closed
#print axioms fine_branch_query
#print axioms fine_branch_function
#print axioms branch_fine
#print axioms branch_every_run_finishes
#print axioms Controls.loop_left_finishes
#print axioms Controls.loop_left_false_finishes
#print axioms Controls.loop_contrast

end IfFinishes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
