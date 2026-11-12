import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.IfBagsFinishes

/-!
# `if` at every frame whose class of `t` agrees

Inside an equation body, `if` is evaluated at the frame the body's unifier reached, not at the empty
entry frame. Under the historical (raw) lookup, `IfSharedType` shows how such a frame can bind `if`'s
type variable `t` (a previous `if`, or a body variable renamed to `t`), and that a declared branch is
then rejected. Here the other side: **for undeclared data branches, the frame does not matter**,
provided the class of `t` in the frame has agreeing values (for instance `t` unbound, or bound to one
value).

* `ifArrow_matches_at`, `ifArrow_accepts_at`, `if_renewal_agree`: the operator `if` meets its arrow at
  such a frame (the self-match `$t ≐ $t` is merged by `AddVarEqualityRel.consistent`), with a model;
* `branch_checks_at`, `branch_selection_at`: every admission at any frame selects `if`'s arrow with
  one activation keeping the frame's bindings;
* `fine_branch_function_gen`: `IfFinishes.fine_branch_function` with the operator's acceptance and
  renewal as hypotheses;
* `branch_runs_at`: every run of `(if b y n)` under `%Undefined%` at such a frame, under any
  continuation fine on the taken branch, finishes (H6's relation `Fine`).

## Controls

* `Controls.number_frame_finishes` (positive): at a frame binding `t := Number`, every run of
  `(if True yes (loop))` finishes with `yes`: the undeclared branch meets `$t` by `undefinedRight`
  whatever `t` is bound to. Against `IfSharedType.number_frame_rejects_bool` (negative: at the same
  frame a branch of type `Bool` is rejected).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace IfAtFrames

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel rawTypeLookupRel
  FunctionTypeRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement (TypeBindingSatisfied)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (AtomOccurs MatchRel MergeRel ValuesAgree
  equalityGroundedSemantic semanticLoopFree_empty)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open HEOnTheStep (HEConfig)
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun NestedValues NestedCalls MarkedValues CompoundBindings DeclaredHeads
  DeclaredEveryRun TypedEveryRun AtomDemands IfEveryRun IfBranches EveryRunFinishes IfFinishes
open AnswerBags.Controls (sym app rule rule_consFree)

variable {dispatch : GroundedDispatch} {policy : Policy}

/-! ## The operator at a frame with an agreeing class of `t` -/

/-- The class of `t` in `b` has agreeing values (after recording `t = t`). -/
def TAgrees (b : Bindings) : Prop := ValuesAgree ((b.addEquality "t" "t").classValues "t")

theorem satisfied_addEquality_self {v : String → Atom} {b : Bindings} (x : String)
    (sat : TypeBindingSatisfied v b) : TypeBindingSatisfied v (b.addEquality x x) := by
  refine ⟨fun name value member => sat.1 name value member, fun left right member => ?_⟩
  simp only [Bindings.addEquality, List.mem_append, List.mem_singleton, Prod.mk.injEq] at member
  rcases member with inB | ⟨rfl, rfl⟩
  · exact sat.2 left right inB
  · rfl

/-- The structural match of `if`'s arrow with itself records `$t = $t`. -/
theorem ifArrow_inner : MatchRel equalityGroundedSemantic ifArrow ifArrow tEq :=
  .expression
    (.cons (.symSym "->" semanticLoopFree_empty)
      (MergeRel.mk (order := [])
        (by simp [Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.constraints, Bindings.empty]) .nil)
      (.cons (.symSym "Bool" semanticLoopFree_empty)
        (MergeRel.mk (order := [])
          (by simp [Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.constraints, Bindings.empty]) .nil)
        (.cons (.symSym "Atom" semanticLoopFree_empty)
          (MergeRel.mk (order := [])
            (by simp [Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.constraints, Bindings.empty])
            .nil)
          (.cons (.symSym "Atom" semanticLoopFree_empty)
            (MergeRel.mk (order := [])
              (by simp [Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.constraints, Bindings.empty])
              .nil)
            (.cons (.varVar "t" "t" tEq_loopFree) merge_tEq .nil)))))
    tEq_loopFree

/-- **`$t = $t` merges into bindings whose class of `t` agrees.** -/
theorem merge_tEq_at {b : Bindings} (agree : TAgrees b) :
    MergeRel equalityGroundedSemantic b tEq (b.addEquality "t" "t") :=
  .mk (order := [.equality "t" "t"]) (by decide) (.equality (.consistent rfl agree) .nil)

/-- **`if`'s arrow matches itself at bindings whose class of `t` agrees.** -/
theorem ifArrow_matches_at {b : Bindings} (agree : TAgrees b) :
    TypeMatchRel ifArrow ifArrow b (b.addEquality "t" "t") :=
  .structural (by simp [Atom.undefinedType]) (by simp [Atom.atomType])
    (by simp [Atom.undefinedType]) (by simp [Atom.atomType]) ifArrow_inner (merge_tEq_at agree)

theorem ifArrow_rel_at (policy : Policy) {frame : Frame} (agree : TAgrees frame.bindings) :
    policy.matching.Rel ifArrow ifArrow frame.bindings (frame.bindings.addEquality "t" "t") := by
  obtain ⟨model, sat⟩ := frame.certified.satisfiable
  cases policy.matching with
  | raw => exact ifArrow_matches_at agree
  | finite => exact ⟨ifArrow_matches_at agree, model, satisfied_addEquality_self "t" sat⟩

/-- **`if`'s arrow accepts itself at a frame whose class of `t` agrees.** -/
theorem ifArrow_accepts_at {frame : Frame} (agree : TAgrees frame.bindings) :
    ∃ output, policy.matching.Rel ifArrow ifArrow frame.bindings output :=
  ⟨_, ifArrow_rel_at policy agree⟩

/-- **The renewal of `if`'s operator at a frame whose class of `t` agrees.** -/
theorem if_renewal_agree (policy : Policy) {frame : Frame} (agree : TAgrees frame.bindings) :
    ∃ after, Completed.Frame.TypeRenewRel policy ifArrow ifArrow frame after := by
  obtain ⟨model, sat⟩ := frame.certified.satisfiable
  obtain ⟨after, _, renewal⟩ := Completed.Frame.TypeRenewRel.of_modelled_match frame
    (ifArrow_rel_at policy agree) ⟨model, satisfied_addEquality_self "t" sat⟩
  exact ⟨after, renewal⟩

/-! ## Admission at any frame -/

/-- **Every application check of `(if b y n)` at any frame keeps exactly one activation, with the
frame's bindings.** -/
theorem branch_checks_at {atoms : List Atom} (b : Bool) {y n Ty Tn : Atom}
    (typesY : StorageTypesRel (Space.ofList atoms) y [Ty])
    (typesN : StorageTypesRel (Space.ofList atoms) n [Tn]) {frame : Frame}
    {signature : SelectedTypePolicy} {frames : List Frame} {errors : List Atom}
    (functionType : signature.functionType = ifArrow)
    (checks : Completed.ApplicationChecksRel (Space.ofList atoms)
      (rawTypeLookupRel (Space.ofList atoms)) policy (callOf b y n) Atom.undefinedType signature
      frame frames errors) :
    ∃ after, frames = [after] ∧ after.bindings = frame.bindings := by
  have projections := if_projections functionType
  cases checks with
  | wrongArity shaped arity =>
      simp only [callOf, app, Atom.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl⟩ := shaped
      rw [projections.1] at arity
      exact absurd rfl arity
  | checked shaped arguments returned =>
      simp only [callOf, app, Atom.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl⟩ := shaped
      rw [projections.1] at arguments
      obtain ⟨f1, same1, rest1⟩ := accepted_step (bool_types_in _ b) (fun _ matched =>
        bool_match_output matched) (bool_accepts _) arguments
      obtain ⟨f2, same2, rest2⟩ := accepted_step typesY (fun _ matched =>
        Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeMatchRel.wildcard_output matched
          (Or.inr (Or.inl rfl))) (atom_demand_accepts _ _) rest1
      obtain ⟨f3, same3, rest3⟩ := accepted_step typesN (fun _ matched =>
        Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeMatchRel.wildcard_output matched
          (Or.inr (Or.inl rfl))) (atom_demand_accepts _ _) rest2
      cases rest3
      obtain ⟨returnCheck, rest', returnChecked, nilReturn, rfl⟩ :=
        List.forall₂_cons_left_iff.mp returned
      obtain rfl := List.forall₂_nil_left_iff.mp nilReturn
      cases returnChecked with
      | accepted renewed =>
          refine ⟨_, rfl, ?_⟩
          rw [Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeMatchRel.wildcard_output renewed.source
            (Or.inl rfl), same3, same2, same1]
      | rejected rejectedAll =>
          obtain ⟨output, matched⟩ := undefined_accepts (policy := policy) _ f3
          exact (rejectedAll output matched).elim

/-- **Every admission of `(if b y n)` at any frame selects `if`'s arrow with one activation keeping
the frame's bindings.** -/
theorem branch_selection_at {atoms : List Atom} (program : IfProgram atoms) (b : Bool)
    {y n Ty Tn : Atom} (typesY : StorageTypesRel (Space.ofList atoms) y [Ty])
    (typesN : StorageTypesRel (Space.ofList atoms) n [Tn]) {live : List Atom} {scope : List String}
    {frame : Frame} {outcome : Completed.InvocationSelection}
    (chosenRel : Completed.InvocationSelectionRel (Space.ofList atoms) Completed.rawLookup policy
      live scope (callOf b y n) (.symbol "if") Atom.undefinedType frame outcome) :
    ∃ (signature : SelectedTypePolicy) (after : Frame), signature.functionType = ifArrow ∧
      after.bindings = frame.bindings ∧ outcome = .selected signature [after] := by
  obtain ⟨candidates, queried, scanned⟩ := chosenRel
  have same := StorageTypesRel.unique
    (show StorageTypesRel (Space.ofList atoms) (.symbol "if") candidates from queried) program.types
  cases scanned with
  | nil => cases same
  | nonFunction notArrow _ =>
      simp only [List.cons.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      exact absurd ⟨_, _, ifPolicy.isFunction⟩ notArrow
  | selected checks nonempty =>
      simp only [List.cons.injEq] at same
      obtain ⟨functionType, rfl⟩ := same
      obtain ⟨after, rfl, bindings⟩ := branch_checks_at b typesY typesN functionType checks
      exact ⟨_, after, functionType, bindings, rfl⟩
  | rejected checks rest =>
      simp only [List.cons.injEq] at same
      obtain ⟨functionType, rfl⟩ := same
      obtain ⟨after, impossible, _⟩ := branch_checks_at b typesY typesN functionType checks
      cases impossible

/-- **HE's admission of `(if b y n)` at any frame selects `if`'s arrow.** -/
theorem branch_selection_succeeds_at (policy : Policy) {atoms : List Atom}
    (program : IfProgram atoms) (b : Bool) {y n Ty Tn : Atom}
    (typesY : StorageTypesRel (Space.ofList atoms) y [Ty])
    (typesN : StorageTypesRel (Space.ofList atoms) n [Tn]) (live : List Atom) (scope : List String)
    (frame : Frame) :
    Completed.InvocationSelectionRel (Space.ofList atoms) Completed.rawLookup policy live scope
      (callOf b y n) (.symbol "if") Atom.undefinedType frame (.selected ifPolicy [frame]) :=
  ⟨[ifPolicy.functionType], program.types, .selected
    (.checked (operator := sym "if") (arguments := [.grounded (.bool b), y, n]) rfl
      (.cons (.cons (bool_types_in _ b)
        (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy _
          (bool_matches _)))) .nil) .nil)
        (.cons (.cons typesY
          (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy _
            (.atomLeft _ _)))) .nil) .nil)
          (.cons (.cons typesN
            (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy _
              (.atomLeft _ _)))) .nil) .nil) .nil)))
      (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy _
        (.undefinedLeft _ _)))) .nil))
    (List.cons_ne_nil _ _)⟩

/-! ## The function application with the operator's acceptance as a hypothesis -/

/-- `IfFinishes.fine_branch_function` with the operator's acceptance and renewal at the activation as
hypotheses. -/
theorem fine_branch_function_gen {atoms : List Atom} (program : IfProgram atoms) {b : Bool}
    {y n : Atom} (closedY : ∀ name, ¬ AtomOccurs y name) (closedN : ∀ name, ¬ AtomOccurs n name)
    {live : List Atom} {scope : List String} {expected : Atom} {signature : SelectedTypePolicy}
    (functionType : signature.functionType = ifArrow) {activation : Frame}
    (renewal : ∃ after, Completed.Frame.TypeRenewRel policy ifArrow ifArrow activation after)
    (accepts : ∃ output, policy.matching.Rel ifArrow ifArrow activation.bindings output)
    (stack : List Continuation) (emitted : List Result)
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
    program.types renewal accepts ?_
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

/-! ## Every run at a frame -/

theorem call_closed {b : Bool} {y n : Atom} (closedY : ∀ name, ¬ AtomOccurs y name)
    (closedN : ∀ name, ¬ AtomOccurs n name) : ∀ name, ¬ AtomOccurs (callOf b y n) name := by
  intro name occurs
  cases occurs with
  | expression member inner =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · cases inner
      · cases inner
      · exact closedY name inner
      · exact closedN name inner

/-- **Every run of `(if b y n)` under `%Undefined%` at a frame whose class of `t` agrees finishes**,
under every continuation fine on the taken branch: the frame's bindings never reach the taken
branch's cast (undeclared, it meets `$t` by `undefinedRight`), and the operator's self-match merges. -/
theorem branch_runs_at (notHost : ¬ dispatch.executable (.symbol "if")) (policy : Policy)
    {atoms : List Atom} (program : IfProgram atoms) {b : Bool} {y n : Atom}
    (branches : Branches atoms b y n) {live : List Atom} {scope : List String} {frame : Frame}
    (agree : TAgrees frame.bindings) (stack : List Continuation) (emitted : List Result)
    (cont : ∀ R : List Result, R.map (fun r => r.1.erase) = [pick b y n] →
      Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms,
      .work (.atom live scope (Entry.Value.ofAtom (callOf b y n)) Atom.undefinedType frame), stack,
      emitted⟩ := by
  obtain ⟨Ty, typesY⟩ := branches.typedYes
  obtain ⟨Tn, typesN⟩ := branches.typedNo
  have readC : frame.read policy (Entry.Value.ofAtom (callOf b y n)) =
      Entry.Value.ofAtom (callOf b y n) :=
    HERuns.read_closed policy frame (call_closed branches.closedYes branches.closedNo)
  have entry : Entry.Rel policy.reentry (frame.read policy (Entry.Value.ofAtom (callOf b y n))).status
      (frame.read policy (Entry.Value.ofAtom (callOf b y n))).erase Atom.undefinedType
      .interpret := by
    have atEmpty := call_entry policy if_data [.grounded (.bool b), y, n]
    rw [Completed.Frame.read_empty] at atEmpty
    rw [readC]
    exact atEmpty
  have shape : frame.read policy (Entry.Value.ofAtom (callOf b y n)) =
      .expression .active (Entry.Value.ofAtom (.symbol "if") ::
        [Atom.grounded (.bool b), y, n].map Entry.Value.ofAtom) := by
    rw [readC]
    simp only [callOf, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  have selection : Completed.ArgumentService.historical.selection (Space.ofList atoms)
      Completed.rawLookup policy live scope
      (frame.read policy (Entry.Value.ofAtom (callOf b y n))).erase
      (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType frame
      (.selected ifPolicy [frame]) := by
    rw [readC, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom]
    exact branch_selection_succeeds_at policy program b typesY typesN live scope frame
  have clean : ∀ R : List Result, R.map (fun r => r.1.erase) = [pick b y n] →
      ∀ r ∈ R, Answerable r.1.erase := by
    intro R eraseR r member
    have inR : r.1.erase ∈ [pick b y n] := by
      rw [← eraseR]
      exact List.mem_map.mpr ⟨r, member, rfl⟩
    rw [List.mem_singleton] at inR
    rw [inR]
    exact answerable_of_data branches.takenData
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
          rw [readC, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosen
          obtain ⟨_, _, _, _, impossible⟩ := branch_selection_at program b typesY typesN chosen
          cases impossible
      | atomSelectionFailed _ shaped chosen =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          rw [readC, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosen
          obtain ⟨_, _, _, _, impossible⟩ := branch_selection_at program b typesY typesN chosen
          cases impossible
      | atomFunction _ shaped chosen =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, rfl⟩ := shaped
          rw [readC, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosen
          obtain ⟨signature, after, functionType, afterBindings, selected⟩ :=
            branch_selection_at program b typesY typesN chosen
          simp only [Completed.InvocationSelection.selected.injEq] at selected
          obtain ⟨rfl, rfl⟩ := selected
          have agreeAfter : TAgrees after.bindings := by
            rw [afterBindings]
            exact agree
          have returnTypeOf : ∀ {s : SelectedTypePolicy}, s.returnType = .var "t" →
              Completed.invocationReturnType s = .var "t" := by
            intro s same
            simp [Completed.invocationReturnType, same, Atom.expressionType]
          apply fine_invocations_cons
          rw [returnTypeOf (if_projections functionType).2]
          simp only [List.map_cons, List.map_nil]
          refine fine_branch_function_gen program branches.closedYes branches.closedNo functionType
            (if_renewal_agree policy agreeAfter) (ifArrow_accepts_at agreeAfter) _ _ ?_
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
          apply cont
          rw [publish_erase]
          simpa using eraseQ

/-- **Every derivation of HE's completed relation for `(if b y n)` under `%Undefined%` at a frame
whose class of `t` agrees publishes the taken branch**, from any live list and scope. -/
theorem branch_source_at {atoms : List Atom} (program : IfProgram atoms) {b : Bool} {y n : Atom}
    (branches : Branches atoms b y n) {live : List Atom} {scope : List String} {frame : Frame}
    (agree : TAgrees frame.bindings) {results : List Result}
    (derived : Completed.AtomRel (Space.ofList atoms) dispatch Completed.rawLookup live scope
      (Entry.Value.ofAtom (callOf b y n)) Atom.undefinedType frame results (policy := policy)) :
    results.map (fun r => r.1.erase) = [pick b y n] := by
  obtain ⟨Ty, typesY⟩ := branches.typedYes
  obtain ⟨Tn, typesN⟩ := branches.typedNo
  have readC : frame.read policy (Entry.Value.ofAtom (callOf b y n)) =
      Entry.Value.ofAtom (callOf b y n) :=
    HERuns.read_closed policy frame (call_closed branches.closedYes branches.closedNo)
  have entry : Entry.Rel policy.reentry (frame.read policy (Entry.Value.ofAtom (callOf b y n))).status
      (frame.read policy (Entry.Value.ofAtom (callOf b y n))).erase Atom.undefinedType
      .interpret := by
    have atEmpty := call_entry policy if_data [.grounded (.bool b), y, n]
    rw [Completed.Frame.read_empty] at atEmpty
    rw [readC]
    exact atEmpty
  have shape : frame.read policy (Entry.Value.ofAtom (callOf b y n)) =
      .expression .active (Entry.Value.ofAtom (.symbol "if") ::
        [Atom.grounded (.bool b), y, n].map Entry.Value.ofAtom) := by
    rw [readC]
    simp only [callOf, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  have outcome : ∀ {result : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList atoms) Completed.rawLookup policy live scope
        (frame.read policy (Entry.Value.ofAtom (callOf b y n))).erase
        (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType frame result →
      ∃ (signature : SelectedTypePolicy) (after : Frame), signature.functionType = ifArrow ∧
        after.bindings = frame.bindings ∧ result = .selected signature [after] := by
    intro result chosenRel
    rw [readC, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosenRel
    exact branch_selection_at program b typesY typesN chosenRel
  have readY : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom y) = Entry.Value.ofAtom y :=
    fun frame => HERuns.read_closed policy frame branches.closedYes
  have readN : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom n) = Entry.Value.ofAtom n :=
    fun frame => HERuns.read_closed policy frame branches.closedNo
  cases derived with
  | delivered entered => cases Entry.functional entered entry
  | cast entered => cases Entry.functional entered entry
  | tuple _ shaped occurs _ _ _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      rw [Entry.Value.erase_ofAtom] at occurs
      have same := Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel.unique occurs
        program.types.occurrences
      simp [Atom.undefinedType] at same
  | fallback _ shaped chosenRel _ _ _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      obtain ⟨_, _, _, _, impossible⟩ := outcome chosenRel
      cases impossible
  | selectionFailed _ shaped chosenRel _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      obtain ⟨_, _, _, _, impossible⟩ := outcome chosenRel
      cases impossible
  | function _ shaped chosenRel invoked priority =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, rfl⟩ := shaped
      obtain ⟨signature, after, functionType, afterBindings, selected⟩ := outcome chosenRel
      simp only [Completed.InvocationSelection.selected.injEq] at selected
      obtain ⟨rfl, rfl⟩ := selected
      have agreeAfter : TAgrees after.bindings := by
        rw [afterBindings]
        exact agree
      have projections := if_projections functionType
      have returnTypeOf : ∀ {s : SelectedTypePolicy}, s.returnType = .var "t" →
          Completed.invocationReturnType s = .var "t" := by
        intro s same
        simp [Completed.invocationReturnType, same, Atom.expressionType]
      have returnType := returnTypeOf projections.2
      cases invoked with
      | cons function calls rest =>
          cases rest
          cases function with
          | evaluated _ operatorRel branchesRel =>
              rw [functionType] at operatorRel
              obtain ⟨frF, rfl⟩ := typed_cast_source_at if_data
                (symbol_cast_entry (by decide) (by decide) (by decide +kernel)) program.types
                (ifArrow_accepts_at agreeAfter) operatorRel
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
                      obtain ⟨fr1, rfl⟩ := typed_cast_source (.grounded (.bool b)) (bool_cast_entry b)
                        (bool_types_in _ b) bool_accepts conditionRel
                      cases conditionBranches with
                      | stopped stopped _ =>
                          obtain ⟨stoppedCondition, _⟩ := stopped
                          rw [Entry.Value.erase_ofAtom] at stoppedCondition
                          exact absurd stoppedCondition (DataAtom.grounded (.bool b)).not_stopped
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
                                                      [Entry.Value.ofAtom (.grounded (.bool b)),
                                                        Entry.Value.ofAtom y,
                                                        Entry.Value.ofAtom n], frame)).1.erase =
                                                    callOf b y n := fun frame => by
                                                simp [Completed.functionAssemble, Entry.Value.erase,
                                                  Entry.Value.erase_ofAtom, callOf, app]
                                              have answered := branch_call_source program branches
                                                (assembled _) callRel
                                              exact publish_answers
                                                (by simp only [List.append_nil]; exact answered)
                                                (fun a member => by
                                                  rw [List.mem_singleton] at member
                                                  subst member
                                                  exact answerable_of_data branches.takenData)
                                                priority

/-- **A `Fine` configuration reaches a final one**: following any step from each configuration. -/
theorem Fine.exists_final {lookup : CastLookup} {x : HEConfig}
    (fine : Fine dispatch lookup policy x) :
    ∃ (space : Space) (emitted : List Result),
      Relation.ReflTransGen (HEStep dispatch lookup policy) x ⟨space, .returning [], [], emitted⟩ := by
  induction fine with
  | final => exact ⟨_, _, .refl⟩
  | step moves _ ih =>
      obtain ⟨y, step⟩ := moves
      obtain ⟨space, emitted, path⟩ := ih y step
      exact ⟨space, emitted, .head step path⟩

/-! ## Controls -/

namespace Controls

open IfBranches.Controls (loopIfRows loop_if_program loop_branches)
open IfSharedType (numberFrame)
open WholeRunWords.Double (noHost)

/-- At a frame binding `t := Number`, the class of `t` agrees. -/
theorem number_agrees : TAgrees numberFrame := by
  unfold TAgrees
  have values : (numberFrame.addEquality "t" "t").classValues "t" = [sym "Number"] := by decide
  rw [values]
  simp [ValuesAgree]

/-- **Positive control**: at every frame binding `t := Number` (and nothing else), every run of
`(if True yes (loop))` under `%Undefined%`, under every continuation fine on `[yes]`, finishes. A
branch of type `Bool` would be rejected at the same frame (`IfSharedType.number_frame_rejects_bool`);
the undeclared `yes` is not. -/
theorem number_frame_finishes (policy : Policy) {frame : Frame} (bound : frame.bindings = numberFrame)
    (live : List Atom) (scope : List String) (stack : List Continuation) (emitted : List Result)
    (cont : ∀ R : List Result, R.map (fun r => r.1.erase) = [sym "yes"] →
      Fine noHost Completed.rawLookup policy ⟨Space.ofList loopIfRows, .returning R, stack,
        emitted⟩) :
    Fine noHost Completed.rawLookup policy ⟨Space.ofList loopIfRows,
      .work (.atom live scope (Entry.Value.ofAtom (callOf true (sym "yes") (app "loop" [])))
        Atom.undefinedType frame), stack, emitted⟩ :=
  branch_runs_at (fun impossible => impossible) policy loop_if_program loop_branches
    (by rw [bound]; exact number_agrees) stack emitted cont

/-- **Positive control, every derivation**: at every frame binding `t := Number`, every derivation of
HE's completed relation for `(if True yes (loop))` publishes `yes`. -/
theorem number_frame_source (policy : Policy) {frame : Frame} (bound : frame.bindings = numberFrame)
    {live : List Atom} {scope : List String} {results : List Result}
    (derived : Completed.AtomRel (Space.ofList loopIfRows) noHost Completed.rawLookup live scope
      (Entry.Value.ofAtom (callOf true (sym "yes") (app "loop" []))) Atom.undefinedType frame
      results (policy := policy)) :
    results.map (fun r => r.1.erase) = [sym "yes"] :=
  branch_source_at loop_if_program loop_branches (by rw [bound]; exact number_agrees) derived

end Controls

#print axioms ifArrow_matches_at
#print axioms ifArrow_accepts_at
#print axioms if_renewal_agree
#print axioms branch_checks_at
#print axioms branch_selection_at
#print axioms branch_selection_succeeds_at
#print axioms fine_branch_function_gen
#print axioms branch_runs_at
#print axioms branch_source_at
#print axioms Fine.exists_final
#print axioms Controls.number_frame_finishes
#print axioms Controls.number_frame_source

end IfAtFrames

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
