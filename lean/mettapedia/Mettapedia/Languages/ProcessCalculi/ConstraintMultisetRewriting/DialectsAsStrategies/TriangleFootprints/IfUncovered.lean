import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.IfBags

/-!
# A named difference: a computed condition with no answer

On `{(: if (-> Bool Atom Atom $t)), (= (if True $then $else) $then),
(= (if False $then $else) $else), (= (isZero 0) True)}`, take `(if (isZero 1) yes no)`. No row of
`isZero` matches `(isZero 1)`.

* **HE** treats a call no row matches as its own answer (`FragmentDifferences`, uncovered): the
  condition evaluates under `Bool` to `(isZero 1)` itself, which `Bool` accepts (its type is
  `%Undefined%`). No row of `if` matches `(if (isZero 1) yes no)` either, so the query of `if` returns
  the call: every complete run publishes `(if (isZero 1) yes no)`.
* **PeTTa** gives the condition no answer (no clause matches, the call fails), so its branch frame
  never runs: the run ends with no value.

The reason is the design split of `FragmentDifferences` (an unreduced call is HE's answer, a failure
in PeTTa) composed with `IfDifference` (HE's `if` has rows only for `True` and `False`).

* `isZero_one_bool`: every derivation of `(isZero 1)` under `Bool` returns `(isZero 1)`, and a run
  exists.
* `uncovered_source`, `uncovered_run`: every complete HE run publishes the `if` call itself; one
  exists.
* `uncovered_condition_differs`: the difference on every run, PeTTa's empty result computed at fuel 8.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace IfUncovered

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
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst isGroundAtom)
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun NestedValues NestedCalls MarkedValues CompoundBindings DeclaredHeads
  DeclaredEveryRun TypedEveryRun AtomDemands IfEveryRun IfBranches DemandSpine IfComputed
  IfCallBranches
open AnswerBags.Controls (sym app rule rule_consFree)
open IfComputed.Controls (num)
open WholeRunWords.Double (noHost)

/-- HE's `if` and `(= (isZero 0) True)`. -/
abbrev uncoveredRows : List Atom :=
  ifProgram ++ [rule (app "isZero" [num 0]) (.grounded (.bool true))]

/-- `(isZero 1)`. -/
abbrev condition : Atom := app "isZero" [num 1]

/-- `(if (isZero 1) yes no)`. -/
abbrev uncoveredCall : Atom := callC condition (sym "yes") (sym "no")

theorem uncovered_types_if : StorageTypesRel (Space.ofList uncoveredRows) (.symbol "if") [ifArrow] :=
  .symbolKnown (.hit (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same)
    (.skip (fun _ same => by simp at same) .nil)))) (by simp)

theorem uncovered_rows : ScopedProgram uncoveredRows := by
  intro row member
  rcases List.mem_append.mp member with inIf | inZero
  · exact if_program row inIf
  · simp only [List.mem_singleton] at inZero
    subst inZero
    refine ⟨rule_consFree fun a inside => ?_, fun lhs rhs same => ?_⟩
    · simp only [List.mem_singleton] at inside
      subst inside
      exact .grounded _
    · cases same
      decide

theorem uncovered_program : IfProgram uncoveredRows := ⟨uncovered_types_if, uncovered_rows⟩

theorem isZero_data : DataAtom (.symbol "isZero") := .symbol (by decide) (by decide)

theorem condition_answerable : Answerable condition :=
  call_answerable isZero_data fun a member => by
    rw [List.mem_singleton] at member
    subst member
    exact .grounded _

theorem condition_untyped :
    (Space.ofList uncoveredRows).atoms.filter (typeRegion (.symbol "isZero")) = [] := by
  decide +kernel

theorem condition_absent : regionBodies uncoveredRows "isZero" [num 1] = [] := by
  decide +kernel

theorem symbol_undeclared (name : String) (notIf : name ≠ "if") :
    StorageTypesRel (Space.ofList uncoveredRows) (sym name) [Atom.undefinedType] :=
  .symbolUndefined (.skip (fun _ same => by cases same; exact notIf rfl)
    (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same)
      (.skip (fun _ same => by simp at same) .nil))))

theorem condition_types :
    StorageTypesRel (Space.ofList uncoveredRows) condition [Atom.undefinedType] :=
  .expressionUndefined (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same)
    (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same) .nil))))

/-! ## The condition under `Bool` -/

/-- **`(isZero 1)` under `Bool`**: HE's machine evaluates it to itself, and every derivation
returns itself; no row matches, so the query returns the call. -/
theorem isZero_one_bool (policy : Policy) :
    HERunsAt noHost policy uncoveredRows (sym "Bool") (Entry.Value.ofAtom condition) [condition] ∧
      RunsDeterminedAt noHost policy uncoveredRows (sym "Bool") (Entry.Value.ofAtom condition)
        [condition] := by
  have shape : Entry.Value.ofAtom condition =
      .expression .active (.symbol "isZero" :: [Entry.Value.ofAtom (num 1)]) := by
    simp [condition, app, Entry.Value.ofAtom]
  have numData : DataAtom (num 1) := .grounded _
  have combosEq : combos [[num 1]] = [[num 1]] := rfl
  have runs := he_nested_at (dispatch := noHost) (policy := policy) (atoms := uncoveredRows)
    bool_transparent isZero_data condition_untyped condition_answerable.closed
    (readiness := .active) (vs := [Entry.Value.ofAtom (num 1)]) (Or.inr rfl) (by simp)
    (Ls := [[num 1]])
    (.cons ⟨he_data_M raw_answers uncoveredRows numData _ (Entry.Value.erase_ofAtom _)
      (marked_ofAtom _), fun a member => by
        rw [List.mem_singleton] at member
        subst member
        exact answerable_of_data numData⟩ .nil)
    (fun vals => [.expression (.symbol "isZero" :: vals)])
    (fun vals member => by
      rw [combosEq, List.mem_singleton] at member
      subst member
      refine ⟨fun live scope activation value erased stack emitted => ?_, fun a inside => ?_⟩
      · exact ⟨[(value, activation)], by simp [erased],
          he_query_absent_at (scoped_consFree uncovered_rows) isZero_data
            (fun impossible => impossible) (by decide) (fun v inside => by
              rw [List.mem_singleton] at inside
              subst inside
              rfl) condition_absent live scope activation value erased stack emitted⟩
      · rw [List.mem_singleton] at inside
        subst inside
        exact condition_answerable)
  have determined := nested_determined_at (dispatch := noHost) (policy := policy)
    (atoms := uncoveredRows) bool_transparent isZero_data condition_untyped
    condition_answerable.closed (readiness := .active) (vs := [Entry.Value.ofAtom (num 1)])
    (by simp) (Ls := [[num 1]])
    (.cons ⟨fun a member => by
        rw [List.mem_singleton] at member
        subst member
        exact answerable_of_data numData,
      fun live scope frame results derived =>
        data_determined_M numData _ (Entry.Value.erase_ofAtom _) (marked_ofAtom _) live scope frame
          results derived⟩ .nil)
    (fun vals => [.expression (.symbol "isZero" :: vals)])
    (fun vals member => by
      rw [combosEq, List.mem_singleton] at member
      subst member
      exact ⟨fun a inside => by
          rw [List.mem_singleton] at inside
          subst inside
          exact condition_answerable,
        query_absent_at (scoped_consFree uncovered_rows) isZero_data (by decide)
          (fun v inside => by
            rw [List.mem_singleton] at inside
            subst inside
            exact answerable_of_data numData) condition_absent⟩)
    (fun impossible _ => by cases impossible)
  rw [shape]
  exact ⟨by simpa [combosEq] using runs, by simpa [combosEq] using determined⟩

/-! ## The query of the `if` call -/

theorem call_ground : ∀ a ∈ [condition, sym "yes", sym "no"], TypeSubst.typeVars a = [] := by
  intro a member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact HERuns.ground_typeVars condition_answerable
  · rfl
  · rfl

theorem if_region_empty : regionSides uncoveredRows "if" [condition, sym "yes", sym "no"] = [] := by
  decide +kernel

/-- **No row of `if` matches**: every derivation of the query of a call value whose atom is
`(if (isZero 1) yes no)` returns the call value. -/
theorem uncovered_call_source {policy : Policy} {live : List Atom} {scope : List String}
    {value : Entry.Value} {expected : Atom} {frame : Frame} {children : List Result}
    (erased : value.erase = uncoveredCall)
    (called : Completed.CallRel (Space.ofList uncoveredRows) noHost Completed.rawLookup live scope
      value expected frame children (policy := policy)) :
    children = [(value, frame)] := by
  cases called with
  | error _ => rfl
  | embedded _ _ instruction _ _ =>
      rw [erased] at instruction
      simp [Minimal.embeddedInstruction] at instruction
  | absent _ _ _ => rfl
  | equations _ _ frontier nonempty _ =>
      rw [erased] at frontier
      have sidesEq := frontier_sides call_ground frame.certified.satisfiable
        (scoped_consFree uncovered_rows) frontier
      rw [if_region_empty] at sidesEq
      exact absurd (List.map_eq_nil_iff.mp sidesEq) nonempty

theorem uncovered_answerable : Answerable uncoveredCall :=
  app_answerable if_data fun a member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact condition_answerable
    · exact answerable_of_data (.symbol (by decide) (by decide))
    · exact answerable_of_data (.symbol (by decide) (by decide))

theorem single_result {heads : List Result} {a : Atom}
    (erased : heads.map (fun r => r.1.erase) = [a]) : ∃ h, heads = [h] ∧ h.1.erase = a := by
  cases heads with
  | nil => simp at erased
  | cons h hs =>
      cases hs with
      | cons _ _ => simp at erased
      | nil => exact ⟨h, rfl, by simpa using erased⟩

/-! ## Every derivation and a complete run -/

theorem readClosed (policy : Policy) (name : String) (frame : Frame) :
    frame.read policy (Entry.Value.ofAtom (sym name)) = Entry.Value.ofAtom (sym name) :=
  HERuns.read_closed policy frame (closed_symbol name)

/-- **Every derivation of HE's completed relation for `(if (isZero 1) yes no)` publishes the call
itself.** -/
theorem uncovered_source {policy : Policy} {results : List Result}
    (derived : Completed.AtomRel (Space.ofList uncoveredRows) noHost Completed.rawLookup [] []
      (Entry.Value.ofAtom uncoveredCall) Atom.undefinedType Completed.Frame.empty results
      (policy := policy)) :
    results.map (fun r => r.1.erase) = [uncoveredCall] := by
  have conditionDetermined := (isZero_one_bool policy).2
  have entry := call_entry policy if_data [condition, sym "yes", sym "no"]
  have shape : Completed.Frame.empty.read policy (Entry.Value.ofAtom uncoveredCall) =
      .expression .active (Entry.Value.ofAtom (.symbol "if") ::
        [condition, sym "yes", sym "no"].map Entry.Value.ofAtom) := by
    rw [Completed.Frame.read_empty]
    simp only [uncoveredCall, callC, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  have keeps : ∀ bnd out : Bindings, TypeMatchRel (sym "Bool") Atom.undefinedType bnd out →
      out = bnd := fun _ _ matched =>
    Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeMatchRel.wildcard_output matched
      (Or.inr (Or.inr (Or.inl rfl)))
  have outcome : ∀ {result : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList uncoveredRows) Completed.rawLookup policy [] []
        (Completed.Frame.empty.read policy (Entry.Value.ofAtom uncoveredCall)).erase
        (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType Completed.Frame.empty result →
      ∃ (signature : SelectedTypePolicy) (after : Frame), signature.functionType = ifArrow ∧
        after.bindings = Bindings.empty ∧ result = .selected signature [after] := by
    intro result chosenRel
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosenRel
    exact cond_selection ⟨uncovered_types_if, fun row member => by
        rcases List.mem_append.mp member with inIf | inZero
        · rcases List.mem_cons.mp inIf with rfl | inRest
          · exact ⟨fun lhs rhs same => by simp at same, fun lhs rhs same => by simp at same⟩
          · rcases List.mem_cons.mp inRest with rfl | inLast
            · refine ⟨rule_consFree fun a inside => ?_, fun lhs rhs same => ?_⟩
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
                rcases inside with rfl | rfl | rfl
                · exact .grounded _
                · exact .var _
                · exact .var _
              · cases same
                exact ⟨by decide, .item (.var _)⟩
            · simp only [List.mem_singleton] at inLast
              subst inLast
              refine ⟨rule_consFree fun a inside => ?_, fun lhs rhs same => ?_⟩
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
                rcases inside with rfl | rfl | rfl
                · exact .grounded _
                · exact .var _
                · exact .var _
              · cases same
                exact ⟨by decide, .item (.var _)⟩
        · simp only [List.mem_singleton] at inZero
          subst inZero
          refine ⟨rule_consFree fun a inside => ?_, fun lhs rhs same => ?_⟩
          · simp only [List.mem_singleton] at inside
            subst inside
            exact .grounded _
          · cases same
            exact ⟨by decide, .item (.grounded _)⟩⟩
      condition_types (fun _ => .undefinedRight _ _) keeps (symbol_undeclared "yes" (by decide))
      (symbol_undeclared "no" (by decide)) chosenRel
  cases derived with
  | delivered entered => cases Entry.functional entered entry
  | cast entered => cases Entry.functional entered entry
  | tuple _ shaped occurs _ _ _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      rw [Entry.Value.erase_ofAtom] at occurs
      have same := Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel.unique occurs
        uncovered_types_if.occurrences
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
      have projections := if_projections functionType
      cases invoked with
      | cons function calls rest =>
          cases rest
          cases function with
          | evaluated _ operatorRel branchesRel =>
              rw [functionType] at operatorRel
              obtain ⟨frF, rfl⟩ := typed_cast_source_at if_data
                (symbol_cast_entry (by decide) (by decide) (by decide +kernel)) uncovered_types_if
                (ifArrow_accepts afterBindings) operatorRel
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
                      have conditionErase := conditionDetermined _ _ _ _ conditionRel
                      obtain ⟨h, rfl, hErase⟩ := single_result conditionErase
                      cases conditionBranches with
                      | stopped stopped _ =>
                          obtain ⟨stoppedCondition, _⟩ := stopped
                          rw [hErase] at stoppedCondition
                          exact absurd stoppedCondition condition_answerable.notStopped
                      | continuing _ yesArguments restCondition =>
                          cases restCondition
                          cases yesArguments with
                          | cons yesRel yesBranches =>
                              have yesDelivered := atom_demand_source yesRel
                              subst yesDelivered
                              rw [readClosed] at yesBranches
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
                                      rw [readClosed] at noBranches
                                      cases noBranches with
                                      | stopped stopped _ =>
                                          obtain ⟨_, different⟩ := stopped
                                          exact absurd rfl different
                                      | continuing _ packets restNo =>
                                          cases restNo
                                          cases packets
                                          simp only [List.map_cons, List.map_nil, List.append_nil,
                                            Completed.argumentPrepend_packet] at calls
                                          cases calls with
                                          | cons callRel restCalls =>
                                              cases restCalls
                                              have valueErase : (Completed.functionAssemble
                                                  (Entry.Value.ofAtom (.symbol "if"))
                                                  (Entry.Value.argumentPacket
                                                    [h.1, Entry.Value.ofAtom (sym "yes"),
                                                      Entry.Value.ofAtom (sym "no")], h.2)).1.erase =
                                                  uncoveredCall := by
                                                simp [Completed.functionAssemble,
                                                  Entry.Value.argumentPacket,
                                                  Entry.Value.unpackArguments, Entry.Value.erase,
                                                  Entry.Value.erase_ofAtom, hErase, uncoveredCall,
                                                  callC, app]
                                              obtain rfl := uncovered_call_source valueErase callRel
                                              exact publish_answers (by simp [valueErase])
                                                (fun a member => by
                                                  rw [List.mem_singleton] at member
                                                  subst member
                                                  exact uncovered_answerable)
                                                priority

/-- **The function application of `(if (isZero 1) yes no)`**: the condition runs under `Bool` to
itself, both branches are delivered, and the call value is assembled. -/
theorem uncovered_function_segment (policy : Policy) (stack : List Continuation) :
    ∃ results : List Result,
      HERuns.HESteps noHost Completed.rawLookup policy
        ⟨Space.ofList uncoveredRows, .work (.function [Completed.invocationReturnType ifPolicy] []
          Atom.undefinedType ifPolicy (Entry.Value.ofAtom (.symbol "if"))
          [Entry.Value.ofAtom condition, Entry.Value.ofAtom (sym "yes"),
            Entry.Value.ofAtom (sym "no")] Completed.Frame.empty), stack, []⟩
        ⟨Space.ofList uncoveredRows, .returning results, stack, []⟩ ∧
      ∃ value activation, results = [(value, activation)] ∧ value.erase = uncoveredCall := by
  obtain ⟨frF, renewal⟩ := if_operator_renewal policy
  have ifCast := renewed_cast_step noHost policy (atom := .symbol "if") (closed_symbol "if")
    (symbol_cast_entry (by decide) (by decide) (by decide +kernel)) uncovered_types_if
    Completed.Frame.empty frF renewal
  obtain ⟨R, eraseR, conditionRun⟩ := (isZero_one_bool policy).1
    (Completed.argumentScope (requestsOf condition (sym "yes") (sym "no")).tail ++
      [(Entry.Value.ofAtom (.symbol "if")).erase, Completed.invocationReturnType ifPolicy])
    [] frF
    (.arguments [(Entry.Value.ofAtom (.symbol "if")).erase, Completed.invocationReturnType ifPolicy]
        [] (Entry.Value.ofAtom condition) (requestsOf condition (sym "yes") (sym "no")).tail ::
      .functionAssemble (Entry.Value.ofAtom (.symbol "if")) ::
      .append (.functionBranches [Completed.invocationReturnType ifPolicy] []
        (requestsOf condition (sym "yes") (sym "no")) []) :: stack) []
  obtain ⟨h, rfl, hErase⟩ := single_result eraseR
  apply Exists.intro
  refine ⟨?_, ?_⟩
  · refine .head (.internal (.functionStart rfl)) ?_
    refine .head (ifCast _ _ _ _) ?_
    refine .head (.internal .functionHeads) ?_
    refine .head (.internal (.functionBranchesContinue ?_)) ?_
    · simpa using if_data.not_stopped
    refine .head (.internal .argumentsCons) ?_
    refine .trans conditionRun ?_
    refine .head (.internal .arguments) ?_
    refine .head (.internal (.argumentBranchesContinue ?_)) ?_
    · rintro ⟨stopped, _⟩
      rw [hErase] at stopped
      exact condition_answerable.notStopped stopped
    refine .head (.internal .argumentsCons) ?_
    refine .head (.internal (.delivered (atom_demand_deliver _))) ?_
    refine .head (.internal .arguments) ?_
    refine .head (.internal (.argumentBranchesContinue ?_)) ?_
    · rintro ⟨_, different⟩
      simp only [readClosed] at different
      exact different rfl
    refine .head (.internal .argumentsCons) ?_
    refine .head (.internal (.delivered (atom_demand_deliver _))) ?_
    refine .head (.internal .arguments) ?_
    refine .head (.internal (.argumentBranchesContinue ?_)) ?_
    · rintro ⟨_, different⟩
      simp only [readClosed] at different
      exact different rfl
    refine .head (.internal .argumentsNil) ?_
    refine .head (.internal .argumentTail) ?_
    refine .head (.internal .append) ?_
    refine .head (.internal .argumentBranchesNil) ?_
    refine .head (.internal .prepend) ?_
    refine .head (.internal .argumentTail) ?_
    refine .head (.internal .append) ?_
    refine .head (.internal .argumentBranchesNil) ?_
    refine .head (.internal .prepend) ?_
    refine .head (.internal .argumentTail) ?_
    refine .head (.internal .append) ?_
    refine .head (.internal .argumentBranchesNil) ?_
    refine .head (.internal .prepend) ?_
    refine .head (.internal .functionAssemble) ?_
    refine .head (.internal .append) ?_
    refine .head (.internal .functionBranchesNil) ?_
    exact .single (.internal .prepend)
  · refine ⟨_, _, rfl, ?_⟩
    simp [Entry.Value.erase, Entry.Value.erase_ofAtom, readClosed, hErase, uncoveredCall, callC,
      app]

/-- **A complete run of `(if (isZero 1) yes no)` on HE's machine, publishing the call itself.** -/
theorem uncovered_run (policy : Policy) :
    ∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList uncoveredRows) uncoveredCall Atom.undefinedType)
          ⟨Space.ofList uncoveredRows, .returning [], [], heAnswers⟩ ∧
        heAnswers.map (fun r => r.1.erase) = [uncoveredCall] := by
  have entry := call_entry policy if_data [condition, sym "yes", sym "no"]
  have shape : Completed.Frame.empty.read policy (Entry.Value.ofAtom uncoveredCall) =
      .expression .active (Entry.Value.ofAtom (.symbol "if") ::
        [condition, sym "yes", sym "no"].map Entry.Value.ofAtom) := by
    rw [Completed.Frame.read_empty]
    simp only [uncoveredCall, callC, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  have selection : Completed.ArgumentService.historical.selection (Space.ofList uncoveredRows)
      Completed.rawLookup policy [] []
      (Completed.Frame.empty.read policy (Entry.Value.ofAtom uncoveredCall)).erase
      (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType Completed.Frame.empty
      (.selected ifPolicy [Completed.Frame.empty]) := by
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom]
    obtain ⟨errors, checks⟩ := cond_arrow_selected policy condition_types
      (fun _ => .undefinedRight _ _) (symbol_undeclared "yes" (by decide))
      (symbol_undeclared "no" (by decide))
    exact ⟨[ifPolicy.functionType], uncovered_types_if, .selected checks (List.cons_ne_nil _ _)⟩
  have step := LocalStepWith.atomFunction (admission := .historical)
    (space := Space.ofList uncoveredRows) (dispatch := noHost) (lookup := Completed.rawLookup)
    (live := []) (scope := []) (stack := []) entry shape selection
  have published : (Completed.Frame.empty.read policy (Entry.Value.ofAtom uncoveredCall)).erase =
      uncoveredCall := by
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom]
  rw [published] at step
  have returned : Completed.invocationReturnType ifPolicy = .var "t" := by
    simp [Completed.invocationReturnType, ifPolicy, Atom.expressionType]
  obtain ⟨F, pathF, value, activation, rfl, erased⟩ := uncovered_function_segment policy
    (.calls [] [] (Completed.invocationReturnType ifPolicy) ::
      .append (.invocations [] [] Atom.undefinedType ifPolicy (Entry.Value.ofAtom (.symbol "if"))
        [Entry.Value.ofAtom condition, Entry.Value.ofAtom (sym "yes"),
          Entry.Value.ofAtom (sym "no")] []) :: [.publish uncoveredCall])
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList uncoveredRows) [.var "t"] uncoveredCall
    activation.bindings
  have sidesEq := frontier_sides call_ground activation.certified.satisfiable
    (scoped_consFree uncovered_rows) frontier
  rw [if_region_empty] at sidesEq
  have none : works = [] := List.map_eq_nil_iff.mp sidesEq
  subst none
  have frontier' : EquationFrontierRel (Space.ofList uncoveredRows) [.var "t"] value.erase
      activation.bindings [] := by
    rw [erased]
    exact frontier
  have notError : ¬ IsErrorRel value.erase := by
    rw [erased]
    rintro ⟨tail, same⟩
    simp at same
  have nonGrounded : NonGroundedCallRel noHost value.erase := by
    rw [erased]
    exact And.intro (fun ⟨_, _, _, executable⟩ => executable) (by simp [Minimal.embeddedInstruction])
  have clean : ∀ r ∈ ([(value, activation)] ++ []) ++ [], Answerable r.1.erase := by
    intro r member
    simp only [List.append_nil, List.mem_singleton] at member
    subst member
    rw [erased]
    exact uncovered_answerable
  obtain ⟨publishedAnswers, eraseP, pathP⟩ := NestedArguments.HENested.publish_step
    (dispatch := noHost) (lookup := Completed.rawLookup) (policy := policy) (atoms := uncoveredRows)
    uncoveredCall (([(value, activation)] ++ []) ++ []) clean [] []
  refine ⟨publishedAnswers, ?_, by rw [eraseP]; simp [erased]⟩
  refine .head (.internal step) ?_
  refine .head (.internal .invocationsCons) ?_
  refine .trans pathF ?_
  refine .head (.internal .calls) ?_
  rw [returned]
  refine .head (.internal .callsCons) ?_
  refine .head (.internal (.callAbsent notError nonGrounded frontier')) ?_
  refine .head (.internal .append) ?_
  refine .head (.internal .callsNil) ?_
  refine .head (.internal .prepend) ?_
  refine .head (.internal .append) ?_
  refine .head (.internal .invocationsNil) ?_
  refine .head (.internal .prepend) ?_
  exact pathP.trans (HERuns.publish_all _ publishedAnswers [])

/-- PeTTa's run of `(if (isZero 1) yes no)`: the condition has no answer, and nothing is pending
from fuel `8` on. -/
theorem petta_uncovered :
    ∀ k, 8 ≤ k → Streaming.values (Streaming.advance (translate uncoveredRows) k
      (Streaming.enter { state := store uncoveredRows } uncoveredCall)) = [] := by
  have done : (Streaming.advance (translate uncoveredRows) 8
      (Streaming.enter { state := store uncoveredRows } uncoveredCall)).agenda.length = 0 := by
    decide +kernel
  have value : Streaming.values (Streaming.advance (translate uncoveredRows) 8
      (Streaming.enter { state := store uncoveredRows } uncoveredCall)) = [] := by
    decide +kernel
  intro k bigger
  rw [advance_stable (List.eq_nil_of_length_eq_zero done) k bigger]
  exact value

/-- **The named difference, on every run.** On HE's standard-library `if` with
`(= (isZero 0) True)`, for `(if (isZero 1) yes no)`: a complete HE run exists and every complete run
publishes the call `(if (isZero 1) yes no)` itself, while PeTTa's run ends with no value from fuel `8`
on. -/
theorem uncovered_condition_differs (policy : Policy) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList uncoveredRows) uncoveredCall Atom.undefinedType)
          ⟨Space.ofList uncoveredRows, .returning [], [], heAnswers⟩) ∧
      (∀ emitted : List Result,
        Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
            (load (Space.ofList uncoveredRows) uncoveredCall Atom.undefinedType)
            ⟨Space.ofList uncoveredRows, .returning [], [], emitted⟩ →
          emitted.map (fun r => r.1.erase) = [uncoveredCall]) ∧
      ∀ k, 8 ≤ k → Streaming.values (Streaming.advance (translate uncoveredRows) k
        (Streaming.enter { state := store uncoveredRows } uncoveredCall)) = [] := by
  obtain ⟨heAnswers, path, _⟩ := uncovered_run policy
  exact ⟨⟨heAnswers, path⟩, fun emitted run => uncovered_source (complete_source run),
    petta_uncovered⟩

#print axioms isZero_one_bool
#print axioms uncovered_call_source
#print axioms uncovered_source
#print axioms uncovered_function_segment
#print axioms uncovered_run
#print axioms petta_uncovered
#print axioms uncovered_condition_differs

end IfUncovered

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
