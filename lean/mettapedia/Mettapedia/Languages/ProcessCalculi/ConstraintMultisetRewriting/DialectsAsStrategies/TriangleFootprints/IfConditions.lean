import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.ScopedIf

/-!
# `if` with a computed condition, on the scoped lookup, at every frame

`ScopedIf` treats `(if b y n)` with a Boolean literal `b`. HE evaluates the condition of `if` under
the demand `Bool` (the arrow's first argument type), at the frame the admission reached. Here the
condition is any term meeting `ScopedCondition`: closed and ground, with one stored type that `Bool`
meets keeping every frame (`Bool` or `%Undefined%`), one marked presentation, and, under `Bool` at
every frame, every derivation returning the one Boolean `b`, every run finishing with it, and PeTTa
evaluating it to `b`.

* `literal_condition`: a Boolean literal is a condition (its cast).
* `call_condition`: **a call of a defined function on data, whose region is one Boolean literal, is a
  condition**: under `Bool` HE interprets the call, queries its equations and casts the body to
  `Bool` (`bool_call_source`, `fine_bool_call`); PeTTa calls it (`AnswerBags.PeTTaRuns.petta_call`).
  For example `(isZero 0)` with `(= (isZero 0) True)`.
* `if_source_c`, `fine_if_c`: every derivation of `(if c y n)` under `%Undefined%` at every frame
  publishes the taken branch, and every run finishes with it.

## Controls

The controls use the instances built later: `UncoveredFinishes.Controls.isZero_condition`
(positive: `(isZero 0)` on `{(= (isZero 0) True)}` with HE's `if` is a condition with `True`),
`UncoveredFinishes.Controls.uncovered_not_condition` (negative: `(isZero 1)` is a condition for
neither Boolean; HE publishes the `if` call itself, a named difference), and
`IfInBodies.Controls.isTrue_call` (a call condition inside a body).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace IfConditions

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel FunctionTypeRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation (specBindingVars)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (AtomOccurs)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open HEOnTheStep (HEConfig)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (isGroundAtom)
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun NestedValues NestedCalls MarkedValues CompoundBindings DeclaredHeads
  DeclaredEveryRun TypedEveryRun AtomDemands IfEveryRun IfBranches EveryRunFinishes IfFinishes
  IfComputed ScopedTransfer ScopedIf
open AnswerBags.Controls (sym app rule rule_consFree)

variable {dispatch : GroundedDispatch} {policy : Policy}

/-! ## Conditions -/

/-- **A condition of `if` with the Boolean `b`, on the scoped lookup.** -/
structure ScopedCondition (dispatch : GroundedDispatch) (policy : Policy) (atoms : List Atom)
    (c : Atom) (b : Bool) : Prop where
  closed : ∀ name, ¬ AtomOccurs c name
  ground : isGroundAtom c = true
  typed : ∃ T, StorageTypesRel (Space.ofList atoms) c [T] ∧
    (T = sym "Bool" ∨ T = Atom.undefinedType)
  plain : ∀ v : Entry.Value, v.erase = c → Marked dispatch atoms v → v = Entry.Value.ofAtom c
  determined : ∀ (live : List Atom) (scope : List String) (frame : Frame) (results : List Result),
    Completed.AtomRel (Space.ofList atoms) dispatch Completed.scopedLookup live scope
      (Entry.Value.ofAtom c) (sym "Bool") frame results (policy := policy) →
    results.map (fun r => r.1.erase) = [.grounded (.bool b)]
  fine : ∀ (live : List Atom) (scope : List String) (frame : Frame) (stack : List Continuation)
    (emitted : List Result),
    (∀ R : List Result, R.map (fun r => r.1.erase) = [.grounded (.bool b)] →
      Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) →
    Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms,
      .work (.atom live scope (Entry.Value.ofAtom c) (sym "Bool") frame), stack, emitted⟩
  petta : PeTTaEvaluates atoms c [.grounded (.bool b)]

theorem typed_keeps {T : Atom} (shape : T = sym "Bool" ∨ T = Atom.undefinedType) {fb out : Bindings}
    (matched : TypeMatchRel (sym "Bool") T fb out) : out = fb := by
  rcases shape with rfl | rfl
  · exact bool_match_output matched
  · exact Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeMatchRel.wildcard_output matched
      (Or.inr (Or.inr (Or.inl rfl)))

theorem typed_matches {T : Atom} (shape : T = sym "Bool" ∨ T = Atom.undefinedType) (fb : Bindings) :
    TypeMatchRel (sym "Bool") T fb fb := by
  rcases shape with rfl | rfl
  · exact bool_matches fb
  · exact .undefinedRight _ _

theorem typed_accepts {T : Atom} (shape : T = sym "Bool" ∨ T = Atom.undefinedType) (frame : Frame) :
    ∃ output, policy.matching.Rel (sym "Bool") T frame.bindings output :=
  ⟨_, Completed.Frame.preserved_type_match policy frame (typed_matches shape _)⟩

theorem typed_closed {T : Atom} (shape : T = sym "Bool" ∨ T = Atom.undefinedType) :
    TypeSubst.typeVars T = [] := by
  rcases shape with rfl | rfl <;> rfl

/-- **A Boolean literal is a condition.** -/
theorem literal_condition (atoms : List Atom) (b : Bool) :
    ScopedCondition dispatch policy atoms (.grounded (.bool b)) b where
  closed := (answerable_of_data (DataAtom.grounded (.bool b))).closed
  ground := rfl
  typed := ⟨_, bool_types_in _ b, Or.inl rfl⟩
  plain := fun _ erased _ => value_of_data (.grounded (.bool b)) erased
  determined := fun _ _ _ _ derived => by
    obtain ⟨after, rfl⟩ := cast_source_any (.grounded (.bool b)) (bool_cast_entry b)
      (closed_accepts (bool_types_in _ b) rfl (bool_accepts _)) derived
    simp
  fine := fun _ _ _ _ _ cont =>
    fine_data_cast_any (.grounded (.bool b)) (bool_cast_entry b)
      (keeping_cast_step (bool_types_in _ b) rfl (bool_matches _))
      (closed_accepts (bool_types_in _ b) rfl (bool_accepts _))
      (fun after => cont _ (by simp))
  petta := PeTTaRuns.petta_data atoms (.grounded (.bool b))

/-! ## Admission with a condition -/

theorem callC_closed {c y n : Atom} (closedC : ∀ name, ¬ AtomOccurs c name)
    (closedY : ∀ name, ¬ AtomOccurs y name) (closedN : ∀ name, ¬ AtomOccurs n name) :
    ∀ name, ¬ AtomOccurs (callC c y n) name := by
  intro name occurs
  cases occurs with
  | expression member inner =>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · cases inner
      · exact closedC name inner
      · exact closedY name inner
      · exact closedN name inner

/-- **Every application check of `(if c y n)` against a fresh copy of the arrow keeps one
activation, with the frame's bindings.** -/
theorem if_checks_c {atoms : List Atom} {P : List String} {c y n Tc Ty Tn : Atom}
    (typesC : StorageTypesRel (Space.ofList atoms) c [Tc])
    (shapeC : Tc = sym "Bool" ∨ Tc = Atom.undefinedType)
    (typesY : StorageTypesRel (Space.ofList atoms) y [Ty]) (closedY : TypeSubst.typeVars Ty = [])
    (typesN : StorageTypesRel (Space.ofList atoms) n [Tn]) (closedN : TypeSubst.typeVars Tn = [])
    {frame : Frame} {signature : SelectedTypePolicy} {frames : List Frame} {errors : List Atom}
    {u : String} (functionType : signature.functionType = ifArrowV u)
    (checks : Completed.ApplicationChecksRel (Space.ofList atoms)
      (Completed.scopedLookup P (Space.ofList atoms)) policy (callC c y n) Atom.undefinedType
      signature frame frames errors) :
    ∃ after, frames = [after] ∧ after.bindings = frame.bindings := by
  have projections := if_projections_v functionType
  cases checks with
  | wrongArity shaped arity =>
      simp only [callC, app, Atom.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl⟩ := shaped
      rw [projections.1] at arity
      exact absurd rfl arity
  | checked shaped arguments returned =>
      simp only [callC, app, Atom.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl⟩ := shaped
      rw [projections.1] at arguments
      obtain ⟨f1, same1, rest1⟩ := accepted_step_scoped typesC (typed_closed shapeC)
        (fun _ matched => typed_keeps shapeC matched) (typed_accepts shapeC _) arguments
      obtain ⟨f2, same2, rest2⟩ := accepted_step_scoped typesY closedY (fun _ matched =>
        Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeMatchRel.wildcard_output matched
          (Or.inr (Or.inl rfl))) (atom_demand_accepts _ _) rest1
      obtain ⟨f3, same3, rest3⟩ := accepted_step_scoped typesN closedN (fun _ matched =>
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

/-- **Every admission of `(if c y n)` at any frame selects a fresh copy of the arrow.** -/
theorem if_selection_c {atoms : List Atom} (program : IfProgram atoms) {c y n Tc Ty Tn : Atom}
    (typesC : StorageTypesRel (Space.ofList atoms) c [Tc])
    (shapeC : Tc = sym "Bool" ∨ Tc = Atom.undefinedType)
    (typesY : StorageTypesRel (Space.ofList atoms) y [Ty]) (closedY : TypeSubst.typeVars Ty = [])
    (typesN : StorageTypesRel (Space.ofList atoms) n [Tn]) (closedN : TypeSubst.typeVars Tn = [])
    {live : List Atom} {scope : List String} {frame : Frame} {outcome : Completed.InvocationSelection}
    (chosenRel : Completed.InvocationSelectionRel (Space.ofList atoms) Completed.scopedLookup policy
      live scope (callC c y n) (.symbol "if") Atom.undefinedType frame outcome) :
    ∃ (u : String) (signature : SelectedTypePolicy) (after : Frame),
      u ∉ specBindingVars frame.bindings ∧ signature.functionType = ifArrowV u ∧
      after.bindings = frame.bindings ∧ outcome = .selected signature [after] := by
  obtain ⟨candidates, queried, scanned⟩ := chosenRel
  obtain ⟨u, same, fresh⟩ := scoped_if_answers program queried
  have freshFrame := (outside_scope fresh).2.2
  cases scanned with
  | nil => cases same
  | nonFunction notArrow _ =>
      simp only [List.cons.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      exact absurd ⟨_, _, (ifPolicyV u).isFunction⟩ notArrow
  | selected checks nonempty =>
      simp only [List.cons.injEq] at same
      obtain ⟨functionType, rfl⟩ := same
      obtain ⟨after, rfl, bindings⟩ := if_checks_c typesC shapeC typesY closedY typesN closedN
        functionType checks
      exact ⟨u, _, after, freshFrame, functionType, bindings, rfl⟩
  | rejected checks rest =>
      simp only [List.cons.injEq] at same
      obtain ⟨functionType, rfl⟩ := same
      obtain ⟨after, impossible, _⟩ := if_checks_c typesC shapeC typesY closedY typesN closedN
        functionType checks
      cases impossible

/-- **Every fresh name is selected** for `(if c y n)`. -/
theorem if_selection_succeeds_c (policy : Policy) {atoms : List Atom} (program : IfProgram atoms)
    {c y n Tc Ty Tn : Atom} (typesC : StorageTypesRel (Space.ofList atoms) c [Tc])
    (shapeC : Tc = sym "Bool" ∨ Tc = Atom.undefinedType)
    (typesY : StorageTypesRel (Space.ofList atoms) y [Ty]) (closedY : TypeSubst.typeVars Ty = [])
    (typesN : StorageTypesRel (Space.ofList atoms) n [Tn]) (closedN : TypeSubst.typeVars Tn = [])
    (live : List Atom) (scope : List String) (frame : Frame) {u : String}
    (fresh : u ∉ invocationTypeScope (invocationTypeScope scope live (callC c y n)
      Atom.undefinedType frame.bindings) [] (.symbol "if") Atom.undefinedType frame.bindings) :
    Completed.InvocationSelectionRel (Space.ofList atoms) Completed.scopedLookup policy live scope
      (callC c y n) (.symbol "if") Atom.undefinedType frame (.selected (ifPolicyV u) [frame]) := by
  refine ⟨[ifArrowV u], ⟨[ifArrow], program.types,
    .cons ⟨Equiv.swap "t" u, (Equiv.swap "t" u).injective, ?_, ?_⟩ (.nil _)⟩, ?_⟩
  · rw [rename_ifArrow, Equiv.swap_apply_left]
  · intro name member
    rw [ifArrow_vars, List.mem_singleton] at member
    subst member
    rw [Equiv.swap_apply_left]
    exact fresh
  · have arguments : Completed.ApplicabilityArgumentsRel (Space.ofList atoms)
        (Completed.scopedLookup (invocationTypeScope scope live (callC c y n) Atom.undefinedType
          frame.bindings) (Space.ofList atoms)) policy (callC c y n) 1
        [c, y, n] [sym "Bool", Atom.atomType, Atom.atomType] [frame] [frame] [] :=
      .cons (.cons (scoped_closed_answers typesC (typed_closed shapeC))
          (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy frame
            (typed_matches shapeC _)))) .nil) .nil)
        (.cons (.cons (scoped_closed_answers typesY closedY)
            (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy frame
              (.atomLeft _ _)))) .nil) .nil)
          (.cons (.cons (scoped_closed_answers typesN closedN)
              (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy frame
                (.atomLeft _ _)))) .nil) .nil) .nil))
    have checks := Completed.ApplicationChecksRel.checked (space := Space.ofList atoms)
      (lookup := Completed.scopedLookup (invocationTypeScope scope live (callC c y n)
        Atom.undefinedType frame.bindings) (Space.ofList atoms)) (policy := policy)
      (expected := Atom.undefinedType) (selected := ifPolicyV u) (before := frame)
      (operator := sym "if") (arguments := [c, y, n]) rfl arguments
      (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy frame
        (.undefinedLeft _ _)))) .nil)
    exact .selected checks (List.cons_ne_nil _ _)

/-! ## Every derivation and every run of `(if c y n)` -/

/-- **Every derivation of HE's completed relation for `(if c y n)` under `%Undefined%`, at every
frame, publishes the taken branch**, on the scoped lookup, for every condition `c` with `b`. -/
theorem if_source_c {atoms : List Atom} (program : IfProgram atoms) {c : Atom} {b : Bool}
    (cond : ScopedCondition dispatch policy atoms c b) {y n : Atom}
    (branches : ScopedBranches atoms b y n) {live : List Atom} {scope : List String} {frame : Frame}
    {results : List Result}
    (derived : Completed.AtomRel (Space.ofList atoms) dispatch Completed.scopedLookup live scope
      (Entry.Value.ofAtom (callC c y n)) Atom.undefinedType frame results (policy := policy)) :
    results.map (fun r => r.1.erase) = [pick b y n] := by
  obtain ⟨Tc, typesC, shapeC⟩ := cond.typed
  obtain ⟨Ty, typesY, closedY⟩ := branches.typedYes
  obtain ⟨Tn, typesN, closedN⟩ := branches.typedNo
  have plain := branches.branches
  have readC : frame.read policy (Entry.Value.ofAtom (callC c y n)) =
      Entry.Value.ofAtom (callC c y n) :=
    HERuns.read_closed policy frame (callC_closed cond.closed plain.closedYes plain.closedNo)
  have entry : Entry.Rel policy.reentry (frame.read policy (Entry.Value.ofAtom (callC c y n))).status
      (frame.read policy (Entry.Value.ofAtom (callC c y n))).erase Atom.undefinedType
      .interpret := by
    have atEmpty := call_entry policy if_data [c, y, n]
    rw [Completed.Frame.read_empty] at atEmpty
    rw [readC]
    exact atEmpty
  have shape : frame.read policy (Entry.Value.ofAtom (callC c y n)) =
      .expression .active (Entry.Value.ofAtom (.symbol "if") ::
        [c, y, n].map Entry.Value.ofAtom) := by
    rw [readC]
    simp only [callC, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  have outcome : ∀ {result : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList atoms) Completed.scopedLookup policy live scope
        (frame.read policy (Entry.Value.ofAtom (callC c y n))).erase
        (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType frame result →
      ∃ (u : String) (signature : SelectedTypePolicy) (after : Frame),
        u ∉ specBindingVars frame.bindings ∧ signature.functionType = ifArrowV u ∧
        after.bindings = frame.bindings ∧ result = .selected signature [after] := by
    intro result chosenRel
    rw [readC, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosenRel
    exact if_selection_c program typesC shapeC typesY closedY typesN closedN chosenRel
  have readY : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom y) = Entry.Value.ofAtom y :=
    fun frame => HERuns.read_closed policy frame plain.closedYes
  have readN : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom n) = Entry.Value.ofAtom n :=
    fun frame => HERuns.read_closed policy frame plain.closedNo
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
      obtain ⟨_, _, _, _, _, _, impossible⟩ := outcome chosenRel
      cases impossible
  | selectionFailed _ shaped chosenRel _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      obtain ⟨_, _, _, _, _, _, impossible⟩ := outcome chosenRel
      cases impossible
  | function _ shaped chosenRel invoked priority =>
      rw [shape] at shaped
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
                        (cond.determined _ _ _ _ conditionRel)
                      subst sameR
                      obtain ⟨rv, fr1⟩ := r
                      have rValue : rv = Entry.Value.ofAtom (.grounded (.bool b)) :=
                        value_of_data (.grounded (.bool b)) rErase
                      subst rValue
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
                                              have answered := branch_call_source_scoped program
                                                plain (assembled _) callRel
                                              exact publish_answers
                                                (by simp only [List.append_nil]; exact answered)
                                                (fun a member => by
                                                  rw [List.mem_singleton] at member
                                                  subst member
                                                  exact answerable_of_data plain.takenData)
                                                priority

/-- **Every run of the function application of `(if c y n)` finishes with the call value of the
condition's Boolean**: the operator meets its own fresh copy, the condition is evaluated under
`Bool`, both branches are delivered under `Atom`, and the call value is assembled. -/
theorem fine_function_c {atoms : List Atom} (program : IfProgram atoms) {c : Atom} {b : Bool}
    (cond : ScopedCondition dispatch policy atoms c b) {y n : Atom}
    (closedY : ∀ name, ¬ AtomOccurs y name) (closedN : ∀ name, ¬ AtomOccurs n name)
    {live : List Atom} {scope : List String} {expected : Atom} {signature : SelectedTypePolicy}
    {u : String} (functionType : signature.functionType = ifArrowV u) {activation : Frame}
    (freshU : u ∉ specBindingVars activation.bindings)
    (stack : List Continuation) (emitted : List Result)
    (cont : ∀ R : List Result, R.map (fun r => r.1.erase) = [callOf b y n] →
      Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms,
      .work (.function live scope expected signature (Entry.Value.ofAtom (.symbol "if"))
        [Entry.Value.ofAtom c, Entry.Value.ofAtom y, Entry.Value.ofAtom n]
        activation), stack, emitted⟩ := by
  have projections := if_projections_v functionType
  refine fine_functionStart (by simp [projections.1]) ?_
  rw [projections.1, functionType]
  simp only [List.zip_cons_cons, List.zip_nil_right]
  refine fine_data_cast_any if_data (symbol_cast_entry (by decide) (by decide) (arrowV_not_raw u))
    (operator_step program freshU) (operator_cast_accepts program freshU) ?_
  intro frF
  apply fine_functionHeads_frame
  refine fine_functionBranches_continue ?_ ?_
  · simpa using if_data.not_stopped
  apply fine_argumentsCons
  refine cond.fine _ _ _ _ _ ?_
  intro R eraseR
  obtain ⟨r, rfl, rErase⟩ := List.map_eq_singleton_iff.mp eraseR
  obtain ⟨rv, fr1⟩ := r
  have rValue : rv = Entry.Value.ofAtom (.grounded (.bool b)) :=
    value_of_data (.grounded (.bool b)) rErase
  subst rValue
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

/-- **Every run of `(if c y n)` under `%Undefined%` at every frame finishes with the taken branch**,
on the scoped lookup, under every continuation fine on it. -/
theorem fine_if_c (notHost : ¬ dispatch.executable (.symbol "if")) (policy : Policy)
    {atoms : List Atom} (program : IfProgram atoms) {c : Atom} {b : Bool}
    (cond : ScopedCondition dispatch policy atoms c b) {y n : Atom}
    (branches : ScopedBranches atoms b y n) {live : List Atom} {scope : List String}
    {frame : Frame} (stack : List Continuation) (emitted : List Result)
    (cont : ∀ R : List Result, R.map (fun r => r.1.erase) = [pick b y n] →
      Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms,
      .work (.atom live scope (Entry.Value.ofAtom (callC c y n)) Atom.undefinedType frame), stack,
      emitted⟩ := by
  obtain ⟨Tc, typesC, shapeC⟩ := cond.typed
  obtain ⟨Ty, typesY, closedY⟩ := branches.typedYes
  obtain ⟨Tn, typesN, closedN⟩ := branches.typedNo
  have plain := branches.branches
  have readC : frame.read policy (Entry.Value.ofAtom (callC c y n)) =
      Entry.Value.ofAtom (callC c y n) :=
    HERuns.read_closed policy frame (callC_closed cond.closed plain.closedYes plain.closedNo)
  have entry : Entry.Rel policy.reentry (frame.read policy (Entry.Value.ofAtom (callC c y n))).status
      (frame.read policy (Entry.Value.ofAtom (callC c y n))).erase Atom.undefinedType
      .interpret := by
    have atEmpty := call_entry policy if_data [c, y, n]
    rw [Completed.Frame.read_empty] at atEmpty
    rw [readC]
    exact atEmpty
  have shape : frame.read policy (Entry.Value.ofAtom (callC c y n)) =
      .expression .active (Entry.Value.ofAtom (.symbol "if") ::
        [c, y, n].map Entry.Value.ofAtom) := by
    rw [readC]
    simp only [callC, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  obtain ⟨target, rename, injective, renamed, fresh⟩ :=
    Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact.TypeCandidateAlphaVariantRel.exists
      (invocationTypeScope (invocationTypeScope scope live (callC c y n) Atom.undefinedType
        frame.bindings) [] (.symbol "if") Atom.undefinedType frame.bindings) ifArrow
  have freshU := fresh "t" (by rw [ifArrow_vars]; exact List.mem_singleton_self _)
  have selection : Completed.ArgumentService.historical.selection (Space.ofList atoms)
      Completed.scopedLookup policy live scope
      (frame.read policy (Entry.Value.ofAtom (callC c y n))).erase
      (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType frame
      (.selected (ifPolicyV (rename "t")) [frame]) := by
    rw [readC, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom]
    exact if_selection_succeeds_c policy program typesC shapeC typesY closedY typesN closedN live
      scope frame freshU
  have clean : ∀ R : List Result, R.map (fun r => r.1.erase) = [pick b y n] →
      ∀ r ∈ R, Answerable r.1.erase := by
    intro R eraseR r member
    have inR : r.1.erase ∈ [pick b y n] := by
      rw [← eraseR]
      exact List.mem_map.mpr ⟨r, member, rfl⟩
    rw [List.mem_singleton] at inR
    rw [inR]
    exact answerable_of_data plain.takenData
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
          obtain ⟨_, _, _, _, _, _, impossible⟩ :=
            if_selection_c program typesC shapeC typesY closedY typesN closedN chosen
          cases impossible
      | atomSelectionFailed _ shaped chosen =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          rw [readC, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosen
          obtain ⟨_, _, _, _, _, _, impossible⟩ :=
            if_selection_c program typesC shapeC typesY closedY typesN closedN chosen
          cases impossible
      | atomFunction _ shaped chosen =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, rfl⟩ := shaped
          rw [readC, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosen
          obtain ⟨u, signature, after, freshFrame, functionType, afterBindings, selected⟩ :=
            if_selection_c program typesC shapeC typesY closedY typesN closedN chosen
          simp only [Completed.InvocationSelection.selected.injEq] at selected
          obtain ⟨rfl, rfl⟩ := selected
          have freshAfter : u ∉ specBindingVars after.bindings := by
            rw [afterBindings]
            exact freshFrame
          apply fine_invocations_cons
          rw [returnType_v functionType]
          simp only [List.map_cons, List.map_nil]
          refine fine_function_c program cond plain.closedYes plain.closedNo functionType freshAfter
            _ _ ?_
          intro R eraseR
          obtain ⟨r, rfl, rErase⟩ : ∃ r, R = [r] ∧ r.1.erase = callOf b y n := by
            obtain ⟨r, sameR, rErase⟩ := List.map_eq_singleton_iff.mp eraseR
            exact ⟨r, sameR, rErase⟩
          apply fine_calls_frame
          apply fine_calls_cons
          refine fine_query_scoped notHost program plain rErase r.2 _ _ ?_
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

/-! ## A call of a defined function is a condition -/

theorem bool_not_raw :
    ¬(sym "Bool" = Atom.atomType ∨ sym "Bool" = Atom.expressionType ∨
      Atom.expressionType = Atom.variableType) := by
  decide +kernel

theorem call_bool_entry (policy : Policy) {g : String} (head : DataAtom (.symbol g))
    (args : List Atom) (frame : Frame)
    (closed : ∀ name, ¬ AtomOccurs (.expression (.symbol g :: args)) name) :
    Entry.Rel policy.reentry (frame.read policy (Entry.Value.ofAtom (.expression (.symbol g :: args)))).status
      (frame.read policy (Entry.Value.ofAtom (.expression (.symbol g :: args)))).erase (sym "Bool")
      .interpret := by
  rw [HERuns.read_closed policy frame closed, Entry.Value.erase_ofAtom]
  have status : (Entry.Value.ofAtom (.expression (.symbol g :: args))).status = .active := by
    simp [Entry.Value.ofAtom, Entry.Value.status]
  rw [status]
  exact .expression (call_not_stopped head) bool_not_raw (Or.inr rfl)

/-- **A Boolean call**: a defined function on data whose region is the one Boolean literal `b`. -/
structure BoolCall (dispatch : GroundedDispatch) (atoms : List Atom) (g : String)
    (args : List Atom) (b : Bool) : Prop where
  ordinary : Ordinary dispatch atoms g args
  head : NodeHead dispatch atoms g
  region : regionInstances atoms g args = [.grounded (.bool b)]
  bodies : regionBodies atoms g args = [.grounded (.bool b)]
  undeclared : StorageTypesRel (Space.ofList atoms) (.expression (.symbol g :: args))
    [Atom.undefinedType]

/-- **Every derivation of a Boolean call under `Bool`, at every frame, returns its Boolean**: HE
interprets the call (by the tuple entry or the fallback), queries its one equation, and casts the
body to `Bool`. -/
theorem bool_call_source {atoms : List Atom} (program : ScopedProgram atoms) {g : String}
    {args : List Atom} {b : Bool} (call : BoolCall dispatch atoms g args b) {live : List Atom}
    {scope : List String} {frame : Frame} {results : List Result}
    (derived : Completed.AtomRel (Space.ofList atoms) dispatch Completed.scopedLookup live scope
      (Entry.Value.ofAtom (.expression (.symbol g :: args))) (sym "Bool") frame results
      (policy := policy)) :
    results.map (fun r => r.1.erase) = [.grounded (.bool b)] := by
  have ordinary := call.ordinary
  have closed := (call_answerable ordinary.head ordinary.arguments).closed
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
  have ground : ∀ v ∈ args, TypeSubst.typeVars v = [] :=
    fun v member => HERuns.ground_typeVars (answerable_of_data (ordinary.arguments v member))
  -- the query of the call under `Bool`
  have query : ∀ {after : Frame} {children : List Result},
      Completed.CallRel (Space.ofList atoms) dispatch Completed.scopedLookup live scope
        (callValue g args) (sym "Bool") after children (policy := policy) →
      children.map (fun r => r.1.erase) = [.grounded (.bool b)] := by
    intro after children called
    cases called with
    | error failed => exact absurd failed (call_not_error ordinary.head args)
    | embedded _ _ instruction _ _ =>
        rw [callValue_erase, ordinary.notInstruction] at instruction
        cases instruction
    | absent _ _ frontier =>
        rw [callValue_erase] at frontier
        have instances := works_instances (policy := policy) ordinary.arguments program
          after.certified.satisfiable frontier
        rw [call.region] at instances
        cases instances
    | equations _ _ frontier _ equations =>
        rw [callValue_erase] at frontier
        have instances := works_instances (policy := policy) ordinary.arguments program
          after.certified.satisfiable frontier
        rw [call.region] at instances
        obtain ⟨w, ws, ⟨_, reads⟩, rest, rfl⟩ := List.forall₂_cons_right_iff.mp instances
        obtain rfl := List.forall₂_nil_right_iff.mp rest
        cases equations with
        | cons sameBindings _ boundary batch later =>
            cases later
            rw [reads _ sameBindings] at boundary
            cases boundary with
            | producerFunction pending _ =>
                obtain ⟨⟨inner, same⟩, _⟩ := pending
                rw [Entry.Value.erase_ofAtom] at same
                cases same
            | producerRaw _ =>
                cases batch with
                | cons returned tail =>
                    cases tail
                    cases returned with
                    | returned answered =>
                        cases answered with
                        | notReducible same =>
                            rw [Entry.Value.erase_ofAtom] at same
                            cases same
                        | stopped stopped =>
                            rw [Entry.Value.erase_ofAtom] at stopped
                            exact absurd stopped (DataAtom.grounded (.bool b)).not_stopped
                        | evaluate _ _ evaluated =>
                            obtain ⟨after', rfl⟩ := cast_source_any (.grounded (.bool b))
                              (bool_cast_entry b) (closed_accepts (bool_types_in _ b) rfl
                                (bool_accepts _)) evaluated
                            simp
  have publish : ∀ {raw selected : List Result},
      raw.map (fun r => r.1.erase) = [.grounded (.bool b)] →
      Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
        (fun result : Result => isErrorAtom result.1.erase)
        (raw.map (Completed.readResult policy)) selected →
      (selected.map (Completed.publishResult policy
        (.expression (.symbol g :: args)))).map (fun r => r.1.erase) = [.grounded (.bool b)] := by
    intro raw selected erased chosen
    exact publish_answers erased (fun a member => by
      rw [List.mem_singleton] at member
      subst member
      exact answerable_of_data (.grounded (.bool b))) chosen
  have rows : ∀ {operator : Entry.Value} {arguments : List Entry.Value} {rows raw : List Result},
      Entry.Value.ofAtom (.symbol g) = operator → args.map Entry.Value.ofAtom = arguments →
      Completed.TupleRel (Space.ofList atoms) dispatch Completed.scopedLookup
        (sym "Bool" :: live) scope (operator :: arguments) frame rows (policy := policy) →
      Completed.CallsRel (Space.ofList atoms) dispatch Completed.scopedLookup live scope
        (sym "Bool") rows raw (policy := policy) →
      raw.map (fun r => r.1.erase) = [.grounded (.bool b)] := by
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

/-- **Every run of the query of a Boolean call under `Bool` finishes with its Boolean.** -/
theorem fine_query_bool {atoms : List Atom} (program : ScopedProgram atoms) {g : String}
    {args : List Atom} {b : Bool} (call : BoolCall dispatch atoms g args b) {live : List Atom}
    {scope : List String} {value : Entry.Value}
    (erased : value.erase = .expression (.symbol g :: args)) (activation : Frame)
    (stack : List Continuation) (emitted : List Result)
    (cont : ∀ R : List Result, R.map (fun r => r.1.erase) = [.grounded (.bool b)] →
      Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms,
      .work (.call live scope value (sym "Bool") activation), stack, emitted⟩ := by
  have notError := HERuns.value_not_error call.ordinary.head erased
  have nonGrounded := HERuns.value_nonGrounded (dispatch := dispatch) call.head.notHost
    (call.head.instruction args) erased
  have notPending : ¬ Completed.FunctionPending policy (Entry.Value.ofAtom (.grounded (.bool b))) := by
    rintro ⟨⟨inner, same⟩, _⟩
    rw [Entry.Value.erase_ofAtom] at same
    cases same
  have fromFrontier : ∀ works : List EquationWork,
      EquationFrontierRel (Space.ofList atoms) (sym "Bool" :: live) (.expression (.symbol g :: args))
        activation.bindings works →
      Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms,
        .work (.equations live scope value (sym "Bool") activation works), stack, emitted⟩ := by
    intro works frontier
    have instances := works_instances (policy := policy) call.ordinary.arguments program
      activation.certified.satisfiable frontier
    rw [call.region] at instances
    obtain ⟨w, ws, ⟨_, reads⟩, rest, rfl⟩ := List.forall₂_cons_right_iff.mp instances
    obtain rfl := List.forall₂_nil_right_iff.mp rest
    have frontier' : EquationFrontierRel (Space.ofList atoms) (sym "Bool" :: live) value.erase
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
            rw [reads _ sameBindings]
            refine fine_boundary_producer notPending ?_
            apply fine_boundaryBatch_frame
            apply fine_boundaryBatch_cons
            apply fine_boundary_returned
            refine fine_returned_evaluate ?_ ?_ ?_
            · rw [Entry.Value.erase_ofAtom]
              intro same
              cases same
            · rw [Entry.Value.erase_ofAtom]
              exact (DataAtom.grounded (.bool b)).not_stopped
            refine fine_data_cast_any (.grounded (.bool b)) (bool_cast_entry b)
              (keeping_cast_step (bool_types_in _ b) rfl (bool_matches _))
              (closed_accepts (bool_types_in _ b) rfl (bool_accepts _)) ?_
            intro final
            apply fine_append
            apply fine_boundaryBatch_nil
            apply fine_prepend
            apply fine_append
            apply fine_equations_nil
            apply fine_prepend
            apply cont
            simp
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms) (sym "Bool" :: live)
    (.expression (.symbol g :: args)) activation.bindings
  have instances := works_instances (policy := policy) call.ordinary.arguments program
    activation.certified.satisfiable frontier
  have worksNonempty : works ≠ [] := by
    intro none
    subst none
    rw [call.region] at instances
    cases instances
  have frontier' : EquationFrontierRel (Space.ofList atoms) (sym "Bool" :: live) value.erase
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
          rw [erased, call.head.instruction args] at instruction
          cases instruction
      | callAbsent _ _ frontierEmpty =>
          rw [erased] at frontierEmpty
          have none := works_instances (policy := policy) call.ordinary.arguments program
            activation.certified.satisfiable frontierEmpty
          rw [call.region] at none
          cases none
      | callEquations _ _ frontierW _ =>
          rw [erased] at frontierW
          exact fromFrontier _ frontierW

/-- **Every run of a Boolean call under `Bool`, at every frame, finishes with its Boolean**, under
every continuation fine on it: the tuple entry or the fallback, the tuple of data, the query, the
publication. -/
theorem fine_bool_call {atoms : List Atom} (program : ScopedProgram atoms) {g : String}
    {args : List Atom} {b : Bool} (call : BoolCall dispatch atoms g args b) {live : List Atom}
    {scope : List String} {frame : Frame} {stack : List Continuation} {emitted : List Result}
    (cont : ∀ R : List Result, R.map (fun r => r.1.erase) = [.grounded (.bool b)] →
      Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms,
      .work (.atom live scope (Entry.Value.ofAtom (.expression (.symbol g :: args))) (sym "Bool")
        frame), stack, emitted⟩ := by
  have ordinary := call.ordinary
  have closed := (call_answerable ordinary.head ordinary.arguments).closed
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
  have afterPublish : ∀ R : List Result, R.map (fun r => r.1.erase) = [.grounded (.bool b)] →
      Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms, .returning R,
        .publish (.expression (.symbol g :: args)) :: stack, emitted⟩ := by
    intro R eraseR
    apply fine_publish (HENested.clean_of_erase eraseR (fun a member => by
      rw [List.mem_singleton] at member
      subst member
      exact answerable_of_data (.grounded (.bool b))))
    apply cont
    rw [publish_erase, eraseR]
  have afterRows : ∀ (rest : List Continuation),
      (∀ R : List Result, R.map (fun r => r.1.erase) = [.grounded (.bool b)] →
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
    refine fine_query_bool program call rErase r.2 _ _ ?_
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

/-- **A Boolean call is a condition** of `if`, on the scoped lookup. -/
theorem call_condition {atoms : List Atom} (program : ScopedProgram atoms) {g : String}
    {args : List Atom} {b : Bool} (call : BoolCall dispatch atoms g args b) :
    ScopedCondition dispatch policy atoms (.expression (.symbol g :: args)) b where
  closed := (call_answerable call.ordinary.head call.ordinary.arguments).closed
  ground := (call_answerable call.ordinary.head call.ordinary.arguments).ground
  typed := ⟨_, call.undeclared, Or.inr rfl⟩
  plain := by
    intro v erased marked
    obtain ⟨readiness, vs, rfl, vsErase⟩ := call_value_shape erased
    have plainArgs : vs = args.map Entry.Value.ofAtom := by
      rw [← vsErase, List.map_map]
      conv_lhs => rw [← List.map_id vs]
      apply List.map_congr_left
      intro w member
      exact value_of_data (call.ordinary.arguments _ (vsErase ▸ List.mem_map_of_mem member)) rfl
    subst plainArgs
    have defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = g := by
      have nonempty : regionInstances atoms g args ≠ [] := by
        rw [call.region]
        exact List.cons_ne_nil _ _
      obtain ⟨x, inRegion⟩ := List.exists_mem_of_ne_nil _ nonempty
      rw [regionInstances_eq] at inRegion
      obtain ⟨e, chosen, _⟩ := List.mem_filterMap.mp inRegion
      obtain ⟨live, selected⟩ := List.mem_filter.mp chosen
      simp only [Bool.and_eq_true, beq_iff_eq] at selected
      exact ⟨e, live, selected.1⟩
    cases readiness with
    | active => simp only [Entry.Value.ofAtom, List.map_cons]
    | held =>
        have value := marked.held_value
        simp only [List.map_cons, Entry.Value.erase] at value
        rw [List.map_map] at value
        simp only [Function.comp_def, Entry.Value.erase_ofAtom, List.map_id'] at value
        exact (value_not_defined defined value).elim
  determined := fun _ _ _ _ derived => bool_call_source program call derived
  fine := fun _ _ _ _ _ cont => fine_bool_call program call cont
  petta := by
    have defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = g ∧
        e.arguments.length = args.length := by
      have nonempty : regionInstances atoms g args ≠ [] := by
        rw [call.region]
        exact List.cons_ne_nil _ _
      obtain ⟨x, inRegion⟩ := List.exists_mem_of_ne_nil _ nonempty
      rw [regionInstances_eq] at inRegion
      obtain ⟨e, chosen, _⟩ := List.mem_filterMap.mp inRegion
      obtain ⟨live, selected⟩ := List.mem_filter.mp chosen
      simp only [Bool.and_eq_true, beq_iff_eq] at selected
      exact ⟨e, live, selected.1, selected.2⟩
    have bodies : List.Forall₂ (fun body L => PeTTaEvaluates atoms body L ∧ isGroundAtom body = true)
        (regionBodies atoms g args) [[.grounded (.bool b)]] := by
      rw [call.bodies]
      exact .cons ⟨PeTTaRuns.petta_data atoms (.grounded (.bool b)), rfl⟩ .nil
    simpa using PeTTaRuns.petta_call call.ordinary defined bodies

#print axioms fine_query_bool
#print axioms fine_bool_call
#print axioms call_condition
#print axioms bool_call_source
#print axioms literal_condition
#print axioms if_checks_c
#print axioms if_selection_c
#print axioms if_source_c
#print axioms fine_function_c
#print axioms fine_if_c

end IfConditions

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
