import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.ScopedTransfer
import Mettapedia.Languages.MeTTa.HE.EqualityClosure

/-!
# HE's `if` on the scoped lookup, at every frame

HE's index renames a stored atom's variables at every query, so each invocation of `if` meets a
fresh copy of its arrow `(-> Bool Atom Atom $t)`. The scoped lookup is that behaviour:

* `scoped_if_answers`: every scoped answer for the subject `if` is `[(-> Bool Atom Atom $u)]` for a
  name `u` outside the protected scope, which contains every name of the frame's bindings;
* `scoped_closed_answer`: for a subject whose stored type is closed, the scoped answer is the
  stored type itself;
* `if_selection_scoped`: every admission of `(if b y n)` at **any** frame selects such a fresh arrow,
  with one activation keeping the frame's bindings (`if_selection_succeeds_scoped`: every fresh name
  is one);
* `operator_accepts`: the operator `if`, cast against its selected arrow `$u`, meets the second fresh
  copy `$w` of its own query by recording `u = w`, at every frame where both names are fresh, under
  either matching policy;
* `cast_source_any`: every derivation of a data atom's cast returns the atom once, under any lookup
  whose answers are accepted;
* `if_source_scoped`: every derivation of HE's completed relation for `(if b y n)` under
  `%Undefined%`, at **any** frame, publishes the branch taken. Against `IfAtFrames.branch_source_at`
  (raw lookup) no condition on the frame is needed: a frame binding `t` is harmless, since the
  arrow's variable is never `t` there.

## Controls

* `Controls.shared_type_removed`: at the frame `{t := Number}` that a first `if` with branch `1`
  leaves under the raw lookup, every scoped selection of a second `if` returns a variable other than
  `t`, which meets `Bool` there (positive), while every raw selection returns `t`, which meets no
  Boolean there (negative, `IfSharedType.number_frame_rejects_bool`). This is the shared `$t` of
  `(pair (if True 1 2) (if True True False))`, removed by the scoped lookup, which agrees with HE
  (`[(pair 1 True)]` on HE's own interpreter).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace ScopedIf

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel FunctionTypeRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact (ArgumentAlphaVariantsRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement (TypeBindingSatisfied renameTypeVars)
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation (specBindingVars)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (AtomOccurs MatchRel MergeRel
  equalityGroundedSemantic semanticLoopFree_empty)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open HEOnTheStep (HEConfig)
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun NestedValues NestedCalls MarkedValues CompoundBindings DeclaredHeads
  DeclaredEveryRun TypedEveryRun AtomDemands IfEveryRun IfBranches EveryRunFinishes IfFinishes
  ScopedTransfer
open AnswerBags.Controls (sym app rule rule_consFree)

variable {dispatch : GroundedDispatch} {policy : Policy}

/-! ## Fresh copies of `if`'s arrow -/

/-- `(-> Bool Atom Atom $v)`. -/
abbrev ifArrowV (v : String) : Atom :=
  .expression [.symbol "->", sym "Bool", Atom.atomType, Atom.atomType, .var v]

/-- The selected signature of the copy `$v`. -/
def ifPolicyV (v : String) : SelectedTypePolicy :=
  ⟨ifArrowV v, [sym "Bool", Atom.atomType, Atom.atomType], .var v, rfl⟩

theorem rename_ifArrow (rename : String → String) :
    renameTypeVars rename ifArrow = ifArrowV (rename "t") := by
  simp [ifArrowV, renameTypeVars, Atom.atomType]

theorem ifArrow_vars : TypeSubst.typeVars ifArrow = ["t"] := by
  simp [TypeSubst.typeVars, TypeSubst.typeVarsList, Atom.atomType]

theorem ifArrowV_vars (v : String) : TypeSubst.typeVars (ifArrowV v) = [v] := by
  simp [TypeSubst.typeVars, TypeSubst.typeVarsList, Atom.atomType]

theorem if_projections_v {signature : SelectedTypePolicy} {v : String}
    (functionType : signature.functionType = ifArrowV v) :
    signature.argumentTypes = [sym "Bool", Atom.atomType, Atom.atomType] ∧
      signature.returnType = .var v := by
  have shaped : FunctionTypeRel (ifArrowV v) signature.argumentTypes signature.returnType :=
    functionType ▸ signature.isFunction
  exact FunctionTypeRel.unique shaped (ifPolicyV v).isFunction

/-- **The scoped lookup answers `if` with one fresh copy of its arrow**: on a program carrying HE's
`if`, every scoped answer is `[ifArrowV u]` with `u` outside the protected scope. -/
theorem scoped_if_answers {atoms : List Atom} (program : IfProgram atoms)
    {protectedScope : List String} {bindings : Bindings} {expected : Atom} {candidates : List Atom}
    (queried : Completed.scopedLookup protectedScope (Space.ofList atoms) bindings (.symbol "if")
      expected candidates) :
    ∃ u, candidates = [ifArrowV u] ∧
      u ∉ invocationTypeScope protectedScope [] (.symbol "if") expected bindings := by
  obtain ⟨raw, stored, variants⟩ := queried
  have same := StorageTypesRel.unique stored program.types
  subst same
  cases variants with
  | cons variant rest =>
      cases rest
      obtain ⟨rename, _, renamed, fresh⟩ := variant
      refine ⟨rename "t", by rw [renamed, rename_ifArrow], fresh "t" ?_⟩
      rw [ifArrow_vars]
      exact List.mem_singleton_self _

/-- **The scoped answer for a subject with one closed stored type is that type.** -/
theorem scoped_closed_answer {protectedScope : List String} {space : Space} {bindings : Bindings}
    {a expected T : Atom} {candidates : List Atom} (stored : StorageTypesRel space a [T])
    (closed : TypeSubst.typeVars T = [])
    (queried : Completed.scopedLookup protectedScope space bindings a expected candidates) :
    candidates = [T] := by
  obtain ⟨raw, storedRaw, variants⟩ := queried
  have same := StorageTypesRel.unique storedRaw stored
  subst same
  exact (variants_closed_iff (fun T' member => by
    rw [List.mem_singleton.mp member]; exact closed)).mp variants

theorem scoped_closed_answers {protectedScope : List String} {space : Space} {bindings : Bindings}
    {a expected T : Atom} (stored : StorageTypesRel space a [T]) (closed : TypeSubst.typeVars T = []) :
    Completed.scopedLookup protectedScope space bindings a expected [T] :=
  ⟨[T], stored, (variants_closed_iff (fun T' member => by
    rw [List.mem_singleton.mp member]; exact closed)).mpr rfl⟩

/-! ## Names outside a frame's support -/

theorem lookup_none_of_keys : ∀ {l : List (String × Atom)} {x : String},
    (∀ e ∈ l, e.1 ≠ x) → l.lookup x = none
  | [], _, _ => rfl
  | (k, v) :: rest, x, absent => by
      have ne : k ≠ x := absent (k, v) List.mem_cons_self
      have later := lookup_none_of_keys (l := rest) (x := x)
        (fun e member => absent e (List.mem_cons_of_mem _ member))
      have beqFalse : (x == k) = false := beq_eq_false_iff_ne.mpr (Ne.symm ne)
      simp only [List.lookup, beqFalse]
      exact later

theorem lookup_none_of_outside {b : Bindings} {x : String} (outside : x ∉ specBindingVars b) :
    b.lookup x = none := by
  apply lookup_none_of_keys
  intro e member same
  apply outside
  simp only [specBindingVars, List.mem_append, List.mem_flatMap]
  exact Or.inl ⟨e, member, by rw [same]; exact List.mem_cons_self⟩

theorem eqVars_of_outside {b : Bindings} {x : String} (outside : x ∉ specBindingVars b) :
    x ∉ b.eqVarsInOrder := by
  intro member
  rw [Mettapedia.Languages.MeTTa.HE.EqualityClosure.mem_eqVarsInOrder_iff] at member
  simp only [Mettapedia.Languages.MeTTa.HE.EqualityClosure.edgeNodes, List.mem_flatMap] at member
  obtain ⟨edge, inEdges, inEdge⟩ := member
  apply outside
  simp only [specBindingVars, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨edge, inEdges, inEdge⟩

/-- **Recording `u = w` for two fresh names leaves their class without values.** -/
theorem classValues_fresh_pair {b : Bindings} {u w : String} (freshU : u ∉ specBindingVars b)
    (freshW : w ∉ specBindingVars b) (different : u ≠ w) :
    (b.addEquality u w).classValues u = [] := by
  unfold Bindings.classValues
  rw [Mettapedia.Languages.MeTTa.HE.EqualityClosure.eqClassOrdered_addEquality_of_fresh
    (eqVars_of_outside freshU) (eqVars_of_outside freshW) different]
  have lookupU : (b.addEquality u w).lookup u = none := by
    change b.lookup u = none
    exact lookup_none_of_outside freshU
  have lookupW : (b.addEquality u w).lookup w = none := by
    change b.lookup w = none
    exact lookup_none_of_outside freshW
  simp [lookupU, lookupW]

/-! ## The operator meets its fresh arrow -/

/-- The bindings `{$u = $w}`. -/
abbrev pairEq (u w : String) : Bindings := Bindings.empty.addEquality u w

theorem pairEq_loopFree (u w : String) :
    Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.SemanticLoopFree (pairEq u w) :=
  Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.semanticLoopFree_of_assignments_nil rfl

theorem pairEq_constraints (u w : String) :
    Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.constraints (pairEq u w) = [.equality u w] := by
  simp [Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.constraints, Bindings.addEquality,
    Bindings.empty, List.eraseDups_cons]

theorem pairEq_empty_classValues {u w : String} (different : u ≠ w) :
    (Bindings.empty.addEquality u w).classValues u = [] := by
  have freshU : u ∉ specBindingVars Bindings.empty := by simp [specBindingVars, Bindings.empty]
  have freshW : w ∉ specBindingVars Bindings.empty := by simp [specBindingVars, Bindings.empty]
  exact classValues_fresh_pair freshU freshW different

/-- `{$u = $w}` merges into bindings where both names are fresh, recording the equality. -/
theorem merge_pairEq {b : Bindings} {u w : String} (freshU : u ∉ specBindingVars b)
    (freshW : w ∉ specBindingVars b) (different : u ≠ w) :
    MergeRel equalityGroundedSemantic b (pairEq u w) (b.addEquality u w) :=
  .mk (order := [.equality u w]) (by rw [pairEq_constraints])
    (.equality (.consistent (classValues_fresh_pair freshU freshW different) trivial) .nil)

/-- The structural match of two copies of the arrow records `$u = $w`. -/
theorem arrows_inner {u w : String} (different : u ≠ w) :
    MatchRel equalityGroundedSemantic (ifArrowV u) (ifArrowV w) (pairEq u w) :=
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
            (.cons (.varVar u w (pairEq_loopFree u w))
              (merge_pairEq (by simp [specBindingVars, Bindings.empty])
                (by simp [specBindingVars, Bindings.empty]) different) .nil)))))
    (pairEq_loopFree u w)

/-- **Two fresh copies of the arrow match**, recording `u = w`, at bindings where both are fresh. -/
theorem arrows_match {b : Bindings} {u w : String} (freshU : u ∉ specBindingVars b)
    (freshW : w ∉ specBindingVars b) (different : u ≠ w) :
    TypeMatchRel (ifArrowV u) (ifArrowV w) b (b.addEquality u w) :=
  .structural (by simp [Atom.undefinedType]) (by simp [Atom.atomType])
    (by simp [Atom.undefinedType]) (by simp [Atom.atomType]) (arrows_inner different)
    (merge_pairEq freshU freshW different)

/-- A model of the frame, updated at a fresh name, models the recorded equality. -/
theorem satisfied_pair {v : String → Atom} {b : Bindings} {u w : String}
    (freshW : w ∉ specBindingVars b) (different : u ≠ w) (sat : TypeBindingSatisfied v b) :
    TypeBindingSatisfied (Function.update v w (v u)) (b.addEquality u w) := by
  have agree : Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ValuationsAgreeOn
      (specBindingVars b) v (Function.update v w (v u)) := by
    intro name member
    have ne : name ≠ w := fun same => freshW (same ▸ member)
    simp [Function.update_of_ne ne]
  have satB := (Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.specTypeBindingSatisfied_congr_of_bindingVars
    agree).mp sat
  refine ⟨fun name value member => satB.1 name value member, fun left right member => ?_⟩
  simp only [Bindings.addEquality, List.mem_append, List.mem_singleton, Prod.mk.injEq] at member
  rcases member with inB | ⟨rfl, rfl⟩
  · exact satB.2 left right inB
  · simp [Function.update_of_ne different]

/-- **The operator accepts its fresh arrow**, under either matching policy, at every frame where both
copies are fresh. -/
theorem operator_accepts (policy : Policy) {frame : Frame} {u w : String}
    (freshU : u ∉ specBindingVars frame.bindings) (freshW : w ∉ specBindingVars frame.bindings)
    (different : u ≠ w) :
    ∃ output, policy.matching.Rel (ifArrowV u) (ifArrowV w) frame.bindings output := by
  obtain ⟨model, sat⟩ := frame.certified.satisfiable
  refine ⟨frame.bindings.addEquality u w, ?_⟩
  cases policy.matching with
  | raw => exact arrows_match freshU freshW different
  | finite => exact ⟨arrows_match freshU freshW different, _, satisfied_pair freshW different sat⟩

/-- The renewal of the operator at a frame where both copies are fresh. -/
theorem operator_renewal (policy : Policy) {frame : Frame} {u w : String}
    (freshU : u ∉ specBindingVars frame.bindings) (freshW : w ∉ specBindingVars frame.bindings)
    (different : u ≠ w) :
    ∃ after, Completed.Frame.TypeRenewRel policy (ifArrowV u) (ifArrowV w) frame after := by
  obtain ⟨model, sat⟩ := frame.certified.satisfiable
  have matched : policy.matching.Rel (ifArrowV u) (ifArrowV w) frame.bindings
      (frame.bindings.addEquality u w) := by
    cases policy.matching with
    | raw => exact arrows_match freshU freshW different
    | finite => exact ⟨arrows_match freshU freshW different, _, satisfied_pair freshW different sat⟩
  obtain ⟨after, _, renewal⟩ := Completed.Frame.TypeRenewRel.of_modelled_match frame matched
    ⟨_, satisfied_pair freshW different sat⟩
  exact ⟨after, renewal⟩

/-! ## Admission at any frame -/

theorem outside_scope {P : List String} {live : List Atom} {subject expected : Atom} {b : Bindings}
    {x : String} (outside : x ∉ invocationTypeScope P live subject expected b) :
    x ∉ P ∧ x ∉ TypeSubst.typeVarsList (live ++ [subject, expected]) ∧ x ∉ specBindingVars b := by
  simp only [invocationTypeScope, List.mem_append, not_or] at outside
  exact ⟨outside.1.1, outside.1.2, outside.2⟩

/-- **One accepted argument under the scoped lookup**, for an argument with one closed stored type:
its check keeps one frame, with the bindings the demand keeps. -/
theorem accepted_step_scoped {space : Space} {P : List String} {expression : Atom} {position : Nat}
    {a T A : Atom} {frame : Frame} {rest restT : List Atom} {after : List Frame} {errors : List Atom}
    (stored : StorageTypesRel space a [A]) (closedA : TypeSubst.typeVars A = [])
    (keeps : ∀ out, TypeMatchRel T A frame.bindings out → out = frame.bindings)
    (accepts : ∃ output, policy.matching.Rel T A frame.bindings output)
    (checked : Completed.ApplicabilityArgumentsRel space (Completed.scopedLookup P space) policy
      expression position (a :: rest) (T :: restT) [frame] after errors) :
    ∃ frame', frame'.bindings = frame.bindings ∧
      Completed.ApplicabilityArgumentsRel space (Completed.scopedLookup P space) policy expression
        (position + 1) rest restT [frame'] after errors := by
  cases checked with
  | cons head later =>
      cases head with
      | cons queried paired nilChecks =>
          cases nilChecks
          have same := scoped_closed_answer stored closedA queried
          subst same
          obtain ⟨check, checks, checkedOne, nilPaired, rfl⟩ := List.forall₂_cons_left_iff.mp paired
          obtain rfl := List.forall₂_nil_left_iff.mp nilPaired
          cases checkedOne with
          | accepted renewed =>
              simp only [Completed.checkedFrames, Completed.checkedFailures, List.filterMap_cons,
                List.filterMap_nil, List.map_nil, List.append_nil, List.nil_append] at later ⊢
              exact ⟨_, keeps _ renewed.source, later⟩
          | rejected rejectedAll =>
              obtain ⟨output, matched⟩ := accepts
              exact (rejectedAll output matched).elim

/-- **Every application check of `(if b y n)` against a fresh copy of the arrow keeps exactly one
activation, with the frame's bindings.** -/
theorem if_checks_scoped {atoms : List Atom} {P : List String} (b : Bool) {y n Ty Tn : Atom}
    (typesY : StorageTypesRel (Space.ofList atoms) y [Ty]) (closedY : TypeSubst.typeVars Ty = [])
    (typesN : StorageTypesRel (Space.ofList atoms) n [Tn]) (closedN : TypeSubst.typeVars Tn = [])
    {frame : Frame} {signature : SelectedTypePolicy} {frames : List Frame} {errors : List Atom}
    {u : String} (functionType : signature.functionType = ifArrowV u)
    (checks : Completed.ApplicationChecksRel (Space.ofList atoms)
      (Completed.scopedLookup P (Space.ofList atoms)) policy (callOf b y n) Atom.undefinedType
      signature frame frames errors) :
    ∃ after, frames = [after] ∧ after.bindings = frame.bindings := by
  have projections := if_projections_v functionType
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
      obtain ⟨f1, same1, rest1⟩ := accepted_step_scoped (bool_types_in _ b) rfl (fun _ matched =>
        bool_match_output matched) (bool_accepts _) arguments
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

/-- **Every admission of `(if b y n)` at any frame selects a fresh copy of the arrow**, outside the
frame's names, with one activation keeping the frame's bindings. -/
theorem if_selection_scoped {atoms : List Atom} (program : IfProgram atoms) (b : Bool)
    {y n Ty Tn : Atom} (typesY : StorageTypesRel (Space.ofList atoms) y [Ty])
    (closedY : TypeSubst.typeVars Ty = []) (typesN : StorageTypesRel (Space.ofList atoms) n [Tn])
    (closedN : TypeSubst.typeVars Tn = []) {live : List Atom} {scope : List String} {frame : Frame}
    {outcome : Completed.InvocationSelection}
    (chosenRel : Completed.InvocationSelectionRel (Space.ofList atoms) Completed.scopedLookup policy
      live scope (callOf b y n) (.symbol "if") Atom.undefinedType frame outcome) :
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
      obtain ⟨after, rfl, bindings⟩ := if_checks_scoped b typesY closedY typesN closedN functionType
        checks
      exact ⟨u, _, after, freshFrame, functionType, bindings, rfl⟩
  | rejected checks rest =>
      simp only [List.cons.injEq] at same
      obtain ⟨functionType, rfl⟩ := same
      obtain ⟨after, impossible, _⟩ := if_checks_scoped b typesY closedY typesN closedN functionType
        checks
      cases impossible

/-- **Every fresh name is selected**: for a name outside the protected scope, HE's admission of
`(if b y n)` at the frame selects the copy of the arrow with that name. -/
theorem if_selection_succeeds_scoped (policy : Policy) {atoms : List Atom} (program : IfProgram atoms)
    (b : Bool) {y n Ty Tn : Atom} (typesY : StorageTypesRel (Space.ofList atoms) y [Ty])
    (closedY : TypeSubst.typeVars Ty = []) (typesN : StorageTypesRel (Space.ofList atoms) n [Tn])
    (closedN : TypeSubst.typeVars Tn = []) (live : List Atom) (scope : List String) (frame : Frame)
    {u : String}
    (fresh : u ∉ invocationTypeScope (invocationTypeScope scope live (callOf b y n)
      Atom.undefinedType frame.bindings) [] (.symbol "if") Atom.undefinedType frame.bindings) :
    Completed.InvocationSelectionRel (Space.ofList atoms) Completed.scopedLookup policy live scope
      (callOf b y n) (.symbol "if") Atom.undefinedType frame (.selected (ifPolicyV u) [frame]) := by
  refine ⟨[ifArrowV u], ⟨[ifArrow], program.types,
    .cons ⟨Equiv.swap "t" u, (Equiv.swap "t" u).injective, ?_, ?_⟩ (.nil _)⟩, ?_⟩
  · rw [rename_ifArrow, Equiv.swap_apply_left]
  · intro name member
    rw [ifArrow_vars, List.mem_singleton] at member
    subst member
    rw [Equiv.swap_apply_left]
    exact fresh
  · have arguments : Completed.ApplicabilityArgumentsRel (Space.ofList atoms)
        (Completed.scopedLookup (invocationTypeScope scope live (callOf b y n) Atom.undefinedType
          frame.bindings) (Space.ofList atoms)) policy (callOf b y n) 1
        [.grounded (.bool b), y, n] [sym "Bool", Atom.atomType, Atom.atomType] [frame] [frame] [] :=
      .cons (.cons (scoped_closed_answers (bool_types_in _ b) rfl)
          (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy frame
            (bool_matches _)))) .nil) .nil)
        (.cons (.cons (scoped_closed_answers typesY closedY)
            (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy frame
              (.atomLeft _ _)))) .nil) .nil)
          (.cons (.cons (scoped_closed_answers typesN closedN)
              (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy frame
                (.atomLeft _ _)))) .nil) .nil) .nil))
    have checks := Completed.ApplicationChecksRel.checked (space := Space.ofList atoms)
      (lookup := Completed.scopedLookup (invocationTypeScope scope live (callOf b y n)
        Atom.undefinedType frame.bindings) (Space.ofList atoms)) (policy := policy)
      (expected := Atom.undefinedType) (selected := ifPolicyV u) (before := frame)
      (operator := sym "if") (arguments := [.grounded (.bool b), y, n]) rfl arguments
      (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy frame
        (.undefinedLeft _ _)))) .nil)
    exact .selected checks (List.cons_ne_nil _ _)

/-! ## Casts under any lookup -/

/-- **A data atom's cast returns the atom once**, under any lookup every answer of which contains a
type the demand accepts at the frame. -/
theorem cast_source_any {lookup : CastLookup} {space : Space} {live : List Atom}
    {scope : List String} {a expected : Atom} (data : DataAtom a)
    (entry : Entry.Rel policy.reentry .active a expected .cast) {frame : Frame}
    {results : List Result}
    (accepts : ∀ types, lookup (invocationTypeScope scope live a expected frame.bindings) space
      frame.bindings a expected types →
      ∃ actual ∈ types, ∃ output, policy.matching.Rel expected actual frame.bindings output)
    (derived : Completed.AtomRel space dispatch lookup live scope
      (Entry.Value.ofAtom a) expected frame results (policy := policy)) :
    ∃ after : Frame, results = [(Entry.Value.ofAtom a, after)] := by
  have entry' : Entry.Rel policy.reentry (frame.read policy (Entry.Value.ofAtom a)).status
      (frame.read policy (Entry.Value.ofAtom a)).erase expected .cast := by
    simp only [CompleteRun.read_data policy frame data, Entry.Value.erase_ofAtom, data.status]
    exact entry
  cases derived with
  | delivered entered => cases Entry.functional entered entry'
  | cast _ batch related =>
      rw [CompleteRun.read_data policy frame data, Entry.Value.erase_ofAtom] at batch related
      cases batch with
      | success _ _ _ _ =>
          obtain ⟨r, rs, first, rest, rfl⟩ := List.forall₂_cons_left_iff.mp related
          obtain rfl := List.forall₂_nil_left_iff.mp rest
          have value : r.1 = Entry.Value.ofAtom a := by
            have payload := first.payload
            split at payload <;> exact payload
          exact ⟨r.2, by rw [← value]⟩
      | failure queried rejected =>
          obtain ⟨actual, member, output, matched⟩ := accepts _ queried
          exact (rejected actual member output matched).elim
  | tuple entered => cases Entry.functional entered entry'
  | function entered => cases Entry.functional entered entry'
  | fallback entered => cases Entry.functional entered entry'
  | selectionFailed entered => cases Entry.functional entered entry'

/-- The scoped answers of a closed single type are accepted when that type is. -/
theorem closed_accepts {P : List String} {space : Space} {bindings : Bindings} {a expected T : Atom}
    (stored : StorageTypesRel space a [T]) (closed : TypeSubst.typeVars T = [])
    (accepts : ∃ output, policy.matching.Rel expected T bindings output) :
    ∀ types, Completed.scopedLookup P space bindings a expected types →
      ∃ actual ∈ types, ∃ output, policy.matching.Rel expected actual bindings output := by
  intro types queried
  rw [scoped_closed_answer stored closed queried]
  exact ⟨T, List.mem_singleton_self _, accepts⟩

/-- **The operator's cast is accepted**: the operator `if`, cast against its selected copy `$u` at
a frame outside whose names `u` lies, meets every second copy `$w` of its own query. -/
theorem operator_cast_accepts {atoms : List Atom} (program : IfProgram atoms) {scope : List String}
    {live : List Atom} {frame : Frame} {u : String} (freshU : u ∉ specBindingVars frame.bindings) :
    ∀ types, Completed.scopedLookup (invocationTypeScope scope live (.symbol "if") (ifArrowV u)
        frame.bindings) (Space.ofList atoms) frame.bindings (.symbol "if") (ifArrowV u) types →
      ∃ actual ∈ types, ∃ output,
        policy.matching.Rel (ifArrowV u) actual frame.bindings output := by
  intro types queried
  obtain ⟨w, rfl, freshW⟩ := scoped_if_answers program queried
  have inner := outside_scope freshW
  have different : u ≠ w := by
    intro same
    apply inner.2.1
    rw [← same]
    simp [TypeSubst.typeVarsList, TypeSubst.typeVars, Atom.atomType]
  exact ⟨ifArrowV w, List.mem_singleton_self _, operator_accepts policy freshU inner.2.2 different⟩

/-! ## The query of `if`'s rows under the fresh return type -/

/-- **Every derivation of the query of `(if b y n)` under its fresh return demand `$u` returns the
taken branch**: the query reads the taken branch as `$then` or `$else`, the other is only bound by the
unifier, and the undeclared taken branch meets `$u` by `undefinedRight` at every frame. -/
theorem branch_call_source_scoped {atoms : List Atom} (program : IfProgram atoms) {b : Bool}
    {y n : Atom} (branches : Branches atoms b y n) {live : List Atom} {scope : List String}
    {u : String} {value : Entry.Value} {frame : Frame} {children : List Result}
    (erased : value.erase = callOf b y n)
    (called : Completed.CallRel (Space.ofList atoms) dispatch Completed.scopedLookup live scope
      value (.var u) frame children (policy := policy)) :
    children.map (fun r => r.1.erase) = [pick b y n] := by
  have ground := call_ground (b := b) branches.closedYes branches.closedNo
  have takenEntry : Entry.Rel policy.reentry .active (pick b y n) (.var u) .cast :=
    data_var_entry branches.takenData u
  cases called with
  | error failed =>
      rw [erased] at failed
      obtain ⟨tail, same⟩ := failed
      simp at same
  | embedded _ _ instruction _ _ =>
      rw [erased] at instruction
      simp [Minimal.embeddedInstruction] at instruction
  | absent _ _ frontier =>
      rw [erased] at frontier
      have sidesEq := frontier_sides ground frame.certified.satisfiable
        (scoped_consFree program.rows) frontier
      have nonempty : regionInstances atoms "if" [.grounded (.bool b), y, n] ≠ [] := by
        rw [branches.region]
        exact List.cons_ne_nil _ _
      apply absurd _ nonempty
      rw [regionInstances_sides, ← sidesEq]
      rfl
  | equations _ _ frontier _ equations =>
      rw [erased] at frontier
      have works := works_instances_ground policy ground program.rows
        frame.certified.satisfiable frontier
      rw [branches.region] at works
      obtain ⟨w, ws, ⟨_, reads⟩, rest, rfl⟩ := List.forall₂_cons_right_iff.mp works
      obtain rfl := List.forall₂_nil_right_iff.mp rest
      cases equations with
      | cons sameBindings _ boundary batch later =>
          cases later
          have readErase := reads _ sameBindings
          have readValue := value_of_data branches.takenData readErase
          rw [readValue] at boundary
          cases boundary with
          | producerFunction pending _ =>
              obtain ⟨⟨inner, same⟩, _⟩ := pending
              rw [Entry.Value.erase_ofAtom] at same
              have data := branches.takenData
              rw [same] at data
              cases data
          | producerRaw _ =>
              cases batch with
              | cons returned tail =>
                  cases tail
                  cases returned with
                  | returned answered =>
                      cases answered with
                      | notReducible same =>
                          rw [Entry.Value.erase_ofAtom] at same
                          exact absurd same branches.takenNotRefused
                      | stopped stopped =>
                          rw [Entry.Value.erase_ofAtom] at stopped
                          exact absurd stopped branches.takenData.not_stopped
                      | evaluate _ _ evaluated =>
                          obtain ⟨after, rfl⟩ := cast_source_any branches.takenData takenEntry
                            (closed_accepts branches.takenUndeclared rfl
                              (variable_meets_undefined u _)) evaluated
                          simp

/-! ## `if` at every frame -/

/-- **The branches of `(if b y n)` for the scoped lookup**: `IfBranches.Branches`, with closed stored
types of both branches. -/
structure ScopedBranches (atoms : List Atom) (b : Bool) (y n : Atom) : Prop where
  branches : Branches atoms b y n
  typedYes : ∃ T, StorageTypesRel (Space.ofList atoms) y [T] ∧ TypeSubst.typeVars T = []
  typedNo : ∃ T, StorageTypesRel (Space.ofList atoms) n [T] ∧ TypeSubst.typeVars T = []

theorem arrowV_not_raw (u : String) :
    ¬(ifArrowV u = Atom.atomType ∨ ifArrowV u = Atom.symbolType ∨
      Atom.symbolType = Atom.variableType) := by
  simp [Atom.atomType, Atom.symbolType, Atom.variableType]

theorem returnType_v {signature : SelectedTypePolicy} {u : String}
    (functionType : signature.functionType = ifArrowV u) :
    Completed.invocationReturnType signature = .var u := by
  simp [Completed.invocationReturnType, (if_projections_v functionType).2, Atom.expressionType]

/-- **Every derivation of HE's completed relation for `(if b y n)` under `%Undefined%`, at every
frame, publishes the taken branch**, on the scoped lookup. The admission selects a fresh copy `$u`
of the arrow; the operator meets it by `u = w` with its own fresh copy `$w`; the condition is cast
to `Bool`; both branches are delivered under `Atom`; the query selects the row of `b`; the taken
branch meets `$u`. -/
theorem if_source_scoped {atoms : List Atom} (program : IfProgram atoms) {b : Bool} {y n : Atom}
    (branches : ScopedBranches atoms b y n) {live : List Atom} {scope : List String} {frame : Frame}
    {results : List Result}
    (derived : Completed.AtomRel (Space.ofList atoms) dispatch Completed.scopedLookup live scope
      (Entry.Value.ofAtom (callOf b y n)) Atom.undefinedType frame results (policy := policy)) :
    results.map (fun r => r.1.erase) = [pick b y n] := by
  obtain ⟨Ty, typesY, closedY⟩ := branches.typedYes
  obtain ⟨Tn, typesN, closedN⟩ := branches.typedNo
  have plain := branches.branches
  have readC : frame.read policy (Entry.Value.ofAtom (callOf b y n)) =
      Entry.Value.ofAtom (callOf b y n) :=
    HERuns.read_closed policy frame (IfAtFrames.call_closed plain.closedYes plain.closedNo)
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
      Completed.InvocationSelectionRel (Space.ofList atoms) Completed.scopedLookup policy live scope
        (frame.read policy (Entry.Value.ofAtom (callOf b y n))).erase
        (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType frame result →
      ∃ (u : String) (signature : SelectedTypePolicy) (after : Frame),
        u ∉ specBindingVars frame.bindings ∧ signature.functionType = ifArrowV u ∧
        after.bindings = frame.bindings ∧ result = .selected signature [after] := by
    intro result chosenRel
    rw [readC, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosenRel
    exact if_selection_scoped program b typesY closedY typesN closedN chosenRel
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
                      obtain ⟨fr1, rfl⟩ := cast_source_any (.grounded (.bool b)) (bool_cast_entry b)
                        (closed_accepts (bool_types_in _ b) rfl (bool_accepts _)) conditionRel
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

/-! ## Every run of `if` at every frame finishes -/

/-- **A cast step under any lookup whose answer has one type**, renewing the frame. -/
theorem renewed_cast_step_any (dispatch : GroundedDispatch) (policy : Policy) {lookup : CastLookup}
    {space : Space} {atom expected actual : Atom}
    (closed : ∀ name, ¬ AtomOccurs atom name)
    (entry : Entry.Rel policy.reentry .active atom expected .cast) {frame after : Frame}
    {live : List Atom} {scope : List String}
    (queried : lookup (invocationTypeScope scope live atom expected frame.bindings) space
      frame.bindings atom expected [actual])
    (renewal : Completed.Frame.TypeRenewRel policy expected actual frame after)
    (stack : List Continuation) (emitted : List Result) :
    HEStep dispatch lookup policy
      ⟨space, .work (.atom live scope (Entry.Value.ofAtom atom) expected frame), stack, emitted⟩
      ⟨space, .returning [(Entry.Value.ofAtom atom, after)], stack, emitted⟩ := by
  have readAtom := HERuns.read_closed policy frame closed
  have matched : policy.matching.Rel expected actual frame.bindings after.bindings := by
    cases renewal with
    | unchanged m => exact m
    | unified m _ => exact m
  refine .internal (LocalStepWith.cast (raw := [(atom, after.bindings)]) ?_ ?_ ?_)
  · rw [readAtom, Entry.Value.erase_ofAtom, ofAtom_status]
    exact entry
  · rw [readAtom, Entry.Value.erase_ofAtom]
    exact Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeCastBatchRel.success (earlierTypes := [])
      queried rfl (fun _ member => by simp at member) matched
  · rw [readAtom, Entry.Value.erase_ofAtom]
    refine .cons ⟨by simp [Completed.rawResult], ?_, by simp⟩ .nil
    rw [Entry.Value.erase_ofAtom]
    cases renewal with
    | unchanged _ => exact .same _
    | unified m unifiedEnv =>
        exact .matched (earlier := []) (later := []) queried rfl
          (fun _ member => by simp at member) m unifiedEnv

/-- **A data atom's cast under any lookup**: some answer of one type renews the frame, every answer
holds a type the demand accepts, and every cast result is the atom. -/
theorem fine_data_cast_any {lookup : CastLookup} {space : Space} {live : List Atom}
    {scope : List String} {stack : List Continuation} {emitted : List Result} {d E : Atom}
    (data : DataAtom d) (entry : Entry.Rel policy.reentry .active d E .cast) {frame : Frame}
    (firstStep : ∃ (T : Atom) (after : Frame),
      lookup (invocationTypeScope scope live d E frame.bindings) space frame.bindings d E [T] ∧
        Completed.Frame.TypeRenewRel policy E T frame after)
    (accepts : ∀ types, lookup (invocationTypeScope scope live d E frame.bindings) space
      frame.bindings d E types →
      ∃ actual ∈ types, ∃ output, policy.matching.Rel E actual frame.bindings output)
    (next : ∀ after : Frame, Fine dispatch lookup policy ⟨space,
      .returning [(Entry.Value.ofAtom d, after)], stack, emitted⟩) :
    Fine dispatch lookup policy ⟨space,
      .work (.atom live scope (Entry.Value.ofAtom d) E frame), stack, emitted⟩ := by
  obtain ⟨T, after, queried, renewed⟩ := firstStep
  refine .step ⟨_, renewed_cast_step_any dispatch policy (answerable_of_data data).closed entry
    queried renewed stack emitted⟩ ?_
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
              obtain ⟨actual, member, output, matched⟩ := accepts _ queried
              exact (rejected actual member output matched).elim
      | atomTuple entered => cases Entry.functional entered entry'
      | atomFunction entered => cases Entry.functional entered entry'
      | atomFallback entered => cases Entry.functional entered entry'
      | atomSelectionFailed entered => cases Entry.functional entered entry'

/-- A data atom with one closed stored type, cast under a demand keeping every frame. -/
theorem keeping_cast_step {P : List String} {space : Space} {d E T : Atom} {frame : Frame}
    (stored : StorageTypesRel space d [T]) (closed : TypeSubst.typeVars T = [])
    (keeps : TypeMatchRel E T frame.bindings frame.bindings) :
    ∃ (T' : Atom) (after : Frame), Completed.scopedLookup P space frame.bindings d E [T'] ∧
      Completed.Frame.TypeRenewRel policy E T' frame after :=
  ⟨T, frame, scoped_closed_answers stored closed,
    .unchanged (Completed.Frame.preserved_type_match policy frame keeps)⟩

/-- **The operator's first cast step exists**: a fresh copy `$w` and a renewal recording `u = w`. -/
theorem operator_step {atoms : List Atom} (program : IfProgram atoms) {scope : List String}
    {live : List Atom} {frame : Frame} {u : String} (freshU : u ∉ specBindingVars frame.bindings) :
    ∃ (T : Atom) (after : Frame),
      Completed.scopedLookup (invocationTypeScope scope live (.symbol "if") (ifArrowV u)
        frame.bindings) (Space.ofList atoms) frame.bindings (.symbol "if") (ifArrowV u) [T] ∧
      Completed.Frame.TypeRenewRel policy (ifArrowV u) T frame after := by
  let avoid := invocationTypeScope (invocationTypeScope scope live (.symbol "if") (ifArrowV u)
    frame.bindings) [] (.symbol "if") (ifArrowV u) frame.bindings
  obtain ⟨target, rename, injective, renamed, fresh⟩ :=
    Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact.TypeCandidateAlphaVariantRel.exists
      avoid ifArrow
  have freshW : rename "t" ∉ avoid := fresh "t" (by rw [ifArrow_vars]; exact List.mem_singleton_self _)
  have inner := outside_scope freshW
  have different : u ≠ rename "t" := by
    intro same
    apply inner.2.1
    rw [← same]
    simp [TypeSubst.typeVarsList, TypeSubst.typeVars, Atom.atomType]
  obtain ⟨after, renewal⟩ := operator_renewal policy freshU inner.2.2 different
  refine ⟨ifArrowV (rename "t"), after, ⟨[ifArrow], program.types,
    .cons ⟨rename, injective, by rw [rename_ifArrow], fresh⟩ (.nil _)⟩, renewal⟩

/-- **Every run of the typed query of `(if b y n)` under its fresh return demand finishes with the
taken branch.** -/
theorem fine_query_scoped (notHost : ¬ dispatch.executable (.symbol "if")) {atoms : List Atom}
    (program : IfProgram atoms) {b : Bool} {y n : Atom} (branches : Branches atoms b y n)
    {live : List Atom} {scope : List String} {u : String} {value : Entry.Value}
    (erased : value.erase = callOf b y n) (activation : Frame) (stack : List Continuation)
    (emitted : List Result)
    (cont : ∀ R : List Result, R.map (fun r => r.1.erase) = [pick b y n] →
      Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms,
      .work (.call live scope value (.var u) activation), stack, emitted⟩ := by
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
      EquationFrontierRel (Space.ofList atoms) (.var u :: live) (callOf b y n)
        activation.bindings works →
      Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms,
        .work (.equations live scope value (.var u) activation works), stack, emitted⟩ := by
    intro works frontier
    have instances := works_instances_ground policy ground program.rows
      activation.certified.satisfiable frontier
    rw [branches.region] at instances
    obtain ⟨w, ws, ⟨_, reads⟩, rest, rfl⟩ := List.forall₂_cons_right_iff.mp instances
    obtain rfl := List.forall₂_nil_right_iff.mp rest
    have frontier' : EquationFrontierRel (Space.ofList atoms) (.var u :: live) value.erase
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
            refine fine_data_cast_any branches.takenData (data_var_entry branches.takenData u)
              (keeping_cast_step branches.takenUndeclared rfl (.undefinedRight _ _))
              (closed_accepts branches.takenUndeclared rfl (variable_meets_undefined u _)) ?_
            intro final
            apply fine_append
            apply fine_boundaryBatch_nil
            apply fine_prepend
            apply fine_append
            apply fine_equations_nil
            apply fine_prepend
            apply cont
            simp
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms) (.var u :: live) (callOf b y n)
    activation.bindings
  have instances := works_instances_ground policy ground program.rows
    activation.certified.satisfiable frontier
  have worksNonempty : works ≠ [] := by
    intro none
    subst none
    rw [branches.region] at instances
    cases instances
  have frontier' : EquationFrontierRel (Space.ofList atoms) (.var u :: live) value.erase
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

/-- **Every run of the function application of `(if b y n)` against a fresh copy finishes with the
call value**: the operator meets its own fresh copy, the condition is cast to `Bool`, both branches
are delivered under `Atom` as they are, and the call value is assembled. -/
theorem fine_function_scoped {atoms : List Atom} (program : IfProgram atoms) {b : Bool}
    {y n : Atom} (closedY : ∀ name, ¬ AtomOccurs y name) (closedN : ∀ name, ¬ AtomOccurs n name)
    {live : List Atom} {scope : List String} {expected : Atom} {signature : SelectedTypePolicy}
    {u : String} (functionType : signature.functionType = ifArrowV u) {activation : Frame}
    (freshU : u ∉ specBindingVars activation.bindings)
    (stack : List Continuation) (emitted : List Result)
    (cont : ∀ R : List Result, R.map (fun r => r.1.erase) = [callOf b y n] →
      Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms,
      .work (.function live scope expected signature (Entry.Value.ofAtom (.symbol "if"))
        [Entry.Value.ofAtom (.grounded (.bool b)), Entry.Value.ofAtom y, Entry.Value.ofAtom n]
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
  refine fine_data_cast_any (DataAtom.grounded (.bool b)) (bool_cast_entry b)
    (keeping_cast_step (bool_types_in _ b) rfl (bool_matches _))
    (closed_accepts (bool_types_in _ b) rfl (bool_accepts _)) ?_
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

/-- **Every run of `(if b y n)` under `%Undefined%` at every frame finishes, with the taken branch**,
on the scoped lookup, under every continuation fine on the taken branch. Against
`IfAtFrames.branch_runs_at` (raw lookup), no condition on the frame is needed. -/
theorem fine_if_scoped (notHost : ¬ dispatch.executable (.symbol "if")) (policy : Policy)
    {atoms : List Atom} (program : IfProgram atoms) {b : Bool} {y n : Atom}
    (branches : ScopedBranches atoms b y n) {live : List Atom} {scope : List String}
    {frame : Frame} (stack : List Continuation) (emitted : List Result)
    (cont : ∀ R : List Result, R.map (fun r => r.1.erase) = [pick b y n] →
      Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms,
      .work (.atom live scope (Entry.Value.ofAtom (callOf b y n)) Atom.undefinedType frame), stack,
      emitted⟩ := by
  obtain ⟨Ty, typesY, closedY⟩ := branches.typedYes
  obtain ⟨Tn, typesN, closedN⟩ := branches.typedNo
  have plain := branches.branches
  have readC : frame.read policy (Entry.Value.ofAtom (callOf b y n)) =
      Entry.Value.ofAtom (callOf b y n) :=
    HERuns.read_closed policy frame (IfAtFrames.call_closed plain.closedYes plain.closedNo)
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
  obtain ⟨target, rename, injective, renamed, fresh⟩ :=
    Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact.TypeCandidateAlphaVariantRel.exists
      (invocationTypeScope (invocationTypeScope scope live (callOf b y n) Atom.undefinedType
        frame.bindings) [] (.symbol "if") Atom.undefinedType frame.bindings) ifArrow
  have freshU := fresh "t" (by rw [ifArrow_vars]; exact List.mem_singleton_self _)
  have selection : Completed.ArgumentService.historical.selection (Space.ofList atoms)
      Completed.scopedLookup policy live scope
      (frame.read policy (Entry.Value.ofAtom (callOf b y n))).erase
      (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType frame
      (.selected (ifPolicyV (rename "t")) [frame]) := by
    rw [readC, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom]
    exact if_selection_succeeds_scoped policy program b typesY closedY typesN closedN live scope
      frame freshU
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
            if_selection_scoped program b typesY closedY typesN closedN chosen
          cases impossible
      | atomSelectionFailed _ shaped chosen =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          rw [readC, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosen
          obtain ⟨_, _, _, _, _, _, impossible⟩ :=
            if_selection_scoped program b typesY closedY typesN closedN chosen
          cases impossible
      | atomFunction _ shaped chosen =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, rfl⟩ := shaped
          rw [readC, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosen
          obtain ⟨u, signature, after, freshFrame, functionType, afterBindings, selected⟩ :=
            if_selection_scoped program b typesY closedY typesN closedN chosen
          simp only [Completed.InvocationSelection.selected.injEq] at selected
          obtain ⟨rfl, rfl⟩ := selected
          have freshAfter : u ∉ specBindingVars after.bindings := by
            rw [afterBindings]
            exact freshFrame
          apply fine_invocations_cons
          rw [returnType_v functionType]
          simp only [List.map_cons, List.map_nil]
          refine fine_function_scoped program plain.closedYes plain.closedNo functionType freshAfter
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

/-! ## Controls -/

namespace Controls

open IfSharedType (numberFrame number_frame_rejects_bool raw_return_shared)

/-- A name without a value in bindings that record no equality has no class value. -/
theorem classValues_no_equalities {b : Bindings} {x : String} (noEq : b.equalities = [])
    (unbound : b.lookup x = none) : b.classValues x = [] := by
  unfold Bindings.classValues Bindings.eqClassOrdered Bindings.eqVarsInOrder
  rw [noEq]
  simp [unbound]

theorem numberFrame_vars : specBindingVars numberFrame = ["t"] := by decide

/-- At `{t := Number}`, every name other than `t` is free. -/
theorem numberFrame_free {u : String} (different : u ≠ "t") : numberFrame.classValues u = [] :=
  classValues_no_equalities rfl (lookup_none_of_outside (by
    rw [numberFrame_vars]
    simpa using different))

/-- **The shared `$t` is removed by the scoped lookup.** At a frame binding `t := Number` (the frame
a first `if` with branch `1` leaves under the raw lookup), every scoped selection of a second `if`
returns a variable other than `t`, and that variable meets `Bool`; every raw selection returns `t`
itself, which meets no Boolean there. On `(pair (if True 1 2) (if True True False))` HE's own
interpreter answers `[(pair 1 True)]`, as the scoped lookup allows and the raw lookup does not. -/
theorem shared_type_removed {atoms : List Atom} (program : IfProgram atoms) {y n Ty Tn : Atom}
    (typesY : StorageTypesRel (Space.ofList atoms) y [Ty]) (closedY : TypeSubst.typeVars Ty = [])
    (typesN : StorageTypesRel (Space.ofList atoms) n [Tn]) (closedN : TypeSubst.typeVars Tn = [])
    {live : List Atom} {scope : List String} {frame : Frame} (bound : frame.bindings = numberFrame) :
    (∀ outcome, Completed.InvocationSelectionRel (Space.ofList atoms) Completed.scopedLookup policy
        live scope (callOf true y n) (.symbol "if") Atom.undefinedType frame outcome →
      ∃ (u : String) (signature : SelectedTypePolicy) (after : Frame),
        outcome = .selected signature [after] ∧ signature.returnType = .var u ∧ u ≠ "t" ∧
        ∃ out, TypeMatchRel signature.returnType (sym "Bool") frame.bindings out) ∧
    (∀ (signature : SelectedTypePolicy) (frames : List Frame),
      Completed.InvocationSelectionRel (Space.ofList atoms) Completed.rawLookup policy live scope
        (callOf true y n) (.symbol "if") Atom.undefinedType frame (.selected signature frames) →
      signature.returnType = .var "t" ∧
        ¬ ∃ out, TypeMatchRel signature.returnType (sym "Bool") frame.bindings out) := by
  refine ⟨fun outcome chosen => ?_, fun signature frames chosen => ?_⟩
  · obtain ⟨u, signature, after, fresh, functionType, _, selected⟩ :=
      if_selection_scoped program true typesY closedY typesN closedN chosen
    have different : u ≠ "t" := by
      intro same
      apply fresh
      rw [bound, numberFrame_vars, same]
      exact List.mem_singleton_self _
    have returned := (if_projections_v functionType).2
    refine ⟨u, signature, after, selected, returned, different, ?_⟩
    rw [returned, bound]
    exact ⟨_, TypeMatchRel.expected_variable_symbol u "Bool" numberFrame (by decide) (by decide)
      (numberFrame_free different)⟩
  · have shared := raw_return_shared program chosen
    refine ⟨shared, ?_⟩
    rw [shared, bound]
    exact number_frame_rejects_bool

end Controls

#print axioms if_selection_scoped
#print axioms if_selection_succeeds_scoped
#print axioms cast_source_any
#print axioms operator_cast_accepts
#print axioms branch_call_source_scoped
#print axioms if_source_scoped
#print axioms fine_data_cast_any
#print axioms fine_query_scoped
#print axioms fine_function_scoped
#print axioms fine_if_scoped
#print axioms Controls.shared_type_removed
#print axioms scoped_if_answers
#print axioms scoped_closed_answer
#print axioms classValues_fresh_pair
#print axioms arrows_match
#print axioms operator_accepts
#print axioms operator_renewal

end ScopedIf

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
