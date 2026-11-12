import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.TypedEveryRun
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.AtomDemands

/-!
# HE's own `if` and PeTTa's `if`, on every run

HE's standard library declares `if` as a typed function:

    (: if (-> Bool Atom Atom $t))
    (= (if True $then $else) $then)
    (= (if False $then $else) $else)

PeTTa has `if` as a special form. On this program, for every Boolean `b`, a complete run of HE on
`(if b yes no)` exists, every complete run publishes exactly the branch `b` selects, and PeTTa yields
the same branch (`if_every_run`).

HE's path, each part inverted for every derivation:

* admission (`if_checks`, `if_selection`): the stored arrow is selected with one activation and no
  bindings: the condition meets `Bool`, an `Atom` demand accepts every type, `%Undefined%` accepts
  `$t`;
* the operator cast (`ifArrow_matches`, `ifArrow_accepts`): the arrow matches itself by recording
  `$t = $t`, so, unlike a closed arrow, the cast renews the frame (`renewed_cast_step`);
* the arguments: the condition is cast to `Bool`; the branches are passed unevaluated under `Atom`
  (`AtomDemands.atom_demand_source`);
* the query (`if_call_source`): the equation of `b` fires, its body `$then` or `$else` is read as the
  chosen branch, and the branch meets the return demand `$t`.

The complete run (`he_if_run`) follows the same path forward.

## Controls

* `Controls.both_branches` (positive): `(if True yes no)` gives `yes`, `(if False yes no)` gives `no`,
  on every complete run.
* `Controls.arrow_records_equality` (why the frame renews): matching the arrow of `if` with itself
  records an equality, so its bindings change, unlike `(-> Number Number)` in `TypedEveryRun`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace IfEveryRun

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel rawTypeLookupRel
  FunctionTypeRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (MatchRel MatchListAccRel MergeRel
  MergeConstraintsRel AddVarEqualityRel equalityGroundedSemantic semanticLoopFree_empty)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun NestedValues NestedCalls MarkedValues CompoundBindings DeclaredHeads
  DeclaredEveryRun TypedEveryRun AtomDemands
open AnswerBags.Controls (sym app rule rule_consFree)

variable {dispatch : GroundedDispatch} {policy : Policy}

/-! ## HE's standard-library `if` -/

/-- `(-> Bool Atom Atom $t)`. -/
abbrev ifArrow : Atom :=
  .expression [.symbol "->", sym "Bool", Atom.atomType, Atom.atomType, .var "t"]

/-- `{(: if (-> Bool Atom Atom $t)), (= (if True $then $else) $then),
(= (if False $then $else) $else)}`. -/
abbrev ifProgram : List Atom :=
  [.expression [.symbol ":", sym "if", ifArrow],
   rule (app "if" [.grounded (.bool true), .var "then", .var "else"]) (.var "then"),
   rule (app "if" [.grounded (.bool false), .var "then", .var "else"]) (.var "else")]

/-- `(if b yes no)`. -/
abbrev ifCall (b : Bool) : Atom := app "if" [.grounded (.bool b), sym "yes", sym "no"]

/-- The branch `if` takes. -/
def chosen : Bool → Atom
  | true => sym "yes"
  | false => sym "no"

/-- The selected arrow of `if`. -/
def ifPolicy : SelectedTypePolicy :=
  ⟨ifArrow, [sym "Bool", Atom.atomType, Atom.atomType], .var "t", rfl⟩

theorem if_types : StorageTypesRel (Space.ofList ifProgram) (.symbol "if") [ifArrow] :=
  .symbolKnown (.hit (.skip (fun _ same => by simp at same)
    (.skip (fun _ same => by simp at same) .nil))) (by simp)

theorem bool_types (b : Bool) :
    StorageTypesRel (Space.ofList ifProgram) (.grounded (.bool b)) [sym "Bool"] :=
  .groundedKnown (.bool b) (by simp [Atom.undefinedType])

theorem yes_types' : StorageTypesRel (Space.ofList ifProgram) (sym "yes") [Atom.undefinedType] :=
  .symbolUndefined (.skip (fun _ same => by simp at same)
    (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same) .nil)))

theorem no_types' : StorageTypesRel (Space.ofList ifProgram) (sym "no") [Atom.undefinedType] :=
  .symbolUndefined (.skip (fun _ same => by simp at same)
    (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same) .nil)))

theorem chosen_types (b : Bool) :
    StorageTypesRel (Space.ofList ifProgram) (chosen b) [Atom.undefinedType] := by
  cases b
  · exact no_types'
  · exact yes_types'

theorem chosen_data (b : Bool) : DataAtom (chosen b) := by
  cases b
  · exact .symbol (by decide) (by decide)
  · exact .symbol (by decide) (by decide)

theorem if_program : ScopedProgram ifProgram := by
  intro row member
  simp only [ifProgram, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨fun lhs rhs same => by simp at same, fun lhs rhs same => by simp at same⟩
  · refine ⟨rule_consFree fun a inside => ?_, fun lhs rhs same => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl
      · exact .grounded _
      · exact .var _
      · exact .var _
    · cases same
      decide
  · refine ⟨rule_consFree fun a inside => ?_, fun lhs rhs same => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl
      · exact .grounded _
      · exact .var _
      · exact .var _
    · cases same
      decide

/-! ## Type matching -/

/-- `Bool` accepts `Bool`, with the bindings unchanged. -/
theorem bool_matches (bindings : Bindings) :
    TypeMatchRel (sym "Bool") (sym "Bool") bindings bindings :=
  .structural (by simp [Atom.undefinedType]) (by simp [Atom.atomType]) (by simp [Atom.undefinedType])
    (by simp [Atom.atomType]) (.symSym "Bool" semanticLoopFree_empty)
    (MergeRel.mk (order := [])
      (by simp [Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.constraints, Bindings.empty]) .nil)

theorem bool_accepts (frame : Frame) :
    ∃ output, policy.matching.Rel (sym "Bool") (sym "Bool") frame.bindings output :=
  ⟨_, Completed.Frame.preserved_type_match policy frame (bool_matches _)⟩

/-- Merging no constraint changes nothing. -/
theorem merge_empty_out {b out : Bindings}
    (merged : MergeRel equalityGroundedSemantic b Bindings.empty out) : out = b := by
  cases merged with
  | @mk _ _ _ order perm folded =>
      have none : order = [] := List.Perm.eq_nil (by
        simpa [Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.constraints, Bindings.empty] using perm)
      subst none
      cases folded
      rfl

/-- **Every match of `Bool` with `Bool` keeps the bindings.** -/
theorem bool_match_output {b out : Bindings}
    (matched : TypeMatchRel (sym "Bool") (sym "Bool") b out) : out = b := by
  generalize sameType : sym "Bool" = type at matched
  cases matched with
  | undefinedLeft => simp [Atom.undefinedType] at sameType
  | atomLeft => simp [Atom.atomType] at sameType
  | undefinedRight => rfl
  | atomRight => rfl
  | structural _ _ _ _ inner merged =>
      subst sameType
      cases inner
      exact merge_empty_out merged

/-- The bindings `{$t = $t}`. -/
abbrev tEq : Bindings := Bindings.empty.addEquality "t" "t"

theorem tEq_loopFree : Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.SemanticLoopFree tEq :=
  Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.semanticLoopFree_of_assignments_nil rfl

theorem tEq_classValues : tEq.classValues "t" = [] := by decide

theorem merge_tEq : MergeRel equalityGroundedSemantic Bindings.empty tEq tEq :=
  .mk (order := [.equality "t" "t"]) (by decide)
    (.equality (.consistent tEq_classValues trivial) .nil)

/-- **The arrow of `if` matches itself**, recording `$t = $t`. -/
theorem ifArrow_matches : TypeMatchRel ifArrow ifArrow Bindings.empty tEq :=
  .structural (by simp [Atom.undefinedType]) (by simp [Atom.atomType])
    (by simp [Atom.undefinedType]) (by simp [Atom.atomType])
    (.expression
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
      tEq_loopFree)
    merge_tEq

/-- **The arrow of `if` accepts itself at a frame with no bindings**, under either matching policy. -/
theorem ifArrow_accepts {frame : Frame} (empty : frame.bindings = Bindings.empty) :
    ∃ output, policy.matching.Rel ifArrow ifArrow frame.bindings output := by
  rw [empty]
  refine ⟨tEq, ?_⟩
  cases policy.matching with
  | raw => exact ifArrow_matches
  | finite =>
      exact ⟨ifArrow_matches, fun _ => Atom.undefinedType, by
        simp [Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied, tEq,
          Bindings.addEquality, Bindings.empty]⟩

/-! ## Admission of `(if b yes no)` -/

theorem if_projections {signature : SelectedTypePolicy} (functionType : signature.functionType = ifArrow) :
    signature.argumentTypes = [sym "Bool", Atom.atomType, Atom.atomType] ∧
      signature.returnType = .var "t" := by
  have shaped : FunctionTypeRel ifArrow signature.argumentTypes signature.returnType :=
    functionType ▸ signature.isFunction
  exact FunctionTypeRel.unique shaped ifPolicy.isFunction

/-- **One accepted argument**: its check keeps one frame, with the bindings the demand keeps. -/
theorem accepted_step {space : Space} {expression : Atom} {position : Nat} {a T A : Atom}
    {frame : Frame} {rest restT : List Atom} {after : List Frame} {errors : List Atom}
    (stored : StorageTypesRel space a [A])
    (keeps : ∀ out, TypeMatchRel T A frame.bindings out → out = frame.bindings)
    (accepts : ∃ output, policy.matching.Rel T A frame.bindings output)
    (checked : Completed.ApplicabilityArgumentsRel space (rawTypeLookupRel space) policy expression
      position (a :: rest) (T :: restT) [frame] after errors) :
    ∃ frame', frame'.bindings = frame.bindings ∧
      Completed.ApplicabilityArgumentsRel space (rawTypeLookupRel space) policy expression
        (position + 1) rest restT [frame'] after errors := by
  cases checked with
  | cons head later =>
      cases head with
      | cons queried paired nilChecks =>
          cases nilChecks
          have same := StorageTypesRel.unique (show StorageTypesRel space a _ from queried) stored
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

/-- **Every application check of `(if b yes no)` keeps exactly one activation, with no bindings.** -/
theorem if_checks (b : Bool) {signature : SelectedTypePolicy} {frames : List Frame}
    {errors : List Atom} (functionType : signature.functionType = ifArrow)
    (checks : Completed.ApplicationChecksRel (Space.ofList ifProgram)
      (rawTypeLookupRel (Space.ofList ifProgram)) policy (ifCall b) Atom.undefinedType signature
      Completed.Frame.empty frames errors) :
    ∃ after, frames = [after] ∧ after.bindings = Bindings.empty := by
  have projections := if_projections functionType
  cases checks with
  | wrongArity shaped arity =>
      simp only [ifCall, app, Atom.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl⟩ := shaped
      rw [projections.1] at arity
      exact absurd rfl arity
  | checked shaped arguments returned =>
      simp only [ifCall, app, Atom.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl⟩ := shaped
      rw [projections.1] at arguments
      obtain ⟨f1, same1, rest1⟩ := accepted_step (bool_types b) (fun _ matched =>
        bool_match_output matched) (bool_accepts _) arguments
      obtain ⟨f2, same2, rest2⟩ := accepted_step yes_types' (fun _ matched =>
        Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeMatchRel.wildcard_output matched
          (Or.inr (Or.inl rfl))) (atom_demand_accepts _ _) rest1
      obtain ⟨f3, same3, rest3⟩ := accepted_step no_types' (fun _ matched =>
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
          rfl
      | rejected rejectedAll =>
          obtain ⟨output, matched⟩ := undefined_accepts (policy := policy) _ f3
          exact (rejectedAll output matched).elim

/-- **Every admission of `(if b yes no)` selects `if`'s arrow with one activation, with no
bindings.** -/
theorem if_selection (b : Bool) {outcome : Completed.InvocationSelection}
    (chosenRel : Completed.InvocationSelectionRel (Space.ofList ifProgram) Completed.rawLookup policy
      [] [] (ifCall b) (.symbol "if") Atom.undefinedType Completed.Frame.empty outcome) :
    ∃ (signature : SelectedTypePolicy) (after : Frame), signature.functionType = ifArrow ∧
      after.bindings = Bindings.empty ∧ outcome = .selected signature [after] := by
  obtain ⟨candidates, queried, scanned⟩ := chosenRel
  have same := StorageTypesRel.unique
    (show StorageTypesRel (Space.ofList ifProgram) (.symbol "if") candidates from queried) if_types
  cases scanned with
  | nil => cases same
  | nonFunction notArrow _ =>
      simp only [List.cons.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      exact absurd ⟨_, _, ifPolicy.isFunction⟩ notArrow
  | selected checks nonempty =>
      simp only [List.cons.injEq] at same
      obtain ⟨functionType, rfl⟩ := same
      obtain ⟨after, rfl, bindings⟩ := if_checks b functionType checks
      exact ⟨_, after, functionType, bindings, rfl⟩
  | rejected checks rest =>
      simp only [List.cons.injEq] at same
      obtain ⟨functionType, rfl⟩ := same
      obtain ⟨after, impossible, _⟩ := if_checks b functionType checks
      cases impossible

/-! ## Casts at one frame -/

/-- `TypedEveryRun.typed_cast_source` with the demand accepting at the one frame of the cast. -/
theorem typed_cast_source_at {space : Space} {live : List Atom} {scope : List String}
    {a expected actual : Atom} (data : DataAtom a)
    (entry : Entry.Rel policy.reentry .active a expected .cast)
    (stored : StorageTypesRel space a [actual]) {frame : Frame}
    (accepts : ∃ output, policy.matching.Rel expected actual frame.bindings output)
    {results : List Result}
    (derived : Completed.AtomRel space dispatch Completed.rawLookup live scope
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
          have same := StorageTypesRel.unique (show StorageTypesRel space a _ from queried) stored
          subst same
          obtain ⟨output, matched⟩ := accepts
          exact (rejected actual List.mem_cons_self output matched).elim
  | tuple entered => cases Entry.functional entered entry'
  | function entered => cases Entry.functional entered entry'
  | fallback entered => cases Entry.functional entered entry'
  | selectionFailed entered => cases Entry.functional entered entry'

/-! ## The typed query of `(if b yes no)` -/

theorem if_values (b : Bool) :
    ∀ v ∈ [Atom.grounded (.bool b), sym "yes", sym "no"], NestedValues.Value dispatch ifProgram v := by
  intro v member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact .data (.grounded _)
  · exact .data (.symbol (by decide) (by decide))
  · exact .data (.symbol (by decide) (by decide))

theorem if_instances (b : Bool) :
    regionInstances ifProgram "if" [.grounded (.bool b), sym "yes", sym "no"] = [chosen b] := by
  cases b <;> decide +kernel

/-- **Every derivation of the typed query of `(if b yes no)` under its return demand `$t` returns the
chosen branch.** -/
theorem if_call_source (b : Bool) {live : List Atom} {scope : List String} {value : Entry.Value}
    {frame : Frame} {children : List Result} (erased : value.erase = ifCall b)
    (called : Completed.CallRel (Space.ofList ifProgram) dispatch Completed.rawLookup live scope
      value (.var "t") frame children (policy := policy)) :
    children.map (fun r => r.1.erase) = [chosen b] := by
  have valsValues := if_values (dispatch := dispatch) b
  have ground : ∀ v ∈ [Atom.grounded (.bool b), sym "yes", sym "no"], TypeSubst.typeVars v = [] :=
    fun v member => HERuns.ground_typeVars (value_answerable (valsValues v member))
  have chosenData := chosen_data b
  have chosenEntry : Entry.Rel policy.reentry .active (chosen b) (.var "t") .cast := by
    cases b
    · exact symbol_cast_entry (name := "no") (by decide) (by decide) (by decide +kernel)
    · exact symbol_cast_entry (name := "yes") (by decide) (by decide) (by decide +kernel)
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
      have sidesEq := frontier_sides ground frame.certified.satisfiable (scoped_consFree if_program)
        frontier
      have nonempty : regionInstances ifProgram "if" [.grounded (.bool b), sym "yes", sym "no"] ≠ [] := by
        rw [if_instances]
        exact List.cons_ne_nil _ _
      apply absurd _ nonempty
      rw [regionInstances_sides, ← sidesEq]
      rfl
  | equations _ _ frontier _ equations =>
      rw [erased] at frontier
      have works := works_instances_K policy valsValues if_program frame.certified.satisfiable frontier
      rw [if_instances] at works
      obtain ⟨w, ws, ⟨_, reads⟩, rest, rfl⟩ := List.forall₂_cons_right_iff.mp works
      obtain rfl := List.forall₂_nil_right_iff.mp rest
      cases equations with
      | cons sameBindings _ boundary batch later =>
          cases later
          obtain ⟨readErase, _⟩ := reads _ sameBindings
          have readValue := value_of_data chosenData readErase
          rw [readValue] at boundary
          cases boundary with
          | producerFunction pending _ =>
              obtain ⟨⟨inner, same⟩, _⟩ := pending
              rw [Entry.Value.erase_ofAtom] at same
              cases b <;> cases same
          | producerRaw _ =>
              cases batch with
              | cons returned tail =>
                  cases tail
                  cases returned with
                  | returned answered =>
                      cases answered with
                      | notReducible same =>
                          rw [Entry.Value.erase_ofAtom] at same
                          cases b <;> simp [chosen, Atom.notReducible] at same
                      | stopped stopped =>
                          rw [Entry.Value.erase_ofAtom] at stopped
                          exact absurd stopped chosenData.not_stopped
                      | evaluate _ _ evaluated =>
                          obtain ⟨after, rfl⟩ := typed_cast_source chosenData chosenEntry
                            (chosen_types b) (variable_meets_undefined (policy := policy) "t")
                            evaluated
                          simp

/-! ## Every derivation for `(if b yes no)` -/

theorem if_data : DataAtom (.symbol "if") := .symbol (by decide) (by decide)

theorem bool_cast_entry (b : Bool) :
    Entry.Rel policy.reentry .active (.grounded (.bool b)) (sym "Bool") .cast :=
  .cast (DataAtom.grounded (.bool b)).not_stopped (.grounded _) (by decide +kernel)
    (Or.inr (Or.inl ⟨_, rfl⟩)) (fun _ => Or.inr rfl)

theorem closed_symbol (name : String) :
    ∀ x, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs (sym name) x :=
  fun _ occurs => by cases occurs

/-- **Every derivation of HE's completed relation for `(if b yes no)` publishes the chosen
branch**: the admission selects `if`'s arrow, the condition is cast to `Bool`, the branches are
passed unevaluated under `Atom`, the query selects the equation of `b`, and its body meets `$t`. -/
theorem if_source (b : Bool) {results : List Result}
    (derived : Completed.AtomRel (Space.ofList ifProgram) dispatch Completed.rawLookup [] []
      (Entry.Value.ofAtom (ifCall b)) Atom.undefinedType Completed.Frame.empty results
      (policy := policy)) :
    results.map (fun r => r.1.erase) = [chosen b] := by
  have entry := call_entry policy if_data [.grounded (.bool b), sym "yes", sym "no"]
  have shape : Completed.Frame.empty.read policy (Entry.Value.ofAtom (ifCall b)) =
      .expression .active (Entry.Value.ofAtom (.symbol "if") ::
        [Atom.grounded (.bool b), sym "yes", sym "no"].map Entry.Value.ofAtom) := by
    rw [Completed.Frame.read_empty]
    simp only [ifCall, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  have outcome : ∀ {result : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList ifProgram) Completed.rawLookup policy [] []
        (Completed.Frame.empty.read policy (Entry.Value.ofAtom (ifCall b))).erase
        (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType Completed.Frame.empty result →
      ∃ (signature : SelectedTypePolicy) (after : Frame), signature.functionType = ifArrow ∧
        after.bindings = Bindings.empty ∧ result = .selected signature [after] := by
    intro result chosenRel
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosenRel
    exact if_selection b chosenRel
  have readYes : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom (sym "yes")) =
      Entry.Value.ofAtom (sym "yes") := fun frame => HERuns.read_closed policy frame (closed_symbol _)
  have readNo : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom (sym "no")) =
      Entry.Value.ofAtom (sym "no") := fun frame => HERuns.read_closed policy frame (closed_symbol _)
  cases derived with
  | delivered entered => cases Entry.functional entered entry
  | cast entered => cases Entry.functional entered entry
  | tuple _ shaped occurs _ _ _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      rw [Entry.Value.erase_ofAtom] at occurs
      have same := Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel.unique occurs
        if_types.occurrences
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
      have returnTypeOf : ∀ {s : SelectedTypePolicy}, s.returnType = .var "t" →
          Completed.invocationReturnType s = .var "t" := by
        intro s same
        simp [Completed.invocationReturnType, same, Atom.expressionType]
      have returnType := returnTypeOf projections.2
      cases invoked with
      | cons function calls rest =>
          cases rest
          cases function with
          | evaluated _ operatorRel branches =>
              rw [functionType] at operatorRel
              obtain ⟨frF, rfl⟩ := typed_cast_source_at if_data
                (symbol_cast_entry (by decide) (by decide) (by decide +kernel)) if_types
                (ifArrow_accepts afterBindings) operatorRel
              rw [projections.1] at branches
              simp only [List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_right]
                at branches
              cases branches with
              | stopped stopped _ =>
                  rw [Entry.Value.erase_ofAtom] at stopped
                  exact absurd stopped if_data.not_stopped
              | continuing _ arguments restBranches =>
                  cases restBranches
                  cases arguments with
                  | cons conditionRel conditionBranches =>
                      obtain ⟨fr1, rfl⟩ := typed_cast_source (.grounded (.bool b)) (bool_cast_entry b)
                        (bool_types b) bool_accepts conditionRel
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
                              rw [readYes] at yesBranches
                              cases yesBranches with
                              | stopped stopped _ =>
                                  obtain ⟨stoppedYes, _⟩ := stopped
                                  rw [Entry.Value.erase_ofAtom] at stoppedYes
                                  exact absurd stoppedYes
                                    (DataAtom.symbol (name := "yes") (by decide) (by decide)).not_stopped
                              | continuing _ noArguments restYes =>
                                  cases restYes
                                  cases noArguments with
                                  | cons noRel noBranches =>
                                      have noDelivered := atom_demand_source noRel
                                      subst noDelivered
                                      rw [readNo] at noBranches
                                      cases noBranches with
                                      | stopped stopped _ =>
                                          obtain ⟨stoppedNo, _⟩ := stopped
                                          rw [Entry.Value.erase_ofAtom] at stoppedNo
                                          exact absurd stoppedNo
                                            (DataAtom.symbol (name := "no") (by decide)
                                              (by decide)).not_stopped
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
                                                        Entry.Value.ofAtom (sym "yes"),
                                                        Entry.Value.ofAtom (sym "no")], frame)).1.erase =
                                                    ifCall b := fun frame => by
                                                simp [Completed.functionAssemble, Entry.Value.erase,
                                                  ifCall, app]
                                              have answered := if_call_source b (assembled _) callRel
                                              exact publish_answers
                                                (by simp only [List.append_nil]; exact answered)
                                                (fun a member => by
                                                  rw [List.mem_singleton] at member
                                                  subst member
                                                  exact answerable_of_data (chosen_data b))
                                                priority

/-! ## A complete run -/

/-- **A cast under a typed demand whose match renews the frame.** -/
theorem renewed_cast_step (dispatch : GroundedDispatch) (policy : Policy) {space : Space}
    {atom expected actual : Atom}
    (closed : ∀ name, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs atom name)
    (entry : Entry.Rel policy.reentry .active atom expected .cast)
    (queried : StorageTypesRel space atom [actual]) (frame after : Frame)
    (renewal : Completed.Frame.TypeRenewRel policy expected actual frame after) (live : List Atom)
    (scope : List String) (stack : List Continuation) (emitted : List Result) :
    HEStep dispatch Completed.rawLookup policy
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

/-- The operator `if` cast against its arrow, at the empty activation: some renewed frame. -/
theorem if_operator_renewal (policy : Policy) :
    ∃ after : Frame, Completed.Frame.TypeRenewRel policy ifArrow ifArrow Completed.Frame.empty after := by
  have model : ∃ valuation : String → Atom,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied valuation tEq :=
    ⟨fun _ => Atom.undefinedType, by
      simp [Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied, tEq,
        Bindings.addEquality, Bindings.empty]⟩
  have matched : policy.matching.Rel ifArrow ifArrow Completed.Frame.empty.bindings tEq := by
    cases policy.matching with
    | raw => exact ifArrow_matches
    | finite => exact ⟨ifArrow_matches, model⟩
  obtain ⟨after, _, renewal⟩ := Completed.Frame.TypeRenewRel.of_modelled_match Completed.Frame.empty
    matched model
  exact ⟨after, renewal⟩

/-- `if`'s arrow is selected with the empty activation. -/
theorem if_arrow_selected (policy : Policy) (b : Bool) :
    ∃ errors, Completed.ApplicationChecksRel (Space.ofList ifProgram)
      (rawTypeLookupRel (Space.ofList ifProgram)) policy (ifCall b) Atom.undefinedType ifPolicy
      Completed.Frame.empty [Completed.Frame.empty] errors :=
  ⟨_, .checked (operator := sym "if") (arguments := [.grounded (.bool b), sym "yes", sym "no"]) rfl
    (.cons (.cons (bool_types b)
      (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy _
        (bool_matches _)))) .nil) .nil)
      (.cons (.cons yes_types'
        (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy _
          (.atomLeft _ _)))) .nil) .nil)
        (.cons (.cons no_types'
          (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy _
            (.atomLeft _ _)))) .nil) .nil) .nil)))
    (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy _
      (.undefinedLeft _ _)))) .nil)⟩

/-- **HE's admission of `(if b yes no)` selects `if`'s arrow.** -/
theorem if_selection_succeeds (policy : Policy) (b : Bool) :
    Completed.InvocationSelectionRel (Space.ofList ifProgram) Completed.rawLookup policy [] []
      (ifCall b) (.symbol "if") Atom.undefinedType Completed.Frame.empty
      (.selected ifPolicy [Completed.Frame.empty]) := by
  obtain ⟨errors, checks⟩ := if_arrow_selected policy b
  exact ⟨[ifPolicy.functionType], if_types, .selected checks (List.cons_ne_nil _ _)⟩

theorem symbol_not_stopped (name : String) (notEmpty : name ≠ "Empty") (notError : name ≠ "Error") :
    ¬ IsEmptyOrErrorRel (sym name) :=
  (DataAtom.symbol notEmpty notError).not_stopped

/-- **The function application of `(if b yes no)`**: the operator is cast against its arrow (the
match renews the frame), the condition against `Bool`, the branches are delivered under `Atom`, and
the call value is assembled. -/
theorem if_function_segment (dispatch : GroundedDispatch) (policy : Policy) (b : Bool)
    (stack : List Continuation) :
    ∃ results : List Result,
      HERuns.HESteps dispatch Completed.rawLookup policy
        ⟨Space.ofList ifProgram, .work (.function [Completed.invocationReturnType ifPolicy] []
          Atom.undefinedType ifPolicy (Entry.Value.ofAtom (.symbol "if"))
          [Entry.Value.ofAtom (.grounded (.bool b)), Entry.Value.ofAtom (sym "yes"),
            Entry.Value.ofAtom (sym "no")] Completed.Frame.empty), stack, []⟩
        ⟨Space.ofList ifProgram, .returning results, stack, []⟩ ∧
      ∃ value activation, results = [(value, activation)] ∧ value.erase = ifCall b := by
  obtain ⟨frF, renewal⟩ := if_operator_renewal policy
  have readYes : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom (sym "yes")) =
      Entry.Value.ofAtom (sym "yes") := fun frame => HERuns.read_closed policy frame (closed_symbol _)
  have readNo : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom (sym "no")) =
      Entry.Value.ofAtom (sym "no") := fun frame => HERuns.read_closed policy frame (closed_symbol _)
  have ifCast := renewed_cast_step dispatch policy (atom := .symbol "if") (closed_symbol "if")
    (symbol_cast_entry (by decide) (by decide) (by decide +kernel)) if_types Completed.Frame.empty frF
    renewal
  have boolCast := typed_cast dispatch policy (atom := .grounded (.bool b)) (expected := sym "Bool")
    (fun _ occurs => by cases occurs) (bool_cast_entry b) (bool_types b) frF (bool_matches _)
  apply Exists.intro
  refine ⟨?_, ?_⟩
  · refine .head (.internal (.functionStart rfl)) ?_
    refine .head (ifCast _ _ _ _) ?_
    refine .head (.internal .functionHeads) ?_
    refine .head (.internal (.functionBranchesContinue ?_)) ?_
    · simpa using if_data.not_stopped
    refine .head (.internal .argumentsCons) ?_
    refine .head (boolCast _ _ _ _) ?_
    refine .head (.internal .arguments) ?_
    refine .head (.internal (.argumentBranchesContinue ?_)) ?_
    · rintro ⟨stopped, _⟩
      exact (DataAtom.grounded (.bool b)).not_stopped (by simpa using stopped)
    refine .head (.internal .argumentsCons) ?_
    refine .head (.internal (.delivered (atom_demand_deliver _))) ?_
    refine .head (.internal .arguments) ?_
    refine .head (.internal (.argumentBranchesContinue ?_)) ?_
    · rintro ⟨stopped, _⟩
      rw [readYes] at stopped
      exact symbol_not_stopped "yes" (by decide) (by decide) (by simpa using stopped)
    refine .head (.internal .argumentsCons) ?_
    refine .head (.internal (.delivered (atom_demand_deliver _))) ?_
    refine .head (.internal .arguments) ?_
    refine .head (.internal (.argumentBranchesContinue ?_)) ?_
    · rintro ⟨stopped, _⟩
      rw [readNo] at stopped
      exact symbol_not_stopped "no" (by decide) (by decide) (by simpa using stopped)
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
    simp [Entry.Value.erase, readYes, readNo, ifCall, app]

/-- **The typed query of `(if b yes no)`**: the query selects the equation of `b`, reads its body
`$then` or `$else` as the chosen branch, and the branch meets the return demand `$t`. -/
theorem if_query (dispatch : GroundedDispatch) (notHost : ¬ dispatch.executable (.symbol "if"))
    (policy : Policy) (b : Bool) (value : Entry.Value) (erased : value.erase = ifCall b)
    (activation : Frame) (stack : List Continuation) :
    ∃ results : List Result,
      HERuns.HESteps dispatch Completed.rawLookup policy
        ⟨Space.ofList ifProgram, .work (.call [] [] value (.var "t") activation), stack, []⟩
        ⟨Space.ofList ifProgram, .returning results, stack, []⟩ ∧
      results.map (fun r => r.1.erase) = [chosen b] := by
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList ifProgram) [.var "t"] (ifCall b)
    activation.bindings
  have instances := works_instances_K policy (if_values (dispatch := dispatch) b) if_program
    activation.certified.satisfiable frontier
  rw [if_instances] at instances
  obtain ⟨w, ws, ⟨_, reads⟩, rest, rfl⟩ := List.forall₂_cons_right_iff.mp instances
  obtain rfl := List.forall₂_nil_right_iff.mp rest
  have frontier' : EquationFrontierRel (Space.ofList ifProgram) [.var "t"] value.erase
      activation.bindings [w] := by
    rw [erased]
    exact frontier
  obtain ⟨environments, paired⟩ := Entry.Value.UnifyRel.equation_frontier
    (policy := policy.rebuilding) activation.certified frontier'
  obtain ⟨after, unified, certificate⟩ := forall₂_left_exists paired w List.mem_cons_self
  let output : Frame := ⟨w.bindings, after, certificate⟩
  obtain ⟨readErase, _⟩ := reads output rfl
  have readBody := value_of_data (chosen_data b) readErase
  have chosenEntry : Entry.Rel policy.reentry .active (chosen b) (.var "t") .cast := by
    cases b
    · exact symbol_cast_entry (name := "no") (by decide) (by decide) (by decide +kernel)
    · exact symbol_cast_entry (name := "yes") (by decide) (by decide) (by decide +kernel)
  have chosenClosed : ∀ name, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs
      (chosen b) name := by
    cases b
    · exact closed_symbol "no"
    · exact closed_symbol "yes"
  have chosenCast := typed_cast dispatch policy (atom := chosen b) (expected := .var "t")
    chosenClosed chosenEntry (chosen_types b) output (.undefinedRight _ _)
  have notError : ¬ IsErrorRel value.erase := by
    rw [erased]
    rintro ⟨tail, same⟩
    simp at same
  have nonGrounded : NonGroundedCallRel dispatch value.erase := by
    rw [erased]
    refine And.intro ?_ (by cases b <;> decide +kernel)
    rintro ⟨operator, arguments, same, executable⟩
    simp only [ifCall, app, Atom.expression.injEq, List.cons.injEq] at same
    rw [← same.1] at executable
    exact notHost executable
  refine ⟨(([(Entry.Value.ofAtom (chosen b), output)] ++ []) ++ []), ?_, by simp⟩
  refine .head (.internal (.callEquations notError nonGrounded frontier' (List.cons_ne_nil _ _))) ?_
  refine .head (.internal (.equationsCons (output := output) rfl unified)) ?_
  rw [readBody]
  refine .head (.internal (.boundaryProducerRaw ?_)) ?_
  · rintro ⟨⟨inner, same⟩, _⟩
    rw [Entry.Value.erase_ofAtom] at same
    cases b <;> cases same
  refine .head (.internal .boundaryBatch) ?_
  refine .head (.internal .boundaryBatchCons) ?_
  refine .head (.internal .boundaryReturned) ?_
  refine .head (.internal (.returnEvaluate ?_ ?_)) ?_
  · rw [Entry.Value.erase_ofAtom]
    cases b <;> simp [chosen, Atom.notReducible]
  · rw [Entry.Value.erase_ofAtom]
    exact (chosen_data b).not_stopped
  refine .head (chosenCast _ _ _ _) ?_
  refine .head (.internal .append) ?_
  refine .head (.internal .boundaryBatchNil) ?_
  refine .head (.internal .prepend) ?_
  refine .head (.internal .append) ?_
  refine .head (.internal .equationsNil) ?_
  exact .single (.internal .prepend)

/-- **A complete run of `(if b yes no)` on HE's machine, publishing the chosen branch.** -/
theorem he_if_run (dispatch : GroundedDispatch) (notHost : ¬ dispatch.executable (.symbol "if"))
    (policy : Policy) (b : Bool) :
    ∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList ifProgram) (ifCall b) Atom.undefinedType)
          ⟨Space.ofList ifProgram, .returning [], [], heAnswers⟩ ∧
        heAnswers.map (fun r => r.1.erase) = [chosen b] := by
  have entry := call_entry policy if_data [.grounded (.bool b), sym "yes", sym "no"]
  have shape : Completed.Frame.empty.read policy (Entry.Value.ofAtom (ifCall b)) =
      .expression .active (Entry.Value.ofAtom (.symbol "if") ::
        [Atom.grounded (.bool b), sym "yes", sym "no"].map Entry.Value.ofAtom) := by
    rw [Completed.Frame.read_empty]
    simp only [ifCall, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  have selection : Completed.ArgumentService.historical.selection (Space.ofList ifProgram)
      Completed.rawLookup policy [] []
      (Completed.Frame.empty.read policy (Entry.Value.ofAtom (ifCall b))).erase
      (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType Completed.Frame.empty
      (.selected ifPolicy [Completed.Frame.empty]) := by
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom]
    exact if_selection_succeeds policy b
  have step := LocalStepWith.atomFunction (admission := .historical)
    (space := Space.ofList ifProgram) (dispatch := dispatch) (lookup := Completed.rawLookup)
    (live := []) (scope := []) (stack := []) entry shape selection
  have published : (Completed.Frame.empty.read policy (Entry.Value.ofAtom (ifCall b))).erase =
      ifCall b := by
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom]
  rw [published] at step
  have returned : Completed.invocationReturnType ifPolicy = .var "t" := by
    simp [Completed.invocationReturnType, ifPolicy, Atom.expressionType]
  obtain ⟨F, pathF, value, activation, rfl, erased⟩ := if_function_segment dispatch policy b
    (.calls [] [] (Completed.invocationReturnType ifPolicy) ::
      .append (.invocations [] [] Atom.undefinedType ifPolicy (Entry.Value.ofAtom (.symbol "if"))
        [Entry.Value.ofAtom (.grounded (.bool b)), Entry.Value.ofAtom (sym "yes"),
          Entry.Value.ofAtom (sym "no")] []) :: [.publish (ifCall b)])
  obtain ⟨Q, pathQ, eraseQ⟩ := if_query dispatch notHost policy b value erased activation
    (.append (.calls [] [] (.var "t") []) ::
      .append (.invocations [] [] Atom.undefinedType ifPolicy (Entry.Value.ofAtom (.symbol "if"))
        [Entry.Value.ofAtom (.grounded (.bool b)), Entry.Value.ofAtom (sym "yes"),
          Entry.Value.ofAtom (sym "no")] []) :: [.publish (ifCall b)])
  have clean : ∀ r ∈ (Q ++ []) ++ [], Answerable r.1.erase := by
    intro r member
    simp only [List.append_nil] at member
    have inQ : r.1.erase ∈ [chosen b] := by
      rw [← eraseQ]
      exact List.mem_map.mpr ⟨r, member, rfl⟩
    rw [List.mem_singleton] at inQ
    rw [inQ]
    exact answerable_of_data (chosen_data b)
  obtain ⟨publishedAnswers, eraseP, pathP⟩ := NestedArguments.HENested.publish_step
    (dispatch := dispatch) (lookup := Completed.rawLookup) (policy := policy) (atoms := ifProgram)
    (ifCall b) ((Q ++ []) ++ []) clean [] []
  refine ⟨publishedAnswers, ?_, by rw [eraseP]; simpa using eraseQ⟩
  refine .head (.internal step) ?_
  refine .head (.internal .invocationsCons) ?_
  refine .trans pathF ?_
  refine .head (.internal .calls) ?_
  rw [returned]
  refine .head (.internal .callsCons) ?_
  refine .trans pathQ ?_
  refine .head (.internal .append) ?_
  refine .head (.internal .callsNil) ?_
  refine .head (.internal .prepend) ?_
  refine .head (.internal .append) ?_
  refine .head (.internal .invocationsNil) ?_
  refine .head (.internal .prepend) ?_
  exact pathP.trans (HERuns.publish_all _ publishedAnswers [])

/-! ## PeTTa's `if` -/

/-- **PeTTa's special form takes the same branch**, from fuel `10` on. -/
theorem petta_if (b : Bool) :
    ∀ n, 10 ≤ n → Streaming.values (Streaming.advance (translate ifProgram) n
      (Streaming.enter { state := store ifProgram } (ifCall b))) = [chosen b] := by
  cases b
  · have done : (Streaming.advance (translate ifProgram) 10
        (Streaming.enter { state := store ifProgram } (ifCall false))).agenda.length = 0 := by
      decide +kernel
    have value : Streaming.values (Streaming.advance (translate ifProgram) 10
        (Streaming.enter { state := store ifProgram } (ifCall false))) = [chosen false] := by
      decide +kernel
    intro n bigger
    rw [advance_stable (List.eq_nil_of_length_eq_zero done) n bigger]
    exact value
  · have done : (Streaming.advance (translate ifProgram) 10
        (Streaming.enter { state := store ifProgram } (ifCall true))).agenda.length = 0 := by
      decide +kernel
    have value : Streaming.values (Streaming.advance (translate ifProgram) 10
        (Streaming.enter { state := store ifProgram } (ifCall true))) = [chosen true] := by
      decide +kernel
    intro n bigger
    rw [advance_stable (List.eq_nil_of_length_eq_zero done) n bigger]
    exact value

/-! ## Every run -/

/-- **HE's own `if` on every run.** On HE's standard-library `if`
(`(: if (-> Bool Atom Atom $t))` with its two equations), historical lookup, any policy and any
dispatch that does not execute `if`: a complete run of `(if b yes no)` exists, every complete run
publishes exactly the branch `b` selects, and PeTTa's special form yields the same from fuel `10`
on. -/
theorem if_every_run (dispatch : GroundedDispatch) (notHost : ¬ dispatch.executable (.symbol "if"))
    (policy : Policy) (b : Bool) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList ifProgram) (ifCall b) Atom.undefinedType)
          ⟨Space.ofList ifProgram, .returning [], [], heAnswers⟩) ∧
      (∀ emitted : List Result,
        Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
            (load (Space.ofList ifProgram) (ifCall b) Atom.undefinedType)
            ⟨Space.ofList ifProgram, .returning [], [], emitted⟩ →
          emitted.map (fun r => r.1.erase) = [chosen b]) ∧
      ∀ n, 10 ≤ n → Streaming.values (Streaming.advance (translate ifProgram) n
        (Streaming.enter { state := store ifProgram } (ifCall b))) = [chosen b] := by
  obtain ⟨heAnswers, path, _⟩ := he_if_run dispatch notHost policy b
  exact ⟨⟨heAnswers, path⟩, fun emitted run => if_source b (complete_source run), petta_if b⟩

/-! ## Controls -/

namespace Controls

open WholeRunWords.Double (noHost)

/-- **Positive control, both branches**: `(if True yes no)` publishes `yes` and `(if False yes no)`
publishes `no`, on every complete run of HE, as in PeTTa. -/
theorem both_branches (policy : Policy) :
    (∀ emitted : List Result,
      Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList ifProgram) (ifCall true) Atom.undefinedType)
          ⟨Space.ofList ifProgram, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [sym "yes"]) ∧
      ∀ emitted : List Result,
        Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
            (load (Space.ofList ifProgram) (ifCall false) Atom.undefinedType)
            ⟨Space.ofList ifProgram, .returning [], [], emitted⟩ →
          emitted.map (fun r => r.1.erase) = [sym "no"] :=
  ⟨(if_every_run noHost (fun impossible => impossible) policy true).2.1,
    (if_every_run noHost (fun impossible => impossible) policy false).2.1⟩

/-- **The arrow of `if` is no closed arrow**: matching it with itself records `$t = $t`, so its cast
renews the frame (`ifArrow_matches`), while `(-> Number Number)` matches itself with the bindings
unchanged. -/
theorem arrow_records_equality :
    TypeMatchRel ifArrow ifArrow Bindings.empty tEq ∧ tEq ≠ Bindings.empty := by
  refine ⟨ifArrow_matches, fun same => ?_⟩
  have equalities := congrArg Bindings.equalities same
  simp [tEq, Bindings.addEquality, Bindings.empty] at equalities

end Controls

#print axioms bool_match_output
#print axioms ifArrow_matches
#print axioms ifArrow_accepts
#print axioms if_checks
#print axioms if_selection
#print axioms typed_cast_source_at
#print axioms if_call_source
#print axioms if_source
#print axioms renewed_cast_step
#print axioms if_function_segment
#print axioms if_query
#print axioms he_if_run
#print axioms petta_if
#print axioms if_every_run
#print axioms Controls.both_branches
#print axioms Controls.arrow_records_equality

end IfEveryRun

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
