import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.IfEveryRun

/-!
# HE's `if` never runs the branch it leaves, whatever that branch is

`IfEveryRun` compares HE's standard-library `if` with PeTTa's on `(if b yes no)` in the program of
`if` alone: both branches are data, and every argument of the equation query is a value. Here the
branch `if` leaves is **any closed atom**, for example `(loop)` in a program whose row
`(= (loop) (loop))` makes it diverge, and the program may hold other rows.

* `work_read_ground`, `works_instances_ground`: HE's read of an equation body for a call whose
  arguments are ground, not necessarily values: the read's atom is PeTTa's instance. This removes the
  value condition of `MarkedValues.works_instances_K` for the queries of `if`, whose `$then` and
  `$else` take any atom.
* `IfProgram`, `Branches`: the conditions, stated on the program and the call: `if` has its stored
  arrow; the rows are symbol-headed `cons`-free equations whose bodies use their left side's
  variables; the branch taken is a data atom without declared type; both branches are closed with one
  stored type each; and `if`'s region on the call has the taken branch as its one instance.
* `branch_source`: every derivation of HE's completed relation for `(if b y n)` publishes the taken
  branch. The other branch is passed under the `Atom` demand and then only bound by the query's
  unifier; no derivation evaluates it.
* `branch_run`: a complete run of HE's machine exists.
* `petta_branch`: PeTTa's special form yields the taken branch from fuel `10` on, for every closed
  branch it leaves (a symbolic run, the left branch is never inspected).
* `branch_every_run`: the three together.

## Controls

* `Controls.loop_left` (the test `(if True yes (loop))`): with `(= (loop) (loop))` in the program,
  every complete run of HE publishes `yes`, and so does PeTTa; `Controls.loop_left_false` is the
  mirror `(if False (loop) no)`.
* `Controls.loop_diverges_alone` (negative): the same `(loop)` loaded under `%Undefined%` has an
  infinite run on HE's machine; only the `Atom` demand of `if` keeps it from running.
* `Controls.empty_left` (positive, a stopped atom): the left branch may even be `Empty`; delivered
  under `Atom` it is the original argument, so it does not stop the application.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace IfBranches

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel rawTypeLookupRel
  FunctionTypeRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement (applyTypeValuation
  TypeBindingSatisfied)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (AtomOccurs)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open HEOnTheStep (HEConfig)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (isGroundAtom applySubst)
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun NestedValues NestedCalls MarkedValues CompoundBindings DeclaredHeads
  DeclaredEveryRun TypedEveryRun AtomDemands IfEveryRun
open AnswerBags.Controls (sym app rule rule_consFree)

variable {dispatch : GroundedDispatch} {policy : Policy}

/-! ## Reads for ground arguments -/

/-- **HE reads a work's body as PeTTa's instance, for ground arguments that need not be values.**
For a work of the frontier of a call whose arguments are ground, on a program whose bodies use only
their left side's variables, the row's sides give an instance, and under every frame whose bindings
are the work's, the atom of HE's read of the fresh body is that instance. -/
theorem work_read_ground (policy : Policy) {atoms live : List Atom} {f : String}
    {args : List Atom} {incoming : Bindings} (ground : ∀ a ∈ args, TypeSubst.typeVars a = [])
    (program : ScopedProgram atoms) {works : List EquationWork}
    (frontier : EquationFrontierRel (Space.ofList atoms) live (.expression (.symbol f :: args))
      incoming works)
    {w : EquationWork} (member : w ∈ works) :
    ∃ i, sidesInstance args (w.left, w.right) = some i ∧
      ∀ output : Frame, output.bindings = w.bindings →
        (output.read policy (Entry.Value.ofAtom w.body)).erase = i := by
  obtain ⟨matched, occurrence⟩ := frontier.occurrence member
  have stored : Atom.expression [.symbol "=", w.left, w.right] ∈ atoms :=
    List.mem_of_getElem? occurrence.stored
  obtain ⟨consFree, boundRow⟩ := program _ stored
  obtain ⟨h, ps, leftShape, psFree⟩ := consFree w.left w.right rfl
  have varsBound := boundRow w.left w.right rfl
  obtain ⟨rename, _, renamedLeft, renamedRight, _⟩ := occurrence.selected.1
  have patternEq := Mettapedia.Languages.MeTTa.HE.EquationFreshening.alphaRename_eq renamedLeft
  have bodyEq := Mettapedia.Languages.MeTTa.HE.EquationFreshening.alphaRename_eq renamedRight
  have groundQuery : TypeSubst.typeVars (.expression (.symbol f :: args)) = [] := by
    simp only [TypeSubst.typeVars, TypeSubst.typeVarsList, List.nil_append]
    exact (Mettapedia.Languages.MeTTa.HE.TypeGrounding.typeVarsList_eq_nil_iff args).mpr ground
  have instantiates : ∀ v, TypeBindingSatisfied v w.bindings →
      applyTypeValuation (v ∘ rename) w.left = .expression (.symbol f :: args) := by
    intro v model
    have equal := ((occurrence.solutions v).mp model).1
    rw [patternEq,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ApplicationEquivariance.applyTypeValuation_renameTypeVars,
      Mettapedia.Languages.MeTTa.HE.HOLContract.applyTypeValuation_of_ground v groundQuery] at equal
    exact equal.symm
  obtain ⟨model, satisfiedWork⟩ := occurrence.result.1.2
  have first := instantiates model satisfiedWork
  rw [leftShape] at first
  simp only [applyTypeValuation, List.map_cons, Atom.expression.injEq, List.cons.injEq,
    Atom.symbol.injEq] at first
  obtain ⟨sameHead, sameArgs⟩ := first
  obtain ⟨bound, matchedBound, _⟩ := RegionsWithVariables.completesConsistent_list (model ∘ rename) ps
    (fun p m => RegionsWithVariables.completesConsistent _ (psFree p m)) []
    (RegionsWithVariables.consistent_nil _)
  rw [sameArgs] at matchedBound
  obtain ⟨_, _, instanceArgs⟩ := RegionsWithVariables.sound_list ps
    (fun p m => RegionsWithVariables.sound (psFree p m)) [] bound args matchedBound
  have boundInstance := instanceArgs bound (RegionsWithVariables.Extends.refl bound)
  have agree : ∀ v, TypeBindingSatisfied v w.bindings → ∀ x ∈ TypeSubst.typeVars w.left,
      (v ∘ rename) x = RegionsWithVariables.asValuation bound x := by
    intro v model x member
    apply agree_of_same (v ∘ rename) (RegionsWithVariables.asValuation bound) w.left
      _ x member
    rw [instantiates v model, leftShape]
    simp only [applyTypeValuation, List.map_cons, boundInstance, sameHead]
  have bodyForced : ∀ v, TypeBindingSatisfied v w.bindings →
      applyTypeValuation v w.body = applySubst bound w.right := by
    intro v model
    rw [bodyEq,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ApplicationEquivariance.applyTypeValuation_renameTypeVars,
      applySubst_eq_valuation]
    exact Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.applyTypeValuation_congr_of_typeVars
      w.right fun x member => agree v model x (varsBound x member)
  have equation : LiveEquations.equationOfRow (.expression [.symbol "=", w.left, w.right]) =
      some ⟨f, ps, w.right⟩ := by
    rw [leftShape, sameHead]
    rfl
  refine ⟨applySubst bound w.right, ?_, fun output sameBindings => ?_⟩
  · simp only [sidesInstance, equation, Option.bind_some, instanceOf, matchedBound, Option.map_some]
  · have certified :
        Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory.ReadoutCertificate
          w.bindings (Entry.Value.eraseEnvironment output.environment) := by
      have := output.certified
      rwa [sameBindings] at this
    unfold Completed.Frame.read
    rw [Entry.Value.erase_substitute_environment, Entry.Value.erase_ofAtom]
    exact certified.forced_read w.body _ bodyForced

/-- **The works of a frontier and the region's instances, for ground arguments.** -/
theorem works_instances_ground (policy : Policy) {atoms live : List Atom} {f : String}
    {args : List Atom} {incoming : Bindings} (ground : ∀ a ∈ args, TypeSubst.typeVars a = [])
    (program : ScopedProgram atoms)
    (satisfiable : ∃ model : String → Atom, TypeBindingSatisfied model incoming)
    {works : List EquationWork}
    (frontier : EquationFrontierRel (Space.ofList atoms) live (.expression (.symbol f :: args))
      incoming works) :
    List.Forall₂ (fun w i => sidesInstance args (w.left, w.right) = some i ∧
        ∀ output : Frame, output.bindings = w.bindings →
          (output.read policy (Entry.Value.ofAtom w.body)).erase = i)
      works (regionInstances atoms f args) := by
  have sidesEq := frontier_sides ground satisfiable (scoped_consFree program) frontier
  have listed := forall₂_filterMap (fun w : EquationWork => sidesInstance args (w.left, w.right))
    (fun w i => ∀ output : Frame, output.bindings = w.bindings →
      (output.read policy (Entry.Value.ofAtom w.body)).erase = i)
    works fun w member => work_read_ground policy ground program frontier member
  have instancesEq : works.filterMap (fun w => sidesInstance args (w.left, w.right)) =
      regionInstances atoms f args := by
    rw [regionInstances_sides, ← sidesEq, List.filterMap_map]
    rfl
  rw [instancesEq] at listed
  exact listed

/-! ## The program and the branches -/

/-- `(if b y n)`. -/
abbrev callOf (b : Bool) (y n : Atom) : Atom := app "if" [.grounded (.bool b), y, n]

/-- The branch `if` takes on `b`. -/
def pick : Bool → Atom → Atom → Atom
  | true, y, _ => y
  | false, _, n => n

/-- **A program carrying HE's `if`**: the stored type of `if` is its standard-library arrow, and the
rows are symbol-headed, `cons`-free equations whose bodies use only their left side's variables. -/
structure IfProgram (atoms : List Atom) : Prop where
  types : StorageTypesRel (Space.ofList atoms) (.symbol "if") [ifArrow]
  rows : ScopedProgram atoms

/-- **The branches of `(if b y n)`**, conditions on the program and the call: the branch taken is a
data atom without declared type; both branches are closed and have one stored type each; and the
region of `if` on the call has the taken branch as its only instance. Nothing else is asked of the
branch left: it may be any closed atom, a divergent call included. -/
structure Branches (atoms : List Atom) (b : Bool) (y n : Atom) : Prop where
  takenData : DataAtom (pick b y n)
  takenNotRefused : pick b y n ≠ Atom.notReducible
  takenUndeclared : StorageTypesRel (Space.ofList atoms) (pick b y n) [Atom.undefinedType]
  closedYes : ∀ name, ¬ AtomOccurs y name
  closedNo : ∀ name, ¬ AtomOccurs n name
  groundYes : isGroundAtom y = true
  groundNo : isGroundAtom n = true
  typedYes : ∃ T, StorageTypesRel (Space.ofList atoms) y [T]
  typedNo : ∃ T, StorageTypesRel (Space.ofList atoms) n [T]
  region : regionInstances atoms "if" [.grounded (.bool b), y, n] = [pick b y n]

/-- Every Boolean has the stored type `Bool`, in every space. -/
theorem bool_types_in (space : Space) (b : Bool) :
    StorageTypesRel space (.grounded (.bool b)) [sym "Bool"] :=
  .groundedKnown (.bool b) (by simp [Atom.undefinedType])

/-- A data atom enters the demand `$t` by a cast. -/
theorem data_var_entry {d : Atom} (data : DataAtom d) (name : String) :
    Entry.Rel policy.reentry .active d (.var name) .cast := by
  cases data with
  | symbol notEmpty notError =>
      exact symbol_cast_entry notEmpty notError
        (by simp [Atom.atomType, Atom.symbolType, Atom.variableType])
  | grounded value =>
      exact .cast (DataAtom.grounded value).not_stopped (.grounded _)
        (by simp [Atom.atomType, Atom.groundedType, Atom.variableType])
        (Or.inr (Or.inl ⟨_, rfl⟩)) (fun _ => Or.inr rfl)

theorem data_closed {d : Atom} (data : DataAtom d) : ∀ name, ¬ AtomOccurs d name :=
  (answerable_of_data data).closed

/-! ## Admission -/

/-- **Every application check of `(if b y n)` keeps exactly one activation, with no bindings**,
when `y` and `n` have one stored type each. -/
theorem branch_checks {atoms : List Atom} (b : Bool) {y n Ty Tn : Atom}
    (typesY : StorageTypesRel (Space.ofList atoms) y [Ty])
    (typesN : StorageTypesRel (Space.ofList atoms) n [Tn])
    {signature : SelectedTypePolicy} {frames : List Frame} {errors : List Atom}
    (functionType : signature.functionType = ifArrow)
    (checks : Completed.ApplicationChecksRel (Space.ofList atoms)
      (rawTypeLookupRel (Space.ofList atoms)) policy (callOf b y n) Atom.undefinedType signature
      Completed.Frame.empty frames errors) :
    ∃ after, frames = [after] ∧ after.bindings = Bindings.empty := by
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
          rfl
      | rejected rejectedAll =>
          obtain ⟨output, matched⟩ := undefined_accepts (policy := policy) _ f3
          exact (rejectedAll output matched).elim

/-- **Every admission of `(if b y n)` selects `if`'s arrow with one activation, with no bindings.** -/
theorem branch_selection {atoms : List Atom} (program : IfProgram atoms) (b : Bool) {y n Ty Tn : Atom}
    (typesY : StorageTypesRel (Space.ofList atoms) y [Ty])
    (typesN : StorageTypesRel (Space.ofList atoms) n [Tn])
    {outcome : Completed.InvocationSelection}
    (chosenRel : Completed.InvocationSelectionRel (Space.ofList atoms) Completed.rawLookup policy
      [] [] (callOf b y n) (.symbol "if") Atom.undefinedType Completed.Frame.empty outcome) :
    ∃ (signature : SelectedTypePolicy) (after : Frame), signature.functionType = ifArrow ∧
      after.bindings = Bindings.empty ∧ outcome = .selected signature [after] := by
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
      obtain ⟨after, rfl, bindings⟩ := branch_checks b typesY typesN functionType checks
      exact ⟨_, after, functionType, bindings, rfl⟩
  | rejected checks rest =>
      simp only [List.cons.injEq] at same
      obtain ⟨functionType, rfl⟩ := same
      obtain ⟨after, impossible, _⟩ := branch_checks b typesY typesN functionType checks
      cases impossible

/-! ## The query of `(if b y n)` -/

theorem call_ground {b : Bool} {y n : Atom} (closedY : ∀ name, ¬ AtomOccurs y name)
    (closedN : ∀ name, ¬ AtomOccurs n name) :
    ∀ a ∈ [Atom.grounded (.bool b), y, n], TypeSubst.typeVars a = [] := by
  intro a member
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name inside
  have occurs := (Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars a
    name).mpr inside
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · cases occurs
  · exact closedY name occurs
  · exact closedN name occurs

/-- **Every derivation of the typed query of `(if b y n)` under its return demand `$t` returns the
taken branch.** The query reads the taken branch as `$then` or `$else`; the other branch is only
bound by the unifier. -/
theorem branch_call_source {atoms : List Atom} (program : IfProgram atoms) {b : Bool} {y n : Atom}
    (branches : Branches atoms b y n) {live : List Atom} {scope : List String}
    {value : Entry.Value} {frame : Frame} {children : List Result} (erased : value.erase = callOf b y n)
    (called : Completed.CallRel (Space.ofList atoms) dispatch Completed.rawLookup live scope
      value (.var "t") frame children (policy := policy)) :
    children.map (fun r => r.1.erase) = [pick b y n] := by
  have ground := call_ground (b := b) branches.closedYes branches.closedNo
  have takenEntry : Entry.Rel policy.reentry .active (pick b y n) (.var "t") .cast :=
    data_var_entry branches.takenData "t"
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
                          obtain ⟨after, rfl⟩ := typed_cast_source branches.takenData takenEntry
                            branches.takenUndeclared (variable_meets_undefined (policy := policy) "t")
                            evaluated
                          simp

/-! ## Every derivation for `(if b y n)` -/

/-- **Every derivation of HE's completed relation for `(if b y n)` publishes the taken branch**:
the admission selects `if`'s arrow, the condition is cast to `Bool`, both branches are delivered
under `Atom` as they are (a delivered argument equals its original, so it never stops the
application), the query selects the equation of `b`, and its body meets `$t`. -/
theorem branch_source {atoms : List Atom} (program : IfProgram atoms) {b : Bool} {y n : Atom}
    (branches : Branches atoms b y n) {results : List Result}
    (derived : Completed.AtomRel (Space.ofList atoms) dispatch Completed.rawLookup [] []
      (Entry.Value.ofAtom (callOf b y n)) Atom.undefinedType Completed.Frame.empty results
      (policy := policy)) :
    results.map (fun r => r.1.erase) = [pick b y n] := by
  obtain ⟨Ty, typesY⟩ := branches.typedYes
  obtain ⟨Tn, typesN⟩ := branches.typedNo
  have entry := call_entry policy if_data [.grounded (.bool b), y, n]
  have shape : Completed.Frame.empty.read policy (Entry.Value.ofAtom (callOf b y n)) =
      .expression .active (Entry.Value.ofAtom (.symbol "if") ::
        [Atom.grounded (.bool b), y, n].map Entry.Value.ofAtom) := by
    rw [Completed.Frame.read_empty]
    simp only [callOf, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  have outcome : ∀ {result : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList atoms) Completed.rawLookup policy [] []
        (Completed.Frame.empty.read policy (Entry.Value.ofAtom (callOf b y n))).erase
        (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType Completed.Frame.empty result →
      ∃ (signature : SelectedTypePolicy) (after : Frame), signature.functionType = ifArrow ∧
        after.bindings = Bindings.empty ∧ result = .selected signature [after] := by
    intro result chosenRel
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosenRel
    exact branch_selection program b typesY typesN chosenRel
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

/-! ## A complete run -/

/-- `if`'s arrow is selected with the empty activation, for branches with one stored type each. -/
theorem branch_arrow_selected (policy : Policy) {atoms : List Atom} (b : Bool) {y n Ty Tn : Atom}
    (typesY : StorageTypesRel (Space.ofList atoms) y [Ty])
    (typesN : StorageTypesRel (Space.ofList atoms) n [Tn]) :
    ∃ errors, Completed.ApplicationChecksRel (Space.ofList atoms)
      (rawTypeLookupRel (Space.ofList atoms)) policy (callOf b y n) Atom.undefinedType ifPolicy
      Completed.Frame.empty [Completed.Frame.empty] errors :=
  ⟨_, .checked (operator := sym "if") (arguments := [.grounded (.bool b), y, n]) rfl
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
      (.undefinedLeft _ _)))) .nil)⟩

/-- **HE's admission of `(if b y n)` selects `if`'s arrow.** -/
theorem branch_selection_succeeds (policy : Policy) {atoms : List Atom} (program : IfProgram atoms)
    (b : Bool) {y n Ty Tn : Atom} (typesY : StorageTypesRel (Space.ofList atoms) y [Ty])
    (typesN : StorageTypesRel (Space.ofList atoms) n [Tn]) :
    Completed.InvocationSelectionRel (Space.ofList atoms) Completed.rawLookup policy [] []
      (callOf b y n) (.symbol "if") Atom.undefinedType Completed.Frame.empty
      (.selected ifPolicy [Completed.Frame.empty]) := by
  obtain ⟨errors, checks⟩ := branch_arrow_selected policy b typesY typesN
  exact ⟨[ifPolicy.functionType], program.types, .selected checks (List.cons_ne_nil _ _)⟩

/-- **The function application of `(if b y n)`**: the operator is cast against its arrow (the
match renews the frame), the condition against `Bool`, both branches are delivered under `Atom`
unevaluated, and the call value is assembled. -/
theorem branch_function_segment (dispatch : GroundedDispatch) (policy : Policy) {atoms : List Atom}
    (program : IfProgram atoms) (b : Bool) {y n : Atom}
    (closedY : ∀ name, ¬ AtomOccurs y name) (closedN : ∀ name, ¬ AtomOccurs n name)
    (stack : List Continuation) :
    ∃ results : List Result,
      HERuns.HESteps dispatch Completed.rawLookup policy
        ⟨Space.ofList atoms, .work (.function [Completed.invocationReturnType ifPolicy] []
          Atom.undefinedType ifPolicy (Entry.Value.ofAtom (.symbol "if"))
          [Entry.Value.ofAtom (.grounded (.bool b)), Entry.Value.ofAtom y,
            Entry.Value.ofAtom n] Completed.Frame.empty), stack, []⟩
        ⟨Space.ofList atoms, .returning results, stack, []⟩ ∧
      ∃ value activation, results = [(value, activation)] ∧ value.erase = callOf b y n := by
  obtain ⟨frF, renewal⟩ := if_operator_renewal policy
  have readY : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom y) = Entry.Value.ofAtom y :=
    fun frame => HERuns.read_closed policy frame closedY
  have readN : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom n) = Entry.Value.ofAtom n :=
    fun frame => HERuns.read_closed policy frame closedN
  have ifCast := renewed_cast_step dispatch policy (atom := .symbol "if") (closed_symbol "if")
    (symbol_cast_entry (by decide) (by decide) (by decide +kernel)) program.types
    Completed.Frame.empty frF renewal
  have boolCast := typed_cast dispatch policy (space := Space.ofList atoms)
    (atom := .grounded (.bool b)) (expected := sym "Bool")
    (fun _ occurs => by cases occurs) (bool_cast_entry b) (bool_types_in _ b) frF (bool_matches _)
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
    · rintro ⟨_, different⟩
      simp only [readY] at different
      exact different rfl
    refine .head (.internal .argumentsCons) ?_
    refine .head (.internal (.delivered (atom_demand_deliver _))) ?_
    refine .head (.internal .arguments) ?_
    refine .head (.internal (.argumentBranchesContinue ?_)) ?_
    · rintro ⟨_, different⟩
      simp only [readN] at different
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
    simp [Entry.Value.erase, Entry.Value.erase_ofAtom, readY, readN, callOf, app]

/-- **The typed query of `(if b y n)`**: the query selects the equation of `b`, reads its body as
the taken branch, and the branch meets the return demand `$t`. -/
theorem branch_query (dispatch : GroundedDispatch) (notHost : ¬ dispatch.executable (.symbol "if"))
    (policy : Policy) {atoms : List Atom} (program : IfProgram atoms) {b : Bool} {y n : Atom}
    (branches : Branches atoms b y n) (value : Entry.Value) (erased : value.erase = callOf b y n)
    (activation : Frame) (stack : List Continuation) :
    ∃ results : List Result,
      HERuns.HESteps dispatch Completed.rawLookup policy
        ⟨Space.ofList atoms, .work (.call [] [] value (.var "t") activation), stack, []⟩
        ⟨Space.ofList atoms, .returning results, stack, []⟩ ∧
      results.map (fun r => r.1.erase) = [pick b y n] := by
  have ground := call_ground (b := b) branches.closedYes branches.closedNo
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms) [.var "t"] (callOf b y n)
    activation.bindings
  have instances := works_instances_ground policy ground program.rows
    activation.certified.satisfiable frontier
  rw [branches.region] at instances
  obtain ⟨w, ws, ⟨_, reads⟩, rest, rfl⟩ := List.forall₂_cons_right_iff.mp instances
  obtain rfl := List.forall₂_nil_right_iff.mp rest
  have frontier' : EquationFrontierRel (Space.ofList atoms) [.var "t"] value.erase
      activation.bindings [w] := by
    rw [erased]
    exact frontier
  obtain ⟨environments, paired⟩ := Entry.Value.UnifyRel.equation_frontier
    (policy := policy.rebuilding) activation.certified frontier'
  obtain ⟨after, unified, certificate⟩ := forall₂_left_exists paired w List.mem_cons_self
  let output : Frame := ⟨w.bindings, after, certificate⟩
  have readErase := reads output rfl
  have readBody := value_of_data branches.takenData readErase
  have takenEntry : Entry.Rel policy.reentry .active (pick b y n) (.var "t") .cast :=
    data_var_entry branches.takenData "t"
  have takenCast := typed_cast dispatch policy (atom := pick b y n) (expected := .var "t")
    (data_closed branches.takenData) takenEntry branches.takenUndeclared output (.undefinedRight _ _)
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
  refine ⟨(([(Entry.Value.ofAtom (pick b y n), output)] ++ []) ++ []), ?_, by simp⟩
  refine .head (.internal (.callEquations notError nonGrounded frontier' (List.cons_ne_nil _ _))) ?_
  refine .head (.internal (.equationsCons (output := output) rfl unified)) ?_
  rw [readBody]
  refine .head (.internal (.boundaryProducerRaw ?_)) ?_
  · rintro ⟨⟨inner, same⟩, _⟩
    rw [Entry.Value.erase_ofAtom] at same
    have data := branches.takenData
    rw [same] at data
    cases data
  refine .head (.internal .boundaryBatch) ?_
  refine .head (.internal .boundaryBatchCons) ?_
  refine .head (.internal .boundaryReturned) ?_
  refine .head (.internal (.returnEvaluate ?_ ?_)) ?_
  · rw [Entry.Value.erase_ofAtom]
    exact branches.takenNotRefused
  · rw [Entry.Value.erase_ofAtom]
    exact branches.takenData.not_stopped
  refine .head (takenCast _ _ _ _) ?_
  refine .head (.internal .append) ?_
  refine .head (.internal .boundaryBatchNil) ?_
  refine .head (.internal .prepend) ?_
  refine .head (.internal .append) ?_
  refine .head (.internal .equationsNil) ?_
  exact .single (.internal .prepend)

/-- **A complete run of `(if b y n)` on HE's machine, publishing the taken branch.** -/
theorem branch_run (dispatch : GroundedDispatch) (notHost : ¬ dispatch.executable (.symbol "if"))
    (policy : Policy) {atoms : List Atom} (program : IfProgram atoms) {b : Bool} {y n : Atom}
    (branches : Branches atoms b y n) :
    ∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList atoms) (callOf b y n) Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ ∧
        heAnswers.map (fun r => r.1.erase) = [pick b y n] := by
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
  have step := LocalStepWith.atomFunction (admission := .historical)
    (space := Space.ofList atoms) (dispatch := dispatch) (lookup := Completed.rawLookup)
    (live := []) (scope := []) (stack := []) entry shape selection
  have published : (Completed.Frame.empty.read policy (Entry.Value.ofAtom (callOf b y n))).erase =
      callOf b y n := by
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom]
  rw [published] at step
  have returned : Completed.invocationReturnType ifPolicy = .var "t" := by
    simp [Completed.invocationReturnType, ifPolicy, Atom.expressionType]
  obtain ⟨F, pathF, value, activation, rfl, erased⟩ := branch_function_segment dispatch policy
    program b branches.closedYes branches.closedNo
    (.calls [] [] (Completed.invocationReturnType ifPolicy) ::
      .append (.invocations [] [] Atom.undefinedType ifPolicy (Entry.Value.ofAtom (.symbol "if"))
        [Entry.Value.ofAtom (.grounded (.bool b)), Entry.Value.ofAtom y,
          Entry.Value.ofAtom n] []) :: [.publish (callOf b y n)])
  obtain ⟨Q, pathQ, eraseQ⟩ := branch_query dispatch notHost policy program branches value erased
    activation
    (.append (.calls [] [] (.var "t") []) ::
      .append (.invocations [] [] Atom.undefinedType ifPolicy (Entry.Value.ofAtom (.symbol "if"))
        [Entry.Value.ofAtom (.grounded (.bool b)), Entry.Value.ofAtom y,
          Entry.Value.ofAtom n] []) :: [.publish (callOf b y n)])
  have clean : ∀ r ∈ (Q ++ []) ++ [], Answerable r.1.erase := by
    intro r member
    simp only [List.append_nil] at member
    have inQ : r.1.erase ∈ [pick b y n] := by
      rw [← eraseQ]
      exact List.mem_map.mpr ⟨r, member, rfl⟩
    rw [List.mem_singleton] at inQ
    rw [inQ]
    exact answerable_of_data branches.takenData
  obtain ⟨publishedAnswers, eraseP, pathP⟩ := NestedArguments.HENested.publish_step
    (dispatch := dispatch) (lookup := Completed.rawLookup) (policy := policy) (atoms := atoms)
    (callOf b y n) ((Q ++ []) ++ []) clean [] []
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

/-- PeTTa's run of `(if b y n)` after ten steps: nothing is pending and the value is the taken
branch. The branch left is never inspected. -/
theorem petta_branch_steps (atoms : List Atom) (b : Bool) (y n : Atom)
    (taken : DataAtom (pick b y n)) :
    (Streaming.advance (translate atoms) 10
        ⟨{ state := store atoms, uses := 1 }, [.execute ⟨.evaluate [] (callOf b y n), []⟩], [], 0⟩
      ).agenda = [] ∧
      Streaming.values (Streaming.advance (translate atoms) 10
        ⟨{ state := store atoms, uses := 1 }, [.execute ⟨.evaluate [] (callOf b y n), []⟩], [], 0⟩) =
        [pick b y n] := by
  cases b with
  | true =>
      have data : DataAtom y := taken
      cases data <;> exact ⟨rfl, rfl⟩
  | false =>
      have data : DataAtom n := taken
      cases data <;> exact ⟨rfl, rfl⟩

/-- **PeTTa's special form takes the same branch from fuel `10` on**, whatever closed branch it
leaves. -/
theorem petta_branch (atoms : List Atom) {b : Bool} {y n : Atom} (groundY : isGroundAtom y = true)
    (groundN : isGroundAtom n = true) (taken : DataAtom (pick b y n)) :
    ∀ k, 10 ≤ k → Streaming.values (Streaming.advance (translate atoms) k
      (Streaming.enter { state := store atoms } (callOf b y n))) = [pick b y n] := by
  have entered : Streaming.enter { state := store atoms } (callOf b y n) =
      ⟨{ state := store atoms, uses := 1 }, [.execute ⟨.evaluate [] (callOf b y n), []⟩], [], 0⟩ := by
    simp only [Streaming.enter]
    rw [Unifying.rename_ground 0 _ (by
      simp [isGroundAtom, isGroundAtom.isGroundList, groundY, groundN])]
  obtain ⟨done, value⟩ := petta_branch_steps atoms b y n taken
  intro k bigger
  rw [entered, advance_stable done k bigger]
  exact value

/-! ## Every run -/

/-- **HE's `if` leaves its other branch alone, on every run.** On a program carrying HE's
standard-library `if` (`(: if (-> Bool Atom Atom $t))` and its two equations, with any other rows
meeting `IfProgram`), historical lookup, any policy and any dispatch that does not execute `if`, for
a call `(if b y n)` whose branches meet `Branches` (the taken one an undeclared data atom, the other
any closed atom with one stored type): a complete run exists, every complete run publishes exactly
the taken branch, and PeTTa's special form yields the same from fuel `10` on. -/
theorem branch_every_run (dispatch : GroundedDispatch) (notHost : ¬ dispatch.executable (.symbol "if"))
    (policy : Policy) {atoms : List Atom} (program : IfProgram atoms) {b : Bool} {y n : Atom}
    (branches : Branches atoms b y n) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList atoms) (callOf b y n) Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩) ∧
      (∀ emitted : List Result,
        Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
            (load (Space.ofList atoms) (callOf b y n) Atom.undefinedType)
            ⟨Space.ofList atoms, .returning [], [], emitted⟩ →
          emitted.map (fun r => r.1.erase) = [pick b y n]) ∧
      ∀ k, 10 ≤ k → Streaming.values (Streaming.advance (translate atoms) k
        (Streaming.enter { state := store atoms } (callOf b y n))) = [pick b y n] := by
  obtain ⟨heAnswers, path, _⟩ := branch_run dispatch notHost policy program branches
  exact ⟨⟨heAnswers, path⟩, fun emitted run => branch_source program branches (complete_source run),
    petta_branch atoms branches.groundYes branches.groundNo branches.takenData⟩

/-! ## A divergent call, in any program whose only `loop` row is `(= (loop) (loop))` -/

/-- Pending work on `(loop)` in the space of `atoms`, anywhere. -/
def LoopEntryIn (atoms : List Atom) (x : HEConfig) : Prop :=
  ∃ (live : List Atom) (scope : List String) (activation : Frame) (stack : List Continuation)
    (emitted : List Result), x = ⟨Space.ofList atoms,
      .work (.atom live scope (Entry.Value.ofAtom (app "loop" [])) Atom.undefinedType activation),
      stack, emitted⟩

/-- **`(loop)` comes back to itself** in every program where `loop` is undeclared, the rows are
symbol-headed and `cons`-free, and the region of `(loop)` has the one body `(loop)`
(`EveryRunFinishes.loop_cycle_on` for `{(= (loop) (loop))}` alone, generalized to such programs). -/
theorem loop_cycle_in {dispatch : GroundedDispatch}
    (notHost : ¬ dispatch.executable (.symbol "loop")) (policy : Policy) {atoms : List Atom}
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol "loop")) = [])
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row)
    (bodies : regionBodies atoms "loop" [] = [app "loop" []]) : ∀ x, LoopEntryIn atoms x →
    ∃ y, Relation.TransGen (HEStep dispatch Completed.rawLookup policy) x y ∧ LoopEntryIn atoms y := by
  rintro x ⟨live, scope, activation, stack, emitted, rfl⟩
  have loopHead : DataAtom (.symbol "loop") := .symbol (by decide) (by decide)
  have loopData : ∀ a ∈ Atom.symbol "loop" :: ([] : List Atom), DataAtom a := by
    intro a member
    simp only [List.mem_singleton] at member
    subst member
    exact loopHead
  have entry := HERuns.call_entry_steps (dispatch := dispatch) (lookup := Completed.rawLookup)
    (policy := policy) raw_answers loopData untyped live scope activation stack emitted
  have loopFixed : ∀ rename : String → String,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars rename
        (app "loop" []) = app "loop" [] := by
    intro rename
    simp [Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars]
  have fixed : ∀ b ∈ regionBodies atoms "loop" [], ∀ rename : String → String,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars rename b = b := by
    rw [bodies]
    intro b member rename
    rw [List.mem_singleton] at member
    subst member
    exact loopFixed rename
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms) (Atom.undefinedType :: live)
    (app "loop" []) activation.bindings
  have bodiesEq := HERuns.frontier_bodies (fun v member => by cases member)
    activation.certified.satisfiable program fixed frontier
  rw [bodies] at bodiesEq
  obtain ⟨w, rfl⟩ : ∃ w, works = [w] := by
    cases works with
    | nil => simp at bodiesEq
    | cons w rest =>
        cases rest with
        | nil => exact ⟨w, rfl⟩
        | cons _ _ => simp at bodiesEq
  have body : w.body = app "loop" [] := by
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at bodiesEq
    exact bodiesEq
  have frontier' : EquationFrontierRel (Space.ofList atoms) (Atom.undefinedType :: live)
      (callValue "loop" []).erase activation.bindings [w] := by
    rw [callValue_erase]
    exact frontier
  obtain ⟨environments, paired⟩ := Entry.Value.UnifyRel.equation_frontier
    (policy := policy.rebuilding) activation.certified frontier'
  obtain ⟨after, unified, certificate⟩ := forall₂_left_exists paired w List.mem_cons_self
  let output : Frame := ⟨w.bindings, after, certificate⟩
  have closedLoop : ∀ name, ¬ AtomOccurs (app "loop" []) name :=
    (call_answerable loopHead fun _ member => by cases member).closed
  have readBody : output.read policy (Entry.Value.ofAtom w.body) =
      Entry.Value.ofAtom (app "loop" []) := by
    rw [body]
    exact HERuns.read_closed policy output closedLoop
  have notFunction : ¬ Completed.FunctionPending policy (Entry.Value.ofAtom (app "loop" [])) := by
    rintro ⟨⟨inner, same⟩, _⟩
    rw [Entry.Value.erase_ofAtom] at same
    simp at same
  have callStep : HEStep dispatch Completed.rawLookup policy
      ⟨Space.ofList atoms, .work (.call live scope (callValue "loop" []) Atom.undefinedType
        activation), .append (.calls live scope Atom.undefinedType []) ::
          .publish (app "loop" []) :: stack, emitted⟩
      ⟨Space.ofList atoms, .work (.equations live scope (callValue "loop" []) Atom.undefinedType
        activation [w]), .append (.calls live scope Atom.undefinedType []) ::
          .publish (app "loop" []) :: stack, emitted⟩ :=
    .internal (.callEquations (HERuns.value_not_error loopHead (callValue_erase "loop" []))
      (HERuns.value_nonGrounded notHost (by decide)
        (callValue_erase "loop" [])) frontier' (List.cons_ne_nil _ _))
  have rest : Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
      ⟨Space.ofList atoms, .work (.equations live scope (callValue "loop" []) Atom.undefinedType
        activation [w]), .append (.calls live scope Atom.undefinedType []) ::
          .publish (app "loop" []) :: stack, emitted⟩
      ⟨Space.ofList atoms, .work (.atom live scope (Entry.Value.ofAtom (app "loop" []))
        Atom.undefinedType output),
        .append (.boundaryBatch live scope none (.returned (callValue "loop" []) Atom.undefinedType)
          []) :: .append (.equations live scope (callValue "loop" []) Atom.undefinedType activation
          []) :: .append (.calls live scope Atom.undefinedType []) :: .publish (app "loop" []) ::
          stack, emitted⟩ := by
    refine .head (.internal (.equationsCons (output := output) rfl unified)) ?_
    rw [readBody]
    refine .head (.internal (.boundaryProducerRaw notFunction)) ?_
    refine .head (.internal .boundaryBatch) ?_
    refine .head (.internal .boundaryBatchCons) ?_
    refine .head (.internal .boundaryReturned) ?_
    refine .head (.internal (.returnEvaluate ?_ ?_)) ?_
    · rw [Entry.Value.erase_ofAtom]
      intro same
      cases same
    · rw [Entry.Value.erase_ofAtom]
      exact call_not_stopped loopHead
    exact .refl
  exact ⟨_, Relation.TransGen.trans_left (Relation.TransGen.tail' entry callStep) rest,
    ⟨_, _, _, _, _, rfl⟩⟩

/-! ## Controls -/

namespace Controls

open AnswerBags.Controls (loopRows)
open WholeRunWords.Double (noHost)

/-- HE's standard-library `if` with the divergent row `(= (loop) (loop))`. -/
abbrev loopIfRows : List Atom := ifProgram ++ [rule (app "loop" []) (app "loop" [])]

theorem loop_if_program : IfProgram loopIfRows := by
  refine ⟨.symbolKnown (.hit (.skip (fun _ same => by simp at same)
    (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same) .nil))))
    (by simp), ?_⟩
  intro row member
  rcases List.mem_append.mp member with inIf | inLoop
  · exact if_program row inIf
  · simp only [List.mem_singleton] at inLoop
    subst inLoop
    refine ⟨rule_consFree fun a inside => (by cases inside), fun lhs rhs same => ?_⟩
    cases same
    decide

theorem loop_closed : ∀ name, ¬ AtomOccurs (app "loop" []) name :=
  (call_answerable (f := "loop") (.symbol (by decide) (by decide))
    fun _ member => by cases member).closed

theorem loop_types :
    StorageTypesRel (Space.ofList loopIfRows) (app "loop" []) [Atom.undefinedType] :=
  .expressionUndefined (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same)
    (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same) .nil))))

theorem symbol_undeclared (name : String) (notIf : name ≠ "if") :
    StorageTypesRel (Space.ofList loopIfRows) (sym name) [Atom.undefinedType] :=
  .symbolUndefined (.skip (fun _ same => by cases same; exact notIf rfl)
    (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same)
      (.skip (fun _ same => by simp at same) .nil))))

/-- The branches of `(if True yes (loop))`. -/
theorem loop_branches : Branches loopIfRows true (sym "yes") (app "loop" []) where
  takenData := .symbol (by decide) (by decide)
  takenNotRefused := by simp [pick, Atom.notReducible]
  takenUndeclared := symbol_undeclared "yes" (by decide)
  closedYes := data_closed (.symbol (by decide) (by decide))
  closedNo := loop_closed
  groundYes := rfl
  groundNo := rfl
  typedYes := ⟨_, symbol_undeclared "yes" (by decide)⟩
  typedNo := ⟨_, loop_types⟩
  region := by decide +kernel

/-- The branches of `(if False (loop) no)`. -/
theorem loop_branches_false : Branches loopIfRows false (app "loop" []) (sym "no") where
  takenData := .symbol (by decide) (by decide)
  takenNotRefused := by simp [pick, Atom.notReducible]
  takenUndeclared := symbol_undeclared "no" (by decide)
  closedYes := loop_closed
  closedNo := data_closed (.symbol (by decide) (by decide))
  groundYes := rfl
  groundNo := rfl
  typedYes := ⟨_, loop_types⟩
  typedNo := ⟨_, symbol_undeclared "no" (by decide)⟩
  region := by decide +kernel

/-- **The test `(if True yes (loop))`**: with `(= (loop) (loop))` in the program, a complete HE run
exists, every complete run publishes `yes`, and PeTTa yields `yes`. -/
theorem loop_left (policy : Policy) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList loopIfRows) (callOf true (sym "yes") (app "loop" []))
            Atom.undefinedType)
          ⟨Space.ofList loopIfRows, .returning [], [], heAnswers⟩) ∧
      (∀ emitted : List Result,
        Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
            (load (Space.ofList loopIfRows) (callOf true (sym "yes") (app "loop" []))
              Atom.undefinedType)
            ⟨Space.ofList loopIfRows, .returning [], [], emitted⟩ →
          emitted.map (fun r => r.1.erase) = [sym "yes"]) ∧
      ∀ k, 10 ≤ k → Streaming.values (Streaming.advance (translate loopIfRows) k
        (Streaming.enter { state := store loopIfRows } (callOf true (sym "yes") (app "loop" [])))) =
          [sym "yes"] :=
  branch_every_run noHost (fun impossible => impossible) policy loop_if_program loop_branches

/-- **The mirror `(if False (loop) no)`**: every complete HE run publishes `no`, as PeTTa does. -/
theorem loop_left_false (policy : Policy) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList loopIfRows) (callOf false (app "loop" []) (sym "no"))
            Atom.undefinedType)
          ⟨Space.ofList loopIfRows, .returning [], [], heAnswers⟩) ∧
      (∀ emitted : List Result,
        Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
            (load (Space.ofList loopIfRows) (callOf false (app "loop" []) (sym "no"))
              Atom.undefinedType)
            ⟨Space.ofList loopIfRows, .returning [], [], emitted⟩ →
          emitted.map (fun r => r.1.erase) = [sym "no"]) ∧
      ∀ k, 10 ≤ k → Streaming.values (Streaming.advance (translate loopIfRows) k
        (Streaming.enter { state := store loopIfRows } (callOf false (app "loop" []) (sym "no")))) =
          [sym "no"] :=
  branch_every_run noHost (fun impossible => impossible) policy loop_if_program loop_branches_false

/-- **Negative control: the left branch really diverges.** In the same program, `(loop)` loaded
under `%Undefined%` has an infinite run on HE's machine: only the `Atom` demand of `if` keeps it
from running inside `(if True yes (loop))`. -/
theorem loop_diverges_alone (policy : Policy) :
    ¬ Acc (fun b a => HEStep noHost Completed.rawLookup policy a b)
      (load (Space.ofList loopIfRows) (app "loop" []) Atom.undefinedType) := fun acc =>
  EveryRunFinishes.not_acc_of_cycle
    (loop_cycle_in (dispatch := noHost) (fun impossible => impossible) policy (atoms := loopIfRows)
      (by decide +kernel)
      (fun row member => (loop_if_program.rows row member).1)
      (by decide +kernel)) _ acc _ .refl
    ⟨[], [], Completed.Frame.empty, [], [], rfl⟩

/-- The branches of `(if True yes Empty)`. -/
theorem empty_branches : Branches loopIfRows true (sym "yes") Atom.empty where
  takenData := .symbol (by decide) (by decide)
  takenNotRefused := by simp [pick, Atom.notReducible]
  takenUndeclared := symbol_undeclared "yes" (by decide)
  closedYes := data_closed (.symbol (by decide) (by decide))
  closedNo := fun _ occurs => by cases occurs
  groundYes := rfl
  groundNo := rfl
  typedYes := ⟨_, symbol_undeclared "yes" (by decide)⟩
  typedNo := ⟨_, symbol_undeclared "Empty" (by decide)⟩
  region := by decide +kernel

/-- **Positive control, a stopped atom left alone**: `(if True yes Empty)` publishes `yes` on every
complete run. `Empty` is delivered under `Atom` as the original argument, and an argument that comes
back as its own original does not stop the application (`ArgumentStopped` asks for a change). -/
theorem empty_left (policy : Policy) :
    ∀ emitted : List Result,
      Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList loopIfRows) (callOf true (sym "yes") Atom.empty) Atom.undefinedType)
          ⟨Space.ofList loopIfRows, .returning [], [], emitted⟩ →
        emitted.map (fun r => r.1.erase) = [sym "yes"] :=
  (branch_every_run noHost (fun impossible => impossible) policy loop_if_program empty_branches).2.1

end Controls

#print axioms work_read_ground
#print axioms works_instances_ground
#print axioms branch_checks
#print axioms branch_selection
#print axioms branch_call_source
#print axioms branch_source
#print axioms branch_function_segment
#print axioms branch_query
#print axioms branch_run
#print axioms petta_branch
#print axioms branch_every_run
#print axioms loop_cycle_in
#print axioms Controls.loop_left
#print axioms Controls.loop_left_false
#print axioms Controls.loop_diverges_alone
#print axioms Controls.empty_left

end IfBranches

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
