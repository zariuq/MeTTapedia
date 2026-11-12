import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.DemandSpine

/-!
# HE's `if` with a computed condition, on every run

`IfBranches` takes a literal condition. Here the condition is any term that settles
(`CompoundBindings.SettlesK`) with one Boolean answer: a call of a defined function, recursion over
data, arguments that are calls. HE evaluates it under the demand `Bool` of `if`'s arrow, which
`DemandSpine.settlesK_at` covers. The branch taken is any value of the program (a data atom or a
constructor tree) that `$t` casts as it is; the branch left is any closed atom, as in `IfBranches`.

* `cond_checks`, `cond_selection`: the admission of `(if c y n)` when the condition's one stored
  type meets `Bool` keeping every binding (an undeclared call has the type `%Undefined%`).
* `value_works`: the query of `(if b y n)` reads the taken branch as a marked value of the program
  (any marking of a value is admissible, `MarkedValues.marked_of_value`), evaluated under `$t`.
* `computed_source`: every derivation of HE's completed relation for `(if c y n)` publishes the taken
  branch; `computed_run`: a complete run exists.
* `petta_if_computed`: PeTTa's special form evaluates the condition, then the branch it selects.
* `computed_every_run`: a complete HE run exists, every complete run publishes the taken branch, and
  PeTTa yields it from some fuel on.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace IfComputed

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel rawTypeLookupRel
  FunctionTypeRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement (TypeBindingSatisfied)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (AtomOccurs)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open HEOnTheStep (HEConfig)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst isGroundAtom)
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun NestedValues NestedCalls MarkedValues CompoundBindings DeclaredHeads
  DeclaredEveryRun TypedEveryRun AtomDemands IfEveryRun IfBranches DemandSpine
open AnswerBags.Controls (sym app rule rule_consFree)

variable {dispatch : GroundedDispatch} {policy : Policy}

/-! ## Demands -/

theorem var_transparent (name : String) : Transparent (.var name) := by
  simp [Transparent, Atom.atomType, Atom.expressionType, Atom.variableType]

theorem bool_transparent : Transparent (sym "Bool") := by
  simp [Transparent, Atom.atomType, Atom.expressionType, Atom.variableType]

/-- **`Bool` casts every Boolean as it is.** -/
theorem bool_casts (atoms : List Atom) (b : Bool) :
    CastsAt atoms (sym "Bool") (.grounded (.bool b)) where
  data := .grounded _
  entry _ := .cast (DataAtom.grounded (.bool b)).not_stopped (.grounded _) (by decide +kernel)
    (Or.inr (Or.inl ⟨_, rfl⟩)) (fun _ => Or.inr rfl)
  typed := ⟨_, bool_types_in _ b, bool_matches⟩

/-- **`$t` casts every undeclared data atom as it is.** -/
theorem undeclared_casts {atoms : List Atom} {d : Atom} (data : DataAtom d)
    (undeclared : StorageTypesRel (Space.ofList atoms) d [Atom.undefinedType]) (name : String) :
    CastsAt atoms (.var name) d where
  data := data
  entry _ := by
    cases data with
    | symbol notEmpty notError =>
        exact .cast (DataAtom.symbol notEmpty notError).not_stopped (.symbol _)
          (by simp [Atom.atomType, Atom.symbolType, Atom.variableType]) (Or.inl ⟨_, rfl⟩)
          (fun _ => Or.inr rfl)
    | grounded value =>
        exact .cast (DataAtom.grounded value).not_stopped (.grounded _)
          (by simp [Atom.atomType, Atom.groundedType, Atom.variableType])
          (Or.inr (Or.inl ⟨_, rfl⟩)) (fun _ => Or.inr rfl)
  typed := ⟨_, undeclared, fun _ => .undefinedRight _ _⟩

/-! ## The program, the condition and the branches -/

/-- `(if c y n)`. -/
abbrev callC (c y n : Atom) : Atom := app "if" [c, y, n]

/-- **A program carrying HE's `if`**: `if`'s stored type is its standard-library arrow, and the rows
are symbol-headed `cons`-free equations whose bodies are trees using their left side's variables. -/
structure IfCallProgram (atoms : List Atom) : Prop where
  types : StorageTypesRel (Space.ofList atoms) (.symbol "if") [ifArrow]
  rows : CallProgram atoms

theorem IfCallProgram.ifProgram {atoms : List Atom} (program : IfCallProgram atoms) :
    IfProgram atoms :=
  ⟨program.types, program.rows.scoped⟩

/-- **The condition**: it settles with one Boolean answer, and its one stored type meets `Bool`
keeping every binding, and only so. -/
structure Condition (dispatch : GroundedDispatch) (atoms : List Atom) (c : Atom) (b : Bool) :
    Prop where
  settles : SettlesK dispatch atoms c [.grounded (.bool b)]
  typed : ∃ T, StorageTypesRel (Space.ofList atoms) c [T] ∧
    (∀ bnd : Bindings, TypeMatchRel (sym "Bool") T bnd bnd) ∧
    (∀ bnd out : Bindings, TypeMatchRel (sym "Bool") T bnd out → out = bnd)

/-- **The branches**: the taken one is a value of the program that settles with itself and whose
data form `$t` casts as it is; both are closed with one stored type each; and the region of `if` on
the call `(if b y n)` has the taken branch as its only instance. -/
structure ValueBranches (dispatch : GroundedDispatch) (atoms : List Atom) (b : Bool) (y n : Atom) :
    Prop where
  takenValue : NestedValues.Value dispatch atoms (pick b y n)
  takenSettles : SettlesK dispatch atoms (pick b y n) [pick b y n]
  takenCasts : ∀ a ∈ [pick b y n], DataAtom a → CastsAt atoms (.var "t") a
  closedYes : ∀ name, ¬ AtomOccurs y name
  closedNo : ∀ name, ¬ AtomOccurs n name
  groundYes : isGroundAtom y = true
  groundNo : isGroundAtom n = true
  typedYes : ∃ T, StorageTypesRel (Space.ofList atoms) y [T]
  typedNo : ∃ T, StorageTypesRel (Space.ofList atoms) n [T]
  region : regionInstances atoms "if" [.grounded (.bool b), y, n] = [pick b y n]

theorem Condition.casts {atoms : List Atom} {c : Atom} {b : Bool}
    (_ : Condition dispatch atoms c b) :
    ∀ a ∈ [Atom.grounded (.bool b)], DataAtom a → CastsAt atoms (sym "Bool") a := by
  intro a member _
  rw [List.mem_singleton] at member
  subst member
  exact bool_casts atoms b

/-! ## Admission -/

/-- **Every application check of `(if c y n)` keeps exactly one activation, with no bindings.** -/
theorem cond_checks {atoms : List Atom} {c y n Tc Ty Tn : Atom}
    (typesC : StorageTypesRel (Space.ofList atoms) c [Tc])
    (acceptsC : ∀ bnd : Bindings, TypeMatchRel (sym "Bool") Tc bnd bnd)
    (keepsC : ∀ bnd out : Bindings, TypeMatchRel (sym "Bool") Tc bnd out → out = bnd)
    (typesY : StorageTypesRel (Space.ofList atoms) y [Ty])
    (typesN : StorageTypesRel (Space.ofList atoms) n [Tn])
    {signature : SelectedTypePolicy} {frames : List Frame} {errors : List Atom}
    (functionType : signature.functionType = ifArrow)
    (checks : Completed.ApplicationChecksRel (Space.ofList atoms)
      (rawTypeLookupRel (Space.ofList atoms)) policy (callC c y n) Atom.undefinedType signature
      Completed.Frame.empty frames errors) :
    ∃ after, frames = [after] ∧ after.bindings = Bindings.empty := by
  have projections := if_projections functionType
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
      obtain ⟨f1, same1, rest1⟩ := accepted_step typesC (fun out matched => keepsC _ out matched)
        ⟨_, Completed.Frame.preserved_type_match policy _ (acceptsC _)⟩ arguments
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

/-- **Every admission of `(if c y n)` selects `if`'s arrow with one activation, with no bindings.** -/
theorem cond_selection {atoms : List Atom} (program : IfCallProgram atoms) {c y n Tc Ty Tn : Atom}
    (typesC : StorageTypesRel (Space.ofList atoms) c [Tc])
    (acceptsC : ∀ bnd : Bindings, TypeMatchRel (sym "Bool") Tc bnd bnd)
    (keepsC : ∀ bnd out : Bindings, TypeMatchRel (sym "Bool") Tc bnd out → out = bnd)
    (typesY : StorageTypesRel (Space.ofList atoms) y [Ty])
    (typesN : StorageTypesRel (Space.ofList atoms) n [Tn])
    {outcome : Completed.InvocationSelection}
    (chosenRel : Completed.InvocationSelectionRel (Space.ofList atoms) Completed.rawLookup policy
      [] [] (callC c y n) (.symbol "if") Atom.undefinedType Completed.Frame.empty outcome) :
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
      obtain ⟨after, rfl, bindings⟩ := cond_checks typesC acceptsC keepsC typesY typesN
        functionType checks
      exact ⟨_, after, functionType, bindings, rfl⟩
  | rejected checks rest =>
      simp only [List.cons.injEq] at same
      obtain ⟨functionType, rfl⟩ := same
      obtain ⟨after, impossible, _⟩ := cond_checks typesC acceptsC keepsC typesY typesN
        functionType checks
      cases impossible

/-! ## The query of `(if b y n)` with a value branch -/

/-- **The works of the query read the taken branch as a marked value**, evaluated and determined
under `$t`. -/
theorem value_works {atoms : List Atom} (program : IfCallProgram atoms) {b : Bool} {y n : Atom}
    (branches : ValueBranches dispatch atoms b y n) {live : List Atom} {incoming : Bindings}
    (satisfiable : ∃ model : String → Atom, TypeBindingSatisfied model incoming)
    {works : List EquationWork}
    (frontier : EquationFrontierRel (Space.ofList atoms) live (callOf b y n) incoming works) :
    List.Forall₂ (fun w L => ∃ i, (∀ output : Frame, output.bindings = w.bindings →
        (output.read policy (Entry.Value.ofAtom w.body)).erase = i ∧
        Marked dispatch atoms (output.read policy (Entry.Value.ofAtom w.body))) ∧
      HEEvaluatesAt dispatch policy atoms (.var "t") i L ∧
      DeterminedAt dispatch policy atoms (.var "t") i L ∧ BodyFacts i) works [[pick b y n]] := by
  have ground := call_ground (b := b) branches.closedYes branches.closedNo
  have instances := works_instances_ground policy ground program.rows.scoped satisfiable frontier
  rw [branches.region] at instances
  obtain ⟨w, ws, ⟨_, reads⟩, rest, rfl⟩ := List.forall₂_cons_right_iff.mp instances
  obtain rfl := List.forall₂_nil_right_iff.mp rest
  have both := settlesK_at (policy := policy) program.rows (var_transparent "t")
    branches.takenSettles branches.takenCasts
  refine .cons ⟨pick b y n, fun output same => ⟨reads output same, ?_⟩, both.1, both.2,
    settlesK_facts branches.takenSettles⟩ .nil
  apply marked_of_value
  rw [reads output same]
  exact branches.takenValue

/-- **Every derivation of the typed query of `(if b y n)` under `$t` returns the taken value.** -/
theorem value_call_source {atoms : List Atom} (program : IfCallProgram atoms) {b : Bool}
    {y n : Atom} (branches : ValueBranches dispatch atoms b y n) {live : List Atom}
    {scope : List String} {value : Entry.Value} {frame : Frame} {children : List Result}
    (erased : value.erase = callOf b y n)
    (called : Completed.CallRel (Space.ofList atoms) dispatch Completed.rawLookup live scope
      value (.var "t") frame children (policy := policy)) :
    children.map (fun r => r.1.erase) = [pick b y n] := by
  have ground := call_ground (b := b) branches.closedYes branches.closedNo
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
        (scoped_consFree program.rows.scoped) frontier
      have nonempty : regionInstances atoms "if" [.grounded (.bool b), y, n] ≠ [] := by
        rw [branches.region]
        exact List.cons_ne_nil _ _
      apply absurd _ nonempty
      rw [regionInstances_sides, ← sidesEq]
      rfl
  | equations _ _ frontier _ equations =>
      rw [erased] at frontier
      have related := value_works (policy := policy) program branches frame.certified.satisfiable
        frontier
      exact bodies_source_at _ [[pick b y n]] (related.imp fun _ _ both => by
        obtain ⟨i, reads, _, determined, facts⟩ := both
        exact ⟨i, reads, determined, facts⟩) equations

/-- **The query of `(if b y n)` under `$t` runs to the taken value**, from any activation. -/
theorem value_query (dispatch : GroundedDispatch) (notHost : ¬ dispatch.executable (.symbol "if"))
    (policy : Policy) {atoms : List Atom} (program : IfCallProgram atoms) {b : Bool} {y n : Atom}
    (branches : ValueBranches dispatch atoms b y n) (value : Entry.Value)
    (erased : value.erase = callOf b y n) (activation : Frame) (stack : List Continuation) :
    ∃ results : List Result,
      HERuns.HESteps dispatch Completed.rawLookup policy
        ⟨Space.ofList atoms, .work (.call [] [] value (.var "t") activation), stack, []⟩
        ⟨Space.ofList atoms, .returning results, stack, []⟩ ∧
      results.map (fun r => r.1.erase) = [pick b y n] := by
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms) [.var "t"] (callOf b y n)
    activation.bindings
  have related := value_works (policy := policy) program branches
    activation.certified.satisfiable frontier
  have frontier' : EquationFrontierRel (Space.ofList atoms) [.var "t"] value.erase
      activation.bindings works := by
    rw [erased]
    exact frontier
  obtain ⟨environments, paired⟩ := Entry.Value.UnifyRel.equation_frontier
    (policy := policy.rebuilding) activation.certified frontier'
  have unifiers : ∀ w ∈ works, ∃ output : Frame, output.bindings = w.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding activation.environment value
        (Entry.Value.ofAtom w.pattern) output.environment := by
    intro w member
    obtain ⟨after, unified, certificate⟩ := forall₂_left_exists paired w member
    exact ⟨⟨w.bindings, after, certificate⟩, rfl, unified⟩
  have worksNonempty : works ≠ [] := by
    intro none
    subst none
    cases related
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
  obtain ⟨R, eraseR, pathR⟩ := equations_steps_at (dispatch := dispatch) (policy := policy)
    (live := []) (scope := []) (original := value) (activation := activation) works
    [[pick b y n]] unifiers (related.imp fun _ _ both => by
      obtain ⟨i, reads, evaluates, _, facts⟩ := both
      exact ⟨i, reads, evaluates, facts⟩) stack []
  exact ⟨R, .head (.internal (.callEquations notError nonGrounded frontier' worksNonempty)) pathR,
    by rw [eraseR]; rfl⟩

/-! ## Every derivation for `(if c y n)` -/

/-- A batch whose atoms are one data atom is that atom's plain value at some frame. -/
theorem single_data_result {d : Atom} (data : DataAtom d) {heads : List Result}
    (erased : heads.map (fun r => r.1.erase) = [d]) :
    ∃ fr, heads = [(Entry.Value.ofAtom d, fr)] := by
  cases heads with
  | nil => simp at erased
  | cons h hs =>
      cases hs with
      | cons _ _ => simp at erased
      | nil =>
          have hErase : h.1.erase = d := by simpa using erased
          exact ⟨h.2, by rw [← value_of_data data hErase]⟩

/-- **Every derivation of HE's completed relation for `(if c y n)` publishes the taken branch**: the
admission selects `if`'s arrow, the condition is evaluated under `Bool` to its one answer, both
branches are delivered under `Atom`, the query selects the equation of that answer, and the taken
value meets `$t`. -/
theorem computed_source {atoms : List Atom} (program : IfCallProgram atoms) {c : Atom} {b : Bool}
    (condition : Condition dispatch atoms c b) {y n : Atom}
    (branches : ValueBranches dispatch atoms b y n) {results : List Result}
    (derived : Completed.AtomRel (Space.ofList atoms) dispatch Completed.rawLookup [] []
      (Entry.Value.ofAtom (callC c y n)) Atom.undefinedType Completed.Frame.empty results
      (policy := policy)) :
    results.map (fun r => r.1.erase) = [pick b y n] := by
  obtain ⟨Tc, typesC, acceptsC, keepsC⟩ := condition.typed
  obtain ⟨Ty, typesY⟩ := branches.typedYes
  obtain ⟨Tn, typesN⟩ := branches.typedNo
  have conditionDetermined := (settlesK_at (policy := policy) program.rows bool_transparent
    condition.settles condition.casts).2
  have entry := call_entry policy if_data [c, y, n]
  have shape : Completed.Frame.empty.read policy (Entry.Value.ofAtom (callC c y n)) =
      .expression .active (Entry.Value.ofAtom (.symbol "if") ::
        [c, y, n].map Entry.Value.ofAtom) := by
    rw [Completed.Frame.read_empty]
    simp only [callC, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  have outcome : ∀ {result : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList atoms) Completed.rawLookup policy [] []
        (Completed.Frame.empty.read policy (Entry.Value.ofAtom (callC c y n))).erase
        (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType Completed.Frame.empty result →
      ∃ (signature : SelectedTypePolicy) (after : Frame), signature.functionType = ifArrow ∧
        after.bindings = Bindings.empty ∧ result = .selected signature [after] := by
    intro result chosenRel
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosenRel
    exact cond_selection program typesC acceptsC keepsC typesY typesN chosenRel
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
                      have conditionErase := conditionDetermined (Entry.Value.ofAtom c)
                        (Entry.Value.erase_ofAtom c) (marked_ofAtom c) _ _ _ _ conditionRel
                      obtain ⟨fr1, rfl⟩ := single_data_result (.grounded (.bool b)) conditionErase
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
                                              have answered := value_call_source program branches
                                                (assembled _) callRel
                                              exact publish_answers
                                                (by simp only [List.append_nil]; exact answered)
                                                (fun a member => by
                                                  rw [List.mem_singleton] at member
                                                  subst member
                                                  exact value_answerable branches.takenValue)
                                                priority

/-! ## A complete run -/

/-- `if`'s arrow is selected with the empty activation. -/
theorem cond_arrow_selected (policy : Policy) {atoms : List Atom} {c y n Tc Ty Tn : Atom}
    (typesC : StorageTypesRel (Space.ofList atoms) c [Tc])
    (acceptsC : ∀ bnd : Bindings, TypeMatchRel (sym "Bool") Tc bnd bnd)
    (typesY : StorageTypesRel (Space.ofList atoms) y [Ty])
    (typesN : StorageTypesRel (Space.ofList atoms) n [Tn]) :
    ∃ errors, Completed.ApplicationChecksRel (Space.ofList atoms)
      (rawTypeLookupRel (Space.ofList atoms)) policy (callC c y n) Atom.undefinedType ifPolicy
      Completed.Frame.empty [Completed.Frame.empty] errors :=
  ⟨_, .checked (operator := sym "if") (arguments := [c, y, n]) rfl
    (.cons (.cons typesC
      (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy _
        (acceptsC _)))) .nil) .nil)
      (.cons (.cons typesY
        (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy _
          (.atomLeft _ _)))) .nil) .nil)
        (.cons (.cons typesN
          (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy _
            (.atomLeft _ _)))) .nil) .nil) .nil)))
    (.cons (.accepted (.unchanged (Completed.Frame.preserved_type_match policy _
      (.undefinedLeft _ _)))) .nil)⟩

/-- The requests of `if`'s function application on `(if c y n)`. -/
abbrev requestsOf (c y n : Atom) : List Completed.ArgumentRequest :=
  [Entry.Value.ofAtom c, Entry.Value.ofAtom y, Entry.Value.ofAtom n].zip ifPolicy.argumentTypes

/-- **The function application of `(if c y n)`**: the operator is cast against its arrow, the
condition evaluated under `Bool` to its one answer, both branches delivered under `Atom`, and the
call value assembled. -/
theorem computed_function_segment (dispatch : GroundedDispatch) (policy : Policy)
    {atoms : List Atom} (program : IfCallProgram atoms) {c : Atom} {b : Bool}
    (condition : Condition dispatch atoms c b) {y n : Atom}
    (closedY : ∀ name, ¬ AtomOccurs y name) (closedN : ∀ name, ¬ AtomOccurs n name)
    (stack : List Continuation) :
    ∃ results : List Result,
      HERuns.HESteps dispatch Completed.rawLookup policy
        ⟨Space.ofList atoms, .work (.function [Completed.invocationReturnType ifPolicy] []
          Atom.undefinedType ifPolicy (Entry.Value.ofAtom (.symbol "if"))
          [Entry.Value.ofAtom c, Entry.Value.ofAtom y, Entry.Value.ofAtom n]
          Completed.Frame.empty), stack, []⟩
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
  have conditionRuns := (settlesK_at (policy := policy) program.rows bool_transparent
    condition.settles condition.casts).1 (Entry.Value.ofAtom c) (Entry.Value.erase_ofAtom c)
    (marked_ofAtom c)
  obtain ⟨R, eraseR, conditionRun⟩ := conditionRuns
    (Completed.argumentScope (requestsOf c y n).tail ++
      [(Entry.Value.ofAtom (.symbol "if")).erase, Completed.invocationReturnType ifPolicy])
    [] frF
    (.arguments [(Entry.Value.ofAtom (.symbol "if")).erase, Completed.invocationReturnType ifPolicy]
        [] (Entry.Value.ofAtom c) (requestsOf c y n).tail ::
      .functionAssemble (Entry.Value.ofAtom (.symbol "if")) ::
      .append (.functionBranches [Completed.invocationReturnType ifPolicy] [] (requestsOf c y n) []) ::
      stack) []
  obtain ⟨fr, rfl⟩ := single_data_result (.grounded (.bool b)) eraseR
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

/-- **HE's admission of `(if c y n)` selects `if`'s arrow.** -/
theorem cond_selection_succeeds (policy : Policy) {atoms : List Atom}
    (program : IfCallProgram atoms) {c y n Tc Ty Tn : Atom}
    (typesC : StorageTypesRel (Space.ofList atoms) c [Tc])
    (acceptsC : ∀ bnd : Bindings, TypeMatchRel (sym "Bool") Tc bnd bnd)
    (typesY : StorageTypesRel (Space.ofList atoms) y [Ty])
    (typesN : StorageTypesRel (Space.ofList atoms) n [Tn]) :
    Completed.InvocationSelectionRel (Space.ofList atoms) Completed.rawLookup policy [] []
      (callC c y n) (.symbol "if") Atom.undefinedType Completed.Frame.empty
      (.selected ifPolicy [Completed.Frame.empty]) := by
  obtain ⟨errors, checks⟩ := cond_arrow_selected policy typesC acceptsC typesY typesN
  exact ⟨[ifPolicy.functionType], program.types, .selected checks (List.cons_ne_nil _ _)⟩

/-- **A complete run of `(if c y n)` on HE's machine, publishing the taken branch.** -/
theorem computed_run (dispatch : GroundedDispatch) (notHost : ¬ dispatch.executable (.symbol "if"))
    (policy : Policy) {atoms : List Atom} (program : IfCallProgram atoms) {c : Atom} {b : Bool}
    (condition : Condition dispatch atoms c b) {y n : Atom}
    (branches : ValueBranches dispatch atoms b y n) :
    ∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList atoms) (callC c y n) Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ ∧
        heAnswers.map (fun r => r.1.erase) = [pick b y n] := by
  obtain ⟨Tc, typesC, acceptsC, _⟩ := condition.typed
  obtain ⟨Ty, typesY⟩ := branches.typedYes
  obtain ⟨Tn, typesN⟩ := branches.typedNo
  have entry := call_entry policy if_data [c, y, n]
  have shape : Completed.Frame.empty.read policy (Entry.Value.ofAtom (callC c y n)) =
      .expression .active (Entry.Value.ofAtom (.symbol "if") ::
        [c, y, n].map Entry.Value.ofAtom) := by
    rw [Completed.Frame.read_empty]
    simp only [callC, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  have selection : Completed.ArgumentService.historical.selection (Space.ofList atoms)
      Completed.rawLookup policy [] []
      (Completed.Frame.empty.read policy (Entry.Value.ofAtom (callC c y n))).erase
      (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType Completed.Frame.empty
      (.selected ifPolicy [Completed.Frame.empty]) := by
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom]
    exact cond_selection_succeeds policy program typesC acceptsC typesY typesN
  have step := LocalStepWith.atomFunction (admission := .historical)
    (space := Space.ofList atoms) (dispatch := dispatch) (lookup := Completed.rawLookup)
    (live := []) (scope := []) (stack := []) entry shape selection
  have published : (Completed.Frame.empty.read policy (Entry.Value.ofAtom (callC c y n))).erase =
      callC c y n := by
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom]
  rw [published] at step
  have returned : Completed.invocationReturnType ifPolicy = .var "t" := by
    simp [Completed.invocationReturnType, ifPolicy, Atom.expressionType]
  obtain ⟨F, pathF, value, activation, rfl, erased⟩ := computed_function_segment dispatch policy
    program condition branches.closedYes branches.closedNo
    (.calls [] [] (Completed.invocationReturnType ifPolicy) ::
      .append (.invocations [] [] Atom.undefinedType ifPolicy (Entry.Value.ofAtom (.symbol "if"))
        [Entry.Value.ofAtom c, Entry.Value.ofAtom y, Entry.Value.ofAtom n] []) ::
        [.publish (callC c y n)])
  obtain ⟨Q, pathQ, eraseQ⟩ := value_query dispatch notHost policy program branches value erased
    activation
    (.append (.calls [] [] (.var "t") []) ::
      .append (.invocations [] [] Atom.undefinedType ifPolicy (Entry.Value.ofAtom (.symbol "if"))
        [Entry.Value.ofAtom c, Entry.Value.ofAtom y, Entry.Value.ofAtom n] []) ::
        [.publish (callC c y n)])
  have clean : ∀ r ∈ (Q ++ []) ++ [], Answerable r.1.erase := by
    intro r member
    simp only [List.append_nil] at member
    have inQ : r.1.erase ∈ [pick b y n] := by
      rw [← eraseQ]
      exact List.mem_map.mpr ⟨r, member, rfl⟩
    rw [List.mem_singleton] at inQ
    rw [inQ]
    exact value_answerable branches.takenValue
  obtain ⟨publishedAnswers, eraseP, pathP⟩ := NestedArguments.HENested.publish_step
    (dispatch := dispatch) (lookup := Completed.rawLookup) (policy := policy) (atoms := atoms)
    (callC c y n) ((Q ++ []) ++ []) clean [] []
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

/-! ## PeTTa's `if` with a computed condition -/

section PeTTaSide

variable {registry : SpaceSemantics.Program}

/-- PeTTa enters `if`: the condition is evaluated under the branch frame. -/
theorem if_enter_step (world : Streaming.World) (σ : Subst) (c y n : Atom)
    (frames : List Streaming.Frame) (older : List Streaming.Job) (answers : List Unifying.Answer)
    (next : Nat) :
    Streaming.Transition registry
      ⟨world, .execute ⟨.evaluate σ (callC c y n), frames⟩ :: older, answers, next⟩
      ⟨world, .execute ⟨.evaluate σ c, .source (.branch y n) :: frames⟩ :: older, answers, next⟩ :=
  .phase rfl rfl (.if_enter rfl) (.waiting rfl rfl)

/-- PeTTa's branch frame takes `y` on `True` and `n` on every other answer. -/
theorem branch_return_step (world : Streaming.World) (answer : Unifying.Answer) (y n : Atom)
    (frames : List Streaming.Frame) (older : List Streaming.Job) (answers : List Unifying.Answer)
    (next : Nat) :
    Streaming.Transition registry
      ⟨world, .execute ⟨.returned [answer], .source (.branch y n) :: frames⟩ :: older, answers, next⟩
      ⟨world, .execute ⟨.sequence [.evaluate answer.bindings
        (if answer.value == Effects.boolean true then y else n)] [], frames⟩ :: older, answers,
        next⟩ :=
  .answer rfl (.source (.if_return rfl rfl) (.plain rfl))

/-- **PeTTa's special form with a computed condition**: the condition is evaluated under the branch
frame; its one Boolean answer selects the branch, whose evaluation the frames then deliver. -/
theorem petta_if_computed {atoms : List Atom} {c y n : Atom} {b : Bool} {L : List Atom}
    (evalC : PeTTaEvaluates atoms c [.grounded (.bool b)])
    (evalTaken : PeTTaEvaluates atoms (pick b y n) L) :
    PeTTaEvaluates atoms (callC c y n) L := by
  intro frames K deliver world σ state privateCode range fresh older answers next
  have branchDelivers : ∀ v ∈ [Atom.grounded (.bool b)],
      Delivers atoms (.source (.branch y n) :: frames) (fun _ => L.flatMap K) v := by
    intro v member
    rw [List.mem_singleton] at member
    subst member
    intro world' σ' state' privateCode' range' fresh' older' answers' next'
    obtain ⟨uses, out, grown, valuesOut, path⟩ := evalTaken frames K deliver world' σ' state'
      privateCode' range' fresh' older' answers' next'
    refine ⟨uses, out, grown, valuesOut, ?_⟩
    have chosen : (if Atom.grounded (.bool b) == Effects.boolean true then y else n) =
        pick b y n := by
      cases b <;> rfl
    refine .head (branch_return_step world' ⟨.grounded (.bool b), σ'⟩ y n frames older' answers'
      next') ?_
    refine .head (PeTTaRuns.alternatives world' _ frames older' answers' next') ?_
    simp only [chosen, List.map_cons, List.map_nil, List.singleton_append]
    exact path
  obtain ⟨uses, out, grown, valuesOut, path⟩ := evalC (.source (.branch y n) :: frames)
    (fun _ => L.flatMap K) branchDelivers world σ state privateCode range fresh older answers next
  refine ⟨uses, out, grown, ?_, .head (if_enter_step world σ c y n frames older answers next) path⟩
  simpa using valuesOut

end PeTTaSide

/-- PeTTa evaluates a settling term from the root of its streaming machine. -/
theorem petta_settles {atoms : List Atom} (program : CallProgram atoms) {t : Atom} {L : List Atom}
    (settles : SettlesK dispatch atoms t L) : PeTTaEvaluates atoms t L := by
  have shape := (settlesK_shape settles).1
  exact over_root_K (settlesK_agree (lookup := Completed.rawLookup) (policy := Policy.unmarked)
    raw_answers program settles).2 fun σ => shows_ground_K shape.tree shape.answerable

/-! ## Every run -/

/-- **HE's `if` with a computed condition, on every run.** On a program carrying HE's
standard-library `if` (`IfCallProgram`), historical lookup, any policy and any dispatch that does
not execute `if`: for a condition `c` that settles with one Boolean answer `b` and whose one stored
type meets `Bool` keeping every binding, and branches meeting `ValueBranches` (the taken one a
value of the program that `$t` casts as it is, the other any closed atom): a complete HE run of
`(if c y n)` exists, every complete run publishes exactly the taken branch, and PeTTa's special form
yields the same from some fuel on. -/
theorem computed_every_run (dispatch : GroundedDispatch)
    (notHost : ¬ dispatch.executable (.symbol "if")) (policy : Policy) {atoms : List Atom}
    (program : IfCallProgram atoms) {c : Atom} {b : Bool} (condition : Condition dispatch atoms c b)
    {y n : Atom} (branches : ValueBranches dispatch atoms b y n) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList atoms) (callC c y n) Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩) ∧
      (∀ emitted : List Result,
        Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
            (load (Space.ofList atoms) (callC c y n) Atom.undefinedType)
            ⟨Space.ofList atoms, .returning [], [], emitted⟩ →
          emitted.map (fun r => r.1.erase) = [pick b y n]) ∧
      ∃ N : Nat, ∀ k, N ≤ k → Streaming.values (Streaming.advance (translate atoms) k
        (Streaming.enter { state := store atoms } (callC c y n))) = [pick b y n] := by
  obtain ⟨heAnswers, path, _⟩ := computed_run dispatch notHost policy program condition branches
  have cShape := (settlesK_shape condition.settles).1
  have ground : isGroundAtom (callC c y n) = true := by
    simp [isGroundAtom, isGroundAtom.isGroundList, cShape.answerable.ground,
      branches.groundYes, branches.groundNo]
  have clean : ∀ a ∈ [pick b y n], Answerable a := by
    intro a member
    rw [List.mem_singleton] at member
    subst member
    exact value_answerable branches.takenValue
  exact ⟨⟨heAnswers, path⟩,
    fun emitted run => computed_source program condition branches (complete_source run),
    petta_complete ground clean (petta_if_computed (petta_settles program.rows condition.settles)
      (petta_settles program.rows branches.takenSettles))⟩

/-! ## Controls -/

namespace Controls

open WholeRunWords.Double (noHost)
open CompoundBindings.Controls (call_single build_values)

/-- An integer. -/
abbrev num (k : Int) : Atom := .grounded (.int k)

/-- HE's `if`, `(= (isZero 0) True)`, `(= (isZero 1) False)` and `(= (loop) (loop))`. -/
abbrev zeroRows : List Atom :=
  ifProgram ++ [rule (app "isZero" [num 0]) (.grounded (.bool true)),
    rule (app "isZero" [num 1]) (.grounded (.bool false)), rule (app "loop" []) (app "loop" [])]

theorem zero_types_if : StorageTypesRel (Space.ofList zeroRows) (.symbol "if") [ifArrow] :=
  .symbolKnown (.hit (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same)
    (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same)
      (.skip (fun _ same => by simp at same) .nil)))))) (by simp)

theorem zero_rows : CallProgram zeroRows := by
  intro row member
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with ((rfl | rfl | rfl) | rfl | rfl | rfl)
  · exact ⟨fun lhs rhs same => by simp at same, fun lhs rhs same => by simp at same⟩
  · refine ⟨rule_consFree fun a inside => ?_, fun lhs rhs same => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl
      · exact .grounded _
      · exact .var _
      · exact .var _
    · cases same
      exact ⟨by decide, .item (.var _)⟩
  · refine ⟨rule_consFree fun a inside => ?_, fun lhs rhs same => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl
      · exact .grounded _
      · exact .var _
      · exact .var _
    · cases same
      exact ⟨by decide, .item (.var _)⟩
  · refine ⟨rule_consFree fun a inside => ?_, fun lhs rhs same => ?_⟩
    · simp only [List.mem_singleton] at inside
      subst inside
      exact .grounded _
    · cases same
      exact ⟨by decide, .item (.grounded _)⟩
  · refine ⟨rule_consFree fun a inside => ?_, fun lhs rhs same => ?_⟩
    · simp only [List.mem_singleton] at inside
      subst inside
      exact .grounded _
    · cases same
      exact ⟨by decide, .item (.grounded _)⟩
  · refine ⟨rule_consFree fun a inside => (by cases inside), fun lhs rhs same => ?_⟩
    cases same
    exact ⟨by decide, .node (by decide) fun u member => by cases member⟩

theorem zero_program : IfCallProgram zeroRows := ⟨zero_types_if, zero_rows⟩

theorem isZero_head : NodeHead noHost zeroRows "isZero" :=
  ⟨.symbol (by decide) (by decide), by decide +kernel, fun impossible => impossible, by decide,
    by decide, by decide, by decide⟩

theorem isZero_defined :
    ∃ e ∈ zeroRows.filterMap LiveEquations.equationOfRow, e.head = "isZero" := by
  decide +kernel

theorem isZero_settles (k : Int) (b : Bool)
    (instances : regionInstances zeroRows "isZero" [num k] = [.grounded (.bool b)]) :
    SettlesK noHost zeroRows (app "isZero" [num k]) [.grounded (.bool b)] :=
  call_single isZero_head isZero_defined (.cons (.data (.grounded _) (fun same => by cases same)) .nil)
    rfl instances (.data (.grounded _) (fun same => by cases same))

/-- Six skips: a call of `isZero` or `pair`, or an undeclared symbol, has no annotation. -/
theorem expression_undeclared (items : List Atom) (notIf : ∀ T,
    Atom.expression [.symbol ":", .symbol "if", ifArrow] ≠ .expression [.symbol ":", .expression items, T]) :
    StorageTypesRel (Space.ofList zeroRows) (.expression items) [Atom.undefinedType] := by
  cases items with
  | nil => exact .unit _
  | cons head tail =>
      exact .expressionUndefined (.skip notIf (.skip (fun _ same => by simp at same)
        (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same)
          (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same) .nil))))))

theorem symbol_undeclared (name : String) (notIf : name ≠ "if") :
    StorageTypesRel (Space.ofList zeroRows) (sym name) [Atom.undefinedType] :=
  .symbolUndefined (.skip (fun _ same => by cases same; exact notIf rfl)
    (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same)
      (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same)
        (.skip (fun _ same => by simp at same) .nil))))))

/-- The condition `(isZero k)` with answer `b`. -/
theorem isZero_condition (k : Int) (b : Bool)
    (instances : regionInstances zeroRows "isZero" [num k] = [.grounded (.bool b)]) :
    Condition noHost zeroRows (app "isZero" [num k]) b :=
  ⟨isZero_settles k b instances, Atom.undefinedType,
    expression_undeclared _ (fun _ same => by simp at same), fun _ => .undefinedRight _ _,
    fun _ _ matched => Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeMatchRel.wildcard_output matched
      (Or.inr (Or.inr (Or.inl rfl)))⟩

theorem loop_closed : ∀ name, ¬ AtomOccurs (app "loop" []) name :=
  (call_answerable (f := "loop") (.symbol (by decide) (by decide))
    fun _ member => by cases member).closed

/-- The branches of `(if (isZero 0) yes (loop))`. -/
theorem yes_branches : ValueBranches noHost zeroRows true (sym "yes") (app "loop" []) where
  takenValue := .data (.symbol (by decide) (by decide))
  takenSettles := .data (.symbol (by decide) (by decide)) (by decide)
  takenCasts := fun a member data => by
    rw [List.mem_singleton] at member
    subst member
    exact undeclared_casts data (symbol_undeclared "yes" (by decide)) "t"
  closedYes := data_closed (.symbol (by decide) (by decide))
  closedNo := loop_closed
  groundYes := rfl
  groundNo := rfl
  typedYes := ⟨_, symbol_undeclared "yes" (by decide)⟩
  typedNo := ⟨_, expression_undeclared _ (fun _ same => by simp at same)⟩
  region := by decide +kernel

/-- **The test with a computed condition**: `(if (isZero 0) yes (loop))` publishes `yes` on every
complete HE run, a complete run exists, and PeTTa yields `yes`. -/
theorem zero_loop (policy : Policy) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList zeroRows) (callC (app "isZero" [num 0]) (sym "yes") (app "loop" []))
            Atom.undefinedType)
          ⟨Space.ofList zeroRows, .returning [], [], heAnswers⟩) ∧
      (∀ emitted : List Result,
        Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
            (load (Space.ofList zeroRows) (callC (app "isZero" [num 0]) (sym "yes") (app "loop" []))
              Atom.undefinedType)
            ⟨Space.ofList zeroRows, .returning [], [], emitted⟩ →
          emitted.map (fun r => r.1.erase) = [sym "yes"]) ∧
      ∃ N : Nat, ∀ k, N ≤ k → Streaming.values (Streaming.advance (translate zeroRows) k
        (Streaming.enter { state := store zeroRows }
          (callC (app "isZero" [num 0]) (sym "yes") (app "loop" [])))) = [sym "yes"] :=
  computed_every_run noHost (fun impossible => impossible) policy zero_program
    (isZero_condition 0 true (by decide +kernel)) yes_branches

theorem pair_head : NodeHead noHost zeroRows "pair" :=
  ⟨.symbol (by decide) (by decide), by decide +kernel, fun impossible => impossible, by decide,
    by decide, by decide, by decide⟩

theorem pair_noEquation : (zeroRows.filterMap LiveEquations.equationOfRow).all
    (fun equation => equation.head != "pair") = true := by
  decide +kernel

/-- The branches of `(if (isZero 1) (loop) (pair a b))`: the taken branch is a constructor tree. -/
theorem pair_branches :
    ValueBranches noHost zeroRows false (app "loop" []) (app "pair" [sym "a", sym "b"]) where
  takenValue := .node (constructor_of_node pair_head pair_noEquation) fun v member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .data (.symbol (by decide) (by decide))
    · exact .data (.symbol (by decide) (by decide))
  takenSettles := build_values pair_head pair_noEquation
    (.cons (.data (.symbol (by decide) (by decide)) (by decide))
      (.cons (.data (.symbol (by decide) (by decide)) (by decide)) .nil))
  takenCasts := fun a member data => by
    rw [List.mem_singleton] at member
    subst member
    cases data
  closedYes := loop_closed
  closedNo := (call_answerable (f := "pair") (.symbol (by decide) (by decide)) fun a member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact .symbol (by decide) (by decide)).closed
  groundYes := rfl
  groundNo := rfl
  typedYes := ⟨_, expression_undeclared _ (fun _ same => by simp at same)⟩
  typedNo := ⟨_, expression_undeclared _ (fun _ same => by simp at same)⟩
  region := by decide +kernel

/-- **A computed condition selecting a constructor tree**: `(if (isZero 1) (loop) (pair a b))`
publishes `(pair a b)` on every complete HE run, as PeTTa does. -/
theorem one_pair (policy : Policy) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList zeroRows)
            (callC (app "isZero" [num 1]) (app "loop" []) (app "pair" [sym "a", sym "b"]))
            Atom.undefinedType)
          ⟨Space.ofList zeroRows, .returning [], [], heAnswers⟩) ∧
      (∀ emitted : List Result,
        Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
            (load (Space.ofList zeroRows)
              (callC (app "isZero" [num 1]) (app "loop" []) (app "pair" [sym "a", sym "b"]))
              Atom.undefinedType)
            ⟨Space.ofList zeroRows, .returning [], [], emitted⟩ →
          emitted.map (fun r => r.1.erase) = [app "pair" [sym "a", sym "b"]]) ∧
      ∃ N : Nat, ∀ k, N ≤ k → Streaming.values (Streaming.advance (translate zeroRows) k
        (Streaming.enter { state := store zeroRows }
          (callC (app "isZero" [num 1]) (app "loop" []) (app "pair" [sym "a", sym "b"])))) =
          [app "pair" [sym "a", sym "b"]] :=
  computed_every_run noHost (fun impossible => impossible) policy zero_program
    (isZero_condition 1 false (by decide +kernel)) pair_branches

/-- **The condition alone, under `Bool`**: every derivation of `(isZero 0)` under `Bool` returns
`True`, and HE's machine has such a run, from every activation. -/
theorem isZero_bool (policy : Policy) :
    HEEvaluatesAt noHost policy zeroRows (sym "Bool") (app "isZero" [num 0])
        [.grounded (.bool true)] ∧
      DeterminedAt noHost policy zeroRows (sym "Bool") (app "isZero" [num 0])
        [.grounded (.bool true)] :=
  settlesK_at zero_rows bool_transparent (isZero_settles 0 true (by decide +kernel))
    (fun a member _ => by
      rw [List.mem_singleton] at member
      subst member
      exact bool_casts zeroRows true)

/-- **Negative control: `Bool` does not cast a number.** `5` has the stored type `Number`, which
`Bool` matches under no binding, so `5` is no `CastsAt` leaf under `Bool`: a condition answering `5`
falls outside the theorem. -/
theorem number_not_bool (atoms : List Atom) : ¬ CastsAt atoms (sym "Bool") (num 5) := by
  rintro ⟨_, _, T, stored, keeps⟩
  have number : StorageTypesRel (Space.ofList atoms) (num 5) [sym "Number"] :=
    .groundedKnown (.int 5) (by simp [Atom.undefinedType])
  have same := StorageTypesRel.unique stored number
  simp only [List.cons.injEq, and_true] at same
  subst same
  have matched := keeps Bindings.empty
  generalize sameE : sym "Bool" = E at matched
  generalize sameT : sym "Number" = T' at matched
  cases matched with
  | undefinedLeft => simp [Atom.undefinedType] at sameE
  | atomLeft => simp [Atom.atomType] at sameE
  | undefinedRight => simp [Atom.undefinedType] at sameT
  | atomRight => simp [Atom.atomType] at sameT
  | structural _ _ _ _ inner _ =>
      subst sameE sameT
      generalize sameL : sym "Bool" = L at inner
      generalize sameR : sym "Number" = R at inner
      cases inner <;> (try simp_all); exact absurd (sameL.trans sameR.symm) (by decide)

/-- **Positive and negative controls of transparency**: `%Undefined%`, `Bool` and `$t` are
transparent demands; `Atom` is not (it delivers its argument unevaluated). -/
theorem transparency :
    Transparent Atom.undefinedType ∧ Transparent (sym "Bool") ∧ Transparent (.var "t") ∧
      ¬ Transparent Atom.atomType :=
  ⟨undefined_transparent, bool_transparent, var_transparent "t", fun transparent =>
    transparent (Or.inl rfl)⟩

end Controls

#print axioms cond_checks
#print axioms cond_selection
#print axioms value_works
#print axioms value_call_source
#print axioms value_query
#print axioms single_data_result
#print axioms computed_source
#print axioms computed_function_segment
#print axioms computed_run
#print axioms petta_if_computed
#print axioms petta_settles
#print axioms computed_every_run
#print axioms Controls.zero_loop
#print axioms Controls.one_pair
#print axioms Controls.isZero_bool
#print axioms Controls.number_not_bool
#print axioms Controls.transparency

end IfComputed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
