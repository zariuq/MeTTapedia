import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.DemandSpineFinishes

/-!
# Every run of `(if c y n)` with a computed condition finishes

`IfComputed.computed_every_run` shows that, for a condition `c` that settles with one Boolean answer
and a taken branch that is a value of the program, a complete HE run of `(if c y n)` exists and every
complete run publishes the taken branch. Here **every run finishes**: HE's machine has no infinite
run from the entry, every reachable configuration steps or is final, and a final one publishes the
taken branch. The branch left, even a divergent call, is never evaluated.

* `fine_value_query`: the typed query of `(if b y n)` under `$t`; the body is read as the taken value
  and runs finely under `$t` (`DemandSpineFinishes.fine_settlesK_at`).
* `fine_computed_function`: the function application; the condition runs finely under `Bool` to its
  one answer, the branches are delivered under `Atom`.
* `computed_fine`, `computed_every_run_finishes`.

## Controls

* `Controls.zero_loop_finishes` (`(if (isZero 0) yes (loop))`): every run finishes, publishing `yes`;
  `Controls.loop_diverges_zero` (negative): `(loop)` alone has an infinite run in the same program.
* `Controls.one_pair_finishes` (`(if (isZero 1) (loop) (pair a b))`): every run finishes, publishing
  the constructor tree `(pair a b)`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace IfComputedFinishes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement (TypeBindingSatisfied)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (AtomOccurs)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open HEOnTheStep (HEConfig)
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun NestedValues NestedCalls MarkedValues CompoundBindings DeclaredHeads
  DeclaredEveryRun TypedEveryRun AtomDemands IfEveryRun IfBranches DemandSpine IfComputed
  EveryRunFinishes IfFinishes DemandSpineFinishes
open AnswerBags.Controls (sym app rule rule_consFree)

variable {dispatch : GroundedDispatch} {policy : Policy}

/-! ## The query under `$t` -/

/-- **The works of the query read the taken value**, which runs finely under `$t`. -/
theorem value_works_fine {atoms : List Atom} (program : IfCallProgram atoms) {b : Bool}
    {y n : Atom} (branches : ValueBranches dispatch atoms b y n) {live : List Atom}
    {incoming : Bindings} (satisfiable : ∃ model : String → Atom, TypeBindingSatisfied model incoming)
    {works : List EquationWork}
    (frontier : EquationFrontierRel (Space.ofList atoms) live (callOf b y n) incoming works) :
    List.Forall₂ (fun w L => ∃ i, (∀ output : Frame, output.bindings = w.bindings →
        (output.read policy (Entry.Value.ofAtom w.body)).erase = i ∧
        Marked dispatch atoms (output.read policy (Entry.Value.ofAtom w.body))) ∧
      FineEvalAt dispatch policy atoms (.var "t") i L ∧ BodyFacts i) works [[pick b y n]] := by
  have ground := call_ground (b := b) branches.closedYes branches.closedNo
  have instances := works_instances_ground policy ground program.rows.scoped satisfiable frontier
  rw [branches.region] at instances
  obtain ⟨w, ws, ⟨_, reads⟩, rest, rfl⟩ := List.forall₂_cons_right_iff.mp instances
  obtain rfl := List.forall₂_nil_right_iff.mp rest
  refine .cons ⟨pick b y n, fun output same => ⟨reads output same, ?_⟩,
    fine_settlesK_at program.rows (var_transparent "t") branches.takenSettles branches.takenCasts,
    settlesK_facts branches.takenSettles⟩ .nil
  apply marked_of_value
  rw [reads output same]
  exact branches.takenValue

/-- **Every run of the typed query of `(if b y n)` under `$t` finishes with the taken value.** -/
theorem fine_value_query (notHost : ¬ dispatch.executable (.symbol "if")) {atoms : List Atom}
    (program : IfCallProgram atoms) {b : Bool} {y n : Atom}
    (branches : ValueBranches dispatch atoms b y n) {live : List Atom} {scope : List String}
    {value : Entry.Value} (erased : value.erase = callOf b y n) (activation : Frame)
    (stack : List Continuation) (emitted : List Result)
    (cont : ∀ R : List Result, R.map (fun r => r.1.erase) = [pick b y n] →
      Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms,
      .work (.call live scope value (.var "t") activation), stack, emitted⟩ := by
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
  have fromFrontier : ∀ works : List EquationWork,
      EquationFrontierRel (Space.ofList atoms) (.var "t" :: live) (callOf b y n)
        activation.bindings works →
      Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms,
        .work (.equations live scope value (.var "t") activation works), stack, emitted⟩ := by
    intro works frontier
    have related := value_works_fine (policy := policy) program branches
      activation.certified.satisfiable frontier
    have frontier' : EquationFrontierRel (Space.ofList atoms) (.var "t" :: live) value.erase
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
    exact fine_equations_at atoms works [[pick b y n]] unifiers related stack emitted
      fun R eraseR => cont R (by rw [eraseR]; rfl)
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms) (.var "t" :: live) (callOf b y n)
    activation.bindings
  have related := value_works_fine (policy := policy) program branches
    activation.certified.satisfiable frontier
  have worksNonempty : works ≠ [] := by
    intro none
    subst none
    cases related
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
          have none := value_works_fine (policy := policy) program branches
            activation.certified.satisfiable frontierEmpty
          cases none
      | callEquations _ _ frontierW _ =>
          rw [erased] at frontierW
          exact fromFrontier _ frontierW

/-! ## The function application with a computed condition -/

/-- **Every run of the function application of `(if c y n)` finishes with the call value
`(if b y n)`**: the operator is cast against its arrow, the condition runs finely under `Bool` to its
one answer, both branches are delivered under `Atom` as they are, and the call value is assembled. -/
theorem fine_computed_function {atoms : List Atom} (program : IfCallProgram atoms) {c : Atom}
    {b : Bool} (condition : Condition dispatch atoms c b) {y n : Atom}
    (closedY : ∀ name, ¬ AtomOccurs y name) (closedN : ∀ name, ¬ AtomOccurs n name)
    {live : List Atom} {scope : List String} {expected : Atom} {signature : SelectedTypePolicy}
    (functionType : signature.functionType = ifArrow) {activation : Frame}
    (empty : activation.bindings = Bindings.empty) (stack : List Continuation)
    (emitted : List Result)
    (cont : ∀ R : List Result, R.map (fun r => r.1.erase) = [callOf b y n] →
      Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms,
      .work (.function live scope expected signature (Entry.Value.ofAtom (.symbol "if"))
        [Entry.Value.ofAtom c, Entry.Value.ofAtom y, Entry.Value.ofAtom n] activation), stack,
      emitted⟩ := by
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
  refine fine_settlesK_at program.rows bool_transparent condition.settles condition.casts
    (Entry.Value.ofAtom c) (Entry.Value.erase_ofAtom c) (marked_ofAtom c) _ _ _ _ _ ?_
  intro R eraseR
  obtain ⟨fr1, rfl⟩ := single_data_result (.grounded (.bool b)) eraseR
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

/-! ## Every run of `(if c y n)` -/

/-- **Every run of `(if c y n)` from HE's entry finishes.** -/
theorem computed_fine (notHost : ¬ dispatch.executable (.symbol "if")) (policy : Policy)
    {atoms : List Atom} (program : IfCallProgram atoms) {c : Atom} {b : Bool}
    (condition : Condition dispatch atoms c b) {y n : Atom}
    (branches : ValueBranches dispatch atoms b y n) :
    Fine dispatch Completed.rawLookup policy
      (load (Space.ofList atoms) (callC c y n) Atom.undefinedType) := by
  obtain ⟨Tc, typesC, acceptsC, keepsC⟩ := condition.typed
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
  have clean : ∀ R : List Result, R.map (fun r => r.1.erase) = [pick b y n] →
      ∀ r ∈ R, Answerable r.1.erase := by
    intro R eraseR r member
    have inR : r.1.erase ∈ [pick b y n] := by
      rw [← eraseR]
      exact List.mem_map.mpr ⟨r, member, rfl⟩
    rw [List.mem_singleton] at inR
    rw [inR]
    exact value_answerable branches.takenValue
  show Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms,
    .work (.atom [] [] (Entry.Value.ofAtom (callC c y n)) Atom.undefinedType Completed.Frame.empty),
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
          obtain ⟨_, _, _, _, impossible⟩ := cond_selection program typesC acceptsC keepsC typesY
            typesN chosen
          cases impossible
      | atomSelectionFailed _ shaped chosen =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom]
            at chosen
          obtain ⟨_, _, _, _, impossible⟩ := cond_selection program typesC acceptsC keepsC typesY
            typesN chosen
          cases impossible
      | atomFunction _ shaped chosen =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, rfl⟩ := shaped
          rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom]
            at chosen
          obtain ⟨signature, after, functionType, afterBindings, selected⟩ :=
            cond_selection program typesC acceptsC keepsC typesY typesN chosen
          simp only [Completed.InvocationSelection.selected.injEq] at selected
          obtain ⟨rfl, rfl⟩ := selected
          have returnTypeOf : ∀ {s : SelectedTypePolicy}, s.returnType = .var "t" →
              Completed.invocationReturnType s = .var "t" := by
            intro s same
            simp [Completed.invocationReturnType, same, Atom.expressionType]
          apply fine_invocations_cons
          rw [returnTypeOf (if_projections functionType).2]
          simp only [List.map_cons, List.map_nil]
          refine fine_computed_function program condition branches.closedYes branches.closedNo
            functionType afterBindings _ _ ?_
          intro R eraseR
          obtain ⟨r, rfl, rErase⟩ : ∃ r, R = [r] ∧ r.1.erase = callOf b y n := by
            obtain ⟨r, sameR, rErase⟩ := List.map_eq_singleton_iff.mp eraseR
            exact ⟨r, sameR, rErase⟩
          apply fine_calls_frame
          apply fine_calls_cons
          refine fine_value_query notHost program branches rErase r.2 _ _ ?_
          intro Q eraseQ
          apply fine_append
          apply fine_calls_nil
          apply fine_prepend
          apply fine_append
          apply fine_invocations_nil
          apply fine_prepend
          refine fine_publish (clean _ (by simpa using eraseQ)) ?_
          exact fine_top _ _

/-- **Every run of `(if c y n)` with a computed condition finishes, and every finished run publishes
the taken branch.** Under the hypotheses of `IfComputed.computed_every_run`: HE's step relation is
well founded from the entry, every reachable configuration steps or is final, a final one publishes
exactly the taken branch, and PeTTa's special form yields the same from some fuel on. -/
theorem computed_every_run_finishes (dispatch : GroundedDispatch)
    (notHost : ¬ dispatch.executable (.symbol "if")) (policy : Policy) {atoms : List Atom}
    (program : IfCallProgram atoms) {c : Atom} {b : Bool} (condition : Condition dispatch atoms c b)
    {y n : Atom} (branches : ValueBranches dispatch atoms b y n) :
    Acc (fun later earlier => HEStep dispatch Completed.rawLookup policy earlier later)
        (load (Space.ofList atoms) (callC c y n) Atom.undefinedType) ∧
      (∀ x, Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList atoms) (callC c y n) Atom.undefinedType) x →
        (∃ z, HEStep dispatch Completed.rawLookup policy x z) ∨
          ∃ emitted : List Result, x = ⟨Space.ofList atoms, .returning [], [], emitted⟩ ∧
            emitted.map (fun r => r.1.erase) = [pick b y n]) ∧
      ∃ N : Nat, ∀ k, N ≤ k → Streaming.values (Streaming.advance (translate atoms) k
        (Streaming.enter { state := store atoms } (callC c y n))) = [pick b y n] := by
  have fine := computed_fine notHost policy program condition branches
  refine ⟨fine.acc, fun x path => ?_,
    (computed_every_run dispatch notHost policy program condition branches).2.2⟩
  rcases (fine.reaches path).progress with moves | ⟨space, emitted, rfl⟩
  · exact Or.inl moves
  · have sameSpace := space_fixed path
    simp only [load, Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual.Configuration.initial]
      at sameSpace
    subst sameSpace
    exact Or.inr ⟨emitted, rfl, computed_source program condition branches (complete_source path)⟩

/-! ## Controls -/

namespace Controls

open WholeRunWords.Double (noHost)
open IfComputed.Controls (num zeroRows zero_program isZero_condition yes_branches pair_branches)

/-- **`(if (isZero 0) yes (loop))`, every run**: no infinite run from the entry, and every final
configuration publishes `yes`. -/
theorem zero_loop_finishes (policy : Policy) :
    Acc (fun later earlier => HEStep noHost Completed.rawLookup policy earlier later)
        (load (Space.ofList zeroRows) (callC (app "isZero" [num 0]) (sym "yes") (app "loop" []))
          Atom.undefinedType) ∧
      ∀ x, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList zeroRows) (callC (app "isZero" [num 0]) (sym "yes") (app "loop" []))
            Atom.undefinedType) x →
        (∃ z, HEStep noHost Completed.rawLookup policy x z) ∨
          ∃ emitted : List Result, x = ⟨Space.ofList zeroRows, .returning [], [], emitted⟩ ∧
            emitted.map (fun r => r.1.erase) = [sym "yes"] := by
  obtain ⟨acc, every, -⟩ := computed_every_run_finishes noHost (fun impossible => impossible) policy
    zero_program (isZero_condition 0 true (by decide +kernel)) yes_branches
  exact ⟨acc, every⟩

/-- **Negative control**: in the same program, `(loop)` loaded alone has an infinite run. -/
theorem loop_diverges_zero (policy : Policy) :
    ¬ Acc (fun later earlier => HEStep noHost Completed.rawLookup policy earlier later)
      (load (Space.ofList zeroRows) (app "loop" []) Atom.undefinedType) := fun acc =>
  EveryRunFinishes.not_acc_of_cycle
    (loop_cycle_in (dispatch := noHost) (fun impossible => impossible) policy (atoms := zeroRows)
      (by decide +kernel)
      (fun row member => (zero_program.rows.scoped row member).1)
      (by decide +kernel)) _ acc _ .refl
    ⟨[], [], Completed.Frame.empty, [], [], rfl⟩

/-- **`(if (isZero 1) (loop) (pair a b))`, every run**: no infinite run, and every final
configuration publishes `(pair a b)`. -/
theorem one_pair_finishes (policy : Policy) :
    Acc (fun later earlier => HEStep noHost Completed.rawLookup policy earlier later)
      (load (Space.ofList zeroRows)
        (callC (app "isZero" [num 1]) (app "loop" []) (app "pair" [sym "a", sym "b"]))
        Atom.undefinedType) :=
  (computed_every_run_finishes noHost (fun impossible => impossible) policy zero_program
    (isZero_condition 1 false (by decide +kernel)) pair_branches).1

end Controls

#print axioms value_works_fine
#print axioms fine_value_query
#print axioms fine_computed_function
#print axioms computed_fine
#print axioms computed_every_run_finishes
#print axioms Controls.zero_loop_finishes
#print axioms Controls.loop_diverges_zero
#print axioms Controls.one_pair_finishes

end IfComputedFinishes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
