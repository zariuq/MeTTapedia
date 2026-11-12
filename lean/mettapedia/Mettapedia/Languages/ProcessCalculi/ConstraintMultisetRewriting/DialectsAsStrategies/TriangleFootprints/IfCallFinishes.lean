import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.IfComputedFinishes

/-!
# Every run of `(if c y n)` with a call branch finishes

`IfCallBranches.call_every_run` shows that, for a computed condition and a taken branch that is any
settling term (a call included), a complete HE run of `(if c y n)` exists and every complete run
publishes the taken branch's answers. Here **every run finishes**: HE's machine has no infinite run
from the entry, every reachable configuration steps or is final, and a final one publishes those
answers.

* `fine_call_function`: the function application assembles exactly the call value `(if b y n)` with
  the branches as delivered.
* `fine_call_query`: the typed query; on every unifier output the body is read as the plain taken
  branch (`IfCallBranches.call_read`), which runs finely under `$t`
  (`DemandSpineFinishes.fine_settlesK_at`).
* `call_fine`, `call_every_run_finishes`.

## Controls

* `Controls.zero_call_finishes` (`(if (isZero 0) (half 4) (loop))`): every run finishes, publishing
  `two`; `Controls.loop_diverges_call` (negative): `(loop)` alone has an infinite run in the same
  program.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace IfCallFinishes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (AtomOccurs)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open HEOnTheStep (HEConfig)
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun NestedValues NestedCalls MarkedValues CompoundBindings DeclaredHeads
  DeclaredEveryRun TypedEveryRun AtomDemands IfEveryRun IfBranches DemandSpine IfComputed
  IfCallBranches EveryRunFinishes IfFinishes DemandSpineFinishes
open AnswerBags.Controls (sym app rule rule_consFree)

variable {dispatch : GroundedDispatch} {policy : Policy}

/-! ## The function application -/

/-- **Every run of the function application of `(if c y n)` finishes with the call value
`(if b y n)` itself**, the branches as delivered. -/
theorem fine_call_function {atoms : List Atom} (program : IfCallProgram atoms) {c : Atom}
    {b : Bool} (condition : Condition dispatch atoms c b) {y n : Atom}
    (closedY : ∀ name, ¬ AtomOccurs y name) (closedN : ∀ name, ¬ AtomOccurs n name)
    {live : List Atom} {scope : List String} {expected : Atom} {signature : SelectedTypePolicy}
    (functionType : signature.functionType = ifArrow) {activation : Frame}
    (empty : activation.bindings = Bindings.empty) (stack : List Continuation)
    (emitted : List Result)
    (cont : ∀ R : List Result, R.map Prod.fst = [callValueOf b y n] →
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
  simp [Completed.functionAssemble, Completed.argumentPrepend, Entry.Value.argumentPacket,
    Entry.Value.unpackArguments, Entry.Value.ofAtom]

/-! ## The query of the call value -/

/-- **Every run of the typed query of `(if b y n)` under `$t` finishes with the taken branch's
answers**: there is one work, every unifier output reads its body as the plain taken branch, and the
branch runs finely under `$t`. -/
theorem fine_call_query (notHost : ¬ dispatch.executable (.symbol "if")) {atoms : List Atom}
    (program : IfCallProgram atoms) {b : Bool} {y n : Atom} {L : List Atom}
    (branches : CallBranches dispatch atoms b y n L) {live : List Atom} {scope : List String}
    (activation : Frame) (stack : List Continuation) (emitted : List Result)
    (cont : ∀ R : List Result, R.map (fun r => r.1.erase) = L →
      Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    Fine dispatch Completed.rawLookup policy ⟨Space.ofList atoms,
      .work (.call live scope (callValueOf b y n) (.var "t") activation), stack, emitted⟩ := by
  have erased := callValue_erase b y n
  have facts := settlesK_facts branches.takenSettles
  have notError : ¬ IsErrorRel (callValueOf b y n).erase := by
    rw [erased]
    rintro ⟨tail, same⟩
    simp at same
  have nonGrounded : NonGroundedCallRel dispatch (callValueOf b y n).erase := by
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
        .work (.equations live scope (callValueOf b y n) (.var "t") activation works), stack,
        emitted⟩ := by
    intro works frontier
    obtain ⟨w, rfl, reads⟩ := call_read policy (scoped_consFree program.rows.scoped)
      branches.closedYes branches.closedNo branches.region frontier
    have frontier' : EquationFrontierRel (Space.ofList atoms) (.var "t" :: live)
        (callValueOf b y n).erase activation.bindings [w] := by
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
        | equationsCons _ unifiedW =>
            rw [reads .active _ unifiedW]
            refine fine_boundary_producer (not_pending facts (Entry.Value.erase_ofAtom _)) ?_
            apply fine_boundaryBatch_frame
            apply fine_boundaryBatch_cons
            apply fine_boundary_returned
            refine fine_returned_evaluate ?_ ?_ ?_
            · simpa [Entry.Value.erase_ofAtom] using facts.notRefused
            · simpa [Entry.Value.erase_ofAtom] using facts.notStopped
            refine fine_settlesK_at program.rows (var_transparent "t") branches.takenSettles
              branches.takenCasts (Entry.Value.ofAtom (pick b y n)) (Entry.Value.erase_ofAtom _)
              (marked_ofAtom _) _ _ _ _ _ ?_
            intro Rb eraseRb
            apply fine_append
            apply fine_boundaryBatch_nil
            apply fine_prepend
            apply fine_append
            apply fine_equations_nil
            apply fine_prepend
            apply cont
            simpa using eraseRb
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms) (.var "t" :: live) (callOf b y n)
    activation.bindings
  obtain ⟨w, rfl, _⟩ := call_read policy (scoped_consFree program.rows.scoped)
    branches.closedYes branches.closedNo branches.region frontier
  have frontier' : EquationFrontierRel (Space.ofList atoms) (.var "t" :: live)
      (callValueOf b y n).erase activation.bindings [w] := by
    rw [erased]
    exact frontier
  refine .step ⟨_, .internal (.callEquations notError nonGrounded frontier'
    (List.cons_ne_nil _ _))⟩ ?_
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
          obtain ⟨_, impossible, _⟩ := call_read policy (scoped_consFree program.rows.scoped)
            branches.closedYes branches.closedNo branches.region frontierEmpty
          cases impossible
      | callEquations _ _ frontierW _ =>
          rw [erased] at frontierW
          exact fromFrontier _ frontierW

/-! ## Every run of `(if c y n)` -/

/-- **Every run of `(if c y n)` with a call branch from HE's entry finishes.** -/
theorem call_fine (notHost : ¬ dispatch.executable (.symbol "if")) (policy : Policy)
    {atoms : List Atom} (program : IfCallProgram atoms) {c : Atom} {b : Bool}
    (condition : Condition dispatch atoms c b) {y n : Atom} {L : List Atom}
    (branches : CallBranches dispatch atoms b y n L) :
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
  have cleanL : ∀ a ∈ L, Answerable a := (settlesK_shape branches.takenSettles).1.answers
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
          refine fine_call_function program condition branches.closedYes branches.closedNo
            functionType afterBindings _ _ ?_
          intro R firstR
          obtain ⟨r, rfl, rFirst⟩ : ∃ r, R = [r] ∧ r.1 = callValueOf b y n := by
            obtain ⟨r, sameR, rFirst⟩ := List.map_eq_singleton_iff.mp firstR
            exact ⟨r, sameR, rFirst⟩
          obtain ⟨value, frame⟩ := r
          simp only at rFirst
          subst rFirst
          apply fine_calls_frame
          apply fine_calls_cons
          refine fine_call_query notHost program branches frame _ _ ?_
          intro Q eraseQ
          apply fine_append
          apply fine_calls_nil
          apply fine_prepend
          apply fine_append
          apply fine_invocations_nil
          apply fine_prepend
          refine fine_publish (HENested.clean_of_erase (by simpa using eraseQ) cleanL) ?_
          exact fine_top _ _

/-- **Every run of `(if c y n)` with a call branch finishes, and every finished run publishes the
taken branch's answers.** Under the hypotheses of `IfCallBranches.call_every_run`: HE's step relation
is well founded from the entry, every reachable configuration steps or is final, a final one
publishes exactly `L`, and PeTTa's special form yields `L` from some fuel on. -/
theorem call_every_run_finishes (dispatch : GroundedDispatch)
    (notHost : ¬ dispatch.executable (.symbol "if")) (policy : Policy) {atoms : List Atom}
    (program : IfCallProgram atoms) {c : Atom} {b : Bool} (condition : Condition dispatch atoms c b)
    {y n : Atom} {L : List Atom} (branches : CallBranches dispatch atoms b y n L) :
    Acc (fun later earlier => HEStep dispatch Completed.rawLookup policy earlier later)
        (load (Space.ofList atoms) (callC c y n) Atom.undefinedType) ∧
      (∀ x, Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList atoms) (callC c y n) Atom.undefinedType) x →
        (∃ z, HEStep dispatch Completed.rawLookup policy x z) ∨
          ∃ emitted : List Result, x = ⟨Space.ofList atoms, .returning [], [], emitted⟩ ∧
            emitted.map (fun r => r.1.erase) = L) ∧
      ∃ N : Nat, ∀ k, N ≤ k → Streaming.values (Streaming.advance (translate atoms) k
        (Streaming.enter { state := store atoms } (callC c y n))) = L := by
  have fine := call_fine notHost policy program condition branches
  refine ⟨fine.acc, fun x path => ?_,
    (call_every_run dispatch notHost policy program condition branches).2.2⟩
  rcases (fine.reaches path).progress with moves | ⟨space, emitted, rfl⟩
  · exact Or.inl moves
  · have sameSpace := space_fixed path
    simp only [load, Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual.Configuration.initial]
      at sameSpace
    subst sameSpace
    exact Or.inr ⟨emitted, rfl, call_source program condition branches (complete_source path)⟩

/-! ## Controls -/

namespace Controls

open WholeRunWords.Double (noHost)
open IfComputed.Controls (num)
open IfCallBranches.Controls (callRows call_program isZero_condition half_branches)

/-- **`(if (isZero 0) (half 4) (loop))`, every run**: no infinite run from the entry, and every
final configuration publishes `two`. -/
theorem zero_call_finishes (policy : Policy) :
    Acc (fun later earlier => HEStep noHost Completed.rawLookup policy earlier later)
        (load (Space.ofList callRows)
          (callC (app "isZero" [num 0]) (app "half" [num 4]) (app "loop" [])) Atom.undefinedType) ∧
      ∀ x, Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList callRows)
            (callC (app "isZero" [num 0]) (app "half" [num 4]) (app "loop" [])) Atom.undefinedType)
          x →
        (∃ z, HEStep noHost Completed.rawLookup policy x z) ∨
          ∃ emitted : List Result, x = ⟨Space.ofList callRows, .returning [], [], emitted⟩ ∧
            emitted.map (fun r => r.1.erase) = [sym "two"] := by
  obtain ⟨acc, every, -⟩ := call_every_run_finishes noHost (fun impossible => impossible) policy
    call_program isZero_condition half_branches
  exact ⟨acc, every⟩

/-- **Negative control**: in the same program, `(loop)` loaded alone has an infinite run. -/
theorem loop_diverges_call (policy : Policy) :
    ¬ Acc (fun later earlier => HEStep noHost Completed.rawLookup policy earlier later)
      (load (Space.ofList callRows) (app "loop" []) Atom.undefinedType) := fun acc =>
  EveryRunFinishes.not_acc_of_cycle
    (loop_cycle_in (dispatch := noHost) (fun impossible => impossible) policy (atoms := callRows)
      (by decide +kernel)
      (fun row member => (call_program.rows.scoped row member).1)
      (by decide +kernel)) _ acc _ .refl
    ⟨[], [], Completed.Frame.empty, [], [], rfl⟩

end Controls

#print axioms fine_call_function
#print axioms fine_call_query
#print axioms call_fine
#print axioms call_every_run_finishes
#print axioms Controls.zero_call_finishes
#print axioms Controls.loop_diverges_call

end IfCallFinishes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
