import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.LetSource

/-!
# Every run of HE's `let` with a variable pattern finishes

The machine side of `LetSource`, in the continuation-passing logical relation of `EveryRunFinishes`
(`Fine`: no run is stuck, none is infinite). Every choice HE's machine has on the path of
`(let $x d b)` is quantified: the admission's frames, the casts' renewals, the frontier's fresh names
and record, the unifier environments of the work and of `unify`'s candidate. The steps that must
exist are built from HE's own existence theorems: `LetPlain.wildcard_selection_exists` for both
closed arrows, `Entry.Value.UnifyRel.equation_frontier` for the work's environment, and
`Entry.Value.UnifyRel.of_source_candidate` for `unify`'s candidate, whose existence comes from the
model of the work's bindings that sends `x` to `d`.

* `fine_cast_keeps`: a data atom's cast under a demand keeping the bindings, every run, with the
  reached frame's bindings and plainness handed to the continuation (it reuses `LetSource.cast_keeps`
  on the step's own premises);
* `unify_steps_env`: every step of a `unify` instruction, keeping the environment unification;
* `unify_call_fine`, `unify_atom_fine`, `let_query_fine`, `let_fine`: every run of the call of
  `unify`, of the body read at the work's frame, of `let`'s query, and of `(let $x d b)` at a frame
  with empty bindings and a plain environment, under every continuation fine on the instance's
  answers.

## Controls

`LetEveryRun` gives the positive controls (`(let $x 5 (pair $x $x))` and others finish on every run).
`Controls.failure_step_at_bound` (negative, the solving model has content): at bindings that hold
`$x := 7`, the instruction `(unify 5 $x yes no)` has no candidate, so its only step is the failure
rule, which publishes the else-branch; the success rule of `unify_call_fine` is not available there.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace LetFine

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel
  UnifyCandidateRel UnifyNoMatchRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement (TypeBindingSatisfied
  applyTypeValuation)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open HEOnTheStep (HEConfig)
open ServiceFootprints EntryToQuery AnswerBags EveryRun EveryRunFinishes IfFinishes
open LetPlain (Plain PlainEnv letArrow unifyArrow)
open LetSource (letCall unifyBody inst LetProgram LetCall WorkFrame)

variable {dispatch : GroundedDispatch} {policy : Policy}

/-- **The instance contract for finishing**: the facts of a body, answerable answers, and every
marked presentation running finely to them on the scoped lookup. -/
structure InstanceFine (dispatch : GroundedDispatch) (policy : Policy) (atoms : List Atom)
    (t : Atom) (L : List Atom) : Prop where
  facts : BodyFacts t
  clean : ∀ a ∈ L, Answerable a
  fine : FineEval dispatch Completed.scopedLookup policy atoms t L

/-! ## Casts and the minimal step -/

/-- **Every run of a data atom's cast under a demand keeping the bindings finishes**, at a frame with
the same bindings and a plain environment when the frame's is. -/
theorem fine_cast_keeps {space : Space} {live : List Atom} {scope : List String}
    {stack : List Continuation} {emitted : List Result} {a E T : Atom} (data : DataAtom a)
    (entry : Entry.Rel policy.reentry .active a E .cast) (stored : StorageTypesRel space a [T])
    (closedT : TypeSubst.typeVars T = []) (matchesSelf : ∀ b : Bindings, TypeMatchRel E T b b)
    (keeps : ∀ {b out : Bindings}, TypeMatchRel E T b out → out = b) {frame : Frame}
    (next : ∀ after : Frame, after.bindings = frame.bindings →
      (PlainEnv frame.environment → PlainEnv after.environment) →
      Fine dispatch Completed.scopedLookup policy
        ⟨space, .returning [(Entry.Value.ofAtom a, after)], stack, emitted⟩) :
    Fine dispatch Completed.scopedLookup policy
      ⟨space, .work (.atom live scope (Entry.Value.ofAtom a) E frame), stack, emitted⟩ := by
  have accepts : ∀ frame : Frame, ∃ output, policy.matching.Rel E T frame.bindings output :=
    fun frame => ⟨_, Completed.Frame.preserved_type_match policy frame (matchesSelf _)⟩
  have entry' : Entry.Rel policy.reentry (frame.read policy (Entry.Value.ofAtom a)).status
      (frame.read policy (Entry.Value.ofAtom a)).erase E .cast := by
    simp only [CompleteRun.read_data policy frame data, Entry.Value.erase_ofAtom, data.status]
    exact entry
  refine .step ⟨_, ScopedIf.renewed_cast_step_any dispatch policy (answerable_of_data data).closed
    entry (ScopedIf.scoped_closed_answers stored closedT)
    (.unchanged (Completed.Frame.preserved_type_match policy frame (matchesSelf _))) stack emitted⟩ ?_
  intro y step
  cases step with
  | internal l =>
      cases l with
      | delivered entered => cases Entry.functional entered entry'
      | cast entered batch related =>
          have derived : Completed.AtomRel space dispatch Completed.scopedLookup live scope
              (Entry.Value.ofAtom a) E frame _ (policy := policy) := .cast entered batch related
          obtain ⟨after, rfl, bindings, plain⟩ :=
            LetSource.cast_keeps data entry stored closedT keeps accepts derived
          exact next after bindings plain
      | atomTuple entered => cases Entry.functional entered entry'
      | atomFunction entered => cases Entry.functional entered entry'
      | atomFallback entered => cases Entry.functional entered entry'
      | atomSelectionFailed entered => cases Entry.functional entered entry'

/-- **Every step of HE's machine on a `unify` instruction** is the success rule, at a candidate frame
whose environment the environment unifier reached, or the failure rule. -/
theorem unify_steps_env {S : Space} {live : List Atom} {scope : List String} {caller : Option Atom}
    {readiness : Entry.Status} {target pattern yes no : Entry.Value} {activation : Frame}
    {stack : List Continuation} {emitted : List Result} {z : HEConfig}
    (moved : HEStep dispatch Completed.scopedLookup policy
      ⟨S, .work (.minimal live scope caller
        (.expression readiness [.symbol "unify", target, pattern, yes, no]) activation), stack, emitted⟩
      z) :
    (∃ output : Frame, UnifyCandidateRel target.erase pattern.erase activation.bindings output.bindings ∧
        Entry.Value.UnifyRel policy.rebuilding activation.environment target pattern
          output.environment ∧
        z = ⟨S, .returning [(output.read policy yes, output)], stack, emitted⟩) ∨
      (UnifyNoMatchRel target.erase pattern.erase activation.bindings ∧
        z = ⟨S, .returning [(no, activation)], stack, emitted⟩) := by
  generalize same : Entry.Value.expression readiness [.symbol "unify", target, pattern, yes, no] =
    instruction at moved
  cases moved with
  | internal l =>
      cases l with
      | minimalData notInstruction =>
          subst same
          simp [Minimal.embeddedInstruction, Entry.Value.erase] at notInstruction
      | minimalUnifyYes candidate unified =>
          simp only [Entry.Value.expression.injEq, List.cons.injEq, and_true, true_and] at same
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := same
          exact Or.inl ⟨_, candidate, unified, rfl⟩
      | minimalUnifyNo noMatch =>
          simp only [Entry.Value.expression.injEq, List.cons.injEq, and_true, true_and] at same
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := same
          exact Or.inr ⟨noMatch, rfl⟩
      | minimalUnifyBadArity badLength =>
          simp only [Entry.Value.expression.injEq, List.cons.injEq, true_and] at same
          obtain ⟨-, rfl⟩ := same
          exact absurd rfl badLength
      | _ => simp at same

/-! ## The call of `unify` -/

/-- **Every run of the call of `unify` on read arguments finishes with the instance's answers**: the
call is embedded, the invocation is embedded, the success rule fires (some model sends `x` to `d`,
so a candidate exists, and HE's environment unifier reaches it), and the then-branch, the plain value
of the instance, runs finely. -/
theorem unify_call_fine (notUnify : ¬ dispatch.executable (.symbol "unify")) {atoms : List Atom}
    {x : String} {d b : Atom} {L : List Atom} (onlyX : ∀ y ∈ TypeSubst.typeVars b, y = x)
    (instance' : InstanceFine dispatch policy atoms (inst x d b) L)
    {live : List Atom} {scope : List String} {F : Frame} (plainF : PlainEnv F.environment)
    {cA cP cT cE : Entry.Value} (plainA : Plain cA) (plainP : Plain cP) (plainT : Plain cT)
    (sees : ∀ v, TypeBindingSatisfied v F.bindings →
      applyTypeValuation v cA.erase = d ∧ applyTypeValuation v cP.erase = v x ∧
        applyTypeValuation v cT.erase = applyTypeValuation v b)
    (solvable : ∃ v, TypeBindingSatisfied v F.bindings ∧ v x = d)
    (stack : List Continuation) (emitted : List Result)
    (cont : ∀ R : List Result, R.map (fun r => r.1.erase) = L →
      Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms,
      .work (.call live scope (.expression .active [.symbol "unify", cA, cP, cT, cE])
        Atom.undefinedType F), stack, emitted⟩ := by
  have embedded := LetSource.unify_embedded cA cP cT cE
  have notError := LetSource.unify_not_error cA cP cT cE
  have notHost : ¬ Minimal.HostCall dispatch
      (Entry.Value.expression .active [.symbol "unify", cA, cP, cT, cE]).erase := by
    rw [LetSource.unify_value_erase]
    rintro ⟨operator, arguments, same, executable⟩
    simp only [Atom.expression.injEq, List.cons.injEq] at same
    rw [← same.1] at executable
    exact notUnify executable
  have grounded : ¬ NonGroundedCallRel dispatch
      (Entry.Value.expression .active [.symbol "unify", cA, cP, cT, cE]).erase := by
    intro nonGrounded
    have notInstruction := nonGrounded.2
    rw [embedded] at notInstruction
    cases notInstruction
  have minimalFine : Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms,
      .work (.minimal (Atom.undefinedType :: live) scope none
        (.expression .active [.symbol "unify", cA, cP, cT, cE]) F),
      .boundaryBatch live scope none
        (.returned (.expression .active [.symbol "unify", cA, cP, cT, cE]) Atom.undefinedType) ::
          stack, emitted⟩ := by
    obtain ⟨v, model, vx⟩ := solvable
    obtain ⟨isA, isP, _⟩ := sees v model
    obtain ⟨out0, candidate0⟩ := (LetFrontier.candidate_iff (target := cA.erase)
      (pattern := cP.erase) (incoming := F.bindings)).mpr ⟨v, model, by rw [isA, isP, vx]⟩
    obtain ⟨environment, unified0, certified⟩ :=
      Entry.Value.UnifyRel.of_source_candidate (policy := policy.rebuilding) F.certified candidate0
    refine .step ⟨_, .internal (.minimalUnifyYes (output := ⟨out0, environment, certified⟩)
      candidate0 unified0)⟩ ?_
    intro z moved
    rcases unify_steps_env moved with ⟨out, candidate, unified, rfl⟩ | ⟨noMatch, _⟩
    · have plainOut : PlainEnv out.environment :=
        LetPlain.unifyRel_plain unified plainA plainP plainF
      have forced : ∀ v, TypeBindingSatisfied v out.bindings →
          applyTypeValuation v cT.erase = inst x d b := by
        intro v model
        obtain ⟨solves, before⟩ := (UnifyCandidateRel.solutions candidate v).mp model
        obtain ⟨isA, isP, isT⟩ := sees v before
        have vx : v x = d := by rw [← isP, ← solves, isA]
        rw [isT, LetSource.inst_of_model onlyX vx]
      have readT : out.read policy cT = Entry.Value.ofAtom (inst x d b) := by
        rw [LetPlain.read_plain policy out plainOut plainT,
          LetFrontier.read_forced policy out cT _ forced]
      rw [readT]
      apply fine_boundaryBatch_frame
      apply fine_boundaryBatch_cons
      apply fine_boundary_returned
      refine fine_returned_evaluate ?_ ?_ ?_
      · rw [Entry.Value.erase_ofAtom]
        exact instance'.facts.notRefused
      · rw [Entry.Value.erase_ofAtom]
        exact instance'.facts.notStopped
      refine instance'.fine (Entry.Value.ofAtom (inst x d b)) (Entry.Value.erase_ofAtom _)
        (MarkedValues.marked_ofAtom _) _ _ out _ _ ?_
      intro R eraseR
      apply fine_append
      apply fine_boundaryBatch_nil
      apply fine_prepend
      apply cont
      simpa using eraseR
    · exact absurd candidate0 (noMatch out0)
  refine .step ⟨_, .internal (.callEmbedded notError notHost embedded)⟩ ?_
  intro z moved
  cases moved with
  | internal l =>
      cases l with
      | callError failed => exact absurd failed notError
      | callAbsent _ nonGrounded _ => exact absurd nonGrounded grounded
      | callEquations _ nonGrounded _ _ => exact absurd nonGrounded grounded
      | callEmbedded _ _ _ =>
          refine .step ⟨_, .internal (.invocationEmbedded notHost embedded)⟩ ?_
          intro z' moved'
          cases moved' with
          | internal l' =>
              cases l' with
              | invocationAbsent nonGrounded _ => exact absurd nonGrounded grounded
              | invocationEquations nonGrounded _ _ => exact absurd nonGrounded grounded
              | invocationEmbedded _ _ => exact minimalFine

/-! ## The body of `let`'s row at the work's frame -/

/-- **Every run of the body of `let`'s work, `(unify $a $p $t Empty)` read at the work's frame,
finishes with the instance's answers.** -/
theorem unify_atom_fine (notUnify : ¬ dispatch.executable (.symbol "unify")) {atoms : List Atom}
    (program : LetProgram atoms) {x : String} {d b : Atom} (call : LetCall atoms x d b)
    {L : List Atom} (instance' : InstanceFine dispatch policy atoms (inst x d b) L)
    {a p t : String} {G : Frame} (work : WorkFrame G x d b a p t)
    {live : List Atom} {scope : List String} (stack : List Continuation) (emitted : List Result)
    (cont : ∀ R : List Result, R.map (fun r => r.1.erase) = L →
      Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms,
      .work (.atom live scope (G.read policy (Entry.Value.ofAtom (unifyBody a p t)))
        Atom.undefinedType G), stack, emitted⟩ := by
  obtain ⟨wA, hwA⟩ : ∃ w, G.read policy (G.read policy (.var a)) = w := ⟨_, rfl⟩
  obtain ⟨wP, hwP⟩ : ∃ w, G.read policy (G.read policy (.var p)) = w := ⟨_, rfl⟩
  obtain ⟨wT, hwT⟩ : ∃ w, G.read policy (G.read policy (.var t)) = w := ⟨_, rfl⟩
  have readR : G.read policy (G.read policy (Entry.Value.ofAtom (unifyBody a p t))) =
      .expression .active [Entry.Value.ofAtom (.symbol "unify"), wA, wP, wT, .symbol "Empty"] := by
    rw [LetSource.read_unify_body, hwA, hwP, hwT]
    simp [Entry.Value.ofAtom]
  have plainA : Plain wA := hwA ▸ LetSource.read_read_plain_var policy G work.plain a
  have plainP : Plain wP := hwP ▸ LetSource.read_read_plain_var policy G work.plain p
  have plainT : Plain wT := hwT ▸ LetSource.read_read_plain_var policy G work.plain t
  have seesR : ∀ v, TypeBindingSatisfied v G.bindings →
      applyTypeValuation v wA.erase = d ∧ applyTypeValuation v wP.erase = v x ∧
        applyTypeValuation v wT.erase = applyTypeValuation v b := by
    intro v model
    obtain ⟨isA, isP, isT⟩ := work.sees v model
    refine ⟨?_, ?_, ?_⟩
    · rw [← hwA, LetSource.read_read_sound policy G _ model]
      simpa [Entry.Value.erase, applyTypeValuation] using isA
    · rw [← hwP, LetSource.read_read_sound policy G _ model]
      simpa [Entry.Value.erase, applyTypeValuation] using isP
    · rw [← hwT, LetSource.read_read_sound policy G _ model]
      simpa [Entry.Value.erase, applyTypeValuation] using isT
  obtain ⟨m, mModel, mx⟩ := work.free
  have eraseA : wA.erase = d := by
    rw [← hwA]
    exact LetFrontier.read_forced policy G _ d fun v model => by
      rw [LetFrontier.read_sound policy G _ model]
      simpa [Entry.Value.erase, applyTypeValuation] using (work.sees v model).1
  obtain ⟨zP, eraseP⟩ : ∃ z, wP.erase = .var z :=
    LetSource.var_of_sees mx (seesR m mModel).2.1
  obtain ⟨h, tl, bShape⟩ := call.expression
  have typesT : StorageTypesRel (Space.ofList atoms) wT.erase [Atom.undefinedType] := by
    have seen := (seesR m mModel).2.2
    rw [LetSource.fixed_of_model call.onlyX mx, bShape] at seen
    rcases LetSource.var_or_expression seen with ⟨z, same⟩ | ⟨h', t', same⟩
    · rw [same]; exact .variable _ z
    · rw [same]; exact program.exprTypes h' t'
  have single : LetPlain.SingleTypes (Space.ofList atoms)
      [wA.erase, wP.erase, wT.erase, .symbol "Empty"] := by
    intro arg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · rw [eraseA]; exact call.typed
    · rw [eraseP]; exact ⟨_, .variable _ zP, rfl⟩
    · exact ⟨_, typesT, rfl⟩
    · exact ⟨_, program.emptyTypes, rfl⟩
  have entry : Entry.Rel policy.reentry (G.read policy (G.read policy
        (Entry.Value.ofAtom (unifyBody a p t)))).status
      (G.read policy (G.read policy (Entry.Value.ofAtom (unifyBody a p t)))).erase
      Atom.undefinedType .interpret := by
    have atEmpty := call_entry policy LetSource.unify_data
      [wA.erase, wP.erase, wT.erase, Atom.empty]
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom] at atEmpty
    rw [readR]
    simpa [Entry.Value.erase, Entry.Value.status, Entry.Value.ofAtom, Atom.empty] using atEmpty
  have shape : G.read policy (G.read policy (Entry.Value.ofAtom (unifyBody a p t))) =
      .expression .active (Entry.Value.ofAtom (.symbol "unify") :: [wA, wP, wT, .symbol "Empty"]) :=
    readR
  have wild : LetPlain.Wildcards LetPlain.unifyPolicy.argumentTypes := by
    intro T member
    simp only [LetPlain.unifyPolicy, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> exact Or.inr rfl
  have selectionExists : Completed.ArgumentService.historical.selection (Space.ofList atoms)
      Completed.scopedLookup policy live scope
      (G.read policy (G.read policy (Entry.Value.ofAtom (unifyBody a p t)))).erase
      (Entry.Value.ofAtom (.symbol "unify")).erase Atom.undefinedType G
      (.selected LetPlain.unifyPolicy [G]) := by
    rw [readR, Entry.Value.erase_ofAtom]
    simp only [Entry.Value.erase, Entry.Value.erase_ofAtom, List.map_cons, List.map_nil]
    exact LetPlain.wildcard_selection_exists policy live scope LetPlain.unifyPolicy G
      program.unifyTypes LetPlain.Controls.unifyArrow_closed single wild rfl rfl
  have selection : ∀ {outcome : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList atoms) Completed.scopedLookup policy live scope
        (G.read policy (G.read policy (Entry.Value.ofAtom (unifyBody a p t)))).erase
        (Entry.Value.ofAtom (.symbol "unify")).erase Atom.undefinedType G outcome →
      ∃ (signature : SelectedTypePolicy) (frame : Frame), signature.functionType = unifyArrow ∧
        outcome = .selected signature [frame] ∧ frame.bindings = G.bindings ∧
        (PlainEnv G.environment → PlainEnv frame.environment) := by
    intro outcome chosen
    rw [readR, Entry.Value.erase_ofAtom] at chosen
    simp only [Entry.Value.erase, Entry.Value.erase_ofAtom, List.map_cons, List.map_nil] at chosen
    exact LetPlain.wildcard_selection program.unifyTypes LetPlain.Controls.unifyArrow_closed
      ⟨_, _, LetPlain.unifyPolicy.isFunction⟩ single
      (fun functionType => by
        obtain ⟨args, returned⟩ := LetPlain.unify_projections functionType
        refine ⟨?_, by simp [args], returned⟩
        rw [args]
        intro T member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> exact Or.inr rfl)
      chosen
  have notStoppedB : ¬ IsEmptyOrErrorRel b :=
    LetSource.not_stopped_of_apply (m := fun y => if y = x then d else .var y) (c := inst x d b) rfl
      instance'.facts.notStopped
  refine .step ⟨_, .internal (LocalStepWith.atomFunction (admission := .historical) entry shape
    selectionExists)⟩ ?_
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
            program.unifyTypes.occurrences
          simp [Atom.undefinedType] at same
      | atomFallback _ shaped chosen =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          obtain ⟨_, _, _, impossible, _⟩ := selection chosen
          cases impossible
      | atomSelectionFailed _ shaped chosen =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          obtain ⟨_, _, _, impossible, _⟩ := selection chosen
          cases impossible
      | atomFunction _ shaped chosen =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, rfl⟩ := shaped
          obtain ⟨signature, after, functionType, selected, afterBindings, afterPlain⟩ :=
            selection chosen
          simp only [Completed.InvocationSelection.selected.injEq] at selected
          obtain ⟨rfl, rfl⟩ := selected
          have projections := LetPlain.unify_projections functionType
          apply fine_invocations_cons
          rw [LetPlain.returnType_undefined projections.2]
          refine fine_functionStart (by simp [projections.1]) ?_
          rw [projections.1, functionType]
          simp only [List.zip_cons_cons, List.zip_nil_right]
          refine fine_cast_keeps LetSource.unify_data
            (LetSource.arrow_cast_entry (by decide) (by decide) ⟨_, rfl⟩) program.unifyTypes
            LetPlain.Controls.unifyArrow_closed LetPlain.unifyArrow_matches LetSource.unifyArrow_keeps ?_
          intro frU frUBindings frUPlain
          have plainU : PlainEnv frU.environment := frUPlain (afterPlain work.plain)
          have bindingsU : frU.bindings = G.bindings := by rw [frUBindings, afterBindings]
          have frModel : TypeBindingSatisfied m frU.bindings := by rw [bindingsU]; exact mModel
          have notStoppedA : ¬ IsEmptyOrErrorRel (frU.read policy wA).erase :=
            LetSource.not_stopped_of_apply (m := m) (c := d)
              (by rw [LetFrontier.read_sound policy frU _ frModel]; exact (seesR m mModel).1)
              call.data.not_stopped
          have notStoppedP : ¬ IsEmptyOrErrorRel (frU.read policy wP).erase :=
            LetSource.not_stopped_of_apply (m := m) (c := .var x)
              (by rw [LetFrontier.read_sound policy frU _ frModel, (seesR m mModel).2.1, mx])
              (LetSource.var_not_stopped x)
          have notStoppedT : ¬ IsEmptyOrErrorRel (frU.read policy wT).erase :=
            LetSource.not_stopped_of_apply (m := m) (c := b)
              (by rw [LetFrontier.read_sound policy frU _ frModel, (seesR m mModel).2.2,
                LetSource.fixed_of_model call.onlyX mx])
              notStoppedB
          apply fine_functionHeads_frame
          refine fine_functionBranches_continue ?_ ?_
          · simpa using LetSource.unify_data.not_stopped
          apply fine_argumentsCons
          apply AtomDemands.atom_demand_fine
          apply fine_arguments_frame
          refine fine_argumentBranches_continue (fun stopped => notStoppedA stopped.1) ?_
          apply fine_argumentsCons
          apply AtomDemands.atom_demand_fine
          apply fine_arguments_frame
          refine fine_argumentBranches_continue (fun stopped => notStoppedP stopped.1) ?_
          apply fine_argumentsCons
          apply AtomDemands.atom_demand_fine
          apply fine_arguments_frame
          refine fine_argumentBranches_continue (fun stopped => notStoppedT stopped.1) ?_
          apply fine_argumentsCons
          apply AtomDemands.atom_demand_fine
          apply fine_arguments_frame
          refine fine_argumentBranches_continue
            (fun stopped => stopped.2 (by simp [LetSource.read_symbol])) ?_
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
          apply fine_argumentTail
          apply fine_append
          apply fine_argumentBranches_nil
          apply fine_prepend
          apply fine_functionAssemble
          apply fine_append
          apply fine_functionBranches_nil
          apply fine_prepend
          simp only [List.map_cons, List.map_nil, List.append_nil, Completed.argumentPrepend_packet,
            Completed.functionAssemble, Entry.Value.unpackArguments_packet]
          apply fine_calls_frame
          apply fine_calls_cons
          simp only [Entry.Value.ofAtom, LetSource.read_symbol]
          refine unify_call_fine notUnify call.onlyX instance' plainU
            (LetPlain.read_plain policy frU plainU plainA)
            (LetPlain.read_plain policy frU plainU plainP)
            (LetPlain.read_plain policy frU plainU plainT)
            (fun v model => by
              have gModel : TypeBindingSatisfied v G.bindings := by rw [← bindingsU]; exact model
              obtain ⟨isA, isP, isT⟩ := seesR v gModel
              refine ⟨?_, ?_, ?_⟩
              · rw [LetFrontier.read_sound policy frU _ model, isA]
              · rw [LetFrontier.read_sound policy frU _ model, isP]
              · rw [LetFrontier.read_sound policy frU _ model, isT])
            (by rw [bindingsU]; exact work.solvable) _ _ ?_
          intro Q eraseQ
          apply fine_append
          apply fine_calls_nil
          apply fine_prepend
          apply fine_append
          apply fine_invocations_nil
          apply fine_prepend
          refine fine_publish (fun r member => ?_) ?_
          · have inQ : r.1.erase ∈ L := by
              rw [← eraseQ]
              exact List.mem_map.mpr ⟨r, by simpa using member, rfl⟩
            exact instance'.clean _ inQ
          apply cont
          rw [NestedEveryRun.publish_erase]
          simpa using eraseQ

/-! ## The query of `let`'s row -/

/-- **Every run of the query of `(let $x d b)` at a frame with empty bindings and a plain
environment finishes with the instance's answers.** -/
theorem let_query_fine (notLet : ¬ dispatch.executable (.symbol "let"))
    (notUnify : ¬ dispatch.executable (.symbol "unify")) {atoms : List Atom}
    (program : LetProgram atoms) {x : String} {d b : Atom} (call : LetCall atoms x d b)
    {L : List Atom} (instance' : InstanceFine dispatch policy atoms (inst x d b) L)
    {live : List Atom} {scope : List String} {F : Frame} (emptyF : F.bindings = Bindings.empty)
    (plainF : PlainEnv F.environment) (stack : List Continuation) (emitted : List Result)
    (cont : ∀ R : List Result, R.map (fun r => r.1.erase) = L →
      Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms,
      .work (.call live scope (Entry.Value.ofAtom (letCall x d b)) Atom.undefinedType F), stack,
      emitted⟩ := by
  have rows := program.rows
  obtain ⟨rest, same, foreign⟩ := rows
  subst same
  have notError : ¬ IsErrorRel (Entry.Value.ofAtom (letCall x d b)).erase := by
    rw [Entry.Value.erase_ofAtom]
    rintro ⟨tail, same⟩
    simp at same
  have nonGrounded : NonGroundedCallRel dispatch (Entry.Value.ofAtom (letCall x d b)).erase :=
    HERuns.value_nonGrounded notLet (by simp [Minimal.embeddedInstruction])
      (Entry.Value.erase_ofAtom _)
  have satisfiable : ∃ m : String → Atom, TypeBindingSatisfied m F.bindings :=
    F.certified.satisfiable
  have fromFrontier : ∀ works : List EquationWork,
      EquationFrontierRel (Space.ofList (LetFrontier.letRows ++ rest)) (Atom.undefinedType :: live)
        (letCall x d b) F.bindings works →
      Fine dispatch Completed.scopedLookup policy ⟨Space.ofList (LetFrontier.letRows ++ rest),
        .work (.equations live scope (Entry.Value.ofAtom (letCall x d b)) Atom.undefinedType F works),
        stack, emitted⟩ := by
    intro works frontier
    obtain ⟨w, rename, rfl, injective, _, bodyEq, fresh, solutions⟩ :=
      LetSource.let_frontier_fresh foreign satisfiable frontier
    have hxp : x ≠ rename "pattern" := fun same => fresh "pattern" (by simp) same.symm
    have hxa : x ≠ rename "atom" := fun same => fresh "atom" (by simp) same.symm
    have hxt : x ≠ rename "template" := fun same => fresh "template" (by simp) same.symm
    have hpa : rename "atom" ≠ rename "pattern" := injective.ne (by decide)
    have hpt : rename "template" ≠ rename "pattern" := injective.ne (by decide)
    have hat : rename "template" ≠ rename "atom" := injective.ne (by decide)
    have frontier' : EquationFrontierRel (Space.ofList (LetFrontier.letRows ++ rest))
        (Atom.undefinedType :: live) (Entry.Value.ofAtom (letCall x d b)).erase F.bindings [w] := by
      rw [Entry.Value.erase_ofAtom]
      exact frontier
    obtain ⟨environments, paired⟩ := Entry.Value.UnifyRel.equation_frontier
      (policy := policy.rebuilding) F.certified frontier'
    obtain ⟨after, unified, certificate⟩ := forall₂_left_exists paired w List.mem_cons_self
    refine .step ⟨_, .internal (.equationsCons (output := ⟨w.bindings, after, certificate⟩) rfl
      unified)⟩ ?_
    intro z step
    cases step with
    | internal l =>
        cases l with
        | equationsCons sameBindings unified' =>
            have work := LetSource.let_work_frame call emptyF plainF hxp hxa hxt hpa hpt hat
              solutions sameBindings unified'
            rw [bodyEq]
            refine fine_boundary_producer ?_ ?_
            · rintro ⟨⟨inner, same⟩, _⟩
              rw [LetSource.unify_body_erase] at same
              simp at same
            apply fine_boundaryBatch_frame
            apply fine_boundaryBatch_cons
            apply fine_boundary_returned
            refine fine_returned_evaluate ?_ ?_ ?_
            · rw [LetSource.unify_body_erase]
              simp [Atom.notReducible]
            · rw [LetSource.unify_body_erase]
              rintro (same | ⟨tail, same⟩)
              · simp [Atom.empty] at same
              · simp at same
            refine unify_atom_fine notUnify program call instance' work _ _ ?_
            intro R eraseR
            apply fine_append
            apply fine_boundaryBatch_nil
            apply fine_prepend
            apply fine_append
            apply fine_equations_nil
            apply fine_prepend
            apply cont
            simpa using eraseR
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList (LetFrontier.letRows ++ rest))
    (Atom.undefinedType :: live) (letCall x d b) F.bindings
  obtain ⟨w, _, rfl, _⟩ := LetSource.let_frontier_fresh foreign satisfiable frontier
  have frontier' : EquationFrontierRel (Space.ofList (LetFrontier.letRows ++ rest))
      (Atom.undefinedType :: live) (Entry.Value.ofAtom (letCall x d b)).erase F.bindings [w] := by
    rw [Entry.Value.erase_ofAtom]
    exact frontier
  refine .step ⟨_, .internal (.callEquations notError nonGrounded frontier'
    (List.cons_ne_nil _ _))⟩ ?_
  intro z step
  cases step with
  | internal l =>
      cases l with
      | callError failed => exact absurd failed notError
      | callEmbedded _ _ instruction =>
          rw [Entry.Value.erase_ofAtom] at instruction
          simp [Minimal.embeddedInstruction] at instruction
      | callAbsent _ _ frontierEmpty =>
          rw [Entry.Value.erase_ofAtom] at frontierEmpty
          obtain ⟨_, _, same, _⟩ := LetSource.let_frontier_fresh foreign satisfiable frontierEmpty
          cases same
      | callEquations _ _ frontierW _ =>
          rw [Entry.Value.erase_ofAtom] at frontierW
          exact fromFrontier _ frontierW

/-! ## `let` -/

/-- **Every run of `(let $x d b)` at a frame with empty bindings and a plain environment (HE's entry
is one) finishes with the instance's answers**, under every continuation fine on them. -/
theorem let_fine (notLet : ¬ dispatch.executable (.symbol "let"))
    (notUnify : ¬ dispatch.executable (.symbol "unify")) {atoms : List Atom}
    (program : LetProgram atoms) {x : String} {d b : Atom} (call : LetCall atoms x d b)
    {L : List Atom} (instance' : InstanceFine dispatch policy atoms (inst x d b) L)
    {live : List Atom} {scope : List String} {F : Frame} (emptyF : F.bindings = Bindings.empty)
    (plainF : PlainEnv F.environment) (stack : List Continuation) (emitted : List Result)
    (cont : ∀ R : List Result, R.map (fun r => r.1.erase) = L →
      Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    Fine dispatch Completed.scopedLookup policy ⟨Space.ofList atoms,
      .work (.atom live scope (Entry.Value.ofAtom (letCall x d b)) Atom.undefinedType F), stack,
      emitted⟩ := by
  have readC : F.read policy (Entry.Value.ofAtom (letCall x d b)) =
      Entry.Value.ofAtom (letCall x d b) := LetSource.read_ofAtom_of_empty policy F emptyF plainF _
  have entry : Entry.Rel policy.reentry (F.read policy (Entry.Value.ofAtom (letCall x d b))).status
      (F.read policy (Entry.Value.ofAtom (letCall x d b))).erase Atom.undefinedType .interpret := by
    have atEmpty := call_entry policy LetSource.let_data [.var x, d, b]
    rw [Completed.Frame.read_empty] at atEmpty
    rw [readC]
    exact atEmpty
  have shape : F.read policy (Entry.Value.ofAtom (letCall x d b)) =
      .expression .active (Entry.Value.ofAtom (.symbol "let") ::
        [Atom.var x, d, b].map Entry.Value.ofAtom) := by
    rw [readC]
    simp only [letCall, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  obtain ⟨Td, typesD, closedD⟩ := call.typed
  obtain ⟨h, tl, bShape⟩ := call.expression
  have single : LetPlain.SingleTypes (Space.ofList atoms) [.var x, d, b] := by
    intro arg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨_, .variable _ x, rfl⟩
    · exact ⟨_, typesD, closedD⟩
    · rw [bShape]; exact ⟨_, program.exprTypes h tl, rfl⟩
  have wild : LetPlain.Wildcards LetPlain.letPolicy.argumentTypes := by
    intro T member
    simp only [LetPlain.letPolicy, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have selectionExists : Completed.ArgumentService.historical.selection (Space.ofList atoms)
      Completed.scopedLookup policy live scope
      (F.read policy (Entry.Value.ofAtom (letCall x d b))).erase
      (Entry.Value.ofAtom (.symbol "let")).erase Atom.undefinedType F
      (.selected LetPlain.letPolicy [F]) := by
    rw [readC, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom]
    exact LetPlain.wildcard_selection_exists policy live scope LetPlain.letPolicy F
      program.letTypes LetPlain.Controls.letArrow_closed single wild rfl rfl
  have selection : ∀ {outcome : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList atoms) Completed.scopedLookup policy live scope
        (F.read policy (Entry.Value.ofAtom (letCall x d b))).erase
        (Entry.Value.ofAtom (.symbol "let")).erase Atom.undefinedType F outcome →
      ∃ (signature : SelectedTypePolicy) (frame : Frame), signature.functionType = letArrow ∧
        outcome = .selected signature [frame] ∧ frame.bindings = F.bindings ∧
        (PlainEnv F.environment → PlainEnv frame.environment) := by
    intro outcome chosen
    rw [readC, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosen
    exact LetPlain.wildcard_selection program.letTypes LetPlain.Controls.letArrow_closed
      ⟨_, _, LetPlain.letPolicy.isFunction⟩ single
      (fun functionType => by
        obtain ⟨args, returned⟩ := LetPlain.let_projections functionType
        refine ⟨?_, by simp [args], returned⟩
        rw [args]
        intro T member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl rfl
        · exact Or.inr rfl)
      chosen
  have notStoppedB : ¬ IsEmptyOrErrorRel b :=
    LetSource.not_stopped_of_apply (m := fun y => if y = x then d else .var y) (c := inst x d b) rfl
      instance'.facts.notStopped
  refine .step ⟨_, .internal (LocalStepWith.atomFunction (admission := .historical) entry shape
    selectionExists)⟩ ?_
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
            program.letTypes.occurrences
          simp [Atom.undefinedType] at same
      | atomFallback _ shaped chosen =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          obtain ⟨_, _, _, impossible, _⟩ := selection chosen
          cases impossible
      | atomSelectionFailed _ shaped chosen =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, _⟩ := shaped
          obtain ⟨_, _, _, impossible, _⟩ := selection chosen
          cases impossible
      | atomFunction _ shaped chosen =>
          rw [shape] at shaped
          simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
          obtain ⟨_, rfl, rfl⟩ := shaped
          obtain ⟨signature, after, functionType, selected, afterBindings, afterPlain⟩ :=
            selection chosen
          simp only [Completed.InvocationSelection.selected.injEq] at selected
          obtain ⟨rfl, rfl⟩ := selected
          have projections := LetPlain.let_projections functionType
          apply fine_invocations_cons
          rw [LetPlain.returnType_undefined projections.2]
          refine fine_functionStart (by simp [projections.1]) ?_
          rw [projections.1, functionType]
          simp only [List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_right]
          refine fine_cast_keeps LetSource.let_data
            (LetSource.arrow_cast_entry (by decide) (by decide) ⟨_, rfl⟩) program.letTypes
            LetPlain.Controls.letArrow_closed LetPlain.letArrow_matches LetSource.letArrow_keeps ?_
          intro frF frFBindings frFPlain
          have emptyFF : frF.bindings = Bindings.empty := by rw [frFBindings, afterBindings, emptyF]
          have plainFF : PlainEnv frF.environment := frFPlain (afterPlain plainF)
          apply fine_functionHeads_frame
          refine fine_functionBranches_continue ?_ ?_
          · simpa using LetSource.let_data.not_stopped
          apply fine_argumentsCons
          apply AtomDemands.atom_demand_fine
          rw [LetSource.read_ofAtom_of_empty policy frF emptyFF plainFF]
          apply fine_arguments_frame
          refine fine_argumentBranches_continue (fun stopped => ?_) ?_
          · have stoppedX := stopped.1
            simp only [Entry.Value.erase_ofAtom] at stoppedX
            exact LetSource.var_not_stopped x stoppedX
          apply fine_argumentsCons
          refine fine_cast_keeps call.data (call.data.entry _) typesD closedD
            (fun b' => .undefinedLeft _ b') (fun matched => matched.undefined_output) ?_
          intro frD frDBindings frDPlain
          have emptyFD : frD.bindings = Bindings.empty := by rw [frDBindings, emptyFF]
          have plainFD : PlainEnv frD.environment := frDPlain plainFF
          apply fine_arguments_frame
          refine fine_argumentBranches_continue (fun stopped => ?_) ?_
          · have stoppedD := stopped.1
            simp only [Entry.Value.erase_ofAtom] at stoppedD
            exact call.data.not_stopped stoppedD
          apply fine_argumentsCons
          apply AtomDemands.atom_demand_fine
          rw [LetSource.read_ofAtom_of_empty policy frD emptyFD plainFD]
          apply fine_arguments_frame
          refine fine_argumentBranches_continue (fun stopped => ?_) ?_
          · have stoppedB := stopped.1
            simp only [Entry.Value.erase_ofAtom] at stoppedB
            exact notStoppedB stoppedB
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
          simp only [List.map_cons, List.map_nil, List.append_nil, Completed.argumentPrepend_packet,
            Completed.functionAssemble, Entry.Value.unpackArguments_packet]
          apply fine_calls_frame
          apply fine_calls_cons
          have valueEq : (Entry.Value.expression .active
              [Entry.Value.ofAtom (.symbol "let"), Entry.Value.ofAtom (.var x), Entry.Value.ofAtom d,
                Entry.Value.ofAtom b]) = Entry.Value.ofAtom (letCall x d b) := by
            simp [letCall, Entry.Value.ofAtom]
          simp only [valueEq]
          refine let_query_fine notLet notUnify program call instance' emptyFD plainFD _ _ ?_
          intro Q eraseQ
          apply fine_append
          apply fine_calls_nil
          apply fine_prepend
          apply fine_append
          apply fine_invocations_nil
          apply fine_prepend
          refine fine_publish (fun r member => ?_) ?_
          · have inQ : r.1.erase ∈ L := by
              rw [← eraseQ]
              exact List.mem_map.mpr ⟨r, by simpa using member, rfl⟩
            exact instance'.clean _ inQ
          apply cont
          rw [NestedEveryRun.publish_erase]
          simpa using eraseQ

/-- **At HE's entry**: every run of `(let $x d b)` finishes with the instance's answers. -/
theorem let_entry_fine (notLet : ¬ dispatch.executable (.symbol "let"))
    (notUnify : ¬ dispatch.executable (.symbol "unify")) {atoms : List Atom}
    (program : LetProgram atoms) {x : String} {d b : Atom} (call : LetCall atoms x d b)
    {L : List Atom} (instance' : InstanceFine dispatch policy atoms (inst x d b) L) :
    Fine dispatch Completed.scopedLookup policy
      (load (Space.ofList atoms) (letCall x d b) Atom.undefinedType) :=
  let_fine notLet notUnify program call instance' rfl LetPlain.plainEnv_nil [] []
    (fun R _ => fine_top R [])

/-! ## Controls -/

namespace Controls

/-- **Negative control, the solving model has content**: at an activation whose bindings hold
`$x := 7`, every step of the instruction `(unify 5 $x yes no)` is the failure rule and publishes the
else-branch `no`: no model sends `x` to `5` there (`LetSource.Controls.var_not_solvable`). -/
theorem failure_step_at_bound {S : Space} {live : List Atom} {scope : List String}
    {caller : Option Atom} {activation : Frame}
    (bound : activation.bindings = ⟨[("x", .grounded (.int 7))], []⟩)
    {stack : List Continuation} {emitted : List Result} {z : HEConfig}
    (moved : HEStep dispatch Completed.scopedLookup policy
      ⟨S, .work (.minimal live scope caller
        (.expression .active [.symbol "unify", .grounded (.int 5), .var "x", .symbol "yes",
          .symbol "no"]) activation), stack, emitted⟩ z) :
    z = ⟨S, .returning [(.symbol "no", activation)], stack, emitted⟩ := by
  rcases unify_steps_env moved with ⟨output, candidate, _, _⟩ | ⟨_, same⟩
  · exfalso
    obtain ⟨v, model, solves⟩ := LetFrontier.candidate_iff.mp ⟨_, candidate⟩
    apply LetSource.Controls.var_not_solvable
    refine ⟨v, bound ▸ model, ?_⟩
    simpa [Entry.Value.erase, applyTypeValuation] using solves.symm
  · exact same

end Controls

#print axioms fine_cast_keeps
#print axioms unify_steps_env
#print axioms unify_call_fine
#print axioms unify_atom_fine
#print axioms let_query_fine
#print axioms let_fine
#print axioms let_entry_fine
#print axioms Controls.failure_step_at_bound

end LetFine

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
