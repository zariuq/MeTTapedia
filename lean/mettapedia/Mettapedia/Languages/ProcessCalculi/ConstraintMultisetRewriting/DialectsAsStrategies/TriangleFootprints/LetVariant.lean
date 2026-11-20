import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.DeclaredTrees
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.LetPeTTaTemplates

/-!
# `let` on the variant machine: templates whose instance has declared branches

`LetEveryRun` proves `(let $x d b)` on every run of HE's model for instances whose answers the model
determines. An instance with a declared branch of `if`, such as `(if True 1 2)` for the template
`(if $x 1 2)`, is not one: the model has a run that publishes a cast error (`DeclaredBranchGap`).
On the variant machine the instance runs to its answers at every frame (`DeclaredTrees`), and this
module carries `let` over.

The run of `let` is the one of `LetFine`: its proof quantifies over every step of the model, so it
holds for the variant machine by `VariantRuns.goodv_of_model`, with the instance's contract stated
for the variant machine.

* `InstanceGood`: the instance contract: the facts of a body, answerable answers, and every run of
  the variant machine from the instance going on with its answers, at every frame.
* `goodv_cast_keeps`, `unify_call_good`, `unify_atom_good`, `let_query_good`, `let_good`,
  `let_entry_good`: every run of the variant machine on `(let $x d b)` at a frame with empty
  bindings and a plain environment goes on with the instance's answers.
* `let_declared_every_run`: **for a data value `d` with one closed stored type and a template whose
  instance is a tree with declared `if` (`DeclaredTrees.SettlesDeclared`): a complete run of the
  variant machine on `(let $x d b)` exists, every complete run publishes the instance's answers, no
  run is infinite, and none is stuck.**
* `let_if_declared_agree`: **`(let $x b (if $x y n))` with a declared taken branch, in both
  dialects**, for every name `x` and every Boolean literal `b`: every run of the variant machine
  finishes with the branch of `b`, and PeTTa yields the same.

The instance is evaluated at the frame that `unify` returns, whose record the model fixes only up to
meaning (`UnifyCandidateGap`). That does not matter here: the `if` of the instance draws its fresh
return name after the `unify`, so the earlier record does not mention it.

## Controls

On HE's `let` and `if` programs (`LetEveryRun.Controls.letIfRows`):
* `Controls.let_number_agree` (positive, both dialects): for each Boolean `b`,
  `(let $x b (if $x 1 2))` gives the branch of `b` on every run of the variant machine and on PeTTa.
  HE's `metta-repl` answers `[1]` for `True` and `[2]` for `False`.
* `Controls.let_number_false` (positive, the other branch): `(let $x False (if $x 1 2))` gives `[2]`.
* `Controls.let_number_not_two` (negative): `(let $x True (if $x 1 2))` does not go on to `[2]`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace LetVariant

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
open Mettapedia.Languages.MeTTa.PeTTa
open ServiceFootprints EntryToQuery AnswerBags EveryRun ScopedTransfer SyntacticMerge VariantRuns
open LetPlain (Plain PlainEnv letArrow unifyArrow)
open LetSource (letCall unifyBody inst LetProgram LetCall WorkFrame)

variable {dispatch : GroundedDispatch} {policy : Policy} {target : List Atom}

/-- **The instance contract on the variant machine**: the facts of a body, answerable answers, and
every run of the variant machine from the instance going on with its answers, at every frame and
under every continuation good on them. -/
structure InstanceGood (dispatch : GroundedDispatch) (policy : Policy) (target : List Atom)
    (atoms : List Atom) (t : Atom) (L : List Atom) : Prop where
  facts : BodyFacts t
  clean : ∀ a ∈ L, Answerable a
  good : GoodRuns dispatch Completed.scopedLookup policy target atoms (Entry.Value.ofAtom t) L

/-! ## Casts -/

/-- **Every run of a data atom's cast under a demand keeping the bindings goes on**, at a frame with
the same bindings and a plain environment when the frame's is. -/
theorem goodv_cast_keeps {space : Space} {live : List Atom} {scope : List String}
    {stack : List Continuation} {emitted : List Result} {a E T : Atom} (data : DataAtom a)
    (entry : Entry.Rel policy.reentry .active a E .cast) (stored : StorageTypesRel space a [T])
    (closedT : TypeSubst.typeVars T = []) (matchesSelf : ∀ b : Bindings, TypeMatchRel E T b b)
    (keeps : ∀ {b out : Bindings}, TypeMatchRel E T b out → out = b) {frame : Frame}
    (next : ∀ after : Frame, after.bindings = frame.bindings →
      (PlainEnv frame.environment → PlainEnv after.environment) →
      GoodV dispatch Completed.scopedLookup policy target
        ⟨space, .returning [(Entry.Value.ofAtom a, after)], stack, emitted⟩) :
    GoodV dispatch Completed.scopedLookup policy target
      ⟨space, .work (.atom live scope (Entry.Value.ofAtom a) E frame), stack, emitted⟩ := by
  have accepts : ∀ frame : Frame, ∃ output, policy.matching.Rel E T frame.bindings output :=
    fun frame => ⟨_, Completed.Frame.preserved_type_match policy frame (matchesSelf _)⟩
  have entry' : Entry.Rel policy.reentry (frame.read policy (Entry.Value.ofAtom a)).status
      (frame.read policy (Entry.Value.ofAtom a)).erase E .cast := by
    simp only [CompleteRun.read_data policy frame data, Entry.Value.erase_ofAtom, data.status]
    exact entry
  refine goodv_of_model ⟨_, ScopedIf.renewed_cast_step_any dispatch policy
    (answerable_of_data data).closed entry (ScopedIf.scoped_closed_answers stored closedT)
    (.unchanged (Completed.Frame.preserved_type_match policy frame (matchesSelf _))) stack
    emitted⟩ ?_
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

/-! ## The call of `unify` -/

/-- **Every run of the call of `unify` on read arguments goes on with the instance's answers**: the
call is embedded, the invocation is embedded, the success rule fires, and the then-branch, the plain
value of the instance, runs at the frame the rule returns. -/
theorem unify_call_good (notUnify : ¬ dispatch.executable (.symbol "unify")) {atoms : List Atom}
    {x : String} {d b : Atom} {L : List Atom} (onlyX : ∀ y ∈ TypeSubst.typeVars b, y = x)
    (instance' : InstanceGood dispatch policy target atoms (inst x d b) L)
    {live : List Atom} {scope : List String} {F : Frame} (plainF : PlainEnv F.environment)
    {cA cP cT cE : Entry.Value} (plainA : Plain cA) (plainP : Plain cP) (plainT : Plain cT)
    (sees : ∀ v, TypeBindingSatisfied v F.bindings →
      applyTypeValuation v cA.erase = d ∧ applyTypeValuation v cP.erase = v x ∧
        applyTypeValuation v cT.erase = applyTypeValuation v b)
    (solvable : ∃ v, TypeBindingSatisfied v F.bindings ∧ v x = d)
    (stack : List Continuation) (emitted : List Result)
    (cont : ∀ R : List Result, R.map (fun r => r.1.erase) = L →
      GoodV dispatch Completed.scopedLookup policy target
        ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    GoodV dispatch Completed.scopedLookup policy target ⟨Space.ofList atoms,
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
  have minimalGood : GoodV dispatch Completed.scopedLookup policy target ⟨Space.ofList atoms,
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
    refine goodv_of_model ⟨_, .internal (.minimalUnifyYes (output := ⟨out0, environment, certified⟩)
      candidate0 unified0)⟩ ?_
    intro z moved
    rcases LetFine.unify_steps_env moved with ⟨out, candidate, unified, rfl⟩ | ⟨noMatch, _⟩
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
      apply goodv_boundaryBatch_frame
      apply goodv_boundaryBatch_cons
      apply goodv_boundary_returned
      refine goodv_returned_evaluate ?_ ?_ ?_
      · rw [Entry.Value.erase_ofAtom]
        exact instance'.facts.notRefused
      · rw [Entry.Value.erase_ofAtom]
        exact instance'.facts.notStopped
      refine instance'.good _ _ out _ _ ?_
      intro R eraseR
      apply goodv_append
      apply goodv_boundaryBatch_nil
      apply goodv_prepend
      apply cont
      simpa using eraseR
    · exact absurd candidate0 (noMatch out0)
  refine goodv_of_model ⟨_, .internal (.callEmbedded notError notHost embedded)⟩ ?_
  intro z moved
  cases moved with
  | internal l =>
      cases l with
      | callError failed => exact absurd failed notError
      | callAbsent _ nonGrounded _ => exact absurd nonGrounded grounded
      | callEquations _ nonGrounded _ _ => exact absurd nonGrounded grounded
      | callEmbedded _ _ _ =>
          refine goodv_of_model ⟨_, .internal (.invocationEmbedded notHost embedded)⟩ ?_
          intro z' moved'
          cases moved' with
          | internal l' =>
              cases l' with
              | invocationAbsent nonGrounded _ => exact absurd nonGrounded grounded
              | invocationEquations nonGrounded _ _ => exact absurd nonGrounded grounded
              | invocationEmbedded _ _ => exact minimalGood

/-! ## The body of `let`'s row at the work's frame -/

/-- **Every run of the body of `let`'s work, `(unify $a $p $t Empty)` read at the work's frame, goes
on with the instance's answers.** -/
theorem unify_atom_good (notUnify : ¬ dispatch.executable (.symbol "unify")) {atoms : List Atom}
    (program : LetProgram atoms) {x : String} {d b : Atom} (call : LetCall atoms x d b)
    {L : List Atom} (instance' : InstanceGood dispatch policy target atoms (inst x d b) L)
    {a p t : String} {G : Frame} (work : WorkFrame G x d b a p t)
    {live : List Atom} {scope : List String} (stack : List Continuation) (emitted : List Result)
    (cont : ∀ R : List Result, R.map (fun r => r.1.erase) = L →
      GoodV dispatch Completed.scopedLookup policy target
        ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    GoodV dispatch Completed.scopedLookup policy target ⟨Space.ofList atoms,
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
  refine goodv_of_model ⟨_, .internal (LocalStepWith.atomFunction (admission := .historical) entry
    shape selectionExists)⟩ ?_
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
          apply goodv_invocations_cons
          rw [LetPlain.returnType_undefined projections.2]
          refine goodv_functionStart (by simp [projections.1]) ?_
          rw [projections.1, functionType]
          simp only [List.zip_cons_cons, List.zip_nil_right]
          refine goodv_cast_keeps LetSource.unify_data
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
          apply goodv_functionHeads_frame
          refine goodv_functionBranches_continue ?_ ?_
          · simpa using LetSource.unify_data.not_stopped
          apply goodv_argumentsCons
          apply goodv_atom_demand
          apply goodv_arguments_frame
          refine goodv_argumentBranches_continue (fun stopped => notStoppedA stopped.1) ?_
          apply goodv_argumentsCons
          apply goodv_atom_demand
          apply goodv_arguments_frame
          refine goodv_argumentBranches_continue (fun stopped => notStoppedP stopped.1) ?_
          apply goodv_argumentsCons
          apply goodv_atom_demand
          apply goodv_arguments_frame
          refine goodv_argumentBranches_continue (fun stopped => notStoppedT stopped.1) ?_
          apply goodv_argumentsCons
          apply goodv_atom_demand
          apply goodv_arguments_frame
          refine goodv_argumentBranches_continue
            (fun stopped => stopped.2 (by simp [LetSource.read_symbol])) ?_
          apply goodv_argumentsNil
          apply goodv_argumentTail
          apply goodv_append
          apply goodv_argumentBranches_nil
          apply goodv_prepend
          apply goodv_argumentTail
          apply goodv_append
          apply goodv_argumentBranches_nil
          apply goodv_prepend
          apply goodv_argumentTail
          apply goodv_append
          apply goodv_argumentBranches_nil
          apply goodv_prepend
          apply goodv_argumentTail
          apply goodv_append
          apply goodv_argumentBranches_nil
          apply goodv_prepend
          apply goodv_functionAssemble
          apply goodv_append
          apply goodv_functionBranches_nil
          apply goodv_prepend
          simp only [List.map_cons, List.map_nil, List.append_nil, Completed.argumentPrepend_packet,
            Completed.functionAssemble, Entry.Value.unpackArguments_packet]
          apply goodv_calls_frame
          apply goodv_calls_cons
          simp only [Entry.Value.ofAtom, LetSource.read_symbol]
          refine unify_call_good notUnify call.onlyX instance' plainU
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
          apply goodv_append
          apply goodv_calls_nil
          apply goodv_prepend
          apply goodv_append
          apply goodv_invocations_nil
          apply goodv_prepend
          refine goodv_publish (fun r member => ?_) ?_
          · have inQ : r.1.erase ∈ L := by
              rw [← eraseQ]
              exact List.mem_map.mpr ⟨r, by simpa using member, rfl⟩
            exact instance'.clean _ inQ
          apply cont
          rw [NestedEveryRun.publish_erase]
          simpa using eraseQ

/-! ## The query of `let`'s row -/

/-- **Every run of the query of `(let $x d b)` at a frame with empty bindings and a plain
environment goes on with the instance's answers.** Every frontier of the model is handled, so the
variant's is. -/
theorem let_query_good (notLet : ¬ dispatch.executable (.symbol "let"))
    (notUnify : ¬ dispatch.executable (.symbol "unify")) {atoms : List Atom}
    (program : LetProgram atoms) {x : String} {d b : Atom} (call : LetCall atoms x d b)
    {L : List Atom} (instance' : InstanceGood dispatch policy target atoms (inst x d b) L)
    {live : List Atom} {scope : List String} {F : Frame} (emptyF : F.bindings = Bindings.empty)
    (plainF : PlainEnv F.environment) (stack : List Continuation) (emitted : List Result)
    (cont : ∀ R : List Result, R.map (fun r => r.1.erase) = L →
      GoodV dispatch Completed.scopedLookup policy target
        ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    GoodV dispatch Completed.scopedLookup policy target ⟨Space.ofList atoms,
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
      GoodV dispatch Completed.scopedLookup policy target
        ⟨Space.ofList (LetFrontier.letRows ++ rest),
          .work (.equations live scope (Entry.Value.ofAtom (letCall x d b)) Atom.undefinedType F
            works), stack, emitted⟩ := by
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
    refine goodv_of_model ⟨_, .internal (.equationsCons (output := ⟨w.bindings, after, certificate⟩)
      rfl unified)⟩ ?_
    intro z step
    cases step with
    | internal l =>
        cases l with
        | equationsCons sameBindings unified' =>
            have work := LetSource.let_work_frame call emptyF plainF hxp hxa hxt hpa hpt hat
              solutions sameBindings unified'
            rw [bodyEq]
            refine goodv_boundary_producer ?_ ?_
            · rintro ⟨⟨inner, same⟩, _⟩
              rw [LetSource.unify_body_erase] at same
              simp at same
            apply goodv_boundaryBatch_frame
            apply goodv_boundaryBatch_cons
            apply goodv_boundary_returned
            refine goodv_returned_evaluate ?_ ?_ ?_
            · rw [LetSource.unify_body_erase]
              simp [Atom.notReducible]
            · rw [LetSource.unify_body_erase]
              rintro (same | ⟨tail, same⟩)
              · simp [Atom.empty] at same
              · simp at same
            refine unify_atom_good notUnify program call instance' work _ _ ?_
            intro R eraseR
            apply goodv_append
            apply goodv_boundaryBatch_nil
            apply goodv_prepend
            apply goodv_append
            apply goodv_equations_nil
            apply goodv_prepend
            apply cont
            simpa using eraseR
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList (LetFrontier.letRows ++ rest))
    (Atom.undefinedType :: live) (letCall x d b) F.bindings
  obtain ⟨w, _, rfl, _⟩ := LetSource.let_frontier_fresh foreign satisfiable frontier
  have frontier' : EquationFrontierRel (Space.ofList (LetFrontier.letRows ++ rest))
      (Atom.undefinedType :: live) (Entry.Value.ofAtom (letCall x d b)).erase F.bindings [w] := by
    rw [Entry.Value.erase_ofAtom]
    exact frontier
  refine goodv_of_model ⟨_, .internal (.callEquations notError nonGrounded frontier'
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

/-- **Every run of the variant machine on `(let $x d b)` at a frame with empty bindings and a plain
environment (HE's entry is one) goes on with the instance's answers**, under every continuation good
on them. -/
theorem let_good (notLet : ¬ dispatch.executable (.symbol "let"))
    (notUnify : ¬ dispatch.executable (.symbol "unify")) {atoms : List Atom}
    (program : LetProgram atoms) {x : String} {d b : Atom} (call : LetCall atoms x d b)
    {L : List Atom} (instance' : InstanceGood dispatch policy target atoms (inst x d b) L)
    {live : List Atom} {scope : List String} {F : Frame} (emptyF : F.bindings = Bindings.empty)
    (plainF : PlainEnv F.environment) (stack : List Continuation) (emitted : List Result)
    (cont : ∀ R : List Result, R.map (fun r => r.1.erase) = L →
      GoodV dispatch Completed.scopedLookup policy target
        ⟨Space.ofList atoms, .returning R, stack, emitted⟩) :
    GoodV dispatch Completed.scopedLookup policy target ⟨Space.ofList atoms,
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
  refine goodv_of_model ⟨_, .internal (LocalStepWith.atomFunction (admission := .historical) entry
    shape selectionExists)⟩ ?_
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
          apply goodv_invocations_cons
          rw [LetPlain.returnType_undefined projections.2]
          refine goodv_functionStart (by simp [projections.1]) ?_
          rw [projections.1, functionType]
          simp only [List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_right]
          refine goodv_cast_keeps LetSource.let_data
            (LetSource.arrow_cast_entry (by decide) (by decide) ⟨_, rfl⟩) program.letTypes
            LetPlain.Controls.letArrow_closed LetPlain.letArrow_matches LetSource.letArrow_keeps ?_
          intro frF frFBindings frFPlain
          have emptyFF : frF.bindings = Bindings.empty := by rw [frFBindings, afterBindings, emptyF]
          have plainFF : PlainEnv frF.environment := frFPlain (afterPlain plainF)
          apply goodv_functionHeads_frame
          refine goodv_functionBranches_continue ?_ ?_
          · simpa using LetSource.let_data.not_stopped
          apply goodv_argumentsCons
          apply goodv_atom_demand
          rw [LetSource.read_ofAtom_of_empty policy frF emptyFF plainFF]
          apply goodv_arguments_frame
          refine goodv_argumentBranches_continue (fun stopped => ?_) ?_
          · have stoppedX := stopped.1
            simp only [Entry.Value.erase_ofAtom] at stoppedX
            exact LetSource.var_not_stopped x stoppedX
          apply goodv_argumentsCons
          refine goodv_cast_keeps call.data (call.data.entry _) typesD closedD
            (fun b' => .undefinedLeft _ b') (fun matched => matched.undefined_output) ?_
          intro frD frDBindings frDPlain
          have emptyFD : frD.bindings = Bindings.empty := by rw [frDBindings, emptyFF]
          have plainFD : PlainEnv frD.environment := frDPlain plainFF
          apply goodv_arguments_frame
          refine goodv_argumentBranches_continue (fun stopped => ?_) ?_
          · have stoppedD := stopped.1
            simp only [Entry.Value.erase_ofAtom] at stoppedD
            exact call.data.not_stopped stoppedD
          apply goodv_argumentsCons
          apply goodv_atom_demand
          rw [LetSource.read_ofAtom_of_empty policy frD emptyFD plainFD]
          apply goodv_arguments_frame
          refine goodv_argumentBranches_continue (fun stopped => ?_) ?_
          · have stoppedB := stopped.1
            simp only [Entry.Value.erase_ofAtom] at stoppedB
            exact notStoppedB stoppedB
          apply goodv_argumentsNil
          apply goodv_argumentTail
          apply goodv_append
          apply goodv_argumentBranches_nil
          apply goodv_prepend
          apply goodv_argumentTail
          apply goodv_append
          apply goodv_argumentBranches_nil
          apply goodv_prepend
          apply goodv_argumentTail
          apply goodv_append
          apply goodv_argumentBranches_nil
          apply goodv_prepend
          apply goodv_functionAssemble
          apply goodv_append
          apply goodv_functionBranches_nil
          apply goodv_prepend
          simp only [List.map_cons, List.map_nil, List.append_nil, Completed.argumentPrepend_packet,
            Completed.functionAssemble, Entry.Value.unpackArguments_packet]
          apply goodv_calls_frame
          apply goodv_calls_cons
          have valueEq : (Entry.Value.expression .active
              [Entry.Value.ofAtom (.symbol "let"), Entry.Value.ofAtom (.var x), Entry.Value.ofAtom d,
                Entry.Value.ofAtom b]) = Entry.Value.ofAtom (letCall x d b) := by
            simp [letCall, Entry.Value.ofAtom]
          simp only [valueEq]
          refine let_query_good notLet notUnify program call instance' emptyFD plainFD _ _ ?_
          intro Q eraseQ
          apply goodv_append
          apply goodv_calls_nil
          apply goodv_prepend
          apply goodv_append
          apply goodv_invocations_nil
          apply goodv_prepend
          refine goodv_publish (fun r member => ?_) ?_
          · have inQ : r.1.erase ∈ L := by
              rw [← eraseQ]
              exact List.mem_map.mpr ⟨r, by simpa using member, rfl⟩
            exact instance'.clean _ inQ
          apply cont
          rw [NestedEveryRun.publish_erase]
          simpa using eraseQ

/-- **At HE's entry**: every run of the variant machine on `(let $x d b)` finishes with the
instance's answers. -/
theorem let_entry_good (notLet : ¬ dispatch.executable (.symbol "let"))
    (notUnify : ¬ dispatch.executable (.symbol "unify")) {atoms : List Atom}
    (program : LetProgram atoms) {x : String} {d b : Atom} (call : LetCall atoms x d b)
    {L : List Atom} (instance' : InstanceGood dispatch policy L atoms (inst x d b) L) :
    GoodV dispatch Completed.scopedLookup policy L
      (load (Space.ofList atoms) (letCall x d b) Atom.undefinedType) :=
  let_good notLet notUnify program call instance' rfl LetPlain.plainEnv_nil [] []
    (fun R eraseR => goodv_top R [] (by rw [List.nil_append]; exact eraseR))

/-! ## Instances with declared branches -/

/-- A tree with declared `if` meets the instance contract on the variant machine. -/
theorem instance_good_of_settles (notHost : ¬ dispatch.executable (.symbol "if"))
    {atoms : List Atom} (ifProgram : IfBranches.IfProgram atoms) {t : Atom} {L : List Atom}
    (settles : DeclaredTrees.SettlesDeclared dispatch atoms t L) :
    InstanceGood dispatch policy target atoms t L :=
  ⟨(DeclaredTrees.settlesDeclared_shape settles).2, (DeclaredTrees.settlesDeclared_shape settles).1,
    DeclaredTrees.settlesDeclared_good notHost ifProgram settles⟩

/-- **`let` over trees with declared `if`, on every run of the variant machine**: for a data value
`d` with one closed stored type and a template `b` whose only variable is `x` and whose instance
`b[x := d]` is a tree with declared `if`, on a program carrying `let` and `if`: a complete run of
`(let $x d b)` exists, every complete run publishes the instance's answers, no run is infinite and
none is stuck. -/
theorem let_declared_every_run (notHost : ¬ dispatch.executable (.symbol "if"))
    (notLet : ¬ dispatch.executable (.symbol "let"))
    (notUnify : ¬ dispatch.executable (.symbol "unify")) (policy : Policy) {atoms : List Atom}
    (letProgram : LetProgram atoms) (ifProgram : IfBranches.IfProgram atoms) {x : String}
    {d b : Atom} (call : LetCall atoms x d b) {L : List Atom}
    (settles : DeclaredTrees.SettlesDeclared dispatch atoms (inst x d b) L) :
    EveryRunV dispatch Completed.scopedLookup policy (Space.ofList atoms) (letCall x d b) L :=
  (let_entry_good notLet notUnify letProgram call
    (instance_good_of_settles notHost ifProgram settles)).every_run

/-- **`(let $x b (if $x y n))` with a declared or undeclared data taken branch, in both dialects**,
for every name `x` and every Boolean literal `b`: every run of the variant machine finishes with the
branch of `b`, and PeTTa's streaming run yields the same from some fuel on. -/
theorem let_if_declared_agree (notHost : ¬ dispatch.executable (.symbol "if"))
    (notLet : ¬ dispatch.executable (.symbol "let"))
    (notUnify : ¬ dispatch.executable (.symbol "unify")) (policy : Policy) {atoms : List Atom}
    (letProgram : LetProgram atoms) (ifProgram : IfBranches.IfProgram atoms) (x : String)
    {b : Bool} {y n : Atom} (dataY : DataAtom y) (dataN : DataAtom n)
    (settles : DeclaredTrees.SettlesDeclared dispatch atoms (IfBranches.callOf b y n)
      [IfBranches.pick b y n]) :
    EveryRunV dispatch Completed.scopedLookup policy (Space.ofList atoms)
        (letCall x (.grounded (.bool b)) (IfComputed.callC (.var x) y n))
        [IfBranches.pick b y n] ∧
      ∃ N : Nat, ∀ n', N ≤ n' → Streaming.values (Streaming.advance (translate atoms) n'
        (Streaming.enter { state := store atoms }
          (letCall x (.grounded (.bool b)) (IfComputed.callC (.var x) y n)))) =
        [IfBranches.pick b y n] := by
  have call : LetCall atoms x (.grounded (.bool b)) (IfComputed.callC (.var x) y n) := by
    refine ⟨.grounded _, ⟨_, IfBranches.bool_types_in _ b, rfl⟩, fun z member => ?_, ⟨_, _, rfl⟩⟩
    have closedY := HERuns.ground_typeVars (answerable_of_data dataY)
    have closedN := HERuns.ground_typeVars (answerable_of_data dataN)
    simpa [IfComputed.callC, AnswerBags.Controls.app, TypeSubst.typeVars, TypeSubst.typeVarsList,
      closedY, closedN] using member
  have settles' : DeclaredTrees.SettlesDeclared dispatch atoms
      (inst x (.grounded (.bool b)) (IfComputed.callC (.var x) y n)) [IfBranches.pick b y n] := by
    rw [LetPeTTaTemplates.inst_if x _ dataY dataN]
    exact settles
  exact ⟨let_declared_every_run notHost notLet notUnify policy letProgram ifProgram call settles',
    LetPeTTaTemplates.petta_let_if atoms x b dataY dataN⟩

/-! ## Controls -/

namespace Controls

open WholeRunWords.Double (noHost)
open AnswerBags.Controls (sym app)
open LetEveryRun.Controls (letIfRows let_program if_program_let)
open IfBranches (callOf pick)

abbrev one : Atom := .grounded (.int 1)
abbrev two : Atom := .grounded (.int 2)

/-- The branches of `(if b 1 2)` on HE's `let` and `if` programs: both are `Number`. -/
theorem number_branches (b : Bool) :
    DeclaredBranchVariant.DeclaredBranches letIfRows b one two (sym "Number") where
  dataYes := .grounded _
  dataNo := .grounded _
  takenNotRefused := by cases b <;> simp [pick, Atom.notReducible]
  takenType := by
    cases b
    · exact .groundedKnown (.int 2) (by simp [Atom.undefinedType])
    · exact .groundedKnown (.int 1) (by simp [Atom.undefinedType])
  notUndefined := by decide
  notAtom := by decide
  notVariable := rfl
  closedType := rfl
  typedYes := ⟨_, .groundedKnown (.int 1) (by simp [Atom.undefinedType]), rfl⟩
  typedNo := ⟨_, .groundedKnown (.int 2) (by simp [Atom.undefinedType]), rfl⟩
  region := by cases b <;> decide +kernel
  sides := by cases b <;> decide +kernel

/-- **Positive control, both dialects, `let` binding the condition of an `if` with declared
branches**: for each Boolean `b`, `(let $x b (if $x 1 2))` gives the branch of `b` on every run of
the variant machine and on PeTTa. HE's `metta-repl` answers `[1]` for `True` and `[2]` for
`False`. -/
theorem let_number_agree (policy : Policy) (b : Bool) :
    EveryRunV noHost Completed.scopedLookup policy (Space.ofList letIfRows)
        (letCall "x" (.grounded (.bool b)) (IfComputed.callC (.var "x") one two))
        [pick b one two] ∧
      ∃ N : Nat, ∀ n', N ≤ n' → Streaming.values (Streaming.advance (translate letIfRows) n'
        (Streaming.enter { state := store letIfRows }
          (letCall "x" (.grounded (.bool b)) (IfComputed.callC (.var "x") one two)))) =
        [pick b one two] :=
  let_if_declared_agree (fun impossible => impossible) (fun impossible => impossible)
    (fun impossible => impossible) policy let_program if_program_let "x" (.grounded _)
    (.grounded _) (.declaredIf (number_branches b))

/-- **Positive control, the other branch**: `(let $x False (if $x 1 2))` gives `[2]` on every run of
the variant machine. -/
theorem let_number_false (policy : Policy) :
    EveryRunV noHost Completed.scopedLookup policy (Space.ofList letIfRows)
      (letCall "x" (.grounded (.bool false)) (IfComputed.callC (.var "x") one two)) [two] :=
  (let_number_agree policy false).1

/-- **Negative control**: `(let $x True (if $x 1 2))` does not go on to `[2]`. -/
theorem let_number_not_two (policy : Policy) :
    ¬ GoodV noHost Completed.scopedLookup policy [two]
      (load (Space.ofList letIfRows)
        (letCall "x" (.grounded (.bool true)) (IfComputed.callC (.var "x") one two))
        Atom.undefinedType) := by
  intro wrong
  obtain ⟨⟨answers, run⟩, _⟩ := (let_number_agree policy true).1
  have published := wrong.every_run.2.1 answers run
  have actual := (let_number_agree policy true).1.2.1 answers run
  rw [actual] at published
  simp [pick] at published

end Controls

#print axioms goodv_cast_keeps
#print axioms unify_call_good
#print axioms unify_atom_good
#print axioms let_query_good
#print axioms let_good
#print axioms let_entry_good
#print axioms let_declared_every_run
#print axioms let_if_declared_agree
#print axioms Controls.number_branches
#print axioms Controls.let_number_agree
#print axioms Controls.let_number_false
#print axioms Controls.let_number_not_two

end LetVariant

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
