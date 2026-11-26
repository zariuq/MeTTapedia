import Mettapedia.Languages.MeTTa.SpaceTheory.AtomEquations
import Mettapedia.Languages.MeTTa.SpaceTheory.HEExecution
import Mettapedia.Languages.MeTTa.SpaceTheory.HEControlOnTransform

/-!
# An explicit equation view of HE's ready-call frontier

The observation is taken after HE's argument and type-demand phases.
It uses HE's own non-grounded-call judgment and complete equation
frontier. The selected representative is retained with the ordered
work: HE's continuation will unify each fresh pattern with that
representative. Neither an expected type nor a capture is quotiented.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HEEquationEntry

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed
  (ArgumentService CastLookup Frame Policy Result WorldEnvironment WorldServices)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationFrontierRel EquationWork)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Continuation WorldConfiguration)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (WorldStepWith)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic (SState)
open HENativeOnTransform (Presentation)
open Mettapedia.GSLT

def select (space : Space) (dispatch : GroundedDispatch) (expected : Atom)
    (live : List Atom) (activation : Frame) (call : Atom) (selected : List EquationWork) : Prop :=
  ¬ IsErrorRel call ∧ NonGroundedCallRel dispatch call ∧
    EquationFrontierRel space (expected :: live) call activation.bindings selected ∧ selected ≠ []

theorem ordinary_entry_exact (space : Space) (dispatch : GroundedDispatch)
    (lookup : CastLookup) (policy : Policy) (expected : Atom) (live : List Atom)
    (activation : Frame) (scope : List String) (value : Entry.Value) (chosen : List EquationWork)
    (stack : List Continuation) (emitted : List Result) :
    select space dispatch expected live activation value.erase chosen ↔
      (HEExecution.theoryAt space dispatch lookup policy).Step
        ⟨.work (.call live scope value expected activation), stack, emitted⟩
        ⟨.work (.equations live scope value expected activation chosen), stack, emitted⟩ := by
  constructor
  · rintro ⟨noError, nongrounded, found, nonempty⟩
    exact HEExecution.Rewrites.evaluate (.callEquations noError nongrounded found nonempty)
  · intro fired
    change HEExecution.Rewrites _ _ _ _ _ _ at fired
    cases fired with
    | evaluate one =>
      cases one with
      | callEquations noError nongrounded found nonempty =>
        exact ⟨noError, nongrounded, found, nonempty⟩

def theory (space : Space) (dispatch : GroundedDispatch) (expected : Atom)
    (live : List Atom) (activation : Frame) : GSLT :=
  EndpointSaturation.inputTheory (AtomEquations.setoid space.atoms)
    (fun call (readout : Atom × List EquationWork) =>
      call = readout.1 ∧ select space dispatch expected live activation call readout.2)

theorem entry_exact (space : Space) (dispatch : GroundedDispatch) (expected : Atom)
    (live : List Atom) (activation : Frame) (query representative : Atom)
    (chosen : List EquationWork) :
    (theory space dispatch expected live activation).Step (.inl query) (.inr (representative, chosen)) ↔
      AtomEquations.Equivalent space.atoms query representative ∧
        select space dispatch expected live activation representative chosen := by
  change (EndpointSaturation.inputTheory (AtomEquations.setoid space.atoms)
    (fun call (readout : Atom × List EquationWork) =>
      call = readout.1 ∧ select space dispatch expected live activation call readout.2)).Step
      (.inl query) (.inr (representative, chosen)) ↔ _
  rw [EndpointSaturation.input_step_iff]
  constructor
  · rintro ⟨rep, equal, same, selected⟩
    change rep = representative at same
    subst rep
    exact ⟨equal, selected⟩
  · rintro ⟨eq, selected⟩
    exact ⟨representative, eq, rfl, selected⟩

/-- In the explicit view every chosen frontier is an actual ordinary
frontier step at its representative, not just an equivalent list of
results. The selected representative and work remain fixed thereafter. -/
theorem equation_entry_is_a_source_frontier (space : Space) (dispatch : GroundedDispatch)
    (lookup : CastLookup) (policy : Policy) (expected : Atom) (live : List Atom)
    (activation : Frame) (scope : List String) (query representative : Atom)
    (chosen : List EquationWork) (stack : List Continuation) (emitted : List Result) :
    (theory space dispatch expected live activation).Step (.inl query) (.inr (representative, chosen)) ↔
      AtomEquations.Equivalent space.atoms query representative ∧
      (HEExecution.theoryAt space dispatch lookup policy).Step
        ⟨.work (.call live scope (Entry.Value.ofAtom representative) expected activation), stack, emitted⟩
        ⟨.work (.equations live scope (Entry.Value.ofAtom representative) expected activation chosen),
          stack, emitted⟩ := by
  rw [entry_exact, ← ordinary_entry_exact, Entry.Value.erase_ofAtom]

/-- The same theorem at the live world: the current view of this context
supplies the equations, but the chosen work is a local observation. It
does not change the world, other contexts, or output already emitted. -/
theorem equation_entry_in_live_world {Context World : Type}
    (view : World → Context → Space) (services : WorldServices Context World)
    (admission : ArgumentService) (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy)
    (world : World) (ctx : Context) (expected : Atom) (live : List Atom)
    (activation : Frame) (scope : List String) (query representative : Atom)
    (chosen : List EquationWork) (stack : List Continuation) (emitted : List Result) :
    (theory (view world ctx) dispatch expected live activation).Step (.inl query) (.inr (representative, chosen)) ↔
      AtomEquations.Equivalent (view world ctx).atoms query representative ∧
      WorldStepWith admission view services dispatch lookup policy
        ⟨world, ctx, .work (.call live scope (Entry.Value.ofAtom representative) expected activation),
          stack, emitted⟩
        ⟨world, ctx, .work (.equations live scope (Entry.Value.ofAtom representative) expected activation chosen),
          stack, emitted⟩ := by
  rw [entry_exact]
  constructor
  · rintro ⟨equal, noError, nongrounded, frontier, nonempty⟩
    have selected :
        select (view world ctx) dispatch expected live activation
          (Entry.Value.ofAtom representative).erase chosen := by
      rw [Entry.Value.erase_ofAtom]
      exact ⟨noError, nongrounded, frontier, nonempty⟩
    obtain ⟨noError, nongrounded, frontier, nonempty⟩ := selected
    exact ⟨equal, .internal (.core (.work _) rfl (.callEquations noError nongrounded frontier nonempty) (.work _))⟩
  · rintro ⟨equal, entered⟩
    refine ⟨equal, ?_⟩
    cases entered with
    | internal step =>
      cases step with
      | core before _ advanced after =>
        cases before
        cases after
        cases advanced with
        | callEquations noError nongrounded frontier nonempty =>
          simpa only [select, Entry.Value.erase_ofAtom] using
            (show select (view world ctx) dispatch expected live activation
              (Entry.Value.ofAtom representative).erase chosen from
              ⟨noError, nongrounded, frontier, nonempty⟩)

/-- At a chosen representative, the explicitly equational entry has
exactly the ordinary ready-call firing and its captured frontier. The
equivalence premise still belongs to the source equation view; this
does not implement the search for representatives. -/
theorem representative_firing_iff {Context World O : Type} [DecidableEq O] [Infinite O]
    (code : Presentation Context World) (env : WorldEnvironment Context World) (policy : Policy)
    (world : World) (scope : Context) (expected : Atom) (live : List Atom)
    (activation : Frame) (names : List String) (query representative : Atom)
    (chosen : List EquationWork) (stack : List Continuation) (emitted : List Result) {initial : SState O}
    (shown : HEControlOnTransform.Shows code
      ⟨world, scope, .work (.call live names (Entry.Value.ofAtom representative) expected activation), stack, emitted⟩
      initial) :
    (theory (env.view world scope) env.dispatch expected live activation).Step
      (.inl query) (.inr (representative, chosen)) ↔
      AtomEquations.Equivalent (env.view world scope).atoms query representative ∧
      ∃ final, (HEControlOnTransform.theory O code env policy).Step initial final ∧
        HEControlOnTransform.Shows code
          ⟨world, scope, .work (.equations live names (Entry.Value.ofAtom representative) expected activation chosen),
            stack, emitted⟩ final := by
  rw [equation_entry_in_live_world env.view env.services env.arguments env.dispatch env.lookup policy
    world scope expected live activation names query representative chosen stack emitted]
  constructor
  · rintro ⟨identified, step⟩
    refine ⟨identified, HEControlOnTransform.realize_step env policy code shown ⟨?_, step⟩⟩
    exact HEControlOnTransform.covered_invocation
      (.invoke ⟨live, names, Entry.Value.ofAtom representative, activation⟩ (.typed expected))
      world scope stack [] emitted
  · rintro ⟨identified, final, fired, retained⟩
    obtain ⟨next, ⟨_, step⟩, reached⟩ := HEControlOnTransform.reflect_step env policy code shown fired
    have same := HEControlOnTransform.shows_unique code reached retained
    subst next
    exact ⟨identified, step⟩

theorem captured_frontier_is_final_for_entry (space : Space) (dispatch : GroundedDispatch)
    (expected : Atom) (live : List Atom) (activation : Frame) (representative : Atom) (chosen : List EquationWork) :
    (theory space dispatch expected live activation).IsNormalForm (.inr (representative, chosen)) :=
  EndpointSaturation.output_is_final (AtomEquations.setoid space.atoms) _ (representative, chosen)

theorem no_entry_in_empty_space (dispatch : GroundedDispatch) (expected : Atom)
    (live : List Atom) (activation : Frame) (query representative : Atom) (chosen : List EquationWork) :
    ¬ (theory Space.empty dispatch expected live activation).Step (.inl query) (.inr (representative, chosen)) := by
  rintro fired
  obtain ⟨_, _, _, found, nonempty⟩ :=
    (entry_exact _ _ _ _ _ _ _ _).mp fired
  cases found with
  | completed covered =>
    change List.Forall₂ _ [] _ at covered
    cases covered
    exact nonempty rfl

end Mettapedia.Languages.MeTTa.SpaceTheory.HEEquationEntry
