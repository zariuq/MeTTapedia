import Mettapedia.Languages.MeTTa.SpaceTheory.HEEquationalExecution
import Mettapedia.Languages.MeTTa.SpaceTheory.HENativeTransformExamples

/-! Actual firings enter an aliased call and resume its captured work.
Removing the alias, while leaving both definitions in place, prevents
new entry. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HEEquationalExamples

open Mettapedia.GSLT.IndexedOperational (ExecutionPath)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings BindingSourceAgreement)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Frame Policy)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.FrontierControls (rule work)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (semanticLoopFree_empty symbol_mismatch_not_match)
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation (LogicalMergeRel)
open Mettapedia.Languages.MeTTa.ContextualTransform.HEWorldControls (World environment)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines (exists_reads)
open Atoms (Content Preference)
open HEFocused (Focus)
open HENativeTransformExamples (code)
open HEEquationalExecution (Request State Shows MayEnter encode source theory)

private def raw : Atom := .symbol "alias"
private def representative : Atom := .symbol "a"
private def written : Atom := (Content.equation .rightward raw representative []).syntax
private def world : World := fun active => if active then [rule, written, rule] else []
private def changed : World := fun active => if active then [rule, rule] else [written]
private def input : HEInvocationEntry.Input := ⟨[], [], .symbol "alias", Frame.empty⟩
private def entry : Request Bool World := ⟨world, true, input, Atom.atomType, [], [], []⟩
private def later : Request Bool World := { entry with world := changed }
private def occurrences : List EquationWork := [work 0, work 2]

private theorem merge : LogicalMergeRel Bindings.empty Bindings.empty Bindings.empty := by
  refine ⟨BindingSourceAgreement.refl _, fun name => .var name, ?_⟩
  simp [Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.TypeBindingSatisfied, Bindings.empty]

private theorem hit (position : Nat) :
    EquationRowResultsRel [Atom.atomType] representative Bindings.empty position rule [work position] :=
  .hit _ _ _ _ _ _ _ (AlphaVariantRel.symbols _ _ _ _ _) (.symSym "a" semanticLoopFree_empty) merge

private theorem complete :
    EquationFrontierRel (environment.view world true) [Atom.atomType] representative Bindings.empty occurrences := by
  apply EquationFrontierRel.completed (blocks := [[work 0], [], [work 2]])
  exact .cons (hit 0) (.cons (.irrelevant 1 written (by
    intro l r equality
    have head := Atom.symbol.inj (List.cons.inj (Atom.expression.inj equality)).1
    exact (by decide : "=e>" ≠ "=") head))
    (.cons (hit 2) .nil))

private theorem eligible : MayEnter environment entry representative occurrences := by
  apply (HEEquationEntry.entry_exact _ _ _ _ _ _ _ _).mpr
  refine ⟨AtomEquations.authored ⟨.rightward, representative, [], ?_, List.mem_cons_self⟩,
    ?_, ?_, complete, by simp [occurrences]⟩
  · have snapshot : (environment.view entry.world entry.scope).atoms = [rule, written, rule] := rfl
    have spelling : entry.input.value.erase = raw := by simp [entry, input, Entry.Value.erase, raw]
    rw [snapshot, spelling]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · simp [IsErrorRel, representative]
  · simp [NonGroundedCallRel, Minimal.HostCall, Minimal.embeddedInstruction, representative]

private def held : State Bool World := .running (HEFocused.restore (entry.captured representative occurrences))

private def captured : HEInvocationEntry.Request :=
  .retained { input with value := Entry.Value.ofAtom representative } (some Atom.atomType) occurrences

private def activeBody : Focus Bool World :=
  ⟨world, true, .work (.boundary [Atom.atomType] [] (some representative) .producer (.symbol "result") Frame.empty),
    [.boundaryBatch [] [] none (.returned (Entry.Value.ofAtom representative) Atom.atomType),
      .append (HEInvocationEntry.Request.task (.retained { input with value := Entry.Value.ofAtom representative }
        (some Atom.atomType) [work 2]))], [], []⟩

private theorem enterBody :
    (source environment .unmarked).Step held (.running (HEFocused.restore activeBody)) := by
  apply HEEquationalExecution.Transition.ordinary
  apply HEFocused.restore_step
  apply (HEInvocationEntry.step_iff environment .unmarked captured world true [] [] [] activeBody).mpr
  refine ⟨.use (work 0) [work 2] Frame.empty, world, _, _, ?_, rfl, ?_⟩
  · refine ⟨rfl, rfl, rfl, .ordinary (.identical ?_)⟩
    simp [input, work, representative, Entry.Value.ofAtom, Entry.Value.substitute]
  · simp [activeBody, representative, input, work, Entry.Value.erase, Entry.Value.ofAtom]

/-- The input contains only the alias, the ready call parameters and
the world. It takes one entry firing and one ordinary firing to reach
the first body with the other equal occurrence still pending. -/
theorem alias_enters_body_without_supplied_representative :
    ∃ start final, Shows code (.pending entry) start ∧
      ∃ path : ExecutionPath (theory Nat code environment .unmarked) start final,
        Shows code (.running (HEFocused.restore activeBody)) final ∧ path.length = 2 := by
  obtain ⟨start, read⟩ := exists_reads {encode code (.pending entry)}
  let path : ExecutionPath (source environment .unmarked) (.pending entry) (.running (HEFocused.restore activeBody)) :=
    .cons ⟨.select eligible⟩ (.cons ⟨enterBody⟩ (.refl _))
  obtain ⟨final, fired, readBack, length⟩ := HEEquationalExecution.realize_path code environment .unmarked read path
  exact ⟨start, final, read, fired, readBack, length.trans rfl⟩

private theorem no_generator (first second : Atom) : ¬ AtomEquations.Generator [rule, rule] first second := by
  rintro ⟨preference, next, tail, member, _⟩
  cases preference <;> simp [Content.syntax, Preference.symbol, rule] at member

private theorem plain_miss (position : Nat) :
    EquationRowResultsRel [Atom.atomType] raw Bindings.empty position rule [] := by
  apply EquationRowResultsRel.miss position (.symbol "a") (.symbol "result") (.symbol "a") (.symbol "result")
    (AlphaVariantRel.symbols _ _ _ _ _)
  intro pattern body alpha considered output viable
  obtain ⟨_, _, renamed, _, _⟩ := alpha
  cases renamed
  exact symbol_mismatch_not_match (by decide) considered viable.1

private theorem unavailable (rep : Atom) (frontier : List EquationWork) :
    ¬ MayEnter environment later rep frontier := by
  intro admitted
  obtain ⟨identified, _, _, claimed, nonempty⟩ := (HEEquationEntry.entry_exact _ _ _ _ _ _ _ _).mp admitted
  have snapshot : (environment.view later.world later.scope).atoms = [rule, rule] := rfl
  have spelling : later.input.value.erase = raw := by simp [later, entry, input, Entry.Value.erase, raw]
  rw [snapshot, spelling] at identified
  have same : raw = rep :=
    (AtomEquations.without_generators [rule, rule] no_generator raw rep).mp identified
  subst rep
  have absent : EquationFrontierRel (environment.view changed true) [Atom.atomType] raw Bindings.empty [] := by
    apply EquationFrontierRel.completed (blocks := [[], []])
    exact .cons (plain_miss 0) (.cons (plain_miss 1) .nil)
  exact nonempty (claimed.empty_iff_no_candidate.mpr (absent.empty_iff_no_candidate.mp rfl))

/-- Leaving the spelling equation in another named space does not
authorize entry in the edited space. -/
theorem alias_in_other_space_cannot_authorize_entry {start final}
    (shown : Shows code (.pending later) start) :
    ¬ (theory Nat code environment .unmarked).Step start final := by
  intro firing
  obtain ⟨_, step, _⟩ := HEEquationalExecution.reflect_step code environment .unmarked shown firing
  cases step with
  | select selected => exact unavailable _ _ selected

end Mettapedia.Languages.MeTTa.SpaceTheory.HEEquationalExamples
