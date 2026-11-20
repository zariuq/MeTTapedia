import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.TraversalProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.SearchReadback
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.PlugReadback

/-!
# Context traversal terminates whenever its actual boundary does

These transfers use the literal size decreases proved for the actual
traversal clauses. Typed representation is retained to identify the boundary's
native term and scope; no global choice of representation is made.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ContextProgress

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing
open ContextStack
open ValueWorkerRank (weight)

abbrev Terminates {dev : Definitions.Development} (built : Compiled dev) (current : MClosed) : Prop :=
  Acc (fun after before => ProgramBinders.Rewrites built.rules.get before after) current

theorem search {dev : Definitions.Development} (built : Compiled dev) {outer : Nat}
    (whole : Tower.Tm outer) (continuation : MClosed)
    (boundary : ∀ current, SearchReadback.Rooted whole continuation current → Terminates built current)
    {current : MClosed} (represented : SearchReadback.Seeking whole continuation current) :
    Terminates built current := by
  have bySize : ∀ bound, ∀ {inner : Nat} (focus : Tower.Tm inner) (stack : Stack outer inner),
      weight (encodeTm focus) = bound → plug stack focus = whole →
      Terminates built (seekC (encodeTm focus) (code stack) continuation) := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
        intro inner focus stack sized restored
        refine .intro _ ?_
        intro next moved
        have classified := MainReadback.seek_step built _ _ _ _ moved
        have preserved := SearchReadback.cases_preserve ⟨inner, focus, stack, rfl, restored⟩ classified
        rcases TraversalProgress.seek_choice _ _ _ _ classified with smaller | terminal
        · obtain ⟨child, rest, rfl, less⟩ := smaller
          rcases preserved with seeking | rooted
          · obtain ⟨newInner, newFocus, newStack, same, reconstructed⟩ := seeking
            have fields := (SearchReadback.seek_eq _ _ _ _ _ _).mp same
            rw [fields.1, sized] at less
            rw [same]
            exact ih _ less newFocus newStack rfl reconstructed
          · obtain ⟨_, _, _, impossible, _⟩ := rooted
            simp [seekC, rootC, activeC, DataEmbedding.nodeC_eq_iff] at impossible
        · subst next
          exact boundary _ ⟨inner, focus, stack, rfl, restored⟩
  obtain ⟨inner, focus, stack, rfl, restored⟩ := represented
  exact bySize _ focus stack rfl restored

theorem reconstruct {dev : Definitions.Development} (built : Compiled dev) {outer : Nat}
    (whole : Tower.Tm outer) (continuation : MClosed)
    (boundary : Terminates built (resumeC (encodeTm whole) continuation))
    {current : MClosed} (represented : PlugReadback.Plugging whole continuation current) :
    Terminates built current := by
  have bySize : ∀ bound, ∀ {inner : Nat} (focus : Tower.Tm inner) (stack : Stack outer inner),
      weight (code stack) = bound → plug stack focus = whole →
      Terminates built (plugC (encodeTm focus) (code stack) continuation) := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
        intro inner focus stack sized restored
        refine .intro _ ?_
        intro next moved
        have classified := MainReadback.plug_step built _ _ _ _ moved
        have preserved := PlugReadback.cases_preserve ⟨inner, focus, stack, rfl, restored⟩ classified
        rcases TraversalProgress.plug_choice _ _ _ _ classified with smaller | terminal
        · obtain ⟨child, rest, rfl, less⟩ := smaller
          rcases preserved with plugging | returned
          · obtain ⟨newInner, newFocus, newStack, same, reconstructed⟩ := plugging
            have fields := (PlugReadback.plug_eq _ _ _ _ _ _).mp same
            rw [fields.2.1, sized] at less
            rw [same]
            exact ih _ less newFocus newStack rfl reconstructed
          · change plugC child rest continuation = resumeC (encodeTm whole) continuation at returned
            simp [plugC, resumeC, activeC, DataEmbedding.nodeC_eq_iff] at returned
        · subst next
          rcases preserved with plugging | returned
          · obtain ⟨_, _, _, impossible, _⟩ := plugging
            simp [plugC, resumeC, activeC, DataEmbedding.nodeC_eq_iff] at impossible
          · exact returned.symm ▸ boundary
  obtain ⟨inner, focus, stack, rfl, restored⟩ := represented
  exact bySize _ focus stack rfl restored

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ContextProgress
