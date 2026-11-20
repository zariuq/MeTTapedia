import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.HelperIsolation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.RuntimeSubstitutionHeads

/-!
# Exact helper episodes inside the compiled program

A pending episode keeps its actual helper prefix and its constructed terminal
run as proof evidence. The program still stores only its ordinary literal
state. Helper determinism identifies a reached port with the constructed one.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.HelperPending

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing

def Pending {n : Nat} (result : Tower.Tm n) (continuation current : MClosed) : Prop :=
  RuntimeSubstitution.Internal current ∧ ∃ entry,
    RuntimeSubstitution.Runs entry current ∧
      RuntimeSubstitution.Runs entry (resumeC (encodeTm result) continuation)

theorem initial {n : Nat} (result : Tower.Tm n) (continuation entry : MClosed)
    (inside : RuntimeSubstitution.Internal entry)
    (complete : RuntimeSubstitution.Runs entry (resumeC (encodeTm result) continuation)) :
    Pending result continuation entry := ⟨inside, entry, .refl, complete⟩

theorem advance {dev : Definitions.Development} (built : Compiled dev) {n : Nat}
    {result : Tower.Tm n} {continuation current next : MClosed}
    (pending : Pending result continuation current)
    (step : ProgramBinders.Rewrites built.rules.get current next) :
    Pending result continuation next ∨ next = resumeC (encodeTm result) continuation := by
  obtain ⟨inside, entry, history, complete⟩ := pending
  have helper := HelperIsolation.assembled_step_is_helper built inside step
  have extended := history.tail helper
  rcases RuntimeSubstitution.step_result_scope helper with internal | returned
  · exact .inl ⟨internal, entry, extended, complete⟩
  · obtain ⟨value, k, rfl⟩ := returned
    obtain ⟨rfl, rfl⟩ := RuntimeSubstitution.resume_endpoints extended complete
    exact .inr rfl

theorem normalizing {n : Nat} {result : Tower.Tm n} {continuation current : MClosed}
    (pending : Pending result continuation current) :
    Acc (fun after before => RuntimeSubstitution.Step before after) current := by
  obtain ⟨inside, entry, history, complete⟩ := pending
  clear inside
  have terminates := RuntimeSubstitution.normalizing_of_run complete (RuntimeSubstitution.no_resume_step _ _)
  induction history with
  | refl => exact terminates
  | @tail middle after _ edge ih => exact Acc.inv ih edge

theorem helper_step_heads {before after : MClosed} (step : RuntimeSubstitution.Step before after) :
    closedHead before = some activeTag ∧ closedHead after = some activeTag := by
  obtain ⟨index, environment, matched, produced⟩ := step
  have heads := RuntimeSubstitution.rules_heads _ (List.get_mem _ index)
  have first := literalHead_instantiate
    ((RuntimeSubstitution.rules.get index).assign environment (ProgramBinders.ground MSig)) heads.1
  have last := literalHead_instantiate
    ((RuntimeSubstitution.rules.get index).assign environment (ProgramBinders.ground MSig)) heads.2
  rw [matched, literalHead_include] at first
  rw [produced, literalHead_include] at last
  exact ⟨first, last⟩

theorem head {n : Nat} {result : Tower.Tm n} {continuation current : MClosed}
    (pending : Pending result continuation current) : closedHead current = some activeTag := by
  obtain ⟨_, entry, history, complete⟩ := pending
  rcases history.cases_tail with same | ⟨previous, _, edge⟩
  · subst current
    rcases complete.cases_head with same | ⟨next, edge, _⟩
    · rw [same]
      rfl
    · exact (helper_step_heads edge).1
  · exact (helper_step_heads edge).2

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.HelperPending
