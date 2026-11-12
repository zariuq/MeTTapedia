import Mettapedia.Languages.MeTTa.PeTTa.UnifyingTransitionPreservation

/-!
# Scope preservation along real source prefixes

Every bounded endpoint and suspended continuation retains the actual variable
supply. These laws need neither termination nor a successful answer. A later
activation cannot alias a returned value or a branch's substitution key.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (atomFreeVars)

theorem steps_wellScoped {registry : SpaceSemantics.Program} {source target : Configuration}
    (path : Relation.ReflTransGen (Transition registry) source target) (well : WellScoped source) :
    WellScoped target := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact well
  | head edge _ ih => exact ih (transition_wellScoped edge well)

theorem step_wellScoped {registry : SpaceSemantics.Program} {source target : Configuration}
    (computed : step registry source = some target) (well : WellScoped source) : WellScoped target :=
  transition_wellScoped (step_transition computed) well

theorem prefix_wellScoped (registry : SpaceSemantics.Program) (fuel : Nat) (source : Configuration)
    (well : WellScoped source) : WellScoped (ScopedSource.endpoint registry fuel source) :=
  steps_wellScoped (bounded_endpoint_reachable registry fuel source) well

theorem exhausted_wellScoped (registry : SpaceSemantics.Program) (fuel : Nat) (source saved : Configuration)
    (well : WellScoped source) (paused : run registry fuel source = .exhausted saved) : WellScoped saved := by
  have observed := run_as_bounded registry fuel source
  rw [paused] at observed
  have same := zero_exhausted_state registry _ saved observed.symm
  exact same ▸ prefix_wellScoped registry fuel source well

theorem next_request_wellScoped (source : Configuration) (expression : Atom) (well : WellScoped source) :
    WellScoped (ScopedSource.next source expression) := by
  have old : ConfigurationSupported (Mettapedia.ScopedString.Before source.uses) source := well
  have later := old.mono
    (fun _ earlier => Mettapedia.ScopedString.before_mono (Nat.le_succ source.uses) earlier)
  dsimp only [WellScoped,ConfigurationSupported,ScopedSource.next]
  rw [ControlSupported]
  refine ⟨⟨?_,ScopedSource.renamed_allocated source.uses expression⟩,by simp,later.2.2.1,later.2.2.2⟩
  intro binding member
  cases member

theorem loaded_prefix_wellScoped (registry program : SpaceSemantics.Program) (scope fuel : Nat)
    (code : List SpaceSemantics.Equation) (expression : Atom) :
    WellScoped (ScopedSource.endpoint registry fuel
      (ScopedSource.enter scope code (Effects.loaded program) expression)) :=
  prefix_wellScoped registry fuel _ (primitive_loaded_entry scope code program expression)

/-- Entry hygiene uses a genuinely unused scope. Merely putting all values
below the post-entry counter would allow a retained cell in the new scope. -/
theorem entry_scope_apart_from_cells (scope : Nat) (state : Effects.State) (expression : Atom)
    (cells : CellsSupported (Mettapedia.ScopedString.Before scope) state) :
    ∀ key ∈ atomFreeVars (rename scope expression), ∀ name value,
      state.cells name = some value → key ∉ atomFreeVars value := by
  intro key member name value stored
  rw [ScopedSource.rename_freeVars] at member
  obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
  exact ScopedSource.later_scope_is_apart (Nat.le_refl _) (cells name value stored) original

theorem next_request_apart_from_cells (source : Configuration) (expression : Atom)
    (well : WellScoped source) :
    ∀ key ∈ atomFreeVars (rename source.uses expression), ∀ name value,
      source.state.cells name = some value → key ∉ atomFreeVars value :=
  entry_scope_apart_from_cells source.uses source.state expression well.2.2.1

theorem returned_future_names_are_fresh (source : Configuration) (answers : List Answer)
    (well : WellScoped source) (returned : source.control = .returned answers) (name : String) :
    ∀ answer ∈ answers,
      answer.bindings.lookup (freshName source.uses name) = none ∧
        freshName source.uses name ∉ atomFreeVars answer.value := by
  have good : ControlSupported (Mettapedia.ScopedString.Before source.uses) source.control := well.1
  simp only [returned,ControlSupported] at good
  intro answer member
  have packet := good answer member
  exact ⟨allocated_bindings_have_no_future_key source.uses answer.bindings packet.2 name,
    ScopedSource.later_scope_is_apart (Nat.le_refl _) packet.1 name⟩

theorem loaded_prefix_returned_names_are_fresh (registry program : SpaceSemantics.Program) (scope fuel : Nat)
    (code : List SpaceSemantics.Equation) (expression : Atom) (answers : List Answer) (name : String)
    (returned : (ScopedSource.endpoint registry fuel
      (ScopedSource.enter scope code (Effects.loaded program) expression)).control = .returned answers) :
    ∀ answer ∈ answers,
      answer.bindings.lookup (freshName (ScopedSource.endpoint registry fuel
        (ScopedSource.enter scope code (Effects.loaded program) expression)).uses name) = none ∧
      freshName (ScopedSource.endpoint registry fuel
        (ScopedSource.enter scope code (Effects.loaded program) expression)).uses name ∉ atomFreeVars answer.value :=
  returned_future_names_are_fresh _ answers
    (loaded_prefix_wellScoped registry program scope fuel code expression) returned name

end Mettapedia.Languages.MeTTa.PeTTa.Unifying
