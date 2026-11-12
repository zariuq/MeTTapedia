import Mettapedia.Languages.MeTTa.PeTTa.StreamingScopePreservation

/-!
# Actual streaming entry, prefixes and next-request freshness

Entry uses a genuinely unused activation. Every paid prefix retains variable
support in the full world/frontier. The next activation is apart from actual
retained cells and returned binding/value records. Marker association remains
separate from logical-variable support.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Streaming.ScopeInvariant

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst atomFreeVars)

theorem enter_wellScoped (world : World) (expression : Atom)
    (ready : worldSupported (Mettapedia.ScopedString.Before world.uses) world) : WellScoped (enter world expression) := by
  have later := world_mono
    (fun key old => Mettapedia.ScopedString.before_mono (Nat.le_succ world.uses) old) ready
  refine ⟨later,(agenda_cons _ _ _).mpr ⟨⟨?_,by simp [framesSupported]⟩,by simp [agendaSupported]⟩,by simp [enter]⟩
  simp only [Unifying.ControlSupported]
  refine ⟨?_,ScopedSource.renamed_allocated world.uses expression⟩
  intro binding present
  cases present

theorem loaded_world_ready (program : SpaceSemantics.Program) (code : List SpaceSemantics.Equation)
    (use : Nat) : worldSupported (Mettapedia.ScopedString.Before use)
      {state := Effects.loaded program,privateCode := code,uses := use} :=
  ⟨Unifying.loaded_cells_supported _ program,by simp⟩

theorem every_request_prefix_wellScoped (registry : SpaceSemantics.Program) (fuel : Nat)
    (world : World) (expression : Atom)
    (ready : worldSupported (Mettapedia.ScopedString.Before world.uses) world) :
    WellScoped (advance registry fuel (enter world expression)) :=
  advance_wellScoped registry fuel _ (enter_wellScoped world expression ready)

theorem loaded_request_prefix_wellScoped (registry program : SpaceSemantics.Program) (fuel use : Nat)
    (code : List SpaceSemantics.Equation) (expression : Atom) :
    WellScoped (advance registry fuel (enter {state := Effects.loaded program,privateCode := code,uses := use} expression)) :=
  every_request_prefix_wellScoped registry fuel _ expression (loaded_world_ready program code use)

theorem next_request_wellScoped (state : State) (expression : Atom) (well : WellScoped state) :
    WellScoped (enter state.world expression) := enter_wellScoped state.world expression well.1

theorem next_request_apart_from_cells (state : State) (expression : Atom) (well : WellScoped state) :
    ∀ key ∈ atomFreeVars (Unifying.rename state.world.uses expression), ∀ name value,
      state.world.state.cells name = some value → key ∉ atomFreeVars value :=
  Unifying.entry_scope_apart_from_cells state.world.uses state.world.state expression well.1.1

theorem returned_future_names_are_fresh (state : State) (well : WellScoped state) (name : String) :
    ∀ answer ∈ state.answers,
      Subst.lookup answer.bindings (Unifying.freshName state.world.uses name) = none ∧
        Unifying.freshName state.world.uses name ∉ atomFreeVars answer.value := by
  intro answer returned
  have supported := well.2.2 answer returned
  exact ⟨Unifying.allocated_bindings_have_no_future_key state.world.uses answer.bindings supported.2 name,
    ScopedSource.later_scope_is_apart (Nat.le_refl _) supported.1 name⟩

theorem actual_prefix_next_request_apart (registry : SpaceSemantics.Program) (fuel : Nat)
    (world : World) (expression next : Atom)
    (ready : worldSupported (Mettapedia.ScopedString.Before world.uses) world) :
    ∀ key ∈ atomFreeVars (Unifying.rename (advance registry fuel (enter world expression)).world.uses next),
      ∀ name value, (advance registry fuel (enter world expression)).world.state.cells name = some value →
        key ∉ atomFreeVars value :=
  next_request_apart_from_cells _ next (every_request_prefix_wellScoped registry fuel world expression ready)

end Mettapedia.Languages.MeTTa.PeTTa.Streaming.ScopeInvariant
