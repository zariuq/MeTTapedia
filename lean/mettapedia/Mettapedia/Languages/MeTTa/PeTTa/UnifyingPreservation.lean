import Mettapedia.Languages.MeTTa.PeTTa.UnifyingPrimitiveScopes
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingContinuationScopes

/-!
# Scope preservation through source execution

The invariant follows the actual source transitions and their allocation
increments. Templates stay unscoped until their existing import/use boundary;
running values, substitutions, continuations, cells and output retain allocated
logical identities. No run-time invariant checker is part of this construction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)

theorem removeRows_supported (allowed : String → Prop) (state after : Effects.State)
    (location pattern : Atom) (use used : Nat) (answers : List Atom)
    (removed : removeRows state location pattern use = some (.ok (after,answers,used))) :
    after.cells = state.cells ∧ ∀ answer ∈ answers, Supported allowed answer := by
  unfold removeRows at removed
  split at removed
  · cases removed
  · rename_i handle decoded
    cases read : state.read handle with
    | none => simp [read] at removed
    | some rows =>
        simp only [read] at removed
        split at removed
        · cases removed
          exact ⟨rfl,by simp [Effects.boolean]⟩
        · rename_i _ head tail
          cases survived : survivors (.expression (head :: tail)) use rows with
          | none => simp [survived] at removed
          | some kept =>
              simp only [survived,Option.map_some] at removed
              cases written : state.write handle kept with
              | none => simp [written] at removed
              | some changed =>
                  simp only [written,Option.some.injEq,Except.ok.injEq,Prod.mk.injEq] at removed
                  obtain ⟨rfl,rfl,rfl⟩ := removed
                  exact ⟨NamedSpaces.Store.write_preserves_cells state handle kept changed written,
                    by simp [Effects.boolean]⟩
        · cases removed
          exact ⟨rfl,by simp⟩

theorem primitive_loaded_entry (scope : Nat) (code : List SpaceSemantics.Equation)
    (program : SpaceSemantics.Program) (expression : Atom) :
    WellScoped (ScopedSource.enter scope code (Effects.loaded program) expression) :=
  scoped_entry scope code (Effects.loaded program) expression (loaded_cells_supported _ program)

end Mettapedia.Languages.MeTTa.PeTTa.Unifying
