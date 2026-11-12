import Mettapedia.Languages.MeTTa.PeTTa.UnifyingPrefixScopes
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaLambdaControls
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaScopeControls

/-!
# Positive and negative consumers of complete source scope preservation

Every fuel prefix of the collision and input fixtures is covered. Raw entry
and a stale supply for retained cells are explicit counterexamples to omitting
the admission/store hypotheses. The laws concern logical variable identities,
not a C allocator or the evaluator's fuel tariff.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaScopePreservationControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (atomFreeVars)
open Unifying

def closureSeed : Configuration :=
  LambdaLifting.enter PeTTaLambdaControls.closed Effects.empty PeTTaLambdaControls.suffixCollision

theorem every_closure_prefix_is_well_scoped (fuel : Nat) :
    WellScoped (ScopedSource.endpoint PeTTaLambdaControls.registry fuel closureSeed) := by
  apply prefix_wellScoped
  exact scoped_entry 0 _ Effects.empty _ (empty_cells_supported _)

def inputSeed : Configuration :=
  {ScopedSource.enter 0 [] Effects.empty PeTTaScopeControls.inputRequest with input := [.var "x#0"]}

theorem every_input_prefix_is_well_scoped (fuel : Nat) :
    WellScoped (ScopedSource.endpoint PeTTaScopeControls.registry fuel inputSeed) := by
  apply prefix_wellScoped
  dsimp only [WellScoped,ConfigurationSupported,inputSeed,ScopedSource.enter]
  rw [ControlSupported]
  exact ⟨⟨by simp [SupportedBindings],ScopedSource.renamed_allocated 0 _⟩,
    by simp,empty_cells_supported _,by simp⟩

theorem raw_entry_is_not_source_admission :
    ¬WellScoped (start Effects.empty (.var "x#0")) := by
  intro well
  have good := well.1
  simp only [start,ControlSupported] at good
  obtain ⟨scope,earlier,_,_⟩ := good.2 "x#0" (by simp [atomFreeVars])
  omega

def staleCell : Effects.State := Effects.empty.putCell "cell" (.var (freshName 1 "x"))
def staleEntry : Configuration := ScopedSource.enter 0 [] staleCell (.symbol "ok")

theorem a_stale_cell_supply_is_not_well_scoped : ¬WellScoped staleEntry := by
  intro well
  have stored : staleEntry.state.cells "cell" = some (.var (freshName 1 "x")) := by
    simp [staleEntry,ScopedSource.enter,staleCell]
  have good := well.2.2.1 "cell" (.var (freshName 1 "x")) stored
  have allocated := good (freshName 1 "x") (by simp [atomFreeVars])
  exact Mettapedia.ScopedString.new_identity_is_fresh allocated "x" rfl

theorem primitive_cell_support_hypothesis_is_necessary :
    StdLib.apply staleCell "get-state" [.symbol "cell"] = .ok (staleCell,[.var (freshName 1 "x")]) ∧
      ¬Supported (Mettapedia.ScopedString.Before 1) (.var (freshName 1 "x")) := by
  refine ⟨by rfl,?_⟩
  intro good
  have allocated := good (freshName 1 "x") (by simp [atomFreeVars])
  exact Mettapedia.ScopedString.new_identity_is_fresh allocated "x" rfl

def reusedCell : Effects.State := Effects.empty.putCell "cell" (.var (freshName 0 "x"))

/-- Post-entry support alone is weaker than source-entry hygiene. The same
scope/name pair really aliases a retained cell if the supply is reused. -/
theorem a_post_entry_bound_does_not_justify_scope_reuse :
    CellsSupported (Mettapedia.ScopedString.Before 1) reusedCell ∧
      freshName 0 "x" ∈ atomFreeVars (rename 0 (.var "x")) ∧
      reusedCell.cells "cell" = some (.var (freshName 0 "x")) := by
  refine ⟨?_,by simp [rename,atomFreeVars],?_⟩
  · refine CellsSupported.putCell (allowed := Mettapedia.ScopedString.Before 1)
      (empty_cells_supported _) "cell" (.var (freshName 0 "x")) ?_
    intro key member
    simp only [atomFreeVars,List.mem_singleton] at member
    subst key
    exact Mettapedia.ScopedString.new_identity_before_next 0 "x"
  · simp [reusedCell]

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaScopePreservationControls
