import Mettapedia.Logic.LP.UnificationIdempotence

/-! Variables forgotten by a relevant unifier already belong to its equation
support. Reading a ground value does not justify forgetting that support. -/

set_option autoImplicit false

namespace Mettapedia.Logic.LP.Subst.RelevantIdempotent

variable {σ : LPSignature} [DecidableEq σ.vars] {θ : Subst σ} {X : Finset σ.vars}

theorem source_freeVars_subset (relevant : θ.RelevantIdempotent X) (term : Term σ) :
    term.freeVars ⊆ X ∪ (θ.applyTerm term).freeVars := by
  intro name present
  by_cases bound : name ∈ X
  · exact Finset.mem_union_left _ bound
  · apply Finset.mem_union_right
    apply Subst.mem_freeVars_applyTerm.mpr
    refine ⟨name, present, ?_⟩
    rw [relevant.fixes name bound]
    exact Term.mem_freeVars_var.mpr rfl

theorem ground_source_freeVars_subset (relevant : θ.RelevantIdempotent X) (term : Term σ)
    (ground : (θ.applyTerm term).freeVars = ∅) : term.freeVars ⊆ X := by
  simpa only [ground, Finset.union_empty] using relevant.source_freeVars_subset term

end Mettapedia.Logic.LP.Subst.RelevantIdempotent
