import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNamedSelfProgress
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelfPairProgressControls

/-!
# Actual same-hole pruning needs the secondary measure

Both the pruned hole and an unrelated declaration remain live in later
equations. A model using its own lambda binder retains five image nodes,
while active parameters drop from four to two. Equal maps provide the
negative control: their helper retains both original parameters.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelfActiveControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualActiveSupport hiding active
open ContextualSelfPair.Controls hiding problem

abbrev base := ScopePullback.Controls.base
def first : Term (signature base old) [(), ()] () :=
  rename (S := signature base old) identityMap (generator old (.inl ()))
def second : Term (signature base old) [(), ()] () :=
  rename (S := signature base old) swappedMap (generator old (.inl ()))
def external : Term (signature base old) [(), ()] () := generator old (.inr 9)
def rest : Problem old := [(observe first, observe first), (observe external, observe external)]
def equations : Problem old := (observe first, observe second) :: rest
def update := ContextualNamedSelfPair.apply old (.inl ()) identityMap swappedMap rest
def sameUpdate := ContextualNamedSelfPair.apply old (.inl ()) identityMap identityMap rest

theorem the_source_model_uses_its_own_lambda_binder : Models locallyBound equations := by
  intro equation member
  simp only [equations, rest, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

def residual : Assignment update.declaration others
  | .inl _ => .op (.inl .lam) (.cons (.var .zero) .nil)
  | .inr ⟨.inr identity, _⟩ => generator others identity
  | .inr ⟨.inl (), impossible⟩ => False.elim (impossible rfl)

theorem the_explicit_residual_solves_every_retained_equation : Models residual update.remaining := by
  change Models residual (mapProblem (ContextualSelfPair.answer swapped ()
    (fun other : ContextualFrameSelection.Remaining (.inl () : Unit ⊕ Nat) => old other.val))
    (mapProblem (ContextualSelectedOccurrences.selected old (.inl ())) rest))
  apply (models_mapProblem _ _ _).mpr
  apply (models_mapProblem _ _ _).mpr
  intro equation member
  simp only [rest, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem the_source_model_has_five_active_image_nodes :
    potential locallyBound (ContextualActiveSupport.active equations) = 5 := by
  decide +kernel

theorem the_actual_residual_still_has_five_active_image_nodes :
    letI := update.equality
    potential residual (ContextualActiveSupport.active update.remaining) = 5 := by
  decide +kernel

theorem the_original_active_interfaces_cost_four :
    ContextualInterfacePotential.cost old (ContextualActiveSupport.active equations) = 4 := by
  decide +kernel

theorem the_actual_pruned_interfaces_cost_two :
    letI := update.equality
    ContextualInterfacePotential.cost update.declaration (ContextualActiveSupport.active update.remaining) = 2 := by
  decide +kernel

theorem the_named_update_preserves_a_model_with_secondary_progress :
    letI := update.equality
    ∃ remaining : Assignment update.declaration others, Models remaining update.remaining ∧
      (∀ identity, locallyBound identity = instantiate remaining (update.answer identity)) ∧
      potential remaining (ContextualActiveSupport.active update.remaining) ≤
        potential locallyBound (ContextualActiveSupport.active equations) ∧
      ContextualInterfacePotential.cost update.declaration (ContextualActiveSupport.active update.remaining) <
        ContextualInterfacePotential.cost old (ContextualActiveSupport.active equations) := by
  exact ContextualNamedSelfProgress.model_progress (S := base) (source := old) (.inl ()) identityMap swappedMap
    ContextualSelfPairProgress.Controls.the_swapped_maps_differ rest locallyBound
    the_source_model_uses_its_own_lambda_binder

theorem equal_maps_do_not_supply_a_strict_interface_decrease :
    ¬ (sameUpdate.declaration (.inl ())).1.length < (old (.inl ())).1.length := by
  change ¬ (ScopeEqualizer.Finite.build identityMap identityMap).context.length < 2
  have unchanged : (ScopeEqualizer.Finite.build (S := base) identityMap identityMap).context.length = 2 :=
    ScopeEqualizer.Finite.context_length_same (S := base) identityMap
  rw [unchanged]
  exact Nat.lt_irrefl 2

theorem the_forbidden_old_dependency_is_still_not_a_model : ¬ Models privateDependency equations := by
  intro solved
  have impossible := solved _ List.mem_cons_self
  change observe (Term.var (S := signature base others) (Γ := [(), ()]) Var.zero) =
    observe (Term.var (S := signature base others) (Γ := [(), ()]) (.succ .zero)) at impossible
  have conflict := observe_injective impossible
  cases conflict

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelfActiveControls
