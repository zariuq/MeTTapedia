import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActiveReindex
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameControls

/-!
# Finite roster transport moves arities as well as arbitrary identities

A two-parameter hole moves from name zero to name two, while a distant
nullary declaration stays fixed. The actual model and its four-node roster
potential survive the transport. Reusing the old declaration at the new name
would give the wrong parameter context.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActiveReindexControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualActiveSupport
open ContextualActiveReindex

abbrev base := ContextualFrame.Controls.signature
def source : Nat → MetaArity base
  | 0 => ([(), ()], ())
  | _ + 1 => ([], ())
def exchange : Nat ≃ Nat := Equiv.swap 0 2
def target (identity : Nat) : MetaArity base := source (exchange.symm identity)
theorem forward (identity : Nat) : target (exchange identity) = source identity := by
  dsimp only [target]
  rw [exchange.symm_apply_apply]
theorem backward (identity : Nat) : source (exchange.symm identity) = target identity := rfl
abbrev extended := signature base source
def constant {Γ : Ctx base} : Term extended Γ () := .op (.inl .constant) .nil
def pair {Γ : Ctx base} (left right : Term extended Γ ()) : Term extended Γ () :=
  .op (.inl .pair) (.cons left (.cons right .nil))
def objectPair : Term extended [(), ()] () := pair (.var .zero) (.var (.succ .zero))
def problem : Problem source :=
  [(observe (generator source 0), observe objectPair),
   (observe (generator source 1000003), observe (constant (Γ := [])))]
def candidate : Assignment source source
  | 0 => objectPair
  | _ + 1 => constant
def mapped := mapProblem (reindex exchange forward) problem
def residual : Assignment target source := Assignment.compose candidate (reindex exchange.symm backward)

theorem two_actual_names_form_the_source_roster : active problem = {0, 1000003} := by
  decide +kernel

theorem the_computed_target_roster_moves_only_the_selected_name : active mapped = {2, 1000003} := by
  decide +kernel

theorem the_new_name_really_carries_the_two_parameters : (target 2).1.length = 2 := by
  decide +kernel

theorem the_old_declaration_at_that_name_would_be_wrong : (source 2).1.length ≠ (target 2).1.length := by
  decide +kernel

theorem source_roster_potential_is_four : potential candidate (active problem) = 4 := by
  decide +kernel

theorem transported_roster_potential_is_the_same_four : potential residual (active mapped) = 4 := by
  exact (potential_reindex_exact exchange forward backward problem candidate).trans source_roster_potential_is_four

theorem the_source_candidate_satisfies_its_equations : Models candidate problem := by
  intro equation member
  simp only [problem, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem the_same_candidate_is_usable_after_actual_interface_transport : Models residual mapped :=
  (models_reindex_back exchange forward backward problem candidate).mpr the_source_candidate_satisfies_its_equations

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActiveReindexControls
