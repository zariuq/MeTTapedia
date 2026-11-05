import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixNativePublication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixPublicationControls

/-!
# An unfinished native publication retains a nontrivial prefix condition

The saved prefix says Y = box(Z). The ambient caller later fixes its own
Z to 1. A private saved copy still admits box(2), while its retained prefix
condition excludes bare 2. This holds at every finite solver budget,
including a zero-budget result with a nonempty residual problem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixNativeControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching ContextualConditionalRows
open ContextualPrefixPublicationControls (DataOperator base none symbol box)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq DataOperator)

abbrev declarations (_ : Bool) : MetaArity base := ([], ())
def savedY : Term (signature base declarations) [] () := generator declarations false
def savedZ : Term (signature base declarations) [] () := generator declarations true
def saved : ContextualResidual.Problem declarations := [(observe savedY, observe (box savedZ))]
def current : ContextualResidual.Problem declarations := saved ++ [(observe savedZ, observe (symbol 1))]

def model {V : Type} (decl : V → MetaArity base) (n : Nat) : Assignment declarations decl
  | false => box (symbol n)
  | true => symbol n

theorem saved_model {V : Type} (decl : V → MetaArity base) (n : Nat) :
    ContextualResidual.Models (model decl n) saved := by
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  rfl

theorem current_model {V : Type} (decl : V → MetaArity base) :
    ContextualResidual.Models (model decl 1) current := by
  apply (ContextualResidual.models_append _ _ _).mpr
  refine ⟨saved_model decl 1, ?_⟩
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  rfl

theorem saved_consistent : ContextualConditionalExecution.Solvable saved :=
  ⟨Empty, none, model none 2, saved_model none 2⟩
theorem current_consistent : ContextualConditionalExecution.Solvable current :=
  ⟨Empty, none, model none 1, current_model none⟩

theorem saved_admits_box_two {V : Type} (decl : V → MetaArity base) :
    ContextualPublication.SourceInstances saved savedY decl (box (symbol 2)) :=
  ⟨Extension.identity decl, model decl 2, saved_model decl 2, rfl⟩

theorem saved_excludes_bare_two {V : Type} (decl : V → MetaArity base) :
    ¬ ContextualPublication.SourceInstances saved savedY decl (symbol 2) := by
  rintro ⟨extension, images, conditions, same⟩
  have shaped := (ContextualResidual.models_observed_iff images savedY (box savedZ)).mp conditions
  change instantiate images savedY = box (instantiate images savedZ) at shaped
  change instantiate images savedY = symbol 2 at same
  have impossible := Sum.inl.inj (Term.op.inj (shaped.symm.trans same)).1
  cases impossible

theorem actual_bounded_publication_keeps_the_prefix (fuel : Nat) :
    ∃ result : ContextualPrefixNativePublication.Computed declarations declarations saved current fuel,
      ∀ (V : Type) (decl : V → MetaArity base) (candidate : Assignment result.targetFamily decl),
        Matches (ContextualPublication.privateFamily none result.update.declaration) result.targetFamily candidate
            (box (symbol 2)) (result.row none savedY) ∧
        ¬ Matches (ContextualPublication.privateFamily none result.update.declaration) result.targetFamily candidate
            (symbol 2) (result.row none savedY) := by
  obtain ⟨result⟩ := ContextualPrefixNativePublication.realize declarations declarations saved current fuel
    saved_consistent current_consistent
  refine ⟨result, ?_⟩
  intro V decl candidate
  exact ⟨(result.row_instances none current_consistent candidate savedY _).mpr (saved_admits_box_two decl),
    fun matched => saved_excludes_bare_two decl ((result.row_instances none current_consistent candidate savedY _).mp matched)⟩

def zeroResult : ContextualPrefixNativePublication.Computed declarations declarations saved current 0 :=
  ⟨ContextualFrameWorklist.identity (ContextualPrefixIsolation.problem declarations declarations saved current), rfl⟩

theorem zero_budget_retains_a_nonempty_problem : zeroResult.update.remaining ≠ [] := by
  intro empty
  have length := congrArg List.length empty
  change (3 : Nat) = 0 at length
  omega

theorem the_zero_budget_row_still_excludes_a_wrong_shape {V : Type} (decl : V → MetaArity base)
    (candidate : Assignment zeroResult.targetFamily decl) :
    ¬ Matches (ContextualPublication.privateFamily none zeroResult.update.declaration) zeroResult.targetFamily candidate
      (symbol 2) (zeroResult.row none savedY) := by
  intro matched
  exact saved_excludes_bare_two decl ((zeroResult.row_instances none current_consistent candidate savedY _).mp matched)

def currentZ {fuel : Nat}
    (result : ContextualPrefixNativePublication.Computed declarations declarations saved current fuel) :
    Term (signature base result.targetFamily) [] () :=
  instantiate (ContextualComputedFreshFrame.includeSource result.update)
    (instantiate (ContextualSelectionViews.capturedSource declarations declarations) savedZ)

theorem the_actual_current_binding_is_retained {fuel : Nat}
    (result : ContextualPrefixNativePublication.Computed declarations declarations saved current fuel)
    {V : Type} (decl : V → MetaArity base) (candidate : Assignment result.targetFamily decl)
    (model : ContextualResidual.Models candidate result.information) :
    instantiate candidate (currentZ result) = symbol 1 := by
  have original := (ContextualResidual.models_mapProblem _ _ _).mp model
  have ambient := (ContextualResidual.models_mapProblem _ _ _).mp
    ((ContextualResidual.models_append _ _ _).mp original).2
  have bound := ((ContextualResidual.models_append _ _ _).mp ambient).2
  have fixed := (ContextualResidual.models_observed_iff _ savedZ (symbol 1)).mp bound
  change instantiate candidate (instantiate _ (instantiate _ savedZ)) = _
  erw [← Assignment.instantiate_compose, ← Assignment.instantiate_compose]
  exact fixed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixNativeControls
