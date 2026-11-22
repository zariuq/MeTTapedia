import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveAbsence

/-!
# Joint query models recover their caller and shared local witnesses

Every model of the actual tuple equation store decomposes into its caller
assignment, one shared query assignment and the separately scoped row
assignments. This is the converse to witness compilation, not a supplied
completeness predicate. It characterizes the all-future absence contract.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveModels

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching
open ContextualConjunctiveQueries

universe u
variable {S : Signature} {Query Local Shared Next : Type} {O : Type u}
  (queries : Query → MetaArity S) (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
  {next : Next → MetaArity S}

def caller (assignment : Assignment (family queries locals captures) next) : Assignment captures next :=
  fun name => assignment (.inr (.inr name))

def queryBodies (assignment : Assignment (family queries locals captures) next) : Assignment queries next :=
  fun name => assignment (.inl name)

def rowBodies (assignment : Assignment (family queries locals captures) next) : Assignment (rowLocals locals) next :=
  fun name => assignment (.inr (.inl name))

theorem reassemble (assignment : Assignment (family queries locals captures) next) :
    combinedAssignment queries locals captures (queryBodies queries locals captures assignment)
      (rowBodies queries locals captures assignment) (generator next) (caller queries locals captures assignment) = assignment := by
  funext name
  cases name with
  | inl name => rfl
  | inr name =>
      cases name with
      | inl name => rfl
      | inr name => exact instantiate_identity _

theorem on_captured_value (assignment : Assignment (family queries locals captures) next)
    {Γ : Ctx S} {sort : S.Srt} (value : Term (signature S captures) Γ sort) :
    instantiate assignment (instantiate (captureEmbedding queries locals captures) value) =
      instantiate (caller queries locals captures assignment) value := by
  have same := instantiated_captured_value queries locals captures
    (queryBodies queries locals captures assignment) (rowBodies queries locals captures assignment)
    (generator next) (caller queries locals captures assignment) value
  rw [reassemble] at same
  exact same.trans (instantiate_identity _)

theorem joint_model_gives_caller_and_match (assignment : Assignment (family queries locals captures) next)
    {Γ : Ctx S} {sort : S.Srt} (problem : EquationStore (Term (signature S captures) Γ sort))
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (chosen : Fin patterns.length → O)
    (models : ContextualFrameUnifier.Models assignment (joint queries locals captures problem patterns rows chosen)) :
    ContextualFrameUnifier.Models (caller queries locals captures assignment) problem ∧
      ContextualConjunctiveQueries.Matches queries locals captures (caller queries locals captures assignment) patterns rows chosen := by
  obtain ⟨before, equations⟩ := (ContextualFrameUnifier.models_append _ _ _).mp models
  constructor
  · intro equation member
    have observed := before _ (List.mem_map.mpr ⟨equation, member, rfl⟩)
    exact (on_captured_value queries locals captures assignment equation.1).symm.trans
      (observed.trans (on_captured_value queries locals captures assignment equation.2))
  · refine ⟨Extension.identity next, queryBodies queries locals captures assignment,
      rowBodies queries locals captures assignment, ?_⟩
    intro port
    have selected := equations _ (List.mem_ofFn.mpr ⟨port, rfl⟩)
    have rowLaw := instantiated_row_view queries locals captures
      (queryBodies queries locals captures assignment) (rowBodies queries locals captures assignment)
      (generator next) (caller queries locals captures assignment) port (rows (chosen port))
    have queryLaw := instantiated_query_view queries locals captures
      (queryBodies queries locals captures assignment) (rowBodies queries locals captures assignment)
      (generator next) (caller queries locals captures assignment) (patterns.get port)
    rw [reassemble] at rowLaw queryLaw
    exact rowLaw.symm.trans (selected.trans queryLaw)

theorem absence_ask_iff_no_joint_model {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S captures) Γ sort))
    (patterns : List (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O) :
    ContextualConjunctiveAbsence.Ask queries locals captures problem patterns rows world ↔
      ∀ chosen : Fin patterns.length → O, (∀ port, chosen port ∈ world) →
        ∀ (Next : Type) (next : Next → MetaArity S) (assignment : Assignment (family queries locals captures) next),
          ¬ ContextualFrameUnifier.Models assignment (joint queries locals captures problem patterns rows chosen) := by
  constructor
  · intro absent chosen present Next next assignment models
    obtain ⟨before, matched⟩ := joint_model_gives_caller_and_match queries locals captures assignment
      problem patterns rows chosen models
    exact absent Next next (caller queries locals captures assignment) before chosen present matched
  · intro impossible Next next candidate before chosen present matched
    obtain ⟨Later, later, assignment, models⟩ := match_gives_joint_model queries locals captures candidate
      problem patterns rows chosen before matched
    exact impossible chosen present Later later assignment models

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveModels
