import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionAsks
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFreshFrameScopeLedger

/-!
# Actual computed helper frames reflect the original all-future asks

The inclusion uses the returned update's complete declaration family and
keeps old source names. It is distinct from applying the returned answer.
Only the pure inclusion reflects earlier asks and prefix-model existence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualComputedFreshFrame

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualFrameUpdate ContextualGuardMatching

universe u
variable {S : Signature} {V Local : Type} {O : Type u} {source : V → MetaArity S}

def declarationExtension {problem : ContextualResidual.Problem source} (update : Update problem) : Extension source where
  Names := V ⊕ (update.Variables ⊕ Empty)
  declarations := active source update.declaration
  name := Sum.inl
  injective := Sum.inl_injective
  preserves _ := rfl

theorem declarationExtension_assignment {problem : ContextualResidual.Problem source} (update : Update problem) :
    (declarationExtension update).assignment = includeSource update := by
  funext name
  exact (ContextualFreshFrameScopeLedger.includeSource_image update name).symm

theorem ask_include_computed_frame_iff (locals : Local → MetaArity S)
    {problem : ContextualResidual.Problem source} (update : Update problem)
    {Γ : Ctx S} {sort : S.Srt}
    (prefixProblem : EquationStore (Term (signature S source) Γ sort))
    (rows : O → ContextualStoredRows.Row locals source Γ sort) (world : Finset O)
    (check : Check (Term (signature S source) Γ sort)) :
    ContextualGuardSemantics.Ask locals (ContextualFrameUnifier.mapProblem (includeSource update) prefixProblem)
        (fun occurrence => (rows occurrence).map locals (includeSource update)) world
        (check.map (instantiate (includeSource update))) ↔
      ContextualGuardSemantics.Ask locals prefixProblem rows world check := by
  have reflected := ContextualGuardSemantics.Ask.extension_iff locals (declarationExtension update)
    prefixProblem rows world check
  rw [declarationExtension_assignment] at reflected
  exact reflected

theorem exists_model_in_computed_frame_iff
    {problem : ContextualResidual.Problem source} (update : Update problem)
    {Γ : Ctx S} {sort : S.Srt} (prefixProblem : EquationStore (Term (signature S source) Γ sort)) :
    (∃ (Future : Type) (future : Future → MetaArity S)
      (candidate : Assignment (active source update.declaration) future),
      ContextualFrameUnifier.Models candidate (ContextualFrameUnifier.mapProblem (includeSource update) prefixProblem)) ↔
    ∃ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment source future),
      ContextualFrameUnifier.Models candidate prefixProblem := by
  have reflected := (declarationExtension update).exists_model_iff prefixProblem
  rw [declarationExtension_assignment] at reflected
  exact reflected

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualComputedFreshFrame
