import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionSplitting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixPrincipals

/-!
# Prefix models lift through actual injective declaration extensions

Off-image names keep separate fresh generators. The assignment square
relates the old model to the lifted one, and model existence is reflected
in both directions without adding future equations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardMatching.Extension

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualPrefixModels

variable {S : Signature} {V Next : Type} {source : V → MetaArity S} {next : Next → MetaArity S}

noncomputable def liftModel (extension : Extension source) (candidate : Assignment source next) :
    Assignment extension.declarations (extended extension.complementDeclarations next) :=
  Assignment.compose (ContextualStoredRows.liftCaptures extension.complementDeclarations candidate)
    extension.unsplitAssignment

theorem liftModel_square (extension : Extension source) (candidate : Assignment source next) :
    Assignment.compose (extension.liftModel candidate) extension.assignment =
      Assignment.compose (inclusion extension.complementDeclarations next) candidate := by
  unfold liftModel
  rw [← extension.split_inclusion]
  rw [← Assignment.compose_associative
    (Assignment.compose extension.splitAssignment (inclusion extension.complementDeclarations source))
    extension.unsplitAssignment (ContextualStoredRows.liftCaptures extension.complementDeclarations candidate)]
  rw [Assignment.compose_associative (inclusion extension.complementDeclarations source)
    extension.splitAssignment extension.unsplitAssignment]
  rw [extension.split_inverse, Assignment.compose_identity_left, lifted_capture_assignment]

theorem models_liftModel_iff (extension : Extension source) (candidate : Assignment source next)
    {Γ : Ctx S} {sort : S.Srt} (problem : EquationStore (Term (signature S source) Γ sort)) :
    ContextualFrameUnifier.Models (extension.liftModel candidate)
        (ContextualFrameUnifier.mapProblem extension.assignment problem) ↔
      ContextualFrameUnifier.Models candidate problem := by
  rw [ContextualFrameUnifier.models_mapProblem, extension.liftModel_square]
  exact models_after_inclusion_iff extension.complementDeclarations candidate problem

theorem exists_model_iff (extension : Extension source) {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S source) Γ sort)) :
    (∃ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment extension.declarations future),
      ContextualFrameUnifier.Models candidate (ContextualFrameUnifier.mapProblem extension.assignment problem)) ↔
    ∃ (Future : Type) (future : Future → MetaArity S) (candidate : Assignment source future),
      ContextualFrameUnifier.Models candidate problem := by
  constructor
  · rintro ⟨Future, future, candidate, solved⟩
    exact ⟨Future, future, Assignment.compose candidate extension.assignment,
      (ContextualFrameUnifier.models_mapProblem extension.assignment candidate problem).mp solved⟩
  · rintro ⟨Future, future, candidate, solved⟩
    exact ⟨Complement extension ⊕ Future, extended extension.complementDeclarations future,
      extension.liftModel candidate, (extension.models_liftModel_iff candidate problem).mpr solved⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardMatching.Extension
