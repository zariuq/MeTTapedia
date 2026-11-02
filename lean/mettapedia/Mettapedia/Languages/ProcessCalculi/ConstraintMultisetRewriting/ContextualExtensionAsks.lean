import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExtensionSplitting
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardReindexing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixAsks

/-!
# Original all-future asks reflect arbitrary names-only declaration extensions

An injective arity-preserving extension has an explicit unused complement.
The split equivalence reflects the original ask, and conservative addition
of that complement reflects it again. Future constraints are never added.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardSemantics

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualGuardMatching ContextualPrefixModels

universe u
variable {S : Signature} {Local V : Type} {O : Type u}
  (locals : Local → MetaArity S) {source : V → MetaArity S}

theorem Ask.extension_iff (extension : Extension source) {Γ : Ctx S} {sort : S.Srt}
    (problem : EquationStore (Term (signature S source) Γ sort))
    (rows : O → ContextualStoredRows.Row locals source Γ sort) (world : Finset O)
    (check : Check (Term (signature S source) Γ sort)) :
    Ask locals (ContextualFrameUnifier.mapProblem extension.assignment problem)
        (fun occurrence => (rows occurrence).map locals extension.assignment) world
        (check.map (instantiate extension.assignment)) ↔
      Ask locals problem rows world check := by
  have problemComp :
      ContextualFrameUnifier.mapProblem extension.splitAssignment
        (ContextualFrameUnifier.mapProblem (inclusion extension.complementDeclarations source) problem) =
      ContextualFrameUnifier.mapProblem extension.assignment problem := by
    rw [ContextualComputedFreshFrame.map_compose, extension.split_inclusion]
  have rowsComp :
      (fun occurrence => ((rows occurrence).map locals (inclusion extension.complementDeclarations source)).map locals
        extension.splitAssignment) = fun occurrence => (rows occurrence).map locals extension.assignment := by
    funext occurrence
    rw [ContextualStoredRows.Row.map_compose, extension.split_inclusion]
  have checkComp :
      (check.map (instantiate (inclusion extension.complementDeclarations source))).map
        (instantiate extension.splitAssignment) = check.map (instantiate extension.assignment) := by
    cases check <;> simp only [Check.map, ← Assignment.instantiate_compose, extension.split_inclusion]
  have reflected :
      Ask locals (ContextualFrameUnifier.mapProblem extension.splitAssignment
          (ContextualFrameUnifier.mapProblem (inclusion extension.complementDeclarations source) problem))
        (fun occurrence => ((rows occurrence).map locals (inclusion extension.complementDeclarations source)).map locals
          extension.splitAssignment) world
        ((check.map (instantiate (inclusion extension.complementDeclarations source))).map
          (instantiate extension.splitAssignment)) ↔
      Ask locals (ContextualFrameUnifier.mapProblem (inclusion extension.complementDeclarations source) problem)
        (fun occurrence => (rows occurrence).map locals (inclusion extension.complementDeclarations source)) world
        (check.map (instantiate (inclusion extension.complementDeclarations source))) :=
    Ask.reindex_iff locals extension.splitNames extension.splitNames.symm
      extension.splitPreserves extension.unsplitPreserves extension.splitNames.left_inv _ _ _ _
  rw [problemComp, rowsComp, checkComp] at reflected
  exact reflected.trans (Ask.unused_extension_iff locals extension.complementDeclarations problem rows world check)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardSemantics
