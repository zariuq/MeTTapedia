import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualUnusedMatching
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardSemantics

/-!
# Original all-future asks reflect names-only prefix extension

Both directions use the actual local-schema matching contract. The common
extension supplies fresh unused names without their future constraints.
Physical regions and counts are unchanged, and the result retains universal
quantification over arbitrary later declaration families.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardSemantics

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualPrefixModels

universe u
variable {S : Signature} {Extra Local Shared Next : Type} {O : Type u}
  (locals : Local → MetaArity S) (unused : Extra → MetaArity S)
  {captures : Shared → MetaArity S} {next : Next → MetaArity S}

theorem region_inclusion (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (pattern : Term (signature S captures) Γ sort) :
    region locals (Assignment.compose (inclusion unused next) candidate) rows world pattern =
      region locals candidate rows world pattern := by
  classical
  ext occurrence
  rw [mem_region, mem_region, Assignment.instantiate_compose]
  exact and_congr_right fun _ => ContextualGuardMatching.matches_inclusion_iff
    locals unused candidate (instantiate candidate pattern) (rows occurrence)

theorem holds_inclusion_iff (candidate : Assignment captures next) {Γ : Ctx S} {sort : S.Srt}
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (check : Check (Term (signature S captures) Γ sort)) :
    Holds locals (Assignment.compose (inclusion unused next) candidate) rows world check ↔
      Holds locals candidate rows world check := by
  cases check with
  | equal first second =>
      change instantiate (Assignment.compose (inclusion unused next) candidate) first =
          instantiate (Assignment.compose (inclusion unused next) candidate) second ↔
        instantiate candidate first = instantiate candidate second
      rw [Assignment.instantiate_compose, Assignment.instantiate_compose]
      exact ⟨fun same => inclusion_injective unused next _ _ same,
        congrArg (instantiate (inclusion unused next))⟩
  | absent pattern =>
      simp only [Holds, Assignment.instantiate_compose, ContextualGuardMatching.matches_inclusion_iff]
  | count pattern number =>
      change (region locals (Assignment.compose (inclusion unused next) candidate) rows world pattern).card = number ↔
        (region locals candidate rows world pattern).card = number
      rw [region_inclusion]

theorem Ask.unused_extension_iff {Γ : Ctx S} {sort : S.Srt}
    (prefixProblem : EquationStore (Term (signature S captures) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) (world : Finset O)
    (check : Check (Term (signature S captures) Γ sort)) :
    Ask locals (ContextualFrameUnifier.mapProblem (inclusion unused captures) prefixProblem)
        (fun occurrence => (rows occurrence).map locals (inclusion unused captures)) world
        (check.map (instantiate (inclusion unused captures))) ↔
      Ask locals prefixProblem rows world check := by
  constructor
  · intro admitted Future future candidate prefixModel
    have liftedModel := (lifted_prefix_models_iff unused candidate prefixProblem).mpr prefixModel
    have held := admitted (Extra ⊕ Future) (extended unused future)
      (ContextualStoredRows.liftCaptures unused candidate) liftedModel
    have before := (holds_after_capture_transport locals (inclusion unused captures)
      (ContextualStoredRows.liftCaptures unused candidate) rows world check).mp held
    rw [lifted_capture_assignment] at before
    exact (holds_inclusion_iff locals unused candidate rows world check).mp before
  · intro admitted
    exact Ask.transport locals admitted (inclusion unused captures)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardSemantics
