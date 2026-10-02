import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedFunding
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationPathConservation

/-!
# Operational consequences of generated source admission

The certifying interpretation links independently erased generated syntax
to the established pure rho carrier. Exact isolated funding additionally
produces a genuine funded step with physical inventory depletion and one
pure COMM step. The generated contractum comparison is a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

theorem decoded_components_binderSafe {term : CostTerm LiteralAuthority}
    (safe : term.BinderSafe) : term.components.BinderSafe := by
  cases term with
  | nil => simp [CostTerm.components, CostConfig.BinderSafe]
  | signed process signature =>
    simpa [CostTerm.components, CostConfig.BinderSafe] using safe
  | par left right =>
    cases safe with
    | par leftSafe rightSafe =>
      intro component membership
      rcases Multiset.mem_add.mp membership with leftMember | rightMember
      · exact decoded_components_binderSafe leftSafe component leftMember
      · exact decoded_components_binderSafe rightSafe component rightMember
  | drop name => simpa [CostTerm.components, CostConfig.BinderSafe] using safe
  | purse location stack => simpa [CostTerm.components, CostConfig.BinderSafe] using safe

theorem GeneratedConfigImage.erase_config_structural {location : CostName LiteralAuthority}
    {source : Pattern} {term : CostTerm LiteralAuthority}
    (image : GeneratedConfigImage location source term)
    (encoding : SignatureNameEncoding LiteralAuthority)
    (pure : ∀ signature, HashSetFree (encoding signature)) :
    StructuralCongruence (CostConfig.eraseCanonical encoding pure term.components)
      (eraseGenerated source) :=
  StructuralCongruence.trans _ _ _
    (CostTerm.eraseCanonical_components_structural encoding pure term)
    (image.erase_structural encoding)

theorem fundedPair_physical_and_pure (location : CostName LiteralAuthority)
    (locationFree : location.purseInventory = 0) (locationSupported : location.RuntimeSupported)
    (fuel : Nat) (source : Pattern) (decoded : DecodedConfig source)
    (accepted : fundedPair? location locationFree locationSupported fuel source = some decoded)
    (encoding : SignatureNameEncoding LiteralAuthority)
    (closed : encoding.MapsToClosedRhoNames) :
    ∃ (spend : CostSig LiteralAuthority) (target : CostConfig LiteralAuthority)
        (targetSafe : target.BinderSafe),
      CostStep decoded.val.components location spend target ∧
      target.ResourceSeparated ∧
      target.physicalPurseCells < decoded.val.components.physicalPurseCells ∧
      decoded.val.components.storedSignatures = target.storedSignatures + spend ∧
      decoded.val.components.physicalPurseOccurrences = target.physicalPurseOccurrences ∧
      rhoLanguageDefGSLT.Step
        (decoded.val.components.eraseCanonicalProcess closed
          (decoded_components_binderSafe decoded.property.2.1))
        (target.eraseCanonicalProcess closed targetSafe) := by
  obtain ⟨_image, spend, target, step, separated⟩ :=
    fundedPair_sound location locationFree locationSupported fuel source decoded accepted
  have sourceSafe := decoded_components_binderSafe decoded.property.2.1
  exact ⟨spend, target, step.preserves_binderSafe sourceSafe, step, separated,
    step.physical_cells_strictly_decrease decoded.property.1,
    step.stored_signatures_balance decoded.property.1,
    step.physical_purse_occurrences_preserved decoded.property.1,
    step.eraseCanonical_rhoLanguageDefGSLTStep closed sourceSafe⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
