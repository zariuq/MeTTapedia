import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILConversionDevelopmentComplete
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FormationSensitiveMILIotaPreservation

/-!
# Qualified contextual preservation for actual native hypothesis computation

The completed parallel development proves the conversion boundaries of the
unchanged authored beta/iota package. Combining them with declaration-spine
argument recovery discharges contextual preservation for arbitrary admitted
judgments, including their original dependent displayed types.

No normalization, raw execution confluence, or total conversion decision is
asserted. The proof-only completion is not installed as a runtime rule.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace FormationSensitiveMILQualification

open Presentation IntrinsicMILHypothesis
open MILConversionParallel MILConversionCompletion

variable {n : Nat}

/-- Root typing preservation is now derived for the actual rules without
an externally supplied Pi-conversion or redex-typing assumption. -/
theorem rootPreservation : FormationSensitive.RootPreservation IntrinsicMILHypothesis.rules :=
  FormationSensitiveMILIotaPreservation.rootPreservation nativePiConversionBoundary

/-- Every finite contextual run of the actual native package preserves the
original refined judgment. No conversion-boundary premise remains. -/
theorem steps_preserve {context : Tower.Ctx n} {source target displayed : Tower.Tm n}
    (judgment : FormationSensitive.Judgment IntrinsicMILHypothesis.rules context source displayed)
    (steps : ConversionCoherence.StepStar IntrinsicMILHypothesis.rules source target) :
    FormationSensitive.Judgment IntrinsicMILHypothesis.rules context target displayed :=
  FormationSensitiveMILIotaPreservation.steps_preserve nativePiConversionBoundary
    nativeSigmaConversionBoundary judgment steps

/-- Function and dependent-pair constructors remain distinct in authored
conversion, even in open terms containing native eliminations. -/
theorem pi_sigma_disjoint {A C : Tower.Tm n} {B D : Tower.Tm (n + 1)} :
    ¬ AuthoredConv (.pi A B) (.sigma C D) := by
  intro conversion
  obtain ⟨common, first, second⟩ := conversion_join conversion
  obtain ⟨A', B', piShape, _, _⟩ := parStar_pi_decomp first
  obtain ⟨C', D', sigmaShape, _, _⟩ := parStar_sigma_decomp second
  rw [piShape] at sigmaShape
  cases sigmaShape

namespace Examples

theorem primitive_step :
    Step IntrinsicMILHypothesis.rules.headEq primitiveIotaLeft primitiveIotaRight
      IntrinsicMILHypothesis.rules.computation :=
  .root (.declared ⟨.primitive (.var 7) (.var 6) (.var 5) (.var 4) (.var 3)
    (.var 2) (.var 1) (.var 0)⟩)

/-- The enclosing identity introduction retains the original endpoints in
its displayed type while the computation inside its witness reduces. -/
theorem native_reduction_inside_identity :
    FormationSensitive.Judgment IntrinsicMILHypothesis.rules contextSPMPCSourceTargetSymbol
      (.refl primitiveIotaRight)
      (.id primitiveIotaResultType primitiveIotaLeft primitiveIotaLeft) := by
  have original := FormationSensitiveMILElimination.primitiveIota_judgments.1
  have identityJudgment : FormationSensitive.Judgment IntrinsicMILHypothesis.rules
      contextSPMPCSourceTargetSymbol (.refl primitiveIotaLeft)
      (.id primitiveIotaResultType primitiveIotaLeft primitiveIotaLeft) :=
    ⟨original.context, .reflIntro original.typing⟩
  exact steps_preserve identityJudgment (.tail .refl (.congRefl primitive_step))

/-- A genuinely different metadata type cannot be smuggled through the
proof-only completion. Its guard would collapse Pi into a head. -/
def incompatibleMetadata : Tower.Tm n :=
  eliminateApp MILConversionCompletion.Examples.ground MILConversionCompletion.Examples.ground
    MILConversionCompletion.Examples.ground (.const hypothesisName)
    MILConversionCompletion.Examples.ground MILConversionCompletion.Examples.ground
    MILConversionCompletion.Examples.ground
    (primitiveApp (.pi MILConversionCompletion.Examples.ground MILConversionCompletion.Examples.ground)
      MILConversionCompletion.Examples.ground MILConversionCompletion.Examples.ground
      MILConversionCompletion.Examples.ground MILConversionCompletion.Examples.ground)

theorem incompatible_metadata_rejected {result : Tower.Tm n} :
    ¬ Root incompatibleMetadata result := by
  intro root
  cases root with
  | primitive sorts _ _ _ => exact nativePiConversionBoundary.headDisjoint sorts

def primitiveChangedSymbol : Tower.Tm 8 :=
  .app (.app (.app (.var 4) (.var 2)) (.var 1)) (.var 1)

theorem changed_primitive_result_rejected :
    ¬ Root primitiveIotaLeft primitiveChangedSymbol := by
  intro altered
  have same := Root.target_unique (Root.of_iota primitiveIotaReceipt.evidence) altered
  exact (by decide : primitiveIotaRight ≠ primitiveChangedSymbol) same

theorem duplicated_chain_result_rejected :
    ¬ Root chainIotaLeft FormationSensitiveMILElimination.chainIotaDuplicatedLater := by
  intro altered
  have same := Root.target_unique (Root.of_iota chainIotaReceipt.evidence) altered
  exact (by decide : chainIotaRight ≠ FormationSensitiveMILElimination.chainIotaDuplicatedLater) same

theorem native_pi_head_rejected {domain : Tower.Tm n} {codomain : Tower.Tm (n + 1)}
    {head : Tower.Head} : ¬ AuthoredConv (.pi domain codomain) (.head head) :=
  nativePiConversionBoundary.headDisjoint

theorem native_sigma_head_rejected {domain : Tower.Tm n} {codomain : Tower.Tm (n + 1)}
    {head : Tower.Head} : ¬ AuthoredConv (.sigma domain codomain) (.head head) :=
  nativeSigmaConversionBoundary.headDisjoint

end Examples

#print axioms rootPreservation
#print axioms steps_preserve
#print axioms pi_sigma_disjoint
#print axioms Examples.primitive_step
#print axioms Examples.native_reduction_inside_identity
#print axioms Examples.incompatible_metadata_rejected
#print axioms Examples.changed_primitive_result_rejected
#print axioms Examples.duplicated_chain_result_rejected
#print axioms Examples.native_pi_head_rejected
#print axioms Examples.native_sigma_head_rejected

end FormationSensitiveMILQualification
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
