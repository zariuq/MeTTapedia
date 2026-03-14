import Mettapedia.Logic.PLNFirstOrder.FuzzyITVBridge
import Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierSemanticsFin

/-!
# Finite ITV Fuzzy Quantifier Bridge

Finite/counting ITV-coordinate bridge for Chapter-11 fuzzy quantifier semantics.
This is the explicit finite-domain ITV surface; the arbitrary-domain fuzzy layer
now lives in `FuzzyQuantifierSemanticsInf`.
-/

namespace Mettapedia.Logic.PLNFirstOrder

abbrev itvLowerProfileFin := @itvLowerProfile
abbrev itvUpperProfileFin := @itvUpperProfile
noncomputable abbrev itvStrengthProfileFin := @itvStrengthProfile
abbrev itvCredibilityProfileFin := @itvCredibilityProfile
noncomputable abbrev itvWidthProfileFin := @itvWidthProfile
noncomputable abbrev itvStrengthComplementProfileFin := @itvStrengthComplementProfile

abbrev nearOneFractionFin_lower_le_strength := @nearOneFraction_lower_le_strength
abbrev nearOneFractionFin_strength_le_upper := @nearOneFraction_strength_le_upper
abbrev fuzzyIntervalHoldsFin_strength_of_lower_upper := @fuzzyIntervalHolds_strength_of_lower_upper
abbrev fuzzyIntervalHoldsFin_itvLower := @fuzzyIntervalHolds_itvLower
abbrev fuzzyIntervalHoldsFin_itvUpper := @fuzzyIntervalHolds_itvUpper
abbrev fuzzyIntervalHoldsFin_itvStrength := @fuzzyIntervalHolds_itvStrength
abbrev fuzzyIntervalHoldsFin_itvCredibility := @fuzzyIntervalHolds_itvCredibility
abbrev fuzzyIntervalHoldsFin_itvWidth := @fuzzyIntervalHolds_itvWidth
abbrev fuzzyExistsScoreFin_pos_of_itvStrengthWitness := @fuzzyExistsScore_pos_of_itvStrengthWitness
abbrev nearOneFin_itvStrength_of_fuzzyForAll_eq_one := @nearOne_itvStrength_of_fuzzyForAll_eq_one
abbrev fuzzyThereExistsHoldsFin_itvStrength_iff_exchange :=
  @fuzzyThereExistsHolds_itvStrength_iff_exchange
abbrev ch11_itv_rule_family_coreFin := @ch11_itv_rule_family_core

end Mettapedia.Logic.PLNFirstOrder
