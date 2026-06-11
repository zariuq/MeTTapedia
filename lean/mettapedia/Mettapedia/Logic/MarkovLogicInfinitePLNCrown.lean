import Mettapedia.Logic.MarkovLogicInfiniteGridExample
import Mettapedia.Logic.MarkovLogicInfiniteReinforcedLineExample

/-!
# Infinite MLN PLN Crown

This module packages the first concrete contrast between a DLR phase-coexistence
model with positive PLN strict-width semantics and a Dobrushin-regime model
whose query envelope collapses.
-/

namespace Mettapedia.Logic.MarkovLogicInfinitePLNCrown

open Mettapedia.Logic.MarkovLogicInfiniteGridExample
open Mettapedia.Logic.MarkovLogicInfiniteReinforcedLineExample
open Mettapedia.Logic.MarkovLogicInfiniteCredalBridge
open Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal

/-- Paper-facing record for the first concrete infinite DLR/PLN contrast.

The left side is a geometrically reinforced half-line with positive strict-width
readout at the origin.  The right side is the zero-weight zero-field grid, where
the same origin-spin style query has a collapsed lower/upper envelope under the
Dobrushin budget. -/
structure ConcreteDLRPLNContrast where
  reinforcedLine_envelopeWidth_pos :
    0 < infiniteMLNQueryEnvelopeWidth
      (reinforcedLineClassicalSpec reinforcedLineGeometricEdgeLogWeight)
      lineOriginSpinUpQuery
  reinforcedLine_widthComplement_lt_one :
    infiniteMLNQueryEnvelopeWidthComplement
      (reinforcedLineClassicalSpec reinforcedLineGeometricEdgeLogWeight)
      lineOriginSpinUpQuery < 1
  reinforcedLine_outcomeCredalWidth_pos :
    0 < credalEnvelopeWidth
      (dlrQueryOutcomeCredalSet
        (reinforcedLineClassicalSpec reinforcedLineGeometricEdgeLogWeight)
        lineOriginSpinUpQuery)
      (PrecisePrevision.FiniteWeights.atomGamble true)
  zeroWeightGrid_originSpinUp_collapse :
    infiniteMLNLowerQueryEnvelope
        (gridZeroFieldClassicalSpec 0) gridOriginSpinUpQuery =
      infiniteMLNUpperQueryEnvelope
        (gridZeroFieldClassicalSpec 0) gridOriginSpinUpQuery

/-- Concrete crown theorem: geometrically reinforced half-line couplings yield
positive PLN strict-width at the origin, while the zero-weight zero-field grid is
in the Dobrushin collapse regime for the analogous origin-spin query. -/
theorem reinforcedLineGeometric_strictWidth_and_zeroWeightGrid_collapse :
    (0 < infiniteMLNQueryEnvelopeWidth
          (reinforcedLineClassicalSpec reinforcedLineGeometricEdgeLogWeight)
          lineOriginSpinUpQuery ∧
      infiniteMLNQueryEnvelopeWidthComplement
          (reinforcedLineClassicalSpec reinforcedLineGeometricEdgeLogWeight)
          lineOriginSpinUpQuery < 1 ∧
        0 < credalEnvelopeWidth
          (dlrQueryOutcomeCredalSet
            (reinforcedLineClassicalSpec reinforcedLineGeometricEdgeLogWeight)
            lineOriginSpinUpQuery)
          (PrecisePrevision.FiniteWeights.atomGamble true)) ∧
      infiniteMLNLowerQueryEnvelope
          (gridZeroFieldClassicalSpec 0) gridOriginSpinUpQuery =
        infiniteMLNUpperQueryEnvelope
          (gridZeroFieldClassicalSpec 0) gridOriginSpinUpQuery := by
  refine ⟨reinforcedLineGeometric_originSpinUp_plnStrictInterval, ?_⟩
  exact gridZeroField_originSpinUp_queryEnvelope_precise_of_dobrushin
    (w := 0) (by norm_num)

/-- Paper-facing packaged form of
`reinforcedLineGeometric_strictWidth_and_zeroWeightGrid_collapse`. -/
theorem reinforcedLineGeometric_zeroWeightGrid_concreteDLRPLNContrast :
    ConcreteDLRPLNContrast := by
  rcases reinforcedLineGeometric_strictWidth_and_zeroWeightGrid_collapse with
    ⟨hLine, hGrid⟩
  exact
    { reinforcedLine_envelopeWidth_pos := hLine.1
      reinforcedLine_widthComplement_lt_one := hLine.2.1
      reinforcedLine_outcomeCredalWidth_pos := hLine.2.2
      zeroWeightGrid_originSpinUp_collapse := hGrid }

/-- Paper-facing alias: the reinforced line has positive origin-spin envelope
width. -/
theorem reinforcedLineGeometric_originSpinUp_queryEnvelopeWidth_pos :
    0 < infiniteMLNQueryEnvelopeWidth
      (reinforcedLineClassicalSpec reinforcedLineGeometricEdgeLogWeight)
      lineOriginSpinUpQuery :=
  reinforcedLineGeometric_zeroWeightGrid_concreteDLRPLNContrast
    |>.reinforcedLine_envelopeWidth_pos

/-- Paper-facing alias: the reinforced line has non-precise PLN confidence
readout for the origin-spin query. -/
theorem reinforcedLineGeometric_originSpinUp_widthComplement_lt_one :
    infiniteMLNQueryEnvelopeWidthComplement
      (reinforcedLineClassicalSpec reinforcedLineGeometricEdgeLogWeight)
      lineOriginSpinUpQuery < 1 :=
  reinforcedLineGeometric_zeroWeightGrid_concreteDLRPLNContrast
    |>.reinforcedLine_widthComplement_lt_one

/-- Paper-facing alias: the zero-weight zero-field grid collapses the
origin-spin query envelope. -/
theorem zeroWeightGrid_originSpinUp_queryEnvelope_collapse :
    infiniteMLNLowerQueryEnvelope
        (gridZeroFieldClassicalSpec 0) gridOriginSpinUpQuery =
      infiniteMLNUpperQueryEnvelope
        (gridZeroFieldClassicalSpec 0) gridOriginSpinUpQuery :=
  reinforcedLineGeometric_zeroWeightGrid_concreteDLRPLNContrast
    |>.zeroWeightGrid_originSpinUp_collapse

end Mettapedia.Logic.MarkovLogicInfinitePLNCrown
