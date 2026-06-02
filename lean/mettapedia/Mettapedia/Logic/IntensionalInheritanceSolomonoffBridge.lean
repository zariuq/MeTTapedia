import Mettapedia.Logic.IntensionalInheritance
import Mettapedia.Logic.UniversalPrediction

/-!
# Intensional Inheritance ↔ Solomonoff / Universal Mixture Bridge

This module connects Chapter-12-style intensional inheritance to the Chapter-3
universal-mixture conditional semantics.

Core interpretation:

- extensional inheritance at context `x`:
  `Pξ(W | F,x) = ξ(x ++ F ++ W) / ξ(x ++ F)`
- prior for `W` at context `x`:
  `Pξ(W | x) = ξ(x ++ W) / ξ(x)`
- intensional inheritance:
  `log₂ ( Pξ(W|F,x) / Pξ(W|x) )`

encoded via `logRatioInformationGainFromEvidence`.
-/

namespace Mettapedia.Logic.IntensionalInheritance

open Mettapedia.Logic.UniversalPrediction
open Mettapedia.Logic.SolomonoffPrior

abbrev BinString := Mettapedia.Logic.SolomonoffPrior.BinString
abbrev Semimeasure := Mettapedia.Logic.SolomonoffInduction.Semimeasure

/-- Universal-mixture prior term `Pξ(W | x)`. -/
noncomputable def priorFromConditional
    (ξ : Semimeasure) (x W : BinString) : ℝ :=
  (conditionalENN ξ W x).toReal

/-- Universal-mixture extensional inheritance term `Pξ(W | F,x)`. -/
noncomputable def extensionalFromConditional
    (ξ : Semimeasure) (x F W : BinString) : ℝ :=
  (conditionalENN ξ W (x ++ F)).toReal

/-- Universal-mixture intensional inheritance as log-ratio information gain:
`log₂(Pξ(W|F,x) / Pξ(W|x))` encoded via
`logRatioInformationGainFromEvidence`. -/
noncomputable def intensionalFromConditional
    (ξ : Semimeasure) (x F W : BinString) : ℝ :=
  logRatioInformationGainFromEvidence
    (extensionalFromConditional ξ x F W)
    (priorFromConditional ξ x W)

/-- Main bridge theorem: intensional inheritance equals the base-2 log ratio
of universal-mixture conditionals when both conditionals are positive. -/
theorem intensionalFromConditional_eq_log2_ratio
    (ξ : Semimeasure) (x F W : BinString)
    (hPrior : 0 < priorFromConditional ξ x W)
    (hExt : 0 < extensionalFromConditional ξ x F W) :
    intensionalFromConditional ξ x F W =
      Real.log
        (extensionalFromConditional ξ x F W / priorFromConditional ξ x W) /
      Real.log 2 := by
  unfold intensionalFromConditional
  exact logRatioInformationGainFromEvidence_eq_log2_ratio hExt hPrior

/-- Specialized bridge for the generic Bayes mixture `ξ = xiSemimeasure ν w`. -/
theorem intensionalFromXiSemimeasure_eq_log2_ratio
    {ι : Type*} (ν : ι → Semimeasure) (w : ι → ENNReal)
    (hw : (∑' i, w i) ≤ 1)
    (x F W : BinString)
    (hPrior : 0 < priorFromConditional (xiSemimeasure ν w hw) x W)
    (hExt : 0 < extensionalFromConditional (xiSemimeasure ν w hw) x F W) :
    intensionalFromConditional (xiSemimeasure ν w hw) x F W =
      Real.log
        (extensionalFromConditional (xiSemimeasure ν w hw) x F W /
          priorFromConditional (xiSemimeasure ν w hw) x W) /
      Real.log 2 :=
  intensionalFromConditional_eq_log2_ratio
    (ξ := xiSemimeasure ν w hw) x F W hPrior hExt

/-- Specialized bridge for the canonical geometric universal mixture `xiGeomSemimeasure`. -/
theorem intensionalFromXiGeom_eq_log2_ratio
    (ν : ℕ → Semimeasure)
    (x F W : BinString)
    (hPrior : 0 < priorFromConditional (xiGeomSemimeasure ν) x W)
    (hExt : 0 < extensionalFromConditional (xiGeomSemimeasure ν) x F W) :
    intensionalFromConditional (xiGeomSemimeasure ν) x F W =
      Real.log
        (extensionalFromConditional (xiGeomSemimeasure ν) x F W /
          priorFromConditional (xiGeomSemimeasure ν) x W) /
      Real.log 2 :=
  intensionalFromConditional_eq_log2_ratio
    (ξ := xiGeomSemimeasure ν) x F W hPrior hExt

end Mettapedia.Logic.IntensionalInheritance
