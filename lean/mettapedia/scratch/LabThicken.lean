import Mettapedia.GSLT.LanguageDef.CostRegionTree

namespace Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- PROBE: thickening ambient binders leaves the free variables alone. -/
theorem CostStaticBinderThinning.thickenAmbientBVars_freeFvarNames
    {source : CIGSLT} {color : CostStaticColor}
    {sourceBound targetBound : List TypeExpr}
    (thinning : CostStaticBinderThinning source color sourceBound targetBound) :
    ∀ pattern depth,
      (thinning.thickenAmbientBVars depth pattern).freeFvarNames =
        pattern.freeFvarNames := by
  intro pattern
  induction pattern using Pattern.inductionOn with
  | hbvar index => intro depth; simp [thickenAmbientBVars, Pattern.freeFvarNames]
  | hfvar name => intro depth; simp [thickenAmbientBVars, Pattern.freeFvarNames]
  | happly constructor arguments inductionHypothesis =>
      intro depth
      simp only [thickenAmbientBVars, Pattern.freeFvarNames, List.flatMap_map]
      apply List.flatMap_congr
      intro argument membership
      exact inductionHypothesis argument membership depth
  | hlambda binder body inductionHypothesis =>
      intro depth
      simp only [thickenAmbientBVars, Pattern.freeFvarNames]
      exact inductionHypothesis (depth + 1)
  | hmultiLambda arity binders body inductionHypothesis =>
      intro depth
      simp only [thickenAmbientBVars, Pattern.freeFvarNames]
      exact inductionHypothesis (depth + arity)
  | hsubst body replacement bodyHypothesis replacementHypothesis =>
      intro depth
      simp only [thickenAmbientBVars, Pattern.freeFvarNames]
      rw [bodyHypothesis (depth + 1), replacementHypothesis depth]
  | hcollection collectionType elements rest inductionHypothesis =>
      intro depth
      simp only [thickenAmbientBVars, Pattern.freeFvarNames, List.flatMap_map]
      congr 1
      apply List.flatMap_congr
      intro element membership
      exact inductionHypothesis element membership depth

end Mettapedia.GSLT.LanguageDef
