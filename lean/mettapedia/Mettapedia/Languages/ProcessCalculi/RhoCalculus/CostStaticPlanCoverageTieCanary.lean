import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoverageCanary

/-!
# Same-declaration localization rejection canary

Declaration equality is necessary but insufficient for a changed site: the
cell endpoints must also localize to the selected occurrence endpoints.  This
small module keeps that negative boundary independent of the larger coverage
fixture elaboration.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoverageTieCanary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanPairCanary
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoverageCanary

/-- The rejected cell and selected occurrence do have the same authored
reflective declaration; localization, not declaration classification, rejects
the false match. -/
theorem rhoCoverage_wrongName_sameDeclaration :
    rhoPairNameCell.sourceDeclaration =
      rhoBreadthTypedOccurrence.sourceDeclaration := rfl

/-- No one-hole context turns the cell's right endpoint `a` into the selected
right endpoint `0`. -/
theorem rhoCoverage_sameDeclaration_wrongName_not_localizable
    (context : OneHoleContext) :
    (.fvar "0" : Pattern) ≠ context.fill rhoPairNameCell.second.pattern := by
  intro localized
  rw [rhoPairNameCell_second_pattern] at localized
  cases context with
  | hole => simp [OneHoleContext.fill] at localized
  | apply => cases localized
  | lambda => cases localized
  | multiLambda => cases localized
  | substBody => cases localized
  | substReplacement => cases localized
  | collection => cases localized

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoverageTieCanary
