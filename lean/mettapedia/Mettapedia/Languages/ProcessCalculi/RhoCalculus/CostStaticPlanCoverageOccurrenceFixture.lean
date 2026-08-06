import Mettapedia.GSLT.LanguageDef.CostStaticPlanOccurrenceCoverage
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanPairCanary

/-! # Typed occurrence for the breadth coverage fixture -/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoverageCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryRouteBreadthCanary
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanPairCanary

/-- The breadth occurrence as a typed generated occurrence with its exact
authored reflective origin at the base colour. -/
noncomputable def rhoBreadthTypedOccurrence :
    CostTypedGeneratorOccurrence rhoCIGSLT rhoBreadth_generator where
  witness := rhoBreadthGeneratorWitness
  erasesTo := Subsingleton.elim _ _
  origin :=
    (⟨.base, rhoReflectivePresentation.toReflectivePresentationDecl,
      rhoPairSourceReflectiveDecl_mem, rfl⟩ :
      CostReflectiveDeclarationOrigin rhoCIGSLT _)

/-- The retained origin's source declaration is rho's sole reflective
presentation. -/
theorem rhoBreadthTypedOccurrence_sourceDeclaration :
    rhoBreadthTypedOccurrence.sourceDeclaration =
      .reflective rhoReflectivePresentation.toReflectivePresentationDecl :=
  rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostStaticPlanCoverageCanary
