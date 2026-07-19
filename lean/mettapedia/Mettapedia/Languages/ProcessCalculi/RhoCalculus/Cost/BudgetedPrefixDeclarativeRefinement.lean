import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.BudgetedPrefixPathRefinement
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimePathRefinement

/-!
# Budgeted-prefix refinement to declarative funded steps

The budgeted runner first yields its exact occurrence-bearing `CostPath`.
The runtime-path bridge then supplies one declarative funded-step witness per
firing, retaining every structural normalization seam explicitly.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.GSLT
open Mettapedia.GSLT.Meredith.RhoExample

namespace BudgetedPrefixPathWitness

/-- A budgeted operational witness carries a declarative funded trace of the
same event depth whenever its initial traced state is canonical. -/
theorem refinesDeclarativeTrace
    {fuel searchBudget eventId : Nat}
    {components : List RawTraceComponent} {reverseReceipt : RawReceipt}
    (witness : BudgetedPrefixPathWitness fuel searchBudget eventId components
      reverseReceipt)
    (canonical : TraceComponentsCanonical components)
    (sourceSafe :
      (decodeRawConfig (components.map RawTraceComponent.term)).BinderSafe) :
    DeclarativeCostTrace components witness.finalComponents
      witness.path.depth :=
  witness.path.refinesDeclarativeTrace canonical sourceSafe

end BudgetedPrefixPathWitness

/-- Every supported budgeted run from the canonical initial presentation has
an exact occurrence-bearing path and a same-length declarative funded trace. -/
theorem budgetedCausalPrefix_refinesDeclarativeTrace
    (fuel searchBudget : Nat) {term : RawCostTerm}
    (supported : term.supported = true) :
    ∃ witness : BudgetedPrefixPathWitness fuel searchBudget 0
        (initialTraceComponents term) [],
      DeclarativeCostTrace (initialTraceComponents term)
        witness.finalComponents witness.path.depth := by
  let witness := boundedBudgetedCausalPrefix_pathWitness
    (fuel := fuel) (searchBudget := searchBudget) supported
  have termSafe : term.binderSafe = true :=
    (RawCostTerm.binderSafe_iff_decode term).mpr
      (RawCostTerm.supported_decode_binderSafe supported)
  have sourceSafe := initialTraceComponents_binderSafe termSafe
  exact ⟨witness,
    witness.refinesDeclarativeTrace (initialTraceComponents_canonical term)
      sourceSafe⟩

/-- Every publicly admitted budgeted execution has an occurrence-bearing
runtime path, a same-length declarative funded trace, and a pure-rho rewrite
path with exactly one COMM step per runtime firing. -/
theorem budgetedCausalPrefix_exists_rhoRewritePath
    {signatureName : SignatureNameEncoding String}
    {free : FreeSortContext} (signatureTyped : signatureName.WellSorted free)
    (fuel searchBudget : Nat) {term : RawCostTerm}
    (supported : term.supported = true) :
    ∃ witness : BudgetedPrefixPathWitness fuel searchBudget 0
        (initialTraceComponents term) [],
      ∃ _trace : DeclarativeCostTrace (initialTraceComponents term)
          witness.finalComponents witness.path.depth,
        ∃ path : rhoGSLT.RewritePath
            (CostConfig.eraseCanonical signatureName
              signatureTyped.hashSetFree
              (decodeRawConfig ((initialTraceComponents term).map
                RawTraceComponent.term)))
            (CostConfig.eraseCanonical signatureName
              signatureTyped.hashSetFree
              (decodeRawConfig (witness.finalComponents.map
                RawTraceComponent.term))),
          path.length = witness.path.depth := by
  obtain ⟨witness, trace⟩ :=
    budgetedCausalPrefix_refinesDeclarativeTrace fuel searchBudget supported
  have termSafe : term.binderSafe = true :=
    (RawCostTerm.binderSafe_iff_decode term).mpr
      (RawCostTerm.supported_decode_binderSafe supported)
  have sourceSafe := initialTraceComponents_binderSafe termSafe
  obtain ⟨path, pathLength⟩ :=
    trace.exists_eraseCanonical_rhoRewritePath signatureTyped sourceSafe
  exact ⟨witness, trace, path, pathLength⟩

/-- Every publicly admitted budgeted execution also reaches the pure GSLT
mechanically derived from the authored `rhoCalc` declaration.  The final scope
witness and the same-length rewrite path are produced compositionally through
the occurrence-bearing runtime path and its declarative trace. -/
theorem budgetedCausalPrefix_exists_rhoLanguageDefRewritePath
    {signatureName : SignatureNameEncoding String}
    (signatureClosed : signatureName.MapsToClosedRhoNames)
    (fuel searchBudget : Nat) {term : RawCostTerm}
    (supported : term.supported = true) :
    ∃ witness : BudgetedPrefixPathWitness fuel searchBudget 0
        (initialTraceComponents term) [],
      ∃ _trace : DeclarativeCostTrace (initialTraceComponents term)
          witness.finalComponents witness.path.depth,
        ∃ sourceSafe :
            (decodeRawConfig ((initialTraceComponents term).map
              RawTraceComponent.term)).BinderSafe,
          ∃ finalSafe :
              (decodeRawConfig
                (witness.finalComponents.map RawTraceComponent.term)).BinderSafe,
            ∃ path : rhoLanguageDefGSLT.RewritePath
              ((decodeRawConfig ((initialTraceComponents term).map
                  RawTraceComponent.term))
                |>.eraseCanonicalProcess signatureClosed sourceSafe)
              ((decodeRawConfig
                  (witness.finalComponents.map RawTraceComponent.term))
                |>.eraseCanonicalProcess signatureClosed finalSafe),
              path.length = witness.path.depth := by
  obtain ⟨witness, trace⟩ :=
    budgetedCausalPrefix_refinesDeclarativeTrace fuel searchBudget supported
  have termSafe : term.binderSafe = true :=
    (RawCostTerm.binderSafe_iff_decode term).mpr
      (RawCostTerm.supported_decode_binderSafe supported)
  have sourceSafe := initialTraceComponents_binderSafe termSafe
  obtain ⟨finalSafe, path, pathLength⟩ :=
    trace.exists_eraseCanonical_rhoLanguageDefRewritePath
      signatureClosed sourceSafe
  exact ⟨witness, trace, sourceSafe, finalSafe, path, pathLength⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
