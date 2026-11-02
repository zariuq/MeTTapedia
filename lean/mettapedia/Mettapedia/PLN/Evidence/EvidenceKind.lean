/-!
# Evidence Kind — Epistemic Classification of Evidence Items

A general-purpose enum classifying the epistemic origin of an evidence item.
This is a WM-PLN concept, not specific to any application domain.

The core distinction (O'Hagan, "Expert Knowledge Elicitation," Am. Stat. 2019):
empirical counts and expert guesses are DIFFERENT TYPES of evidence. Silently
mixing "P=0.8 from 100 trials" with "I believe P=0.8" is a foundational error.

## References

- O'Hagan, A. "Expert Knowledge Elicitation: Subjective but Scientific."
  The American Statistician, 73(sup1), 69–81, 2019.
- Morita, S., Thall, P.F., Müller, P. "Determining the effective sample size
  of a parametric prior." Biometrics, 64(2), 595–602, 2008.
- Colson, A.R., Cooke, R.M. "Expert Elicitation: Using the Classical Model
  to Validate Experts' Judgments." REEP, 12(1), 113–132, 2018.
- EFSA. "Guidance on Expert Knowledge Elicitation in Food and Feed Safety
  Risk Assessment." EFSA Journal, 12(6):3734, 2014.
-/

namespace Mettapedia.PLN.Evidence

/-- Epistemic classification of an evidence item.

    An origin label for an assessment layer, not a proof certificate or an
    independence license. A checked derivation and observations of a checker run
    have different meanings: only the latter are empirical performance data.

    Consumers may use this to:
    - assign different effective sample sizes by default
    - flag when a conclusion rests entirely on elicited evidence
    - separate calibrated from uncalibrated inputs in aggregation -/
inductive EvidenceKind where
  | empirical          -- identified observations or recorded test outcomes; excludes proof multiplicity
  | expertElicited     -- structured expert judgment (SHELF/Cooke protocol)
  | modelDerived       -- output of a computational model (LLM, classifier, ATP)
  | textInterpreted    -- human/LLM interpretation of natural-language source
  | logicalDerivation  -- logical-inference origin; proof authority requires a separate checked witness
  deriving Repr, BEq, DecidableEq

end Mettapedia.PLN.Evidence
