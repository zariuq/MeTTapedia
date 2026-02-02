-- Re-export all modules
import Mettapedia.Logic.StratifiedPLN.Partition
import Mettapedia.Logic.StratifiedPLN.LocalExchangeability
import Mettapedia.Logic.StratifiedPLN.HistogramEstimator
import Mettapedia.Logic.StratifiedPLN.Consistency

/-!
# Stratified PLN: Complete Formalization

This file re-exports all theorems from the Stratified PLN formalization,
providing the complete mathematical justification for why PLN works on
logistic regression tasks.

## Summary

**Main Result**: Stratified PLN is a consistent estimator of P(Y=1|X).

**Proof Structure**:
1. **Partition.lean**: Defines measurable partitions (histogram bins)
2. **LocalExchangeability.lean**: Within-bin exchangeability implies PLN optimality per bin
3. **HistogramEstimator.lean**: Error decomposition for histogram estimator
4. **Consistency.lean**: Main consistency theorem and logistic regression corollary

**Key Theorems**:
- `stratified_pln_consistent`: Error bound 2/(N+2) + L×δ
- `stratified_pln_error_tends_to_zero`: Convergence as N→∞, δ→0
- `pln_works_on_logistic_regression`: Consistent for logistic regression

**Building Blocks (from EvidenceBeta.lean)**:
- `pln_is_bayes_optimal_for_exchangeable`: PLN is optimal for exchangeable binary
- `strength_vs_uniform_difference`: Rate bound O(1/n)

## References

- de Finetti's theorem (Exchangeability → Beta-Bernoulli)
- Györfi et al., "A Distribution-Free Theory of Nonparametric Regression"
- Stone (1977), "Consistent Nonparametric Regression"
-/

namespace Mettapedia.Logic.StratifiedPLN

/-!
## Quick Reference

### Partition (Partition.lean)
- `HistogramBins` - K-bin measurable partition
- `binIndex` - Function mapping points to bins
- `BinEvidence` - Evidence counts per bin

### Local Exchangeability (LocalExchangeability.lean)
- `binPLNStrength` - PLN strength for a bin
- `pln_optimal_within_bin` - PLN is optimal per bin
- `binwise_error_bound` - O(1/n) error bound

### Histogram Estimator (HistogramEstimator.lean)
- `histogramEstimator` - Piecewise-constant PLN estimator
- `LipschitzRegularity` - Lipschitz assumption on true function
- `error_decomposition` - Error = PLN error + variation error

### Consistency (Consistency.lean)
- `stratified_pln_consistent` - Main consistency theorem
- `sigmoid` - Logistic function
- `pln_works_on_logistic_regression` - PLN works on logistic regression
-/

end Mettapedia.Logic.StratifiedPLN
