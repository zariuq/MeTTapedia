import Mettapedia.Logic.PLNFirstOrder.Basic
import Mettapedia.Logic.PLNFirstOrder.SatisfyingSet
import Mettapedia.Logic.PLNFirstOrder.QuantifierSemantics
import Mettapedia.Logic.PLNFirstOrder.ThirdOrderQuantifierSemantics
import Mettapedia.Logic.PLNFirstOrder.WeaknessConnection
import Mettapedia.Logic.PLNFirstOrder.FoundationBridge
import Mettapedia.Logic.PLNFirstOrder.Soundness
import Mettapedia.Logic.PLNFirstOrder.Infinite
import Mettapedia.Logic.PLNFirstOrder.InfiniteSoundness
import Mettapedia.Logic.PLNFirstOrder.InfiniteCanary
import Mettapedia.Logic.PLNFirstOrder.InfiniteRegression
import Mettapedia.Logic.PLNFirstOrder.FuzzyMeasureCore
import Mettapedia.Logic.PLNFirstOrder.SugenoIntegral
import Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierSemanticsInf
import Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierSoundnessInf
import Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierCanaryInf
import Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierRegressionInf
import Mettapedia.Logic.PLNFirstOrder.ChoquetQuantifierSemantics
import Mettapedia.Logic.PLNFirstOrder.ChoquetQuantifierCanary
import Mettapedia.Logic.PLNFirstOrder.ChoquetQuantifierRegression
import Mettapedia.Logic.PLNFirstOrder.GradedQuantifierSpecialization
import Mettapedia.Logic.PLNFirstOrder.GradedQuantifierCanary
import Mettapedia.Logic.PLNFirstOrder.GradedQuantifierRegression
import Mettapedia.Logic.PLNFirstOrder.FuzzyDomainQuantifiers
import Mettapedia.Logic.PLNFirstOrder.FuzzyDomainQuantifierCanary
import Mettapedia.Logic.PLNFirstOrder.FuzzyDomainQuantifierRegression
import Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierSemanticsFin
import Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierAlgorithmTheoremsFin
import Mettapedia.Logic.PLNFirstOrder.FuzzyITVBridgeFin
import Mettapedia.Logic.PLNFirstOrder.QuantifierCanary
import Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierWorkedExamplesFin
import Mettapedia.Logic.PLNFirstOrder.QuantifierRegression
import Mettapedia.Logic.PLNFirstOrder.FuzzySyllogismCanaryFin
import Mettapedia.Logic.PLNFirstOrder.FuzzySyllogismRegressionFin

/-!
# PLN First-Order Quantifiers

Complete formalization of PLN first-order quantifiers via:
- **Subobject classifier pattern**: SatisfyingSet as χ : U → Ω where Ω = Evidence (Frame)
- **Goertzel's weakness theory**: ∀x:P(x) = weakness({(u,v) | P(u) ∧ P(v)})
- **Integration with Foundation**: Architecture for full FOL bridge
- **Arbitrary-domain infinitary semantics**: exported through `PLNFirstOrder.Infinite`
- **Arbitrary-domain fuzzy semantics**: exported through `FuzzyMeasureCore`,
  `SugenoIntegral`, `ChoquetQuantifierSemantics`,
  `GradedQuantifierSpecialization`,
  `FuzzyQuantifierSemanticsInf`, and `FuzzyDomainQuantifiers`
- **Finite/counting fuzzy semantics**: now explicitly packaged through
  `FuzzyQuantifierSemanticsFin` and companion `...Fin` wrappers

## Main Exports

- `SatisfyingSet` - Frame-valued predicates (characteristic morphisms)
- `forAllEval` - Universal quantifier evaluation via weakness
- `thereExistsEval` - Existential quantifier evaluation via De Morgan dual
- `SatisfyingSetInf` / `forAllEvalInf` / `thereExistsEvalInf` - arbitrary-domain
  weakness-based quantifier semantics
- `forAllEvalExtInf` / `thereExistsEvalExtInf` - arbitrary-domain extensional
  quantifier views
- `FuzzyQuantifierParamsInf` / `FuzzyProfile` / `FuzzyCapacity` - arbitrary-domain
  fuzzy quantifier core
- `nearOneMassInf` / `nearZeroMassInf` / `fuzzyExistsScoreInf` /
  `fuzzyForAllHoldsInf` / `fuzzyThereExistsHoldsInf` - arbitrary-domain fuzzy
  quantifier semantics
  - `choquetScoreInf` / `choquetForAllHoldsInf` / `choquetThereExistsHoldsInf` -
  Choquet-style arbitrary-domain fuzzy semantics
- `GradedQuantifierSemantics` / `sugenoGradedQuantifierSemantics` /
  `choquetGradedQuantifierSemantics` - shared graded quantifier specialization
  layer with explicit Sugeno and Choquet instances
- `GradedQuantifierCanary` / `GradedQuantifierRegression` - direct canary and
  regression surfaces for the shared graded layer itself
- `domainRestrict` / `eqOnDomain` / `fuzzyAllOnDomainHoldsInf` /
  `choquetAllOnDomainHoldsInf` - fuzzy-domain restriction and relativization layer
- `FuzzyQuantifierParamsFin` / `nearOneFractionFin` / `nearZeroFractionFin` /
  `fuzzyExistsScoreFin` - finite/counting fuzzy quantifier instance
- Key theorems:
  - `forAll_is_weakness_of_diagonal` - Goertzel's insight (✅ proven)
  - `forAllEval_mono_weights` - Monotonicity (✅ proven)
  - `main_theorem_3_de_morgan` - Existential/universal duality (✅ proven)
  - `main_theorem_5_functoriality` - Functoriality (✅ proven)
  - `main_theorem_1_forAll_is_weakness_inf` / `main_theorem_2_monotonicity_inf` /
    `main_theorem_3_de_morgan_inf` / `main_theorem_5_functoriality_inf` -
    arbitrary-domain theorem surface
  - `main_theorem_1_fuzzy_exists_is_nearOneMass_inf` /
    `main_theorem_2_fuzzy_monotonicity_inf` /
    `main_theorem_3_fuzzy_complement_transport_inf` -
    arbitrary-domain fuzzy theorem surface
  - `choquetScoreInf_mono` / `choquetScoreInf_constantOne_eq_one` -
    Choquet-style theorem surface
  - `scoreOnDomain_eq_of_eqOnDomain` /
    `forAllOnDomainHolds_mono_of_pointwise` -
    shared graded specialization theorems
  - `canary_graded_nat_sugeno_lives_on` /
    `canary_graded_nat_choquet_singleton_not_strict` -
    direct graded canaries for the shared Sugeno/Choquet spine
  - `fuzzyExistsOnDomainScoreInf_eq_of_eqOnDomain` /
    `choquetOnDomainScoreInf_eq_of_eqOnDomain` -
    fuzzy-domain "living on the domain" theorem surface
  - `nearOneMassInf_counting_eq_nearOneFractionFin` /
    `fuzzyIntervalHoldsInf_counting_iff_fuzzyIntervalHoldsFin` -
    exact finite-to-infinitary reduction theorems for the counting instance
  - `canary_ch11_exists_deMorgan` / `canary_ch11_existential_generalization_ext` /
    `canary_ch11_universal_specification_ext` - literature-aligned quantifier canaries
  - `canary_inf_nat_exists_deMorgan` / `canary_inf_nat_weight_monotonicity` /
    `canary_inf_nat_parity_non_equivalence_extensional` - genuine infinite-domain canaries
  - `canary_inf_fuzzy_nat_deMorgan` / `canary_inf_fuzzy_nat_monotonicity` /
    `canary_inf_fuzzy_nat_support_contrast` - genuine infinite-domain fuzzy canaries
  - `canary_choquet_nat_parity` / `canary_choquet_nat_singleton` -
    Choquet infinitary canaries
  - `canary_fuzzy_domain_nat_proxy_lives_on` /
    `canary_fuzzy_domain_nat_choquet_lives_on` -
    fuzzy-domain infinitary canaries

## Status

**Proven (no sorries)**:
- Core connection to weakness theory ✅
- Monotonicity properties ✅
- De Morgan existential duality ✅
- Functoriality ✅
- Basic properties (constantTrue, constantFalse) ✅
- Empty-domain vacuity for extensional quantifiers ✅
- Arbitrary-domain theorem/canary/regression surface ✅
- Arbitrary-domain fuzzy theorem/canary/regression surface ✅
- Choquet infinitary fuzzy branch ✅
- Shared graded specialization branch ✅
- Fuzzy-domain restriction / relativization branch ✅
- Finite/counting fuzzy layer explicitly rebased as an instance ✅

**Open direction**:
- Frame-distributivity formulation for the `isTrue`-filtered weakness quantifier semantics
- Higher-order / WM / Henkin promotion is still future work after this arbitrary-domain
  FOL and fuzzy-FOL cleanup

## Build

```bash
cd /home/zar/claude/lean-projects/mettapedia
ulimit -v 6291456 && lake build Mettapedia.Logic.PLNFirstOrder
```

## References

- Plan file: /home/zar/.claude/plans/hashed-baking-bumblebee.md
- Goertzel, "Weakness and Its Quantale"
- QuantaleWeakness.lean (820+ proven lines)
- EvidenceQuantale.lean (Evidence with Frame structure)
-/
