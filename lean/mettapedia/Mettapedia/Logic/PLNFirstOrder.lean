import Mettapedia.Logic.PLNFirstOrder.Basic
import Mettapedia.Logic.PLNFirstOrder.SatisfyingSet
import Mettapedia.Logic.PLNFirstOrder.QuantifierSemantics
import Mettapedia.Logic.PLNFirstOrder.ThirdOrderQuantifierSemantics
import Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierSemantics
import Mettapedia.Logic.PLNFirstOrder.FuzzyITVBridge
import Mettapedia.Logic.PLNFirstOrder.FuzzySyllogismCanary
import Mettapedia.Logic.PLNFirstOrder.WeaknessConnection
import Mettapedia.Logic.PLNFirstOrder.FoundationBridge
import Mettapedia.Logic.PLNFirstOrder.Soundness
import Mettapedia.Logic.PLNFirstOrder.QuantifierCanary
import Mettapedia.Logic.PLNFirstOrder.QuantifierWorkedExamples
import Mettapedia.Logic.PLNFirstOrder.QuantifierRegression
import Mettapedia.Logic.PLNFirstOrder.FuzzySyllogismRegression

/-!
# PLN First-Order Quantifiers

Complete formalization of PLN first-order quantifiers via:
- **Subobject classifier pattern**: SatisfyingSet as χ : U → Ω where Ω = Evidence (Frame)
- **Goertzel's weakness theory**: ∀x:P(x) = weakness({(u,v) | P(u) ∧ P(v)})
- **Integration with Foundation**: Architecture for full FOL bridge

## Main Exports

- `SatisfyingSet` - Frame-valued predicates (characteristic morphisms)
- `forAllEval` - Universal quantifier evaluation via weakness
- `thereExistsEval` - Existential quantifier evaluation via De Morgan dual
- Key theorems:
  - `forAll_is_weakness_of_diagonal` - Goertzel's insight (✅ proven)
  - `forAllEval_mono_weights` - Monotonicity (✅ proven)
  - `main_theorem_3_de_morgan` - Existential/universal duality (✅ proven)
  - `main_theorem_5_functoriality` - Functoriality (✅ proven)
  - `canary_ch11_exists_deMorgan` / `canary_ch11_existential_generalization_ext` /
    `canary_ch11_universal_specification_ext` - literature-aligned quantifier canaries

## Status

**Proven (no sorries)**:
- Core connection to weakness theory ✅
- Monotonicity properties ✅
- De Morgan existential duality ✅
- Functoriality ✅
- Basic properties (constantTrue, constantFalse) ✅
- Empty-domain vacuity for extensional quantifiers ✅

**Open direction**:
- Frame-distributivity formulation for the `isTrue`-filtered weakness quantifier semantics

## Build

```bash
cd /home/zar/claude/lean-projects/mettapedia
export LAKE_JOBS=3
nice -n 19 lake build Mettapedia.Logic.PLNFirstOrder
```

## References

- Plan file: /home/zar/.claude/plans/hashed-baking-bumblebee.md
- Goertzel, "Weakness and Its Quantale"
- QuantaleWeakness.lean (820+ proven lines)
- EvidenceQuantale.lean (Evidence with Frame structure)
-/
