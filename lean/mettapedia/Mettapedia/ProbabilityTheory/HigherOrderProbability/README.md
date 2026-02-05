# Higher-Order Probability Theory in Mettapedia

Formalization of Kyburg's flattening theorem and higher-order probability foundations.

## Files in This Directory

### Week 1: Foundations ✅
- **`Basic.lean`** (176 lines)
  - Core structures: `ParametrizedDistribution`, `kyburgJoint`, `flatten`
  - Foundation for all higher-order probability work

### Week 2: Main Theorem ✅
- **`KyburgFlattening.lean`** (163 lines)
  - Kyburg's flattening theorem
  - Expectation consistency and decision-theoretic equivalence
  - Connection to Giry monad

### Week 3: Connections ✅
- **`DeFinettiConnection.lean`** (237 lines)
  - Connect to `Mettapedia/Logic/DeFinetti.lean`
  - Show BernoulliMixture is a Kyburg flattening
  - Exchangeability ↔ Kyburg flattening

### Week 6: Giry Monad ✅
- **`GiryMonad.lean`** (308 lines)
  - Connect to mathlib's Giry monad
  - Prove flatten = monadic bind
  - Monad laws for Kyburg flattening

### Status & Planning
- **`STATUS.md`** - Implementation progress tracker
- **`README.md`** - This file

## Quick Build

```bash
# Build all higher-order probability modules
lake build Mettapedia.ProbabilityTheory.HigherOrderProbability.Basic
lake build Mettapedia.ProbabilityTheory.HigherOrderProbability.KyburgFlattening

# Or build the whole HigherOrderProbability namespace
lake build Mettapedia.ProbabilityTheory.HigherOrderProbability
```

## Master Plan

Full 6-week implementation plan: `/home/zar/.claude/plans/eventual-mapping-wadler.md`

**Phases**:
1. Kyburg Flattening (Weeks 1-3) - COMPLETE ✅
2. PLN-Kyburg Bridge (Weeks 4-5) - COMPLETE ✅
3. Giry Monad Integration (Week 6) - COMPLETE ✅
4. Quasi-Borel Foundations (Future) - PLANNED

## Key Theorems

**Phase 1-2: Kyburg Flattening**
- `kyburg_flattening` : P(x) = ∫ kernel(θ)(x) dμ(θ)
- `expectation_consistency` : E[U] = E[E[U|θ]]
- `kyburg_no_advantage` : Decision equivalence

**Phase 3: Giry Monad**
- `flatten_is_bind` : flatten = monadic bind (identity)
- `flatten_left_identity` : join ∘ dirac = id
- `flatten_right_identity` : join ∘ map dirac = id
- `flatten_associativity` : join ∘ join = join ∘ map join

**Phase 2: PLN-Kyburg Bridge**
- `evidence_encodes_beta_mixture` : (n⁺, n⁻) → Beta(α+n⁺, β+n⁻)
- `pln_satisfies_kyburg_expectation` : strength = ∫ θ dBeta
- `kyburg_reduction_for_pln` : PLN IS Kyburg-optimal

## Connections to Existing Work

**De Finetti Theorem** (`Mettapedia/Logic/DeFinetti.lean`):
- BernoulliMixture IS already a Kyburg flattening
- Exchangeability = Kyburg reduction
- Week 3 will make this connection explicit

**PLN Evidence** (`Mettapedia/Logic/EvidenceQuantale.lean`):
- (n⁺, n⁻) = sufficient statistic for Kyburg flattening
- Strength/confidence = compact encoding of Beta mixture
- Weeks 4-5 will formalize this bridge

**Giry Monad** (mathlib):
- `flatten` = monadic join operation
- Week 6 will connect to mathlib's categorical infrastructure

## For the Global Gödel Brain 🧠

This formalization provides the mathematical foundations for:
- Higher-order uncertainty in PLN
- Kyburg's justification of compact probability representations
- Path to quasi-Borel spaces (probability over functions)
- Connection between decision theory and category theory

---

**Last Updated**: 2026-02-03
**Status**: Phases 1-3 complete (Weeks 1-6), builds clean (2524 jobs)
