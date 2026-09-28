/-
# Universal Hyperprior: the computable layer

Connection to Hutter's lower-semicomputable (LSC) framework.

## What this file establishes

One thing, and it is a construction rather than an assumption:
`DyadicEvidence` is genuinely countable, so it carries a real `Primcodable`
instance. That is the type over which any LSC statement about this development
can be made.

## What this file does NOT establish, and why

Nothing about lower semicomputability of the hyperprior is proved here, and the
statements that used to appear were not merely unproved:

* An earlier version carried `instance : Primcodable NormalGammaEvidence`,
  discharged by `sorry`, so that LSC statements over real-valued evidence would
  typecheck. That instance is **false**, not open. `NormalGammaEvidence` stores
  `sum sumSq : ℝ`, and `⟨1, r, r^2, _, _⟩` satisfies its Cauchy–Schwarz field
  for every real `r`, so the type has at least the cardinality of the
  continuum, while `Primcodable` extends `Encodable` and asserts an injection
  into `ℕ`. Everything downstream of it was therefore derivable from a
  contradiction. It has been removed.

* Two declarations named `M₂_dominates_UHP` and `uhp_regret_bound` carried
  `sorry` in their *statements* — as the right-hand side of an inequality and
  as the body of an existential — so they asserted nothing while reading as
  theorems. Their intended statements are also category errors:
  `SolomonoffBridge.M₂` is a semimeasure on `Word α` for `α` a `Fintype`
  alphabet, whereas the hyperprior's evidence space is infinite and is not an
  alphabet. They have been removed rather than restated, because the correct
  statement is a different theorem about a different object.

## The real obligation, recorded

To connect this development to Hutter's framework one needs, in order:

1. a computable dyadic approximation
   `DyadicEvidence → ℕ → ℕ` to `logMarginalLikelihood`, monotone increasing and
   convergent — i.e. a genuine witness for `LowerSemicomputable`, not a
   `sorry`-bodied definition;
2. lower semicomputability of the mixture, from (1) and closure properties;
3. a dominance statement relating the mixture to a universal LSC mixture **over
   the same space**, which requires an enumeration theorem for semimeasures on
   a countable non-alphabet domain.

None of the three is available here, and none is claimed.
-/

import Mettapedia.UniversalAI.UniversalHyperprior
import Mettapedia.UniversalAI.UniversalHyperprior.DyadicRealization
import Mettapedia.Computability.HutterComputability

namespace Mettapedia.UniversalAI.UniversalHyperprior.LSC

open Mettapedia.Computability.Hutter
open Mettapedia.UniversalAI.UniversalHyperprior
open Mettapedia.UniversalAI.UniversalHyperprior.Dyadic
open Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceNormalGamma

/-! ## Dyadic evidence is countable

This is the honest replacement for the removed instance.  `DyadicEvidence` is
five integers, so the encoding is a construction and not an assumption. -/

/-- `DyadicEvidence` is exactly a tuple of integers. -/
def dyadicEvidenceEquiv : DyadicEvidence ≃ ℕ × ℤ × ℕ × ℕ × ℕ where
  toFun ev := (ev.n, ev.mean_num, ev.mean_denom_pow, ev.var_num, ev.var_denom_pow)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv := by intro ev; cases ev; rfl
  right_inv := by intro p; rfl

/-- **Dyadic evidence is primitively codable**, by an explicit equivalence with
a tuple of integers.  Compare the removed `Primcodable NormalGammaEvidence`,
which was false. -/
instance : Primcodable DyadicEvidence :=
  Primcodable.ofEquiv _ dyadicEvidenceEquiv

/-! ## Controls -/

namespace ComputabilityControls

/-- The encoding really is a bijection, so the instance rests on a
construction. -/
theorem dyadicEvidenceEquiv_roundTrip (ev : DyadicEvidence) :
    dyadicEvidenceEquiv.symm (dyadicEvidenceEquiv ev) = ev :=
  dyadicEvidenceEquiv.left_inv ev

/-- **And the real-valued evidence type is not countable**, which is why the
removed instance was false rather than open: distinct reals give distinct
evidence values. -/
theorem normalGammaEvidence_injects_real :
    Function.Injective (fun r : ℝ =>
      (⟨1, r, r ^ 2, by positivity, by push_cast; ring_nf; exact le_refl _⟩ :
        NormalGammaEvidence)) := by
  intro a b hab
  exact congrArg NormalGammaEvidence.sum hab

end ComputabilityControls

end Mettapedia.UniversalAI.UniversalHyperprior.LSC

#print axioms Mettapedia.UniversalAI.UniversalHyperprior.LSC.dyadicEvidenceEquiv
#print axioms Mettapedia.UniversalAI.UniversalHyperprior.LSC.ComputabilityControls.normalGammaEvidence_injects_real
