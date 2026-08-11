import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.MapFold
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Zero and Prime: erasure, and what it forgets

A minimal dialect observes a bag of answers.  A cost-aware dialect observes a
bag of answers each carrying a weight.  The relationship between them is not
initial-and-terminal — in an algebraic setting the terminal object is the
*collapsed* one, so "richest" is never terminality.  It is an adjunction, and
its content is the asymmetry of the two round trips.

```
                 erase   (forget the weights)
   costed answers ──────────────────────────▶ plain answers
                 ◀──────────────────────────
                 enrich  (give every answer the unit weight)
```

* `erase_enrich` — enriching then erasing is the **identity**.  Adding weights
  and forgetting them returns exactly what you had, so the base dialect is a
  retract of the cost-aware one and nothing about answers is disturbed.
* `cost_not_determined_by_answers` — erasing then enriching is **not** the
  identity, and not repairable: the weights are gone, and no function of the
  answers recovers them.
* `enrich_erase_eq_iff` — the round trip is the identity **exactly** on
  observations whose weights are all the unit.  So the fixed points of the
  comonad are precisely the dialects where cost carries no information, which
  is the honest sense in which the base dialect sits inside the enriched one.
* `erase_surjective` — every base observation is the erasure of some costed
  one, so the base is the *image*, not a separate thing.

Together: the base dialect is the image of the cost-aware one under erasure,
and the fibres of that map are exactly the cost structures.  That is a
fibration, and it is what "minimal and maximal ends of one spectrum" means
precisely.
-/

namespace Mettapedia.GSLT.Core.CostAdjunction

open Mettapedia.GSLT.Core.NonFactorization

variable {Answer Cost : Type}

/-- What a minimal dialect observes: a bag of answers. -/
abbrev BaseAnswers (Answer : Type) := Multiset Answer

/-- What a cost-aware dialect observes: a bag of weighted answers. -/
abbrev CostedAnswers (Answer Cost : Type) := Multiset (Answer × Cost)

/-- Forget the weights. -/
def erase : CostedAnswers Answer Cost → BaseAnswers Answer :=
  Multiset.map Prod.fst

/-- Give every answer the unit weight. -/
def enrich (unit : Cost) : BaseAnswers Answer → CostedAnswers Answer Cost :=
  Multiset.map (fun answer => (answer, unit))

/-! ## One round trip is the identity -/

/-- **Enriching then erasing changes nothing.**  So the base dialect is a
retract of the cost-aware one: attaching weights cannot disturb the answers. -/
@[simp] theorem erase_enrich (unit : Cost) (bag : BaseAnswers Answer) :
    erase (enrich unit bag) = bag := by
  simp [erase, enrich, Multiset.map_map]

/-- The base observation of a costed one is unchanged by re-enriching it. -/
@[simp] theorem erase_enrich_erase (unit : Cost)
    (costed : CostedAnswers Answer Cost) :
    erase (enrich unit (erase costed)) = erase costed :=
  erase_enrich unit _

/-- **Every base observation is an erasure.**  The base dialect is the image of
the cost-aware one, not a separate construction. -/
theorem erase_surjective (unit : Cost) :
    Function.Surjective (erase : CostedAnswers Answer Cost → BaseAnswers Answer) :=
  fun bag => ⟨enrich unit bag, erase_enrich unit bag⟩

/-! ## The other round trip is not -/

/-- **The fixed points, characterised.**  Erasing and re-enriching returns the
original observation exactly when every weight was already the unit.  So the
base dialect sits inside the cost-aware one precisely as the cost-trivial
fragment — nothing wider, nothing narrower. -/
theorem enrich_erase_eq_iff (unit : Cost) (costed : CostedAnswers Answer Cost) :
    enrich unit (erase costed) = costed ↔ ∀ pair ∈ costed, pair.2 = unit := by
  have rewritten :
      enrich unit (erase costed) =
        costed.map (fun pair => (pair.1, unit)) := by
    simp [erase, enrich, Multiset.map_map]
  rw [rewritten]
  constructor
  · intro fixed pair member
    rw [← fixed] at member
    obtain ⟨original, _, shape⟩ := Multiset.mem_map.mp member
    exact (shape ▸ rfl : pair.2 = unit)
  · intro trivialCost
    refine Multiset.map_congr rfl ?_ |>.trans (Multiset.map_id' costed)
    intro pair member
    rw [← trivialCost pair member]

/-! ### And the failure is irreparable -/

private def costFiber :
    NonTrivialFiber (erase : CostedAnswers Bool Bool → BaseAnswers Bool)
      (fun costed => costed) where
  left := {(true, true)}
  right := {(true, false)}
  sameShadow := rfl
  differentValue := by decide

/-- **Weights are not a function of answers.**  Two cost-aware observations
with the same answers and different weights, so no map from the base dialect
recovers the cost.  Erasure loses information that cannot be reconstructed —
which is why the cost-aware dialect is genuinely larger and not a notational
variant. -/
theorem cost_not_determined_by_answers :
    ¬ Factors (erase : CostedAnswers Bool Bool → BaseAnswers Bool)
      (fun costed => costed) :=
  costFiber.not_factors

/-! ## The relationship, stated once

Surjective, so the base is the image; non-injective, so the fibres are the cost
structures; identity one way round and identity the other way only on the
cost-trivial fragment. -/

theorem base_is_the_erasure_of_costed (unit : Bool) :
    Function.Surjective (erase : CostedAnswers Bool Bool → BaseAnswers Bool) ∧
      (∀ bag : BaseAnswers Bool, erase (enrich unit bag) = bag) ∧
      ¬ Factors (erase : CostedAnswers Bool Bool → BaseAnswers Bool)
        (fun costed => costed) :=
  ⟨erase_surjective unit, erase_enrich unit, cost_not_determined_by_answers⟩

/-! ## What this does not say

`enrich` gives every answer the *same* weight, so it is the free construction
over a chosen unit rather than a canonical inverse.  Nothing here claims the
cost-aware dialect is determined by the base one; the fixed-point theorem says
the opposite, and `cost_not_determined_by_answers` is the obstruction.
-/

end Mettapedia.GSLT.Core.CostAdjunction
