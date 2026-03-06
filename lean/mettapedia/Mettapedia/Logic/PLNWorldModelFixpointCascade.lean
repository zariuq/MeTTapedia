import Mettapedia.Logic.PLNWorldModelFixpointClosure

/-!
# WM Fixpoint Cascade and Discovery Theorems

Finite-query consequence systems admit an explicit bounded cascade semantics:

- by time `card(Query)`, fair synchronous closure iteration reaches the full
  least rule closure;
- therefore every closure member is discovered within that bound;
- threshold-valid seeds transport their threshold to every discovered target.

Conceptual note:
- This packages the existing Hyperseed-style closure machinery into a concrete
  bounded-cascade/detection theorem family.
-/

namespace Mettapedia.Logic.PLNWorldModelFixpointCascade

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModelFixpointClosure
open scoped ENNReal

variable {State Query : Type*} [EvidenceType State] [WorldModel State Query]

/-- On finite query spaces, the fair synchronous cascade reaches the full least
rule closure by time `card(Query)`. -/
theorem immediateIter_eq_leastRuleClosure_at_card_of_finite
    [Fintype Query]
    (R : RuleSet State Query) (W : State) (seed : Set Query) :
    immediateIter (State := State) (Query := Query) R W seed (Fintype.card Query) =
      leastRuleClosure (State := State) (Query := Query) R W seed := by
  apply Set.Subset.antisymm
  · exact
      immediateIter_subset_leastRuleClosure
        (State := State) (Query := Query) R W seed (Fintype.card Query)
  · let S :=
      immediateIter (State := State) (Query := Query) R W seed (Fintype.card Query)
    have hFixed :
        immediateStep (State := State) (Query := Query) R W seed S = S := by
      simpa [S, immediateIter] using
        (immediateIter_stable_at_card_of_finite
          (State := State) (Query := Query) R W seed).symm
    have hPref :
        immediateStep (State := State) (Query := Query) R W seed S ⊆ S := by
      intro q hq
      simpa [hFixed] using hq
    exact
      leastRuleClosure_least
        (State := State) (Query := Query) R W seed S hPref

/-- Any stage past `card(Query)` already equals the full least rule closure. -/
theorem immediateIter_eq_leastRuleClosure_of_ge_card_of_finite
    [Fintype Query]
    (R : RuleSet State Query) (W : State) (seed : Set Query)
    {m : ℕ} (hm : Fintype.card Query ≤ m) :
    immediateIter (State := State) (Query := Query) R W seed m =
      leastRuleClosure (State := State) (Query := Query) R W seed := by
  calc
    immediateIter (State := State) (Query := Query) R W seed m
        = immediateIter (State := State) (Query := Query) R W seed (Fintype.card Query) := by
            exact
              immediateIter_eq_card_of_ge_card_of_finite
                (State := State) (Query := Query) (R := R) (W := W) (seed := seed)
                m hm
    _ = leastRuleClosure (State := State) (Query := Query) R W seed :=
          immediateIter_eq_leastRuleClosure_at_card_of_finite
            (State := State) (Query := Query) R W seed

/-- Closure membership is equivalent to bounded-time discovery at stage
`card(Query)`. -/
theorem mem_leastRuleClosure_iff_mem_immediateIter_card_of_finite
    [Fintype Query]
    (R : RuleSet State Query) (W : State) (seed : Set Query) (q : Query) :
    q ∈ leastRuleClosure (State := State) (Query := Query) R W seed ↔
      q ∈ immediateIter (State := State) (Query := Query) R W seed (Fintype.card Query) := by
  rw [immediateIter_eq_leastRuleClosure_at_card_of_finite
    (State := State) (Query := Query) (R := R) (W := W) (seed := seed)]

/-- Every closure target is discovered within a bounded number of fair
synchronous exploration rounds. -/
theorem mem_leastRuleClosure_implies_eventual_discovery_of_finite
    [Fintype Query]
    (R : RuleSet State Query) (W : State) (seed : Set Query)
    {q : Query}
    (hq : q ∈ leastRuleClosure (State := State) (Query := Query) R W seed) :
    ∃ N ≤ Fintype.card Query,
      q ∈ immediateIter (State := State) (Query := Query) R W seed N := by
  refine ⟨Fintype.card Query, le_rfl, ?_⟩
  exact
    (mem_leastRuleClosure_iff_mem_immediateIter_card_of_finite
      (State := State) (Query := Query) R W seed q).mp hq

/-- Finite-cascade threshold endpoint:
if seed assumptions are valid at threshold `τ`, then every closure target
inherits the same threshold bound. -/
theorem leastRuleClosure_target_threshold_of_seed
    (R : RuleSet State Query) (W : State) (seed : Set Query) (τ : ℝ≥0∞)
    (hSeed :
      thresholdValid (State := State) (Query := Query) W τ seed)
    {q : Query}
    (hq : q ∈ leastRuleClosure (State := State) (Query := Query) R W seed) :
    τ ≤ WorldModel.queryStrength (State := State) (Query := Query) W q := by
  exact
    leastRuleClosure_thresholdValid
      (State := State) (Query := Query)
      (R := R) (W := W) (seed := seed) (τ := τ) hSeed q hq

/-- Bounded-time cascade threshold theorem on finite query spaces:
if a target lies in the least closure, then by time `card(Query)` it is
discovered and already carries the transported threshold bound. -/
theorem bounded_cascade_threshold_of_finite
    [Fintype Query]
    (R : RuleSet State Query) (W : State) (seed : Set Query) (τ : ℝ≥0∞)
    (hSeed :
      thresholdValid (State := State) (Query := Query) W τ seed)
    {q : Query}
    (hq : q ∈ leastRuleClosure (State := State) (Query := Query) R W seed) :
    q ∈ immediateIter (State := State) (Query := Query) R W seed (Fintype.card Query) ∧
      τ ≤ WorldModel.queryStrength (State := State) (Query := Query) W q := by
  refine ⟨?_, ?_⟩
  · exact
      (mem_leastRuleClosure_iff_mem_immediateIter_card_of_finite
        (State := State) (Query := Query) R W seed q).mp hq
  · exact
      leastRuleClosure_target_threshold_of_seed
        (State := State) (Query := Query) (R := R) (W := W) (seed := seed)
        τ hSeed hq

end Mettapedia.Logic.PLNWorldModelFixpointCascade
