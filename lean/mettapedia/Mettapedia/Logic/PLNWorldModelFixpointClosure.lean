import Mettapedia.Logic.PLNWorldModelCalculus
import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Card

/-!
# WM Consequence Fixpoint Closure

Hyperseed-style consequence dynamics for WM/PLN:

- define a monotone immediate-consequence operator from WM consequence rules,
- iterate to closure as a least fixpoint,
- prove canonical closure laws (extensive / stable / least),
- prove threshold-soundness transport from seed obligations to closure obligations.
-/

namespace Mettapedia.Logic.PLNWorldModelFixpointClosure

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open scoped ENNReal

variable {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]

/-- Rule pool used by the closure operator. -/
abbrev RuleSet (State Query : Type*) [EvidenceType State] [BinaryWorldModel State Query] :=
  Set (WMConsequenceRuleOn State Query)

/-- One-step rule consequences from a query set `S` at state `W`. -/
def derivedByRules
    (R : RuleSet State Query) (W : State) (S : Set Query) : Set Query :=
  { q | ∃ r ∈ R, r.side W ∧ r.premise ∈ S ∧ q = r.conclusion }

/-- Immediate closure step:
keep prior consequences, keep seed assumptions, add one-step rule conclusions. -/
def immediateStep
    (R : RuleSet State Query) (W : State) (seed S : Set Query) : Set Query :=
  (S ∪ seed) ∪ derivedByRules (State := State) (Query := Query) R W S

theorem derivedByRules_mono
    (R : RuleSet State Query) (W : State) {S₁ S₂ : Set Query}
    (hS : S₁ ⊆ S₂) :
    derivedByRules (State := State) (Query := Query) R W S₁ ⊆
      derivedByRules (State := State) (Query := Query) R W S₂ := by
  intro q hq
  rcases hq with ⟨r, hrR, hside, hprem, rfl⟩
  exact ⟨r, hrR, hside, hS hprem, rfl⟩

theorem immediateStep_mono
    (R : RuleSet State Query) (W : State) (seed : Set Query) :
    Monotone (immediateStep (State := State) (Query := Query) R W seed) := by
  intro S₁ S₂ hS q hq
  rcases hq with hq | hq
  · rcases hq with hq | hq
    · exact Or.inl (Or.inl (hS hq))
    · exact Or.inl (Or.inr hq)
  · exact Or.inr (derivedByRules_mono (State := State) (Query := Query) R W hS hq)

theorem immediateStep_extensive
    (R : RuleSet State Query) (W : State) (seed S : Set Query) :
    S ⊆ immediateStep (State := State) (Query := Query) R W seed S := by
  intro q hq
  exact Or.inl (Or.inl hq)

/-- Bundle the immediate closure step as an order hom on `Set Query`. -/
noncomputable def immediateStepOrderHom
    (R : RuleSet State Query) (W : State) (seed : Set Query) :
    Set Query →o Set Query where
  toFun := immediateStep (State := State) (Query := Query) R W seed
  monotone' := immediateStep_mono (State := State) (Query := Query) R W seed

/-- Least rule-closed set extending `seed`. -/
noncomputable def leastRuleClosure
    (R : RuleSet State Query) (W : State) (seed : Set Query) : Set Query :=
  OrderHom.lfp (immediateStepOrderHom (State := State) (Query := Query) R W seed)

/-- Canonical stability law: closure is a fixpoint of the immediate step. -/
theorem leastRuleClosure_fixedpoint
    (R : RuleSet State Query) (W : State) (seed : Set Query) :
    immediateStep (State := State) (Query := Query) R W seed
        (leastRuleClosure (State := State) (Query := Query) R W seed) =
      leastRuleClosure (State := State) (Query := Query) R W seed :=
  OrderHom.isFixedPt_lfp (immediateStepOrderHom (State := State) (Query := Query) R W seed)

/-- Canonical extensivity law: closure contains all seed assumptions. -/
theorem seed_subset_leastRuleClosure
    (R : RuleSet State Query) (W : State) (seed : Set Query) :
    seed ⊆ leastRuleClosure (State := State) (Query := Query) R W seed := by
  intro q hq
  have hstep :
      q ∈ immediateStep (State := State) (Query := Query) R W seed
          (leastRuleClosure (State := State) (Query := Query) R W seed) :=
    Or.inl (Or.inr hq)
  simpa [leastRuleClosure_fixedpoint (State := State) (Query := Query) R W seed] using hstep

/-- Rule-closure law: if a premise is in closure and side conditions hold, the
conclusion is in closure. -/
theorem leastRuleClosure_rule_closed
    (R : RuleSet State Query) (W : State) (seed : Set Query)
    {r : WMConsequenceRuleOn State Query}
    (hr : r ∈ R)
    (hside : r.side W)
    (hprem : r.premise ∈ leastRuleClosure (State := State) (Query := Query) R W seed) :
    r.conclusion ∈ leastRuleClosure (State := State) (Query := Query) R W seed := by
  have hstep :
      r.conclusion ∈ immediateStep (State := State) (Query := Query) R W seed
          (leastRuleClosure (State := State) (Query := Query) R W seed) :=
    Or.inr ⟨r, hr, hside, hprem, rfl⟩
  simpa [leastRuleClosure_fixedpoint (State := State) (Query := Query) R W seed] using hstep

/-- Leastness law (prefixed form): closure is below every pre-fixpoint. -/
theorem leastRuleClosure_least
    (R : RuleSet State Query) (W : State) (seed S : Set Query)
    (hS : immediateStep (State := State) (Query := Query) R W seed S ⊆ S) :
    leastRuleClosure (State := State) (Query := Query) R W seed ⊆ S :=
  OrderHom.lfp_le (immediateStepOrderHom (State := State) (Query := Query) R W seed) hS

/-- Leastness law (rulewise form): if `S` contains seed assumptions and is closed
under all active rule steps, then closure is contained in `S`. -/
theorem leastRuleClosure_least_of_seed_and_rules
    (R : RuleSet State Query) (W : State) (seed S : Set Query)
    (hSeed : seed ⊆ S)
    (hRules : ∀ r ∈ R, r.side W → r.premise ∈ S → r.conclusion ∈ S) :
    leastRuleClosure (State := State) (Query := Query) R W seed ⊆ S := by
  apply leastRuleClosure_least (State := State) (Query := Query) R W seed S
  intro q hq
  rcases hq with hq | hq
  · rcases hq with hq | hq
    · exact hq
    · exact hSeed hq
  · rcases hq with ⟨r, hrR, hside, hprem, hqEq⟩
    simpa [hqEq] using hRules r hrR hside hprem

/-- Query obligations valid at threshold `τ` in state `W`. -/
def thresholdValid (W : State) (τ : ℝ≥0∞) (S : Set Query) : Prop :=
  ∀ q, q ∈ S →
    τ ≤ BinaryWorldModel.queryStrength (State := State) (Query := Query) W q

theorem thresholdValid_mono
    (W : State) (τ : ℝ≥0∞) {S₁ S₂ : Set Query}
    (hS : S₁ ⊆ S₂)
    (hV : thresholdValid (State := State) (Query := Query) W τ S₂) :
    thresholdValid (State := State) (Query := Query) W τ S₁ := by
  intro q hq
  exact hV q (hS hq)

/-- One-step semantic transport:
if `seed` and current `S` satisfy threshold obligations, then the next
immediate closure step also satisfies them. -/
theorem immediateStep_thresholdValid
    (R : RuleSet State Query) (W : State) (seed S : Set Query) (τ : ℝ≥0∞)
    (hSeed :
      thresholdValid (State := State) (Query := Query) W τ seed)
    (hS :
      thresholdValid (State := State) (Query := Query) W τ S) :
    thresholdValid (State := State) (Query := Query) W τ
      (immediateStep (State := State) (Query := Query) R W seed S) := by
  intro q hq
  rcases hq with hq | hq
  · rcases hq with hq | hq
    · exact hS q hq
    · exact hSeed q hq
  · rcases hq with ⟨r, _hrR, hside, hprem, hqEq⟩
    have hpremτ :
        τ ≤ BinaryWorldModel.queryStrength (State := State) (Query := Query) W r.premise :=
      hS r.premise hprem
    have hrc :
        BinaryWorldModel.queryStrength (State := State) (Query := Query) W r.premise ≤
          BinaryWorldModel.queryStrength (State := State) (Query := Query) W r.conclusion :=
      r.sound hside
    have hconc :
        τ ≤ BinaryWorldModel.queryStrength (State := State) (Query := Query) W r.conclusion :=
      le_trans hpremτ hrc
    simpa [hqEq] using hconc

/-- Closure-level semantic transport:
if seed obligations hold at threshold `τ`, then all least-closure obligations
also hold at threshold `τ`. -/
theorem leastRuleClosure_thresholdValid
    (R : RuleSet State Query) (W : State) (seed : Set Query) (τ : ℝ≥0∞)
    (hSeed :
      thresholdValid (State := State) (Query := Query) W τ seed) :
    thresholdValid (State := State) (Query := Query) W τ
      (leastRuleClosure (State := State) (Query := Query) R W seed) := by
  let goodSet : Set Query :=
    { q | τ ≤ BinaryWorldModel.queryStrength (State := State) (Query := Query) W q }
  have hPref : immediateStep (State := State) (Query := Query) R W seed goodSet ⊆ goodSet := by
    intro q hq
    exact
      (immediateStep_thresholdValid
        (State := State) (Query := Query)
        R W seed goodSet τ hSeed
        (by intro q hq'; exact hq')
        q hq)
  have hClosure :
      leastRuleClosure (State := State) (Query := Query) R W seed ⊆ goodSet :=
    OrderHom.lfp_le (immediateStepOrderHom (State := State) (Query := Query) R W seed) hPref
  intro q hq
  exact hClosure hq

/-- Iterative operational view of closure dynamics. -/
def immediateIter
    (R : RuleSet State Query) (W : State) (seed : Set Query) : ℕ → Set Query
  | 0 => seed
  | n + 1 =>
      immediateStep (State := State) (Query := Query) R W seed
        (immediateIter R W seed n)

theorem immediateIter_succ_mono
    (R : RuleSet State Query) (W : State) (seed : Set Query) (n : ℕ) :
    immediateIter (State := State) (Query := Query) R W seed n ⊆
      immediateIter (State := State) (Query := Query) R W seed (n + 1) := by
  intro q hq
  simp [immediateIter, immediateStep, hq]

theorem immediateIter_mono
    (R : RuleSet State Query) (W : State) (seed : Set Query)
    {m n : ℕ} (h : m ≤ n) :
    immediateIter (State := State) (Query := Query) R W seed m ⊆
      immediateIter (State := State) (Query := Query) R W seed n := by
  induction h with
  | refl =>
      exact Set.Subset.rfl
  | @step n h ih =>
      exact Set.Subset.trans ih (immediateIter_succ_mono (State := State) (Query := Query) R W seed n)

/-- Every finite iterate is contained in the least closure. -/
theorem immediateIter_subset_leastRuleClosure
    (R : RuleSet State Query) (W : State) (seed : Set Query) (n : ℕ) :
    immediateIter (State := State) (Query := Query) R W seed n ⊆
      leastRuleClosure (State := State) (Query := Query) R W seed := by
  induction n with
  | zero =>
      exact seed_subset_leastRuleClosure (State := State) (Query := Query) R W seed
  | succ n ih =>
      intro q hq
      have hStepMono :=
        immediateStep_mono (State := State) (Query := Query) R W seed ih
      have hInStep :
          q ∈ immediateStep (State := State) (Query := Query) R W seed
              (leastRuleClosure (State := State) (Query := Query) R W seed) :=
        hStepMono hq
      simpa [leastRuleClosure_fixedpoint (State := State) (Query := Query) R W seed] using hInStep

/-! ## Finite-rulepool fair-schedule stabilization (immediate iteration) -/

/-- Immediate iteration is a fully fair synchronous schedule:
every step applies the complete rule pool (`immediateStep`) once. -/
theorem immediateIter_is_fair_schedule
    (R : RuleSet State Query) (W : State) (seed : Set Query) (n : ℕ) :
    immediateIter (State := State) (Query := Query) R W seed (n + 1) =
      immediateStep (State := State) (Query := Query) R W seed
        (immediateIter (State := State) (Query := Query) R W seed n) := by
  rfl

/-- Finite-query stabilization witness:
on finite query spaces, the fair synchronous `immediateIter` schedule has a
successor-stable stage within `card(Query)` steps. -/
theorem immediateIter_exists_stable_succ_of_finite
    [Fintype Query]
    (R : RuleSet State Query) (W : State) (seed : Set Query) :
    ∃ N ≤ Fintype.card Query,
      immediateIter (State := State) (Query := Query) R W seed N =
        immediateIter (State := State) (Query := Query) R W seed (N + 1) := by
  by_contra hNo
  have hNe :
      ∀ n, n ≤ Fintype.card Query →
        immediateIter (State := State) (Query := Query) R W seed n ≠
          immediateIter (State := State) (Query := Query) R W seed (n + 1) := by
    intro n hn hEq
    exact hNo ⟨n, hn, hEq⟩
  have hCardLower :
      ∀ n, n ≤ Fintype.card Query + 1 →
        n ≤
          (immediateIter (State := State) (Query := Query) R W seed n).ncard := by
    intro n
    induction n with
    | zero =>
        intro _hn
        simp
    | succ n ih =>
        intro hn
        have hnCard : n ≤ Fintype.card Query :=
          Nat.succ_le_succ_iff.mp hn
        have hPrev :
            n ≤
              (immediateIter (State := State) (Query := Query) R W seed n).ncard :=
          ih (le_trans (Nat.le_succ n) hn)
        have hStrict :
            (immediateIter (State := State) (Query := Query) R W seed n).ncard <
              (immediateIter (State := State) (Query := Query) R W seed (n + 1)).ncard := by
          have hNotSubset :
              ¬ immediateIter (State := State) (Query := Query) R W seed (n + 1) ⊆
                immediateIter (State := State) (Query := Query) R W seed n := by
            intro hSub
            have hEq :
                immediateIter (State := State) (Query := Query) R W seed n =
                  immediateIter (State := State) (Query := Query) R W seed (n + 1) :=
              Set.Subset.antisymm
                (immediateIter_succ_mono (State := State) (Query := Query) R W seed n)
                hSub
            exact hNe n hnCard hEq
          exact
            Set.ncard_lt_ncard
              ⟨immediateIter_succ_mono (State := State) (Query := Query) R W seed n,
               hNotSubset⟩
        have hSucc :
            (immediateIter (State := State) (Query := Query) R W seed n).ncard + 1 ≤
              (immediateIter (State := State) (Query := Query) R W seed (n + 1)).ncard :=
          Nat.succ_le_of_lt hStrict
        exact le_trans (Nat.succ_le_succ hPrev) hSucc
  have hLower :
      Fintype.card Query + 1 ≤
        (immediateIter (State := State) (Query := Query) R W seed
          (Fintype.card Query + 1)).ncard :=
    hCardLower (Fintype.card Query + 1) (le_rfl)
  have hUpper :
      (immediateIter (State := State) (Query := Query) R W seed
        (Fintype.card Query + 1)).ncard ≤ Fintype.card Query := by
    have hUniv :
        (immediateIter (State := State) (Query := Query) R W seed
          (Fintype.card Query + 1)).ncard ≤ (Set.univ : Set Query).ncard :=
      Set.ncard_le_ncard (by intro q _hq; simp)
    simpa [Set.ncard_univ] using hUniv
  exact Nat.not_succ_le_self (Fintype.card Query) (le_trans hLower hUpper)

/-- Once a successor-stable stage is reached, all later iterates are identical. -/
theorem immediateIter_eq_of_stable_succ
    (R : RuleSet State Query) (W : State) (seed : Set Query) (N : ℕ)
    (hStable :
      immediateIter (State := State) (Query := Query) R W seed N =
        immediateIter (State := State) (Query := Query) R W seed (N + 1)) :
    ∀ m, N ≤ m →
      immediateIter (State := State) (Query := Query) R W seed m =
        immediateIter (State := State) (Query := Query) R W seed N := by
  have hStepFixed :
      immediateStep (State := State) (Query := Query) R W seed
          (immediateIter (State := State) (Query := Query) R W seed N) =
        immediateIter (State := State) (Query := Query) R W seed N := by
    simpa [immediateIter] using hStable.symm
  intro m hm
  rcases Nat.exists_eq_add_of_le hm with ⟨k, rfl⟩
  induction k with
  | zero =>
      simp
  | succ k ih =>
      calc
        immediateIter (State := State) (Query := Query) R W seed (N + (k + 1))
            = immediateStep (State := State) (Query := Query) R W seed
                (immediateIter (State := State) (Query := Query) R W seed (N + k)) := by
                simp [immediateIter]
        _ = immediateStep (State := State) (Query := Query) R W seed
              (immediateIter (State := State) (Query := Query) R W seed N) := by
                simp [ih]
        _ = immediateIter (State := State) (Query := Query) R W seed N := hStepFixed

/-- Finite-query fair-schedule convergence:
on finite query spaces, `immediateIter` reaches a stable stage in at most
`card(Query)` steps and stays constant afterwards. -/
theorem immediateIter_eventually_constant_of_finite
    [Fintype Query]
    (R : RuleSet State Query) (W : State) (seed : Set Query) :
    ∃ N ≤ Fintype.card Query,
      ∀ m, N ≤ m →
        immediateIter (State := State) (Query := Query) R W seed m =
          immediateIter (State := State) (Query := Query) R W seed N := by
  rcases
    immediateIter_exists_stable_succ_of_finite
      (State := State) (Query := Query) R W seed with ⟨N, hN, hStable⟩
  refine ⟨N, hN, ?_⟩
  exact immediateIter_eq_of_stable_succ (State := State) (Query := Query) R W seed N hStable

/-- Explicit bounded-time stabilization:
on finite query spaces, the fair synchronous iterator stabilizes by
time `card(Query)`. -/
theorem immediateIter_eq_card_of_ge_card_of_finite
    [Fintype Query]
    (R : RuleSet State Query) (W : State) (seed : Set Query) :
    ∀ m, Fintype.card Query ≤ m →
      immediateIter (State := State) (Query := Query) R W seed m =
        immediateIter (State := State) (Query := Query) R W seed (Fintype.card Query) := by
  rcases
    immediateIter_exists_stable_succ_of_finite
      (State := State) (Query := Query) R W seed with ⟨N, hN, hStable⟩
  have hConst :=
    immediateIter_eq_of_stable_succ
      (State := State) (Query := Query) R W seed N hStable
  intro m hm
  have hmN : N ≤ m := le_trans hN hm
  have hCardN : N ≤ Fintype.card Query := hN
  calc
    immediateIter (State := State) (Query := Query) R W seed m
        = immediateIter (State := State) (Query := Query) R W seed N :=
          hConst m hmN
    _ = immediateIter (State := State) (Query := Query) R W seed (Fintype.card Query) := by
          symm
          exact hConst (Fintype.card Query) hCardN

/-- In particular, the card bound is successor-stable. -/
theorem immediateIter_stable_at_card_of_finite
    [Fintype Query]
    (R : RuleSet State Query) (W : State) (seed : Set Query) :
    immediateIter (State := State) (Query := Query) R W seed (Fintype.card Query) =
      immediateIter (State := State) (Query := Query) R W seed (Fintype.card Query + 1) := by
  symm
  exact immediateIter_eq_card_of_ge_card_of_finite
    (State := State) (Query := Query) (R := R) (W := W) (seed := seed)
    (Fintype.card Query + 1) (Nat.le_succ _)

end Mettapedia.Logic.PLNWorldModelFixpointClosure
