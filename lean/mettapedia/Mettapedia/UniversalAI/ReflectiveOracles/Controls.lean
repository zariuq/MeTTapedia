import Mettapedia.UniversalAI.ReflectiveOracles.FixedPoints

/-!
# Reflective oracles: worked systems

Five small query systems, each solved completely.

* `liar`: one machine asks the oracle about itself and outputs the opposite
  (Example 3 of Leike, Taylor and Fallenstein). Its only reflective oracle
  answers `1` with probability one half. No oracle with answers in `{0, 1}` is
  reflective, and the system is not stratified.
* `matchingPennies`: one machine copies the predicted output of the other,
  which outputs the opposite of the predicted output of the first. The only
  reflective oracle answers one half on both queries: the mixed equilibrium of
  the game. The existence theorem applies to both systems
  (`liar_general_answer`, `matchingPennies_general_answer`).
* `coordination`: each machine copies the predicted output of the other. There
  are exactly three reflective oracles: both `0`, both `1`, both one half.
  These are the three equilibria of the coordination game, so a reflective
  oracle is not unique in general.
* `silent`: a machine that never outputs anything. Every oracle is reflective,
  so the answer `1` does not mean that the probability of output `1` exceeds
  the threshold.
* `chain`: machine `0` outputs `1` with probability two thirds, machine `n + 1`
  repeats the predicted output of machine `n`. The system is stratified; its
  threshold oracle answers `1` everywhere. The oracle that never answers `1`
  is not reflective for it, although it answers `1` only when the probability
  exceeds the threshold (`never_one_not_reflective`).
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAI.ReflectiveOracles.Controls

open Set
open scoped unitInterval

/-! ## The liar -/

/-- One machine: it asks the oracle whether it outputs `1` with probability
above one half, and outputs the opposite of the answer. So it outputs `1` with
the probability that the oracle answers `0`. -/
noncomputable def liar : QuerySystem Unit where
  threshold _ := 1 / 2
  outputOne _ O := 1 - (O () : ℝ)
  outputZero _ O := (O () : ℝ)
  outputOne_nonneg _ O := sub_nonneg.mpr (O ()).2.2
  outputZero_nonneg _ O := (O ()).2.1
  output_le_one _ O := by simp

/-- **The liar has exactly one reflective answer: one half.** -/
theorem liar_reflective_iff (O : Oracle Unit) : liar.Reflective O ↔ (O () : ℝ) = 1 / 2 := by
  constructor
  · intro reflective
    obtain ⟨one, zero⟩ := reflective ()
    by_contra different
    rcases lt_or_gt_of_ne different with below | above
    · have forced : O () = 1 := one (by simp only [liar]; linarith)
      rw [forced, Set.Icc.coe_one] at below
      norm_num at below
    · have forced : O () = 0 := zero (by simp only [liar]; linarith)
      rw [forced, Set.Icc.coe_zero] at above
      norm_num at above
  · intro half q
    refine ⟨fun above => ?_, fun above => ?_⟩
    · simp only [liar] at above
      linarith
    · simp only [liar] at above
      linarith

/-- The oracle that answers the liar's query by a fair coin. -/
noncomputable def fairCoin : Oracle Unit := fun _ => ⟨1 / 2, by norm_num, by norm_num⟩

theorem liar_reflective_fairCoin : liar.Reflective fairCoin :=
  (liar_reflective_iff fairCoin).mpr rfl

theorem liar_existsUnique : ∃! O, liar.Reflective O := by
  refine ⟨fairCoin, liar_reflective_fairCoin, fun O reflective => ?_⟩
  funext q
  exact Subtype.ext ((liar_reflective_iff O).mp reflective)

/-- No oracle with answers in `{0, 1}` is reflective for the liar. -/
theorem liar_not_reflective_of_deterministic (O : Oracle Unit)
    (deterministic : O () = 0 ∨ O () = 1) : ¬liar.Reflective O := by
  intro reflective
  have half := (liar_reflective_iff O).mp reflective
  rcases deterministic with zero | one
  · rw [zero, Set.Icc.coe_zero] at half
    norm_num at half
  · rw [one, Set.Icc.coe_one] at half
    norm_num at half

/-- The liar refers to itself: no well-founded order stratifies it. -/
theorem liar_not_stratified (r : Unit → Unit → Prop) (wf : WellFounded r) :
    ¬liar.Stratified r := fun stratified =>
  liar_not_reflective_of_deterministic (liar.thresholdOracle wf)
    (liar.thresholdOracle_eq_zero_or_one wf stratified ())
    (liar.thresholdOracle_reflective wf stratified)

theorem liar_semicontinuous : liar.OutputsLowerSemicontinuous := fun _ =>
  ⟨(continuous_const.sub (continuous_subtype_val.comp (continuous_apply ()))).lowerSemicontinuous,
    (continuous_subtype_val.comp (continuous_apply ())).lowerSemicontinuous⟩

/-- The existence theorem applies to the liar, and what it finds is the fair
coin. -/
theorem liar_general_answer : ∃ O, liar.Reflective O ∧ (O () : ℝ) = 1 / 2 := by
  obtain ⟨O, reflective⟩ := QuerySystem.exists_reflective liar_semicontinuous
  exact ⟨O, reflective, (liar_reflective_iff O).mp reflective⟩

/-! ## Two machines that refer to each other -/

/-- The two machines of a two-player game. -/
inductive Player where
  | first
  | second
  deriving DecidableEq

/-- The other player. -/
def Player.other : Player → Player
  | .first => .second
  | .second => .first

/-- The first machine outputs the predicted output of the second; the second
outputs the opposite of the predicted output of the first. -/
noncomputable def matchingPennies : QuerySystem Player where
  threshold _ := 1 / 2
  outputOne
    | .first, O => (O .second : ℝ)
    | .second, O => 1 - (O .first : ℝ)
  outputZero
    | .first, O => 1 - (O .second : ℝ)
    | .second, O => (O .first : ℝ)
  outputOne_nonneg
    | .first, O => (O .second).2.1
    | .second, O => sub_nonneg.mpr (O .first).2.2
  outputZero_nonneg
    | .first, O => sub_nonneg.mpr (O .second).2.2
    | .second, O => (O .first).2.1
  output_le_one
    | .first, O => by simp
    | .second, O => by simp

/-- **Matching pennies has exactly one reflective oracle: one half on both
queries.** -/
theorem matchingPennies_reflective_iff (O : Oracle Player) :
    matchingPennies.Reflective O ↔
      (O .first : ℝ) = 1 / 2 ∧ (O .second : ℝ) = 1 / 2 := by
  constructor
  · intro reflective
    obtain ⟨firstOne, firstZero⟩ := reflective .first
    obtain ⟨secondOne, secondZero⟩ := reflective .second
    simp only [matchingPennies] at firstOne firstZero secondOne secondZero
    have second : (O .second : ℝ) = 1 / 2 := by
      by_contra different
      rcases lt_or_gt_of_ne different with below | above
      · have forced : O .first = 0 := firstZero (by linarith)
        have also : O .second = 1 := secondOne (by rw [forced, Set.Icc.coe_zero]; norm_num)
        rw [also, Set.Icc.coe_one] at below
        norm_num at below
      · have forced : O .first = 1 := firstOne above
        have also : O .second = 0 := secondZero (by rw [forced, Set.Icc.coe_one]; norm_num)
        rw [also, Set.Icc.coe_zero] at above
        norm_num at above
    refine ⟨?_, second⟩
    by_contra different
    rcases lt_or_gt_of_ne different with below | above
    · have forced : O .second = 1 := secondOne (by linarith)
      rw [forced, Set.Icc.coe_one] at second
      norm_num at second
    · have forced : O .second = 0 := secondZero (by linarith)
      rw [forced, Set.Icc.coe_zero] at second
      norm_num at second
  · rintro ⟨first, second⟩ q
    cases q
    · refine ⟨fun above => ?_, fun above => ?_⟩ <;>
        · simp only [matchingPennies] at above
          linarith
    · refine ⟨fun above => ?_, fun above => ?_⟩ <;>
        · simp only [matchingPennies] at above
          linarith

theorem matchingPennies_semicontinuous : matchingPennies.OutputsLowerSemicontinuous := by
  have answer : ∀ q : Player, Continuous fun O : Oracle Player => (O q : ℝ) := fun q =>
    continuous_subtype_val.comp (continuous_apply q)
  intro q
  cases q
  · exact ⟨(answer .second).lowerSemicontinuous,
      (continuous_const.sub (answer .second)).lowerSemicontinuous⟩
  · exact ⟨(continuous_const.sub (answer .first)).lowerSemicontinuous,
      (answer .first).lowerSemicontinuous⟩

/-- The existence theorem applies to two machines that refer to each other,
and what it finds is the mixed equilibrium. -/
theorem matchingPennies_general_answer :
    ∃ O, matchingPennies.Reflective O ∧
      (O .first : ℝ) = 1 / 2 ∧ (O .second : ℝ) = 1 / 2 := by
  obtain ⟨O, reflective⟩ := QuerySystem.exists_reflective matchingPennies_semicontinuous
  exact ⟨O, reflective, (matchingPennies_reflective_iff O).mp reflective⟩

/-- Each machine outputs the predicted output of the other. -/
noncomputable def coordination : QuerySystem Player where
  threshold _ := 1 / 2
  outputOne q O := (O q.other : ℝ)
  outputZero q O := 1 - (O q.other : ℝ)
  outputOne_nonneg q O := (O q.other).2.1
  outputZero_nonneg q O := sub_nonneg.mpr (O q.other).2.2
  output_le_one q O := by simp

/-- **Coordination has exactly three reflective oracles**: both answers `0`,
both `1`, or both one half. -/
theorem coordination_reflective_iff (O : Oracle Player) :
    coordination.Reflective O ↔
      (O .first = 0 ∧ O .second = 0) ∨ (O .first = 1 ∧ O .second = 1) ∨
        ((O .first : ℝ) = 1 / 2 ∧ (O .second : ℝ) = 1 / 2) := by
  constructor
  · intro reflective
    obtain ⟨firstOne, firstZero⟩ := reflective .first
    obtain ⟨secondOne, secondZero⟩ := reflective .second
    simp only [coordination, Player.other] at firstOne firstZero secondOne secondZero
    rcases lt_trichotomy (O .second : ℝ) (1 / 2) with below | half | above
    · have first : O .first = 0 := firstZero (by linarith)
      have second : O .second = 0 := secondZero (by rw [first, Set.Icc.coe_zero]; norm_num)
      exact Or.inl ⟨first, second⟩
    · refine Or.inr (Or.inr ⟨?_, half⟩)
      by_contra different
      rcases lt_or_gt_of_ne different with below | above
      · have forced : O .second = 0 := secondZero (by linarith)
        rw [forced, Set.Icc.coe_zero] at half
        norm_num at half
      · have forced : O .second = 1 := secondOne above
        rw [forced, Set.Icc.coe_one] at half
        norm_num at half
    · have first : O .first = 1 := firstOne above
      have second : O .second = 1 := secondOne (by rw [first, Set.Icc.coe_one]; norm_num)
      exact Or.inr (Or.inl ⟨first, second⟩)
  · rintro (⟨first, second⟩ | ⟨first, second⟩ | ⟨first, second⟩) q
    · cases q <;>
        refine ⟨fun above => ?_, fun _ => by simp [first, second]⟩ <;>
        · simp only [coordination, Player.other, first, second, Set.Icc.coe_zero] at above
          norm_num at above
    · cases q <;>
        refine ⟨fun _ => by simp [first, second], fun above => ?_⟩ <;>
        · simp only [coordination, Player.other, first, second, Set.Icc.coe_one] at above
          norm_num at above
    · cases q <;>
        refine ⟨fun above => ?_, fun above => ?_⟩ <;>
        · simp only [coordination, Player.other] at above
          linarith

/-- The three reflective oracles are different, so a reflective oracle is not
determined by the system. -/
theorem coordination_not_unique :
    ∃ O O', coordination.Reflective O ∧ coordination.Reflective O' ∧ O ≠ O' := by
  refine ⟨fun _ => 0, fun _ => 1, ?_, ?_, ?_⟩
  · exact (coordination_reflective_iff _).mpr (Or.inl ⟨rfl, rfl⟩)
  · exact (coordination_reflective_iff _).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · intro same
    have at_first := congrFun same Player.first
    exact zero_ne_one (Subtype.ext_iff.mp at_first)

/-! ## A machine without output -/

/-- A machine that never outputs anything. -/
noncomputable def silent : QuerySystem Unit where
  threshold _ := 1 / 2
  outputOne _ _ := 0
  outputZero _ _ := 0
  outputOne_nonneg _ _ := le_refl 0
  outputZero_nonneg _ _ := le_refl 0
  output_le_one _ _ := by norm_num

/-- Every answer is allowed: the whole unit interval is free. -/
theorem silent_reflective (O : Oracle Unit) : silent.Reflective O := fun q =>
  silent.reflectiveAt_of_mem_interval O q (by norm_num [silent])
    (by norm_num [silent, QuerySystem.upper])

/-- **The answer `1` does not mean that the probability of output `1` exceeds
the threshold.** The oracle that always answers `1` is reflective for the
silent machine, whose probability of output `1` is zero. -/
theorem answer_one_without_output :
    silent.Reflective (fun _ => 1) ∧ silent.outputOne () (fun _ => 1) = 0 :=
  ⟨silent_reflective _, rfl⟩

theorem silent_noOutput (O : Oracle Unit) : silent.noOutput () O = 1 := by
  simp [silent, QuerySystem.noOutput]

/-! ## A stratified system -/

/-- Machine `0` outputs `1` with probability two thirds; machine `n + 1`
outputs the predicted output of machine `n`. -/
noncomputable def chain : QuerySystem ℕ where
  threshold _ := 1 / 2
  outputOne
    | 0, _ => 2 / 3
    | n + 1, O => (O n : ℝ)
  outputZero
    | 0, _ => 1 / 3
    | n + 1, O => 1 - (O n : ℝ)
  outputOne_nonneg
    | 0, _ => by norm_num
    | n + 1, O => (O n).2.1
  outputZero_nonneg
    | 0, _ => by norm_num
    | n + 1, O => sub_nonneg.mpr (O n).2.2
  output_le_one
    | 0, _ => by norm_num
    | n + 1, O => by simp

theorem chain_stratified : chain.Stratified (· < ·) := by
  intro q O O' agree
  cases q with
  | zero => rfl
  | succ n => simp only [chain]; rw [agree n (Nat.lt_succ_self n)]

/-- The threshold oracle of the chain answers `1` on every query. -/
theorem chain_thresholdOracle (n : ℕ) : chain.thresholdOracle Nat.lt_wfRel.wf n = 1 := by
  classical
  induction n with
  | zero =>
    rw [chain.thresholdOracle_apply Nat.lt_wfRel.wf chain_stratified 0, if_pos]
    show (1 / 2 : ℝ) < 2 / 3
    norm_num
  | succ n previous =>
    rw [chain.thresholdOracle_apply Nat.lt_wfRel.wf chain_stratified (n + 1), if_pos]
    show (1 / 2 : ℝ) < (chain.thresholdOracle Nat.lt_wfRel.wf n : ℝ)
    rw [previous, Set.Icc.coe_one]
    norm_num

/-- **Answering `1` only when the probability exceeds the threshold is not
enough.** The oracle that never answers `1` satisfies that condition for every
system, and it is not reflective for the chain: machine `0` outputs `1` with
probability two thirds. -/
theorem never_one_not_reflective :
    (∀ n, (fun _ => 0 : Oracle ℕ) n = 1 →
        chain.threshold n < chain.outputOne n (fun _ => 0)) ∧
      ¬chain.Reflective (fun _ => 0) := by
  refine ⟨fun n impossible => absurd impossible zero_ne_one, fun reflective => ?_⟩
  have forced : (0 : I) = 1 := (reflective 0).1 (by
    show (1 / 2 : ℝ) < 2 / 3
    norm_num)
  exact zero_ne_one forced

theorem chain_reflective : chain.Reflective (fun _ => 1) := by
  have := chain.thresholdOracle_reflective Nat.lt_wfRel.wf chain_stratified
  have same : chain.thresholdOracle Nat.lt_wfRel.wf = fun _ => 1 :=
    funext chain_thresholdOracle
  rwa [same] at this

end Mettapedia.UniversalAI.ReflectiveOracles.Controls
