import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Order.WellFounded

/-!
# Reflective oracles

An oracle answers queries of the form "does this machine output `1` with
probability greater than `p`?", and the machine asked about may itself call the
oracle, also about itself. Answers are random: an oracle gives, for each query,
the probability of answering `1` (Leike, Taylor and Fallenstein 2016,
Definition 1; Leike's thesis, Definition 7.2).

An oracle `O` is *reflective* when, for every query `(T, x, p)`,

* `λ_T^O(1 | x) > p` implies `O(T, x, p) = 1`, and
* `λ_T^O(0 | x) > 1 - p` implies `O(T, x, p) = 0`,

where `λ_T^O(b | x)` is the probability that `T`, run with `O`, outputs `b`
(Definition 2 of the paper, Definition 7.3 of the thesis; the form for machines
that halt almost surely is due to Fallenstein, Taylor and Christiano 2015).

This file states that definition for an arbitrary family of queries. A
`QuerySystem` records, for each query, the threshold and the two output
probabilities as functions of the oracle. Nothing is assumed about where those
functions come from, so the results apply to any machine model in which they
can be defined.

## Main definitions

* `Oracle Q`: the probability of the answer `1`, for each query.
* `QuerySystem Q`, `QuerySystem.ReflectiveAt`, `ReflectiveOn`, `Reflective`.
* `QuerySystem.upper`: one minus the probability of output `0`.
* `QuerySystem.Stratified`: no query refers to itself, directly or through
  other queries.
* `QuerySystem.thresholdOracle`: the answers obtained by going through a
  stratified system in order.

## Main statements

* `reflectiveAt_iff_interval`: the answer is forced to `1` when the threshold
  lies below the probability of output `1`, forced to `0` when it lies above
  `upper`, and free in between. The length of the free interval is the
  probability that the machine gives no output.
* `thresholdOracle_reflective`, `eq_thresholdOracle`: a stratified system has a
  reflective oracle with answers in `{0, 1}`, and it is the only oracle that
  answers `1` exactly when the probability of output `1` exceeds the threshold.
* `exists_reflectiveOn_of_finite`: if every finite set of queries of `R` has an
  oracle that is reflective on it and agrees with a given oracle outside `R`,
  then so has `R`. This reduces the existence of reflective oracles to finitely
  many queries; it needs the output probabilities to be lower semicontinuous
  in the oracle.

A system in which queries refer to each other need not be stratified, and its
reflective oracles need not take values in `{0, 1}`:
`ReflectiveOracles/Controls.lean`. The existence of a reflective oracle for
such systems (Theorem 4 of the paper) is proved in
`ReflectiveOracles/FixedPoints.lean` from Brouwer's fixed-point theorem for
cubes.

## References

* Fallenstein, Taylor & Christiano (2015). "Reflective Oracles: A Foundation for
  Classical Game Theory"
* Leike, Taylor & Fallenstein (2016). "A Formal Solution to the Grain of Truth Problem"
* Leike (2016). PhD Thesis "Nonparametric General Reinforcement Learning", Chapter 7
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAI.ReflectiveOracles

open Set
open scoped unitInterval

universe u

/-- A randomized oracle on the queries `Q`: `O q` is the probability that it
answers `1` on the query `q`. Different calls are independent. -/
abbrev Oracle (Q : Type u) := Q → I

/-- A family of queries. Each query has a threshold and asks about a machine;
`outputOne q O` and `outputZero q O` are the probabilities that this machine,
run with the oracle `O`, outputs `1` and `0`. Their sum may be less than one:
the machine may give no output. -/
structure QuerySystem (Q : Type u) where
  /-- The threshold `p` of the query. -/
  threshold : Q → ℝ
  /-- The probability that the queried machine outputs `1`. -/
  outputOne : Q → Oracle Q → ℝ
  /-- The probability that the queried machine outputs `0`. -/
  outputZero : Q → Oracle Q → ℝ
  outputOne_nonneg : ∀ q O, 0 ≤ outputOne q O
  outputZero_nonneg : ∀ q O, 0 ≤ outputZero q O
  output_le_one : ∀ q O, outputOne q O + outputZero q O ≤ 1

namespace QuerySystem

variable {Q : Type u} (S : QuerySystem Q)

/-! ## The definition -/

/-- The oracle answers the query `q` as a reflective oracle must. -/
def ReflectiveAt (O : Oracle Q) (q : Q) : Prop :=
  (S.threshold q < S.outputOne q O → O q = 1) ∧
    (1 - S.threshold q < S.outputZero q O → O q = 0)

/-- The oracle is reflective on the set `R` of queries. -/
def ReflectiveOn (R : Set Q) (O : Oracle Q) : Prop :=
  ∀ q ∈ R, S.ReflectiveAt O q

/-- The oracle is reflective. -/
def Reflective (O : Oracle Q) : Prop :=
  ∀ q, S.ReflectiveAt O q

theorem reflective_iff_reflectiveOn_univ (O : Oracle Q) :
    S.Reflective O ↔ S.ReflectiveOn univ O := by
  simp [Reflective, ReflectiveOn]

theorem ReflectiveOn.mono {S : QuerySystem Q} {R R' : Set Q} {O : Oracle Q}
    (reflective : S.ReflectiveOn R O) (subset : R' ⊆ R) : S.ReflectiveOn R' O :=
  fun q member => reflective q (subset member)

/-- The two conditions never apply to the same query. -/
theorem not_forced_both (O : Oracle Q) (q : Q) :
    ¬(S.threshold q < S.outputOne q O ∧ 1 - S.threshold q < S.outputZero q O) := by
  rintro ⟨one, zero⟩
  linarith [S.output_le_one q O]

/-! ## Forced and free answers -/

/-- The largest probability of output `1` that the observed outputs allow:
every run without output is counted as an output `1`. -/
def upper (q : Q) (O : Oracle Q) : ℝ :=
  1 - S.outputZero q O

/-- The probability that the queried machine gives no output. -/
def noOutput (q : Q) (O : Oracle Q) : ℝ :=
  1 - S.outputOne q O - S.outputZero q O

theorem outputOne_le_upper (q : Q) (O : Oracle Q) : S.outputOne q O ≤ S.upper q O := by
  unfold upper
  linarith [S.output_le_one q O]

theorem upper_sub_outputOne (q : Q) (O : Oracle Q) :
    S.upper q O - S.outputOne q O = S.noOutput q O := by
  unfold upper noOutput
  ring

theorem noOutput_nonneg (q : Q) (O : Oracle Q) : 0 ≤ S.noOutput q O := by
  unfold noOutput
  linarith [S.output_le_one q O]

/-- **The answer is forced outside an interval and free inside it.** Below the
probability of output `1` the answer is `1`; above `upper` it is `0`; for a
threshold in between, any answer is allowed. -/
theorem reflectiveAt_iff_interval (O : Oracle Q) (q : Q) :
    S.ReflectiveAt O q ↔
      (S.threshold q < S.outputOne q O → O q = 1) ∧
        (S.upper q O < S.threshold q → O q = 0) := by
  unfold ReflectiveAt upper
  constructor
  · rintro ⟨one, zero⟩
    exact ⟨one, fun above => zero (by linarith)⟩
  · rintro ⟨one, zero⟩
    exact ⟨one, fun above => zero (by linarith)⟩

/-- Every answer is allowed when the threshold lies in the interval. -/
theorem reflectiveAt_of_mem_interval (O : Oracle Q) (q : Q)
    (lower : S.outputOne q O ≤ S.threshold q) (upper : S.threshold q ≤ S.upper q O) :
    S.ReflectiveAt O q :=
  (S.reflectiveAt_iff_interval O q).mpr
    ⟨fun above => absurd above (not_lt.mpr lower), fun above => absurd above (not_lt.mpr upper)⟩

/-- For a machine that outputs `0` or `1` almost surely the interval is a
point, and the definition is that of Fallenstein, Taylor and Christiano. -/
theorem reflectiveAt_iff_of_noOutput_eq_zero (O : Oracle Q) (q : Q)
    (halts : S.noOutput q O = 0) :
    S.ReflectiveAt O q ↔
      (S.threshold q < S.outputOne q O → O q = 1) ∧
        (S.outputOne q O < S.threshold q → O q = 0) := by
  have same : S.upper q O = S.outputOne q O := by
    have := S.upper_sub_outputOne q O
    linarith
  rw [reflectiveAt_iff_interval, same]

/-! ## Systems without self-reference -/

section Stratified

variable {r : Q → Q → Prop}

/-- The probability of output `1` at each query is determined by the answers
at the queries below it. So no query refers to itself, directly or through
other queries. -/
def Stratified (r : Q → Q → Prop) : Prop :=
  ∀ q (O O' : Oracle Q), (∀ q', r q' q → O q' = O' q') → S.outputOne q O = S.outputOne q O'

open Classical in
/-- Go through the queries in order and answer `1` exactly when the
probability of output `1`, computed from the answers already given, exceeds
the threshold. -/
noncomputable def thresholdOracle (wf : WellFounded r) : Oracle Q :=
  wf.fix fun q below =>
    if S.threshold q < S.outputOne q (fun q' => if h : r q' q then below q' h else 0) then 1
    else 0

open Classical in
theorem thresholdOracle_apply (wf : WellFounded r) (stratified : S.Stratified r) (q : Q) :
    S.thresholdOracle wf q =
      if S.threshold q < S.outputOne q (S.thresholdOracle wf) then 1 else 0 := by
  have unfolded : S.thresholdOracle wf q =
      if S.threshold q < S.outputOne q
          (fun q' => if _ : r q' q then S.thresholdOracle wf q' else 0) then 1
      else 0 :=
    wf.fix_eq _ q
  have same : S.outputOne q (fun q' => if _ : r q' q then S.thresholdOracle wf q' else 0) =
      S.outputOne q (S.thresholdOracle wf) :=
    stratified q _ _ fun q' below => by simp [below]
  rw [unfolded, same]

/-- The answers are `0` or `1`: no randomization is needed. -/
theorem thresholdOracle_eq_zero_or_one (wf : WellFounded r) (stratified : S.Stratified r)
    (q : Q) : S.thresholdOracle wf q = 0 ∨ S.thresholdOracle wf q = 1 := by
  classical
  rw [S.thresholdOracle_apply wf stratified q]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **A stratified system has a reflective oracle.** -/
theorem thresholdOracle_reflective (wf : WellFounded r) (stratified : S.Stratified r) :
    S.Reflective (S.thresholdOracle wf) := by
  classical
  intro q
  have value := S.thresholdOracle_apply wf stratified q
  refine ⟨fun above => by rw [value, if_pos above], fun below => ?_⟩
  have notAbove : ¬S.threshold q < S.outputOne q (S.thresholdOracle wf) := by
    intro above
    exact S.not_forced_both _ q ⟨above, below⟩
  rw [value, if_neg notAbove]

open Classical in
/-- It is the only oracle that answers `1` exactly when the probability of
output `1` exceeds the threshold. -/
theorem eq_thresholdOracle (wf : WellFounded r) (stratified : S.Stratified r) (O : Oracle Q)
    (answers : ∀ q, O q = if S.threshold q < S.outputOne q O then 1 else 0) :
    O = S.thresholdOracle wf := by
  funext q
  refine wf.induction (C := fun q => O q = S.thresholdOracle wf q) q ?_
  intro q below
  rw [answers q, S.thresholdOracle_apply wf stratified q,
    stratified q O (S.thresholdOracle wf) below]

end Stratified

/-! ## Reduction to finitely many queries -/

/-- Both output probabilities of every query are lower semicontinuous in the
oracle: a small change of the answers cannot make an output much less likely.
This holds when each output is produced after finitely many steps. -/
def OutputsLowerSemicontinuous : Prop :=
  ∀ q, LowerSemicontinuous (S.outputOne q) ∧ LowerSemicontinuous (S.outputZero q)

variable {S}

/-- The oracles that answer one query correctly form a closed set. -/
theorem isClosed_reflectiveAt (semicontinuous : S.OutputsLowerSemicontinuous) (q : Q) :
    IsClosed {O : Oracle Q | S.ReflectiveAt O q} := by
  have answerClosed : ∀ value : I, IsClosed {O : Oracle Q | O q = value} := fun value =>
    isClosed_eq (continuous_apply q) continuous_const
  exact IsClosed.and
    (isClosed_imp ((semicontinuous q).1.isOpen_preimage (S.threshold q)) (answerClosed 1))
    (isClosed_imp ((semicontinuous q).2.isOpen_preimage (1 - S.threshold q)) (answerClosed 0))

/-- **Finitely many queries suffice.** If every finite subset of `R` has an
oracle that is reflective on it and agrees with `base` outside `R`, then `R`
has one. -/
theorem exists_reflectiveOn_of_finite (semicontinuous : S.OutputsLowerSemicontinuous)
    (R : Set Q) (base : Oracle Q)
    (finite : ∀ F : Finset Q, ↑F ⊆ R →
      ∃ O, S.ReflectiveOn ↑F O ∧ ∀ q, q ∉ R → O q = base q) :
    ∃ O, S.ReflectiveOn R O ∧ ∀ q, q ∉ R → O q = base q := by
  classical
  let frozen : Set (Oracle Q) := {O | ∀ q, q ∉ R → O q = base q}
  have frozenClosed : IsClosed frozen := by
    have : frozen = ⋂ q, ⋂ (_ : q ∉ R), {O : Oracle Q | O q = base q} := by
      ext O
      simp [frozen]
    rw [this]
    exact isClosed_iInter fun q => isClosed_iInter fun _ =>
      isClosed_eq (continuous_apply q) continuous_const
  obtain ⟨O, inFrozen, inAll⟩ := frozenClosed.isCompact.inter_iInter_nonempty
    (fun q : R => {O : Oracle Q | S.ReflectiveAt O q})
    (fun q => isClosed_reflectiveAt semicontinuous q) (fun F => by
      obtain ⟨O, reflective, agrees⟩ := finite (F.image Subtype.val) (by
        intro q member
        obtain ⟨⟨q', inR⟩, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp member)
        exact inR)
      refine ⟨O, agrees, mem_iInter₂.mpr fun q member => ?_⟩
      exact reflective q (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ member)))
  exact ⟨O, fun q member => mem_iInter.mp inAll ⟨q, member⟩, inFrozen⟩

/-- The same for all queries. -/
theorem exists_reflective_of_finite (semicontinuous : S.OutputsLowerSemicontinuous)
    (finite : ∀ F : Finset Q, ∃ O, S.ReflectiveOn ↑F O) : ∃ O, S.Reflective O := by
  obtain ⟨O, reflective, _⟩ := exists_reflectiveOn_of_finite semicontinuous univ (fun _ => 0)
    fun F _ => by
      obtain ⟨O, reflective⟩ := finite F
      exact ⟨O, reflective, fun q notMember => absurd (mem_univ q) notMember⟩
  exact ⟨O, (S.reflective_iff_reflectiveOn_univ O).mpr reflective⟩

end QuerySystem

end Mettapedia.UniversalAI.ReflectiveOracles
