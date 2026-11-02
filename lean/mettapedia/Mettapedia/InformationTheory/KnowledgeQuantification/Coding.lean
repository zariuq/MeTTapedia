import Mettapedia.InformationTheory.KnowledgeQuantification.Amortization
import Mettapedia.InformationTheory.CodebookRelativity
import Mettapedia.InformationTheory.CountablePriorCoding
import Mettapedia.InformationTheory.FinitePriorCoding
import Mettapedia.InformationTheory.RelationStoreKolmogorov
import Mettapedia.Enactive.Razor

/-!
# Knowledge and codes: codebook relativity, Kolmogorov floors and razors

The theory length `−log p(τ)` of D. Fanelli, *A theory and methodology to quantify
knowledge*, R. Soc. open sci. 6: 181055 (2019), is a code length.  The paper treats it as
language-independent up to a constant (§2.2.3); at a finite number of uses the constant
matters.

* `knowledgeSelector_strictlyPrefersShorter`, `knowledgeSelector_not_codebookInvariant`:
  among theories with one effect, selecting by `K` with lengths read from a prefix codebook
  prefers the shorter codeword, so reindexing the codebook reverses its choice
  (`CodebookRelativity.not_codebookInvariant_of_unequal_lengths`), on finite and countably
  infinite theory classes alike.
* `eventually_knowledgeSelectorAt_iff`: as the uses grow, any two codebooks eventually agree
  on every pair of theories with different residuals.
* `knowledge_codePrior_sandwich`: a positive finite prior and the factor-two prefix codebook
  of `FinitePriorCoding` give theory lengths within `log 2` of each other, so they bound each
  other's knowledge.
* `tendsto_knowledge_of_summable_prior`: the paper takes theories uniform over a finite
  alphabet.  Over a countably infinite class no positive prior is uniform
  (`CountablePriorCoding.no_strictlyPositive_uniform_summable_mass`), and under every positive
  summable prior the theory lengths grow without bound, so at a fixed number of uses the
  knowledge of the `n`-th theory tends to zero; `geometricPrior_length` gives the lengths
  `(n + 1) log 2` of the unary code.
* `exists_relation_lossless_knowledge_le`: for every size `N ≤ M` some `N`-element relation
  over `M` tuples has no program shorter than `⌊log₂ C(M, N)⌋` bits for its bitmap
  (`RelationStoreFloors.exists_relation_kolmogorov_ge`), so a lossless theory that is a
  program for it holds at most `E / (E + ⌊log₂ C(M, N)⌋)` knowledge.  This is the rigorous
  form of the paper's argument that listing is not knowledge (eq. 2.28).
* `twoPartCode_knowledge_disagree`: knowledge and the two-part code are different razor
  profiles (`Enactive.Razor`); on the pair of `mdl_choice_ne_knowledge_choice` they disagree,
  and their product leaves the pair incomparable.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.InformationTheory.KnowledgeQuantification

open Filter Topology
open Mettapedia.InformationTheory.CodebookRelativity

namespace Budget

/-! ## Codebook relativity -/

section Codebooks

universe u

variable {Hypothesis : Type u}

/-- Select by `K` among theories with one explanandum, residual and input, reading each
theory's length from the codebook: `left` is selected over `right` when its knowledge is at
least as large. -/
def knowledgeSelector (E R I : ℝ) : Selector Hypothesis :=
  fun codebook left right =>
    (⟨E, R, I, (codebook.length right : ℝ)⟩ : Budget).knowledge ≤
      (⟨E, R, I, (codebook.length left : ℝ)⟩ : Budget).knowledge

theorem knowledge_lt_of_length_lt {E R I : ℝ} (hexpl : R < E) (hpos : 0 < E + I) {m n : ℕ}
    (hmn : m < n) :
    (⟨E, R, I, (n : ℝ)⟩ : Budget).knowledge < (⟨E, R, I, (m : ℝ)⟩ : Budget).knowledge := by
  apply knowledge_lt_of_theory_lt (b := ⟨E, R, I, (m : ℝ)⟩) (b' := ⟨E, R, I, (n : ℝ)⟩) rfl rfl rfl
  · change 0 < E - R
    linarith
  · change 0 < E + I + (m : ℝ)
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  · change (m : ℝ) < n
    exact_mod_cast hmn

/-- Selecting by `K` among equally effective theories prefers the shorter codeword. -/
theorem knowledgeSelector_strictlyPrefersShorter {E R I : ℝ} (hexpl : R < E)
    (hpos : 0 < E + I) :
    StrictlyPrefersShorter (knowledgeSelector (Hypothesis := Hypothesis) E R I) := by
  intro codebook shorter longer hlen
  have hlt := knowledge_lt_of_length_lt hexpl hpos hlen
  exact ⟨hlt.le, not_le.2 hlt⟩

/-- **`K` is codebook-relative.**  On any theory class with two codewords of different
lengths, reindexing the codebook reverses the selection by `K`. -/
theorem knowledgeSelector_not_codebookInvariant {E R I : ℝ} (hexpl : R < E) (hpos : 0 < E + I)
    (codebook : PrefixCodebook Hypothesis) {shorter longer : Hypothesis}
    (hlen : codebook.length shorter < codebook.length longer) :
    ¬ CodebookInvariant (knowledgeSelector (Hypothesis := Hypothesis) E R I) :=
  not_codebookInvariant_of_unequal_lengths _
    (knowledgeSelector_strictlyPrefersShorter hexpl hpos) codebook hlen

/-- The reversal already occurs on a countably infinite class of theories. -/
theorem knowledgeSelector_nat_not_codebookInvariant {E R I : ℝ} (hexpl : R < E)
    (hpos : 0 < E + I) :
    ¬ CodebookInvariant (knowledgeSelector (Hypothesis := ℕ) E R I) :=
  nat_not_codebookInvariant _ (knowledgeSelector_strictlyPrefersShorter hexpl hpos)

/-- Select by `K` at `n` uses: theory `h` leaves residual `residual h` per use, and its
length is read from the codebook. -/
def knowledgeSelectorAt (n : ℕ) (e i : ℝ) (residual : Hypothesis → ℝ) : Selector Hypothesis :=
  fun codebook left right =>
    (ofUses n e (residual right) i (codebook.length right)).knowledge ≤
      (ofUses n e (residual left) i (codebook.length left)).knowledge

/-- **Codebook relativity vanishes with use.**  For any two codebooks and any two theories
with different residuals, the selections by `K` eventually agree as the uses grow. -/
theorem eventually_knowledgeSelectorAt_iff {e i : ℝ} (hpos : 0 < e + i)
    (residual : Hypothesis → ℝ) (first second : PrefixCodebook Hypothesis)
    {left right : Hypothesis} (hne : residual left ≠ residual right) :
    ∀ᶠ n : ℕ in atTop,
      (knowledgeSelectorAt n e i residual first left right ↔
        knowledgeSelectorAt n e i residual second left right) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hlim : (e - residual right) / (e + i) < (e - residual left) / (e + i) :=
      div_lt_div_of_pos_right (by linarith) hpos
    filter_upwards [eventually_knowledge_lt (L := (first.length right : ℝ))
        (L' := (first.length left : ℝ)) hpos hpos hlim,
      eventually_knowledge_lt (L := (second.length right : ℝ))
        (L' := (second.length left : ℝ)) hpos hpos hlim] with n h1 h2
    exact ⟨fun _ => h2.le, fun _ => h1.le⟩
  · have hlim : (e - residual left) / (e + i) < (e - residual right) / (e + i) :=
      div_lt_div_of_pos_right (by linarith) hpos
    filter_upwards [eventually_knowledge_lt (L := (first.length left : ℝ))
        (L' := (first.length right : ℝ)) hpos hpos hlim,
      eventually_knowledge_lt (L := (second.length left : ℝ))
        (L' := (second.length right : ℝ)) hpos hpos hlim] with n h1 h2
    exact ⟨fun h => absurd h (not_le.2 h1), fun h => absurd h (not_le.2 h2)⟩

end Codebooks

/-! ## A finite prior and its prefix code -/

section FinitePriors

open Mettapedia.InformationTheory.FinitePriorCoding

variable {Hypothesis : Type*} [Fintype Hypothesis] [Nonempty Hypothesis]

theorem inducedOccamPrior_pos (prior : PositivePrior Hypothesis) (τ : Hypothesis) :
    0 < prior.inducedOccamPrior τ :=
  lt_of_lt_of_le (div_pos (prior.positive τ) two_pos) (prior.half_mass_le_inducedOccamPrior τ)

theorem inducedOccamPrior_le_one (prior : PositivePrior Hypothesis) (τ : Hypothesis) :
    prior.inducedOccamPrior τ ≤ 1 := by
  rw [← prior.sum_inducedOccamPrior]
  exact Finset.single_le_sum (fun σ _ => (inducedOccamPrior_pos prior σ).le) (Finset.mem_univ τ)

/-- **A prior and its prefix code give nearly the same knowledge.**  The theory length
`−log p(τ)` comes from a prior; `FinitePriorCoding` builds a prefix codebook whose normalized
code prior `inducedOccamPrior` lies within a factor two of it
(`exists_prefixCodebook_factor_two`).  Its theory length therefore lies within `log 2` of
`−log p(τ)`, and the knowledge it gives lies between the values at those two lengths. -/
theorem knowledge_codePrior_sandwich (prior : PositivePrior Hypothesis) (τ : Hypothesis)
    {E R I : ℝ} (hRE : R ≤ E)
    (hshort : 0 < E + I + (-Real.log (prior.mass τ) - Real.log 2)) :
    (⟨E, R, I, -Real.log (prior.mass τ) + Real.log 2⟩ : Budget).knowledge ≤
        (⟨E, R, I, -Real.log (prior.inducedOccamPrior τ)⟩ : Budget).knowledge ∧
      (⟨E, R, I, -Real.log (prior.inducedOccamPrior τ)⟩ : Budget).knowledge ≤
        (⟨E, R, I, -Real.log (prior.mass τ) - Real.log 2⟩ : Budget).knowledge := by
  have hm := prior.positive τ
  have hq := inducedOccamPrior_pos prior τ
  have hlow : Real.log (prior.mass τ / 2) ≤ Real.log (prior.inducedOccamPrior τ) :=
    Real.log_le_log (by positivity) (prior.half_mass_le_inducedOccamPrior τ)
  have hhigh : Real.log (prior.inducedOccamPrior τ) ≤ Real.log (2 * prior.mass τ) :=
    Real.log_le_log hq (prior.inducedOccamPrior_le_twice_mass τ)
  rw [Real.log_div hm.ne' two_ne_zero] at hlow
  rw [Real.log_mul two_ne_zero hm.ne'] at hhigh
  have hlen : 0 ≤ -Real.log (prior.inducedOccamPrior τ) := by
    have := Real.log_nonpos hq.le (inducedOccamPrior_le_one prior τ)
    linarith
  constructor
  · apply knowledge_le_knowledge_of_le
    · change 0 < E + I + -Real.log (prior.inducedOccamPrior τ)
      linarith
    · change 0 ≤ E - R
      linarith
    · exact le_rfl
    · change E + I + -Real.log (prior.inducedOccamPrior τ) ≤
        E + I + (-Real.log (prior.mass τ) + Real.log 2)
      linarith
  · apply knowledge_le_knowledge_of_le
    · exact hshort
    · change 0 ≤ E - R
      linarith
    · exact le_rfl
    · change E + I + (-Real.log (prior.mass τ) - Real.log 2) ≤
        E + I + -Real.log (prior.inducedOccamPrior τ)
      linarith

end FinitePriors

/-! ## Priors over infinitely many theories -/

section CountablePriors

open Mettapedia.InformationTheory.CountablePriorCoding

/-- **No uniform cost over infinitely many theories.**  The paper takes the theory variable
uniform over the `2^l` theories of a given length (§2.2.1).  Over a countably infinite
class no positive mass is uniform (`no_strictlyPositive_uniform_summable_mass`), and under
every positive summable prior the theory lengths `−log p(τ_n)` grow without bound, so at a
fixed number of uses the knowledge of the `n`-th theory tends to zero. -/
theorem tendsto_knowledge_of_summable_prior {mass : ℕ → ℝ} (hpos : ∀ n, 0 < mass n)
    (hsum : Summable mass) (E R I : ℝ) :
    Tendsto (fun n => (⟨E, R, I, -Real.log (mass n)⟩ : Budget).knowledge) atTop (𝓝 0) := by
  have h0 : Tendsto mass atTop (𝓝 0) := hsum.tendsto_atTop_zero
  have h0' : Tendsto mass atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨h0, Eventually.of_forall hpos⟩
  have hlog : Tendsto (fun n => Real.log (mass n)) atTop atBot :=
    Real.tendsto_log_nhdsGT_zero.comp h0'
  have hL : Tendsto (fun n => -Real.log (mass n)) atTop atTop :=
    tendsto_neg_atBot_atTop.comp hlog
  have hden : Tendsto (fun n => E + I + -Real.log (mass n)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ hL
  show Tendsto (fun n => (E - R) / (E + I + -Real.log (mass n))) atTop (𝓝 0)
  exact tendsto_const_nhds.div_atTop hden

/-- Under the prior of the unary code, the `n`-th theory has length `(n + 1) log 2`. -/
theorem geometricPrior_length (n : ℕ) :
    -Real.log (geometricPrior.mass n) = ((n : ℝ) + 1) * Real.log 2 := by
  rw [geometricPrior_mass, geometricMass,
    Real.log_div (by norm_num : (1 : ℝ) / 2 ≠ 0) (by positivity : (2 : ℝ) ^ n ≠ 0),
    Real.log_pow, one_div, Real.log_inv]
  ring

/-- The unary-code prior is summable, so its theories' knowledge vanishes along the code. -/
theorem tendsto_knowledge_geometricPrior (E R I : ℝ) :
    Tendsto (fun n => (⟨E, R, I, -Real.log (geometricPrior.mass n)⟩ : Budget).knowledge) atTop
      (𝓝 0) :=
  tendsto_knowledge_of_summable_prior geometricPrior.positive geometricPrior_hasSum_one.summable
    E R I

end CountablePriors

/-! ## Kolmogorov floors -/

section Kolmogorov

open KolmogorovComplexity Mettapedia.InformationTheory.RelationStoreFloors

/-- **Incompressible explananda bound lossless knowledge** (eq. 2.28, §2.3.4).  For every size
`N ≤ M` some `N`-element relation over `M` tuples has no program for its bitmap shorter than
`⌊log₂ C(M, N)⌋` bits.  A lossless, input-free theory that is such a program, explaining `E`
bits, holds at most `E / (E + ⌊log₂ C(M, N)⌋)`. -/
theorem exists_relation_lossless_knowledge_le {M N : ℕ} (hN : N ≤ M) {E : ℝ} (hE : 0 < E) :
    ∃ s : Finset (Fin M), s.card = N ∧
      ∀ p : BinString, bitmapEncode s ∈ (Classical.choose exists_optimal_algorithm) p →
        (⟨E, 0, 0, (p.length : ℝ)⟩ : Budget).knowledge ≤
          E / (E + (Nat.log 2 (M.choose N) : ℝ)) := by
  obtain ⟨s, hs, hK⟩ := exists_relation_kolmogorov_ge hN
  refine ⟨s, hs, fun p hp => ?_⟩
  have hlen : Nat.log 2 (M.choose N) ≤ p.length :=
    hK.trans (complexity_le_of_program _ _ p hp)
  have hlen' : ((Nat.log 2 (M.choose N) : ℕ) : ℝ) ≤ (p.length : ℝ) := by exact_mod_cast hlen
  have hlog : (0 : ℝ) ≤ ((Nat.log 2 (M.choose N) : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold knowledge explained total
  dsimp only
  rw [sub_zero, add_zero]
  exact div_le_div_of_nonneg_left hE.le (by linarith) (by linarith)

end Kolmogorov

end Budget

/-! ## Razor profiles -/

section Razors

open Mettapedia.Enactive.Razor

/-- Knowledge as a selection profile: maximize `K`. -/
def knowledgeCriterion {Candidate : Type*} (admissible : Candidate → Prop)
    (budget : Candidate → Budget) : Criterion Candidate :=
  Criterion.ofBenefit admissible fun candidate => (budget candidate).knowledge

/-- The two theories of `Budget.mdl_choice_ne_knowledge_choice`, as candidates. -/
def mdlPair : Bool → Budget
  | false => Budget.shortLossy
  | true => Budget.longerSharper

/-- Their theory lengths. -/
def mdlTheory : Bool → ℕ
  | false => 1
  | true => 5

/-- Their residuals. -/
def mdlResidual : Bool → ℕ
  | false => 6
  | true => 4

theorem mdlPair_twoPartLength (b : Bool) :
    (mdlPair b).twoPartLength = ((mdlTheory b + mdlResidual b : ℕ) : ℝ) := by
  cases b <;> norm_num [mdlPair, mdlTheory, mdlResidual, Budget.twoPartLength,
    Budget.shortLossy, Budget.longerSharper]

/-- **Knowledge and the two-part code are different razors.**  On the pair of
`Budget.mdl_choice_ne_knowledge_choice` the two-part code prefers the first theory and
knowledge the second; their product, which assigns no exchange rate, leaves the pair
incomparable. -/
theorem twoPartCode_knowledge_disagree :
    let mdl := twoPartCode (fun b => (mdlPair b).Admissible) mdlTheory mdlResidual
    let kq := knowledgeCriterion (fun b => (mdlPair b).Admissible) mdlPair
    (mdl.atLeastAsGood false true ∧ ¬ mdl.atLeastAsGood true false) ∧
      (kq.atLeastAsGood true false ∧ ¬ kq.atLeastAsGood false true) ∧
      ¬ (mdl.product kq).atLeastAsGood false true ∧ ¬ (mdl.product kq).atLeastAsGood true false := by
  intro mdl kq
  have hK := Budget.mdl_choice_ne_knowledge_choice.2
  have hmdl1 : mdl.atLeastAsGood false true := by
    change mdlTheory false + mdlResidual false ≤ mdlTheory true + mdlResidual true
    decide
  have hmdl2 : ¬ mdl.atLeastAsGood true false := by
    change ¬ (mdlTheory true + mdlResidual true ≤ mdlTheory false + mdlResidual false)
    decide
  have hkq1 : kq.atLeastAsGood true false := by
    change (mdlPair false).knowledge ≤ (mdlPair true).knowledge
    exact hK.le
  have hkq2 : ¬ kq.atLeastAsGood false true := by
    change ¬ ((mdlPair true).knowledge ≤ (mdlPair false).knowledge)
    exact not_le.2 hK
  refine ⟨⟨hmdl1, hmdl2⟩, ⟨hkq1, hkq2⟩, ?_, ?_⟩
  · rw [Criterion.product_atLeastAsGood]
    exact fun h => hkq2 h.2
  · rw [Criterion.product_atLeastAsGood]
    exact fun h => hmdl2 h.1

end Razors

end Mettapedia.InformationTheory.KnowledgeQuantification
