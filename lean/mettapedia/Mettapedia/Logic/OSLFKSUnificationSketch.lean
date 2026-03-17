import Mettapedia.OSLF.Formula
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.PLNWorldModel
import Mettapedia.Logic.PLNWorldModelCalculus
import Mettapedia.Logic.PLN_KS_Bridge
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.TotalityImprecision

/-!
# OSLF × KS × WM Unification

Core unification theorems connecting three layers:

1. **Meredith** — OSLF behavioral semantics: bisimulation invariance,
   Hennessy-Milner converse (observational equivalence = bisimilarity
   under image-finiteness), observational equivalence quotients
2. **Stay/Baez** — WM evidence semantics: threshold atoms, checker soundness,
   evidence revision, rewrite rule preservation
3. **Knuth/Skilling** — Totality gate: faithful scalarization exists only for
   total orders; BinaryEvidence is non-total (imprecision gate)

All theorems are fully proved (0 sorry).
-/

namespace Mettapedia.Logic.OSLFKSUnificationSketch

open scoped ENNReal

open Mettapedia.OSLF.Formula
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.ProbabilityTheory.KnuthSkilling.TotalityImprecision

abbrev Pat := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
abbrev LangDef := Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef
abbrev RelEnv := Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv

/-! ## Behavioral Equivalence Layer -/

/-- Formula-indistinguishability for OSLF semantics on patterns. -/
def OSLFObsEq (R : Pat → Pat → Prop) (I : AtomSem) (p q : Pat) : Prop :=
  ∀ φ : OSLFFormula, sem R I φ p ↔ sem R I φ q

/-- One-step bisimulation schema over a step relation. -/
def StepBisimulation (R : Pat → Pat → Prop)
    (equiv : Pat → Pat → Prop) : Prop :=
  (∀ p q, equiv p q → ∀ p', R p p' → ∃ q', R q q' ∧ equiv p' q') ∧
  (∀ p q, equiv p q → ∀ q', R q q' → ∃ p', R p p' ∧ equiv p' q')

/-- Main invariance target: bisimilar states satisfy the same OSLF formulas. -/
theorem bisimulation_invariant_sem
    {R : Pat → Pat → Prop}
    {I : AtomSem}
    {equiv : Pat → Pat → Prop}
    (hBisim : StepBisimulation R equiv)
    (hBisimRev : StepBisimulation (fun a b => R b a) equiv)
    (hAtom : ∀ a p q, equiv p q → (I a p ↔ I a q)) :
    ∀ {p q}, equiv p q → ∀ φ : OSLFFormula, sem R I φ p ↔ sem R I φ q := by
  intro p q hpq φ
  induction φ generalizing p q with
  | top => simp [sem]
  | bot => simp [sem]
  | atom a => exact hAtom a p q hpq
  | and φ ψ ihφ ihψ => exact and_congr (ihφ hpq) (ihψ hpq)
  | or φ ψ ihφ ihψ => exact or_congr (ihφ hpq) (ihψ hpq)
  | imp φ ψ ihφ ihψ => exact imp_congr (ihφ hpq) (ihψ hpq)
  | dia φ ih =>
    constructor
    · rintro ⟨p', hp', hsem⟩
      obtain ⟨q', hq', heq⟩ := hBisim.1 p q hpq p' hp'
      exact ⟨q', hq', (ih heq).mp hsem⟩
    · rintro ⟨q', hq', hsem⟩
      obtain ⟨p', hp', heq⟩ := hBisim.2 p q hpq q' hq'
      exact ⟨p', hp', (ih heq).mpr hsem⟩
  | box φ ih =>
    constructor
    · intro h s hsq
      obtain ⟨t, htp, het⟩ := hBisimRev.2 p q hpq s hsq
      exact (ih het).mp (h t htp)
    · intro h s hsp
      obtain ⟨t, htq, het⟩ := hBisimRev.1 p q hpq s hsp
      exact (ih het).mpr (h t htq)

/-- Canonical bisimilarity: two patterns are bisimilar iff some bisimulation relates them. -/
def Bisimilar (R : Pat → Pat → Prop) (p q : Pat) : Prop :=
  ∃ E : Pat → Pat → Prop, StepBisimulation R E ∧ E p q

/-! ### Hennessy-Milner Helpers -/

/-- OSLFObsEq is symmetric: if p and q satisfy the same formulas, so do q and p. -/
lemma obsEq_symm {R : Pat → Pat → Prop} {I : AtomSem} {p q : Pat}
    (h : OSLFObsEq R I p q) : OSLFObsEq R I q p :=
  fun φ => (h φ).symm

/-- If two patterns are NOT observationally equivalent, there exists a formula
that holds at the first but not the second.

If the raw witness separates the wrong way (holds at q, fails at p),
we flip it via negation: `.imp φ .bot`. -/
lemma separator_of_not_obsEq {R : Pat → Pat → Prop} {I : AtomSem} {p q : Pat}
    (h : ¬ OSLFObsEq R I p q) : ∃ φ, sem R I φ p ∧ ¬ sem R I φ q := by
  simp only [OSLFObsEq, not_forall] at h
  obtain ⟨φ, hne⟩ := h
  by_cases hp : sem R I φ p
  · -- φ holds at p; it must fail at q (else ↔ would hold)
    exact ⟨φ, hp, fun hq => hne ⟨fun _ => hq, fun _ => hp⟩⟩
  · -- ¬ sem φ p; then sem φ q must hold (else ↔ would hold trivially)
    have hq : sem R I φ q := by
      by_contra hq; exact hne ⟨fun h => absurd h hp, fun h => absurd h hq⟩
    -- Flip via negation: (.imp φ .bot) holds at p (vacuously) and fails at q
    exact ⟨.imp φ .bot, hp, fun h => h hq⟩

/-- Fold a list of formulas into a conjunction. -/
def conjList : List OSLFFormula → OSLFFormula
  | [] => .top
  | [φ] => φ
  | φ :: rest => .and φ (conjList rest)

/-- Semantics of conjList: holds iff every formula in the list holds. -/
lemma sem_conjList_iff {R : Pat → Pat → Prop} {I : AtomSem} {p : Pat}
    (L : List OSLFFormula) : sem R I (conjList L) p ↔ ∀ φ ∈ L, sem R I φ p := by
  induction L with
  | nil => simp [conjList, sem]
  | cons φ rest ih =>
    cases rest with
    | nil =>
      simp [conjList]
    | cons ψ tl =>
      simp only [conjList, sem]
      constructor
      · rintro ⟨hφ, hrest⟩
        intro χ hχ
        rcases List.mem_cons.mp hχ with rfl | hχ'
        · exact hφ
        · exact (ih.mp hrest) χ hχ'
      · intro hall
        exact ⟨hall φ (.head _),
               ih.mpr (fun χ hχ => hall χ (.tail _ hχ))⟩

/-! ### Main HM Converse -/

/-- OSLFObsEq is itself a step-bisimulation when R is image-finite.

This is the core of the Hennessy-Milner theorem: under finite branching,
observational equivalence coincides with bisimilarity. -/
theorem obsEq_is_stepBisimulation
    {R : Pat → Pat → Prop} {I : AtomSem}
    (hImageFinite : ∀ p : Pat, Set.Finite {q : Pat | R p q}) :
    StepBisimulation R (OSLFObsEq R I) := by
  constructor
  · -- Forth: OSLFObsEq p q → R p p' → ∃ q', R q q' ∧ OSLFObsEq p' q'
    intro p q hpq p' hpp'
    by_contra h_no_match
    push_neg at h_no_match
    -- Every successor q' of q fails to be obsEq to p'
    -- Get finite set of q-successors
    have hfin := hImageFinite q
    -- For each q-successor, get a separator formula
    have hsep : ∀ q' : Pat, R q q' →
        ∃ φ, sem R I φ p' ∧ ¬ sem R I φ q' := by
      intro q' hqq'
      exact separator_of_not_obsEq (h_no_match q' hqq')
    -- Use classical choice to pick separators
    have hchoice := fun q' (h : q' ∈ hfin.toFinset) =>
      hsep q' (hfin.mem_toFinset.mp h)
    choose f hf using hchoice
    -- Build the conjunction of all separator formulas
    let formulas := hfin.toFinset.val.toList.map
      (fun q' => if h : q' ∈ hfin.toFinset then f q' h else .top)
    let Φ := conjList formulas
    -- p' satisfies Φ (each conjunct holds at p')
    have hp'Φ : sem R I Φ p' := by
      rw [sem_conjList_iff]
      intro ψ hψ
      simp only [formulas, List.mem_map] at hψ
      obtain ⟨q', _, rfl⟩ := hψ
      split_ifs with hmem
      · exact (hf q' hmem).1
      · exact trivial
    -- q has no successor satisfying Φ
    have hqΦ : ¬ sem R I (.dia Φ) q := by
      intro ⟨q', hqq', hq'Φ⟩
      have hmem : q' ∈ hfin.toFinset := hfin.mem_toFinset.mpr hqq'
      -- The formula f q' hmem doesn't hold at q'
      have hfail := (hf q' hmem).2
      -- But q' satisfies Φ, so q' satisfies f q' hmem
      rw [sem_conjList_iff] at hq'Φ
      have : sem R I (f q' hmem) q' := by
        apply hq'Φ
        simp only [formulas, List.mem_map]
        exact ⟨q', Multiset.mem_toList.mpr (Finset.mem_val.mpr hmem),
          dif_pos hmem⟩
      exact hfail this
    -- But p satisfies ◇Φ (witnessed by p')
    have hpΦ : sem R I (.dia Φ) p := ⟨p', hpp', hp'Φ⟩
    -- This contradicts OSLFObsEq p q
    exact hqΦ ((hpq (.dia Φ)).mp hpΦ)
  · -- Back: OSLFObsEq p q → R q q' → ∃ p', R p p' ∧ OSLFObsEq p' q'
    -- By symmetry of OSLFObsEq, reduce to the forth direction
    intro p q hpq q' hqq'
    have hpq' := obsEq_symm hpq
    -- Apply forth direction with roles swapped
    by_contra h_no_match
    push_neg at h_no_match
    have hfin := hImageFinite p
    have hsep : ∀ p' : Pat, R p p' →
        ∃ φ, sem R I φ q' ∧ ¬ sem R I φ p' := by
      intro p' hpp'
      have h := h_no_match p' hpp'
      exact separator_of_not_obsEq (fun hobs => h (obsEq_symm hobs))
    choose f hf using fun p' (h : p' ∈ hfin.toFinset) =>
      hsep p' (hfin.mem_toFinset.mp h)
    let formulas := hfin.toFinset.val.toList.map
      (fun p' => if h : p' ∈ hfin.toFinset then f p' h else .top)
    let Φ := conjList formulas
    have hq'Φ : sem R I Φ q' := by
      rw [sem_conjList_iff]
      intro ψ hψ
      simp only [formulas, List.mem_map] at hψ
      obtain ⟨p', _, rfl⟩ := hψ
      split_ifs with hmem
      · exact (hf p' hmem).1
      · exact trivial
    have hpΦ : ¬ sem R I (.dia Φ) p := by
      intro ⟨p', hpp', hp'Φ⟩
      have hmem : p' ∈ hfin.toFinset := hfin.mem_toFinset.mpr hpp'
      have hfail := (hf p' hmem).2
      rw [sem_conjList_iff] at hp'Φ
      have : sem R I (f p' hmem) p' := by
        apply hp'Φ
        simp only [formulas, List.mem_map]
        exact ⟨p', Multiset.mem_toList.mpr (Finset.mem_val.mpr hmem),
          dif_pos hmem⟩
      exact hfail this
    have hqΦ : sem R I (.dia Φ) q := ⟨q', hqq', hq'Φ⟩
    exact hpΦ ((hpq (.dia Φ)).mpr hqΦ)

/-- Hennessy-Milner converse: under image-finiteness, observational equivalence
implies bisimilarity. The proof shows that OSLFObsEq is itself a bisimulation. -/
theorem hm_converse_schema
    {R : Pat → Pat → Prop} {I : AtomSem}
    (hImageFinite : ∀ p : Pat, Set.Finite {q : Pat | R p q}) :
    ∀ {p q}, OSLFObsEq R I p q → Bisimilar R p q := by
  intro p q hpq
  exact ⟨OSLFObsEq R I, obsEq_is_stepBisimulation hImageFinite, hpq⟩

/-! ## WM BinaryEvidence Semantics Layer -/

/-- Thresholded atom semantics induced by WM evidence extraction. -/
noncomputable def thresholdAtomSemOfWM
    {State : Type*}
    [Mettapedia.Logic.EvidenceClass.EvidenceType State]
    [BinaryWorldModel State Pat]
    (W : State) (tau : ℝ≥0∞)
    (queryOfAtom : String → Pat → Pat) : AtomSem :=
  fun a p =>
    tau ≤ BinaryEvidence.toStrength
      (BinaryWorldModel.evidence (State := State) (Query := Pat) W (queryOfAtom a p))

/-- End-to-end executable-to-denotational bridge under WM-threshold atoms. -/
theorem checker_sat_implies_threshold_sem
    {State : Type*}
    [Mettapedia.Logic.EvidenceClass.EvidenceType State]
    [BinaryWorldModel State Pat]
    (lang : LangDef) (relEnv : RelEnv)
    (W : State) (tau : ℝ≥0∞)
    (queryOfAtom : String → Pat → Pat)
    {Icheck : AtomCheck}
    (hAtoms :
      ∀ a p, Icheck a p = true → thresholdAtomSemOfWM W tau queryOfAtom a p)
    {fuel : Nat} {p : Pat} {φ : OSLFFormula}
    (hSat : checkLangUsing relEnv lang Icheck fuel p φ = .sat) :
    sem (Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing relEnv lang)
      (thresholdAtomSemOfWM W tau queryOfAtom) φ p := by
  exact
    checkLangUsing_sat_sound
      (relEnv := relEnv) (lang := lang)
      (I_check := Icheck)
      (I_sem := thresholdAtomSemOfWM W tau queryOfAtom)
      hAtoms hSat

/-- WM revision law lifted directly at query level. -/
theorem wm_evidence_revision
    {State : Type*}
    [Mettapedia.Logic.EvidenceClass.EvidenceType State]
    [BinaryWorldModel State Pat]
    (W1 W2 : State) (q : Pat) :
    BinaryWorldModel.evidence (State := State) (Query := Pat) (W1 + W2) q =
      BinaryWorldModel.evidence (State := State) (Query := Pat) W1 q +
      BinaryWorldModel.evidence (State := State) (Query := Pat) W2 q := by
  simpa using
    (BinaryWorldModel.evidence_add' (State := State) (Query := Pat) W1 W2 q)

/-- WM rewrite soundness preserves thresholded query atoms. -/
theorem wmRewriteRule_preserves_threshold
    {State : Type*}
    [Mettapedia.Logic.EvidenceClass.EvidenceType State]
    [BinaryWorldModel State Pat]
    (r : WMRewriteRule State Pat)
    (hSide : r.side)
    (W : State) (tau : ℝ≥0∞)
    (hDerive : tau ≤ BinaryEvidence.toStrength (r.derive W)) :
    tau ≤ BinaryEvidence.toStrength
      (BinaryWorldModel.evidence (State := State) (Query := Pat) W r.conclusion) := by
  have hSound : r.derive W =
      BinaryWorldModel.evidence (State := State) (Query := Pat) W r.conclusion :=
    r.sound hSide W
  simpa [hSound] using hDerive

/-- Unfolded `◇` semantics as an explicit successor witness theorem. -/
theorem diamond_sem_unfold
    (R : Pat → Pat → Prop) (I : AtomSem) (φ : OSLFFormula) (p : Pat) :
    sem R I (.dia φ) p ↔ ∃ q, R p q ∧ sem R I φ q := by
  rfl

/-! ## KS Totality Gate Layer -/

/-- Scalar faithful regrading exists exactly when requested as a hypothesis. -/
theorem ks_regrading_boolean_fragment
    {alpha : Type*} [PartialOrder alpha]
    (hFaithful : FaithfulPointRepresentation alpha) :
    ∃ Theta : alpha → ℝ, ∀ a b : alpha, a ≤ b ↔ Theta a ≤ Theta b := by
  simpa [FaithfulPointRepresentation] using hFaithful

/-- BinaryEvidence is a canonical non-total case: no faithful point-valued scalarization. -/
theorem evidence_imprecision_gate :
    ¬ FaithfulPointRepresentation BinaryEvidence := by
  exact Mettapedia.Logic.PLN_KS_Bridge.evidence_no_faithfulPointRepresentation

/-- Measurement factors through observational equivalence classes (schema). -/
theorem valuation_factors_through_obsEq
    (mu : Pat → ℝ)
    (equiv : Pat → Pat → Prop)
    (hCompat : ∀ p q, equiv p q → mu p = mu q) :
    ∃ muQ : Quot (fun p q => equiv p q) → ℝ,
      ∀ p, muQ (Quot.mk _ p) = mu p := by
  exact ⟨Quot.lift mu (fun a b h => hCompat a b h), fun _ => rfl⟩

/-! ## Grand Composition Target -/

/-- Grand composition schema (3 layers):
  1. Meredith: bisimulation → observational equivalence
  2. Stay/Baez: measurement factors through observational equivalence classes
  3. Knuth/Skilling: imprecision gate (BinaryEvidence has no faithful point scalarization) -/
theorem oslf_ks_wm_unification_schema :
    -- Layer 1 (Meredith): bisimulation → observational equivalence
    (∀ (R : Pat → Pat → Prop) (I : AtomSem) (equiv : Pat → Pat → Prop),
      StepBisimulation R equiv →
      StepBisimulation (fun a b => R b a) equiv →
      (∀ a p q, equiv p q → (I a p ↔ I a q)) →
      ∀ p q, equiv p q → OSLFObsEq R I p q) ∧
    -- Layer 2 (Stay/Baez): measurement factors through obs eq
    (∀ (mu : Pat → ℝ) (equiv : Pat → Pat → Prop),
      (∀ p q, equiv p q → mu p = mu q) →
      ∃ muQ : Quot (fun p q => equiv p q) → ℝ, ∀ p, muQ (Quot.mk _ p) = mu p) ∧
    -- Layer 3 (Knuth/Skilling): imprecision gate
    (¬ FaithfulPointRepresentation BinaryEvidence) := by
  exact ⟨
    fun R I equiv hB hBR hA p q hpq φ => bisimulation_invariant_sem hB hBR hA hpq φ,
    fun mu equiv hC => (valuation_factors_through_obsEq mu equiv hC),
    evidence_imprecision_gate⟩

end Mettapedia.Logic.OSLFKSUnificationSketch
