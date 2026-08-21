import Mettapedia.OSLF.Formula
import Mettapedia.OSLF.Framework.CategoryBridge
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.NativeType.Construction
import Mettapedia.PLN.Evidence.EvidenceQuantale
import Mettapedia.PLN.WorldModel.PLNWorldModel
import Mettapedia.PLN.WorldModel.PLNWorldModelCalculus
import Mettapedia.PLN.Evidence.PLN_KS_Bridge
import KnuthSkilling.Core.HeytingBounds
import KnuthSkilling.Core.TotalityImprecision

/-!
# OSLF × KS × WM Unification

Core unification theorems connecting three layers:

1. **Meredith** — OSLF behavioral semantics: bisimulation invariance,
   Hennessy-Milner converse (observational equivalence = bisimilarity
   under image-finiteness), observational equivalence quotients
2. **Stay/Baez** — WM evidence semantics: threshold atoms, checker soundness,
   evidence revision, rewrite rule preservation
3. **Knuth/Skilling** — one-way scalar fidelity is distinguished from the
   stronger order-reflection gate; Heyting complement slack is distinguished
   from both

-/

namespace Mettapedia.OSLF.Framework.KSUnificationSketch

open scoped ENNReal

open CategoryTheory
open Opposite
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.Framework.CategoryBridge
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.PLN.Evidence.EvidenceQuantale
open Mettapedia.PLN.WorldModel.PLNWorldModel
open KnuthSkilling.Heyting
open KnuthSkilling.TotalityImprecision

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
    push Not at h_no_match
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
    push Not at h_no_match
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
    [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
    [BinaryWorldModel State Pat]
    (W : State) (tau : ℝ≥0∞)
    (queryOfAtom : String → Pat → Pat) : AtomSem :=
  fun a p =>
    tau ≤ BinaryEvidence.toStrength
      (BinaryWorldModel.evidence (State := State) (Query := Pat) W (queryOfAtom a p))

/-- End-to-end executable-to-denotational bridge under WM-threshold atoms. -/
theorem checker_sat_implies_threshold_sem
    {State : Type*}
    [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
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
    [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
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
    [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
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

/-! ## Scalar Order-Reflection Gate -/

/-- An order-reflecting scalar readout is exactly an order embedding into `ℝ`.
This is stronger than the one-way fidelity condition used by K&S. -/
theorem orderReflecting_scalar_readout
    {alpha : Type*} [PartialOrder alpha]
    (hReflecting : OrderReflectingPointRepresentation alpha) :
    ∃ Theta : alpha → ℝ, ∀ a b : alpha, a ≤ b ↔ Theta a ≤ Theta b := by
  simpa [OrderReflectingPointRepresentation] using hReflecting

/-- BinaryEvidence is a canonical non-total case: no scalar readout can both
preserve and reflect its coordinatewise order. -/
theorem evidence_orderReflection_gate :
    ¬ OrderReflectingPointRepresentation BinaryEvidence := by
  exact Mettapedia.PLN.Evidence.PLN_KS_Bridge.evidence_no_orderReflectingPointRepresentation

/-! ## Native-Type Heyting Probability Gate -/

/-- Every OSLF native-type fiber is a complete Heyting algebra.  For any
normalized modular valuation, Boolean complement behavior collapses the
canonical lower and upper bounds to a point.  If the valuation detects a
failure of excluded middle, the classical complement equation fails and the
bounds are strictly distinct. -/
theorem nativeType_heyting_probability_gate
    (L : Mettapedia.CategoryTheory.LambdaTheories.LambdaTheory)
    (S : L.Obj)
    (ν : ModularValuation (Mettapedia.OSLF.NativeType.NatTypeFiber L S))
    (a : Mettapedia.OSLF.NativeType.NatTypeFiber L S) :
    ν.val a + ν.val aᶜ = ν.val (a ⊔ aᶜ) ∧
    lowerBound ν a ≤ upperBound ν a ∧
    (a ⊔ aᶜ = ⊤ → lowerBound ν a = upperBound ν a) ∧
    (ν.val (a ⊔ aᶜ) < 1 →
      ν.val a + ν.val aᶜ < 1 ∧ lowerBound ν a < upperBound ν a) := by
  have hmod := ν.modular a aᶜ
  rw [inf_compl_self, ν.val_bot, add_zero] at hmod
  refine ⟨hmod, lower_le_upper ν a, ?_, ?_⟩
  · intro hem
    have hgap := gap_zero_of_em ν a hem
    linarith
  · intro hdetect
    constructor
    · rw [hmod]
      exact hdetect
    · have hnot : a ⊔ aᶜ ≠ ⊤ := by
        intro hem
        rw [hem, ν.val_top] at hdetect
        exact (lt_irrefl 1) hdetect
      have hgap := gap_pos_of_not_em ν a hnot hdetect
      linarith

/-! ### A concrete `LanguageDef → NTT → Heyting gap` witness -/

/-- Native predicates over the representable `Name` sort generated from the
actual `rhoCalc` language presentation. -/
abbrev RhoNameNativeFiber :=
  languageSortFiber rhoCalc rhoName

noncomputable instance : Order.Frame RhoNameNativeFiber := by
  dsimp [RhoNameNativeFiber, languageSortFiber, languagePresheafLambdaTheory]
  infer_instance

/-- The identity path at the rho name sort, named to keep the two sampled
constructor paths syntactically explicit. -/
def rhoNameIdentity : rhoNameObj ⟶ rhoNameObj :=
  SortPath.nil

/-- The native predicate generated by the authored constructor
`NQuote : Proc → Name`.  At a constructor context `X`, it contains exactly the
paths `X → Name` that factor through `NQuote`. -/
noncomputable def rhoQuotePredicate : RhoNameNativeFiber where
  obj X := {g | ∃ h : SortPath rhoCalc (unop X).sort rhoProc,
    SortPath.comp h nquoteMor = g}
  map := by
    intro X Y i g
    rintro ⟨h, rfl⟩
    refine ⟨SortPath.comp i.unop h, ?_⟩
    change SortPath.comp (SortPath.comp i.unop h) nquoteMor =
      SortPath.comp i.unop (SortPath.comp h nquoteMor)
    exact SortPath.comp_assoc i.unop h nquoteMor

theorem nquote_mem_rhoQuotePredicate :
    rhoQuotePredicate.obj (op rhoProcObj) nquoteMor := by
  exact ⟨SortPath.nil, SortPath.nil_comp nquoteMor⟩

theorem nameIdentity_not_mem_rhoQuotePredicate :
    ¬ rhoQuotePredicate.obj (op rhoNameObj) rhoNameIdentity := by
  rintro ⟨h, hh⟩
  change SortPath.comp h nquoteMor = SortPath.nil at hh
  simp [nquoteMor, SortArrow.toPath, SortPath.comp] at hh

/-- The real-valued indicator of a proposition. -/
private noncomputable def truthIndicator (p : Prop) : ℝ :=
  by
    classical
    exact if p then 1 else 0

private theorem truthIndicator_mono {p q : Prop} (hpq : p → q) :
    truthIndicator p ≤ truthIndicator q := by
  classical
  by_cases hp : p
  · have hq : q := hpq hp
    simp [truthIndicator, hp, hq]
  · by_cases hq : q <;> simp [truthIndicator, hp, hq]

private theorem truthIndicator_modular (p q : Prop) :
    truthIndicator p + truthIndicator q =
      truthIndicator (p ∨ q) + truthIndicator (p ∧ q) := by
  classical
  by_cases hp : p <;> by_cases hq : q <;>
    simp [truthIndicator, hp, hq]

/-- A normalized modular valuation on the concrete rho native-type fiber.
It observes whether a native predicate contains the identity at `Name` and
whether it contains `NQuote`, assigning equal weight to the two observations.
Naturality ensures identity membership implies `NQuote` membership. -/
noncomputable def rhoNameNativeValuation : ModularValuation RhoNameNativeFiber where
  val := fun predicate =>
    (truthIndicator (predicate.obj (op rhoNameObj) rhoNameIdentity) +
      truthIndicator (predicate.obj (op rhoProcObj) nquoteMor)) / 2
  monotone := by
    intro first second h
    apply div_le_div_of_nonneg_right
    · exact add_le_add
        (truthIndicator_mono (fun hp ↦ h _ hp))
        (truthIndicator_mono (fun hp ↦ h _ hp))
    · norm_num
  val_bot := by
    change (truthIndicator False + truthIndicator False) / 2 = 0
    norm_num [truthIndicator]
  val_top := by
    change (truthIndicator True + truthIndicator True) / 2 = 1
    norm_num [truthIndicator]
  modular := by
    intro first second
    have hIdentity := truthIndicator_modular
      (first.obj (op rhoNameObj) rhoNameIdentity)
      (second.obj (op rhoNameObj) rhoNameIdentity)
    have hQuote := truthIndicator_modular
      (first.obj (op rhoProcObj) nquoteMor)
      (second.obj (op rhoProcObj) nquoteMor)
    change
      (truthIndicator (first.obj (op rhoNameObj) rhoNameIdentity) +
          truthIndicator (first.obj (op rhoProcObj) nquoteMor)) / 2 +
        (truthIndicator (second.obj (op rhoNameObj) rhoNameIdentity) +
          truthIndicator (second.obj (op rhoProcObj) nquoteMor)) / 2 =
      (truthIndicator
          (first.obj (op rhoNameObj) rhoNameIdentity ∨
            second.obj (op rhoNameObj) rhoNameIdentity) +
          truthIndicator
            (first.obj (op rhoProcObj) nquoteMor ∨
              second.obj (op rhoProcObj) nquoteMor)) / 2 +
        (truthIndicator
          (first.obj (op rhoNameObj) rhoNameIdentity ∧
            second.obj (op rhoNameObj) rhoNameIdentity) +
          truthIndicator
            (first.obj (op rhoProcObj) nquoteMor ∧
              second.obj (op rhoProcObj) nquoteMor)) / 2
    linarith

theorem rhoQuotePredicate_value :
    rhoNameNativeValuation.val rhoQuotePredicate = (1 : ℝ) / 2 := by
  norm_num [rhoNameNativeValuation, truthIndicator,
    nameIdentity_not_mem_rhoQuotePredicate, nquote_mem_rhoQuotePredicate]

theorem nquote_not_mem_rhoQuotePredicate_compl :
    ¬ (rhoQuotePredicateᶜ).obj (op rhoProcObj) nquoteMor := by
  intro hcompl
  have hboth :
      (rhoQuotePredicate ⊓ rhoQuotePredicateᶜ).obj (op rhoProcObj) nquoteMor :=
    ⟨nquote_mem_rhoQuotePredicate, hcompl⟩
  rw [inf_compl_self] at hboth
  exact hboth

theorem nameIdentity_not_mem_rhoQuotePredicate_compl :
    ¬ (rhoQuotePredicateᶜ).obj (op rhoNameObj) rhoNameIdentity := by
  intro hid
  have hnquote : (rhoQuotePredicateᶜ).obj (op rhoProcObj) nquoteMor := by
    have hmapped := (rhoQuotePredicateᶜ).map nquoteMor.op hid
    change (rhoQuotePredicateᶜ).obj (op rhoProcObj)
      (SortPath.comp nquoteMor rhoNameIdentity) at hmapped
    change (rhoQuotePredicateᶜ).obj (op rhoProcObj)
      (SortPath.comp nquoteMor SortPath.nil) at hmapped
    have hpath : SortPath.comp nquoteMor SortPath.nil = nquoteMor :=
      SortPath.comp_nil nquoteMor
    exact hpath ▸ hmapped
  exact nquote_not_mem_rhoQuotePredicate_compl hnquote

theorem rhoQuotePredicate_compl_value :
    rhoNameNativeValuation.val rhoQuotePredicateᶜ = 0 := by
  norm_num [rhoNameNativeValuation, truthIndicator,
    nameIdentity_not_mem_rhoQuotePredicate_compl,
    nquote_not_mem_rhoQuotePredicate_compl]

/-- The quote-generated native predicate is an explicit failure of excluded
middle in the `Name` fiber of `rhoCalc`. -/
theorem rhoQuotePredicate_excludedMiddle_ne_top :
    rhoQuotePredicate ⊔ rhoQuotePredicateᶜ ≠ ⊤ := by
  intro hem
  have hcollapse := gap_zero_of_em rhoNameNativeValuation rhoQuotePredicate hem
  change
    (1 - rhoNameNativeValuation.val rhoQuotePredicateᶜ) -
      rhoNameNativeValuation.val rhoQuotePredicate = 0 at hcollapse
  rw [rhoQuotePredicate_compl_value, rhoQuotePredicate_value] at hcollapse
  norm_num at hcollapse

/-- The concrete rho `Name` native fiber is not Boolean under its canonical
Heyting pseudo-complement. -/
theorem rhoNameNativeFiber_not_boolean :
    ¬ ∀ predicate : RhoNameNativeFiber, predicate ⊔ predicateᶜ = ⊤ := by
  intro hBoolean
  exact rhoQuotePredicate_excludedMiddle_ne_top (hBoolean rhoQuotePredicate)

/-- **Concrete OSLF dimensionality witness.**  The actual `rhoCalc`
`LanguageDef`, passed through its presheaf native type theory, has a native
predicate whose direct-support and not-refuted plausibility bounds are
different.  Consequently no single point probability can equal both bounds.

This is a necessity theorem for the two-bound readout, not a claim that the
whole Heyting lattice lacks scalar valuations or cannot be encoded into one
real number under weaker requirements. -/
theorem rhoCalc_nativeType_requires_distinct_probability_bounds :
    rhoNameNativeValuation.val rhoQuotePredicate = (1 : ℝ) / 2 ∧
    rhoNameNativeValuation.val rhoQuotePredicateᶜ = 0 ∧
    rhoQuotePredicate ⊔ rhoQuotePredicateᶜ ≠ ⊤ ∧
    lowerBound rhoNameNativeValuation rhoQuotePredicate = (1 : ℝ) / 2 ∧
    upperBound rhoNameNativeValuation rhoQuotePredicate = 1 ∧
    lowerBound rhoNameNativeValuation rhoQuotePredicate <
      upperBound rhoNameNativeValuation rhoQuotePredicate ∧
    ¬ ∃ point : ℝ,
      point = lowerBound rhoNameNativeValuation rhoQuotePredicate ∧
      point = upperBound rhoNameNativeValuation rhoQuotePredicate := by
  have hvalue := rhoQuotePredicate_value
  have hcompl := rhoQuotePredicate_compl_value
  constructor
  · exact hvalue
  constructor
  · exact hcompl
  constructor
  · exact rhoQuotePredicate_excludedMiddle_ne_top
  constructor
  · change rhoNameNativeValuation.val rhoQuotePredicate = (1 : ℝ) / 2
    exact hvalue
  constructor
  · change 1 - rhoNameNativeValuation.val rhoQuotePredicateᶜ = 1
    rw [hcompl]
    norm_num
  constructor
  · change rhoNameNativeValuation.val rhoQuotePredicate <
      1 - rhoNameNativeValuation.val rhoQuotePredicateᶜ
    rw [hvalue, hcompl]
    norm_num
  · rintro ⟨point, hlower, hupper⟩
    change point = rhoNameNativeValuation.val rhoQuotePredicate at hlower
    change point = 1 - rhoNameNativeValuation.val rhoQuotePredicateᶜ at hupper
    rw [hvalue] at hlower
    rw [hcompl] at hupper
    norm_num at hupper
    linarith

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
  3. Scalar order reflection: BinaryEvidence has no order embedding into `ℝ` -/
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
    -- Layer 3: order-reflection gate
    (¬ OrderReflectingPointRepresentation BinaryEvidence) := by
  exact ⟨
    fun R I equiv hB hBR hA p q hpq φ => bisimulation_invariant_sem hB hBR hA hpq φ,
    fun mu equiv hC => (valuation_factors_through_obsEq mu equiv hC),
    evidence_orderReflection_gate⟩

end Mettapedia.OSLF.Framework.KSUnificationSketch
