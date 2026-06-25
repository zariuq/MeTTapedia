import Mettapedia.OSLF.Framework.KSUnificationSketch
import Mettapedia.OSLF.Framework.EvidenceSemantics

/-!
# Observer-Induced Distinction Graph

Repackages OSLF observational equivalence (`OSLFObsEq`) as an explicit graph
structure on patterns:

- **Nodes** = patterns (OSLF terms)
- **Edges** = observer-distinguishability: an edge (p, q) means some OSLF formula
  separates p from q
- **Equivalence classes** = indistinguishability quotient

Key bridge theorems:
- Full bisimilarity (R + R⁻¹ + atom compat) implies indistinguishability
- Under image-finiteness (forward + backward), indist implies full bisimilarity
- Under image-finiteness, they coincide (Hennessy-Milner iff)

## References

- Goertzel, "MetaGoal Stability" (2026)
- Goertzel, "Graphtropy" (2026)
- Meredith & Stay, "Operational Semantics in Logical Form"
-/

namespace Mettapedia.OSLF.Framework.DistinctionGraph

open Mettapedia.OSLF.Framework.KSUnificationSketch
open Mettapedia.OSLF.Framework.EvidenceSemantics
open Mettapedia.OSLF.Formula

abbrev Pat := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

/-! ## Core Definitions -/

/-- Observer-induced indistinguishability: two patterns satisfy the same OSLF formulas.
Definitional wrapper around `OSLFObsEq`. -/
def indistObs (R : Pat → Pat → Prop) (I : AtomSem) (p q : Pat) : Prop :=
  OSLFObsEq R I p q

/-- The distinction graph: an edge (p, q) exists when patterns are
observer-distinguishable, i.e., some formula separates them. -/
def distinguished (R : Pat → Pat → Prop) (I : AtomSem) (p q : Pat) : Prop :=
  ¬ indistObs R I p q

/-! ## Equivalence Relation Properties -/

theorem indistObs_refl (R : Pat → Pat → Prop) (I : AtomSem) (p : Pat) :
    indistObs R I p p :=
  fun _ => Iff.rfl

theorem indistObs_symm {R : Pat → Pat → Prop} {I : AtomSem} {p q : Pat}
    (h : indistObs R I p q) : indistObs R I q p :=
  fun φ => (h φ).symm

theorem indistObs_trans {R : Pat → Pat → Prop} {I : AtomSem} {p q r : Pat}
    (h1 : indistObs R I p q) (h2 : indistObs R I q r) : indistObs R I p r :=
  fun φ => (h1 φ).trans (h2 φ)

/-- `indistObs` is an equivalence relation. -/
theorem indistObs_equivalence (R : Pat → Pat → Prop) (I : AtomSem) :
    Equivalence (indistObs R I) :=
  ⟨indistObs_refl R I, fun h => indistObs_symm h, fun h1 h2 => indistObs_trans h1 h2⟩

/-- The indistinguishability setoid on patterns. -/
def indistObs_setoid (R : Pat → Pat → Prop) (I : AtomSem) : Setoid Pat :=
  ⟨indistObs R I, indistObs_equivalence R I⟩

/-- The quotient type of observer-equivalence classes. -/
def ObsClass (R : Pat → Pat → Prop) (I : AtomSem) : Type :=
  Quotient (indistObs_setoid R I)

/-! ## Distinction Graph Properties -/

/-- Distinguished is irreflexive. -/
theorem distinguished_irrefl (R : Pat → Pat → Prop) (I : AtomSem) (p : Pat) :
    ¬ distinguished R I p p :=
  not_not.mpr (indistObs_refl R I p)

/-- Distinguished is symmetric. -/
theorem distinguished_symm {R : Pat → Pat → Prop} {I : AtomSem} {p q : Pat}
    (h : distinguished R I p q) : distinguished R I q p :=
  fun hqp => h (indistObs_symm hqp)

/-- Distinguished patterns have a separating formula. -/
theorem distinguished_has_separator {R : Pat → Pat → Prop} {I : AtomSem} {p q : Pat}
    (h : distinguished R I p q) : ∃ φ, sem R I φ p ∧ ¬ sem R I φ q :=
  separator_of_not_obsEq h

/-! ## Full Bisimilarity

`Bisimilar R` (from OSLFKSUnificationSketch) stores a StepBisimulation for R only.
The box modality (R-predecessors) requires the R⁻¹ bisimulation too.
`FullBisimilar` bundles both, plus atom compatibility. -/

/-- Full bisimilarity: related by some equivalence that is a step-bisimulation
for both R and R⁻¹, and respects atom semantics. -/
def FullBisimilar (R : Pat → Pat → Prop) (I : AtomSem) (p q : Pat) : Prop :=
  ∃ E : Pat → Pat → Prop,
    StepBisimulation R E ∧
    StepBisimulation (fun a b => R b a) E ∧
    (∀ a p' q', E p' q' → (I a p' ↔ I a q')) ∧
    E p q

/-! ## Bisimulation Bridge -/

/-- Full bisimilar patterns are observer-indistinguishable. -/
theorem fullBisim_implies_indist
    {R : Pat → Pat → Prop} {I : AtomSem}
    {p q : Pat} (h : FullBisimilar R I p q) :
    indistObs R I p q := by
  obtain ⟨E, hE, hERev, hAtom, hpq⟩ := h
  exact fun φ => bisimulation_invariant_sem hE hERev hAtom hpq φ

/-- Under forward image-finiteness, `OSLFObsEq R I` is a step-bisimulation for R. -/
theorem indistObs_is_stepBisimulation
    {R : Pat → Pat → Prop} {I : AtomSem}
    (hImageFinite : ∀ p : Pat, Set.Finite {q : Pat | R p q}) :
    StepBisimulation R (indistObs R I) :=
  obsEq_is_stepBisimulation hImageFinite

/-- Under backward image-finiteness, `OSLFObsEq R I` is a step-bisimulation for R⁻¹.

The proof mirrors `obsEq_is_stepBisimulation` but uses the formula `¬□¬Ψ`
(= `.imp (.box (.imp Ψ .bot)) .bot`) to express "∃ R-predecessor satisfying Ψ",
which is the R⁻¹ diamond. -/
theorem indistObs_is_revStepBisimulation
    {R : Pat → Pat → Prop} {I : AtomSem}
    (hPredFinite : ∀ p : Pat, Set.Finite {q : Pat | R q p}) :
    StepBisimulation (fun a b => R b a) (indistObs R I) := by
  constructor
  · -- Forth for R⁻¹: indistObs p q → R p' p → ∃ q', R q' q ∧ indistObs p' q'
    intro p q hpq p' hpp'
    by_contra h_no_match
    push_neg at h_no_match
    -- Every R-predecessor q' of q fails to be indistObs to p'
    have hfin := hPredFinite q
    have hsep : ∀ q' : Pat, R q' q →
        ∃ φ, sem R I φ p' ∧ ¬ sem R I φ q' := by
      intro q' hq'q
      exact separator_of_not_obsEq (h_no_match q' hq'q)
    choose f hf using fun q' (h : q' ∈ hfin.toFinset) =>
      hsep q' (hfin.mem_toFinset.mp h)
    let formulas := hfin.toFinset.val.toList.map
      (fun q' => if h : q' ∈ hfin.toFinset then f q' h else .top)
    let Ψ := conjList formulas
    -- p' satisfies Ψ
    have hp'Ψ : sem R I Ψ p' := by
      rw [sem_conjList_iff]
      intro ψ hψ
      simp only [formulas, List.mem_map] at hψ
      obtain ⟨q', _, rfl⟩ := hψ
      split_ifs with hmem
      · exact (hf q' hmem).1
      · exact trivial
    -- No R-predecessor of q satisfies Ψ
    have hqΨ : ∀ t, R t q → ¬ sem R I Ψ t := by
      intro t htq
      have hmem : t ∈ hfin.toFinset := hfin.mem_toFinset.mpr htq
      intro htΨ
      rw [sem_conjList_iff] at htΨ
      have : sem R I (f t hmem) t := by
        apply htΨ
        simp only [formulas, List.mem_map]
        exact ⟨t, Multiset.mem_toList.mpr (Finset.mem_val.mpr hmem), dif_pos hmem⟩
      exact (hf t hmem).2 this
    -- Use ¬□¬Ψ = .imp (.box (.imp Ψ .bot)) .bot
    -- At p: p has predecessor p' satisfying Ψ, so □(¬Ψ) fails at p, so ¬□(¬Ψ) holds
    have hpForm : sem R I (.imp (.box (.imp Ψ .bot)) .bot) p := by
      intro hbox
      -- hbox : ∀ s, R s p → sem R I Ψ s → False
      exact hbox p' hpp' hp'Ψ
    -- At q: all R-predecessors of q fail Ψ, so □(¬Ψ) holds at q, so ¬□(¬Ψ) fails
    have hqForm : ¬ sem R I (.imp (.box (.imp Ψ .bot)) .bot) q := by
      intro h
      apply h
      exact fun t htq htΨ => hqΨ t htq htΨ
    -- This contradicts OSLFObsEq p q
    exact hqForm ((hpq _).mp hpForm)
  · -- Back for R⁻¹: indistObs p q → R q' q → ∃ p', R p' p ∧ indistObs p' q'
    intro p q hpq q' hq'q
    by_contra h_no_match
    push_neg at h_no_match
    have hfin := hPredFinite p
    have hsep : ∀ p' : Pat, R p' p →
        ∃ φ, sem R I φ q' ∧ ¬ sem R I φ p' := by
      intro p' hp'p
      have h := h_no_match p' hp'p
      exact separator_of_not_obsEq (fun hobs => h (obsEq_symm hobs))
    choose f hf using fun p' (h : p' ∈ hfin.toFinset) =>
      hsep p' (hfin.mem_toFinset.mp h)
    let formulas := hfin.toFinset.val.toList.map
      (fun p' => if h : p' ∈ hfin.toFinset then f p' h else .top)
    let Ψ := conjList formulas
    have hq'Ψ : sem R I Ψ q' := by
      rw [sem_conjList_iff]
      intro ψ hψ
      simp only [formulas, List.mem_map] at hψ
      obtain ⟨p', _, rfl⟩ := hψ
      split_ifs with hmem
      · exact (hf p' hmem).1
      · exact trivial
    have hpΨ : ∀ t, R t p → ¬ sem R I Ψ t := by
      intro t htp
      have hmem : t ∈ hfin.toFinset := hfin.mem_toFinset.mpr htp
      intro htΨ
      rw [sem_conjList_iff] at htΨ
      have : sem R I (f t hmem) t := by
        apply htΨ
        simp only [formulas, List.mem_map]
        exact ⟨t, Multiset.mem_toList.mpr (Finset.mem_val.mpr hmem), dif_pos hmem⟩
      exact (hf t hmem).2 this
    have hqForm : sem R I (.imp (.box (.imp Ψ .bot)) .bot) q := by
      intro hbox
      exact hbox q' hq'q hq'Ψ
    have hpForm : ¬ sem R I (.imp (.box (.imp Ψ .bot)) .bot) p := by
      intro h
      apply h
      exact fun t htp htΨ => hpΨ t htp htΨ
    exact hpForm ((hpq _).mpr hqForm)

/-- Under both forward and backward image-finiteness, observer-indistinguishability
implies full bisimilarity. -/
theorem indist_implies_fullBisim_imageFinite
    {R : Pat → Pat → Prop} {I : AtomSem}
    (hImageFinite : ∀ p : Pat, Set.Finite {q : Pat | R p q})
    (hPredFinite : ∀ p : Pat, Set.Finite {q : Pat | R q p})
    {p q : Pat} (h : indistObs R I p q) :
    FullBisimilar R I p q :=
  ⟨indistObs R I,
   indistObs_is_stepBisimulation hImageFinite,
   indistObs_is_revStepBisimulation hPredFinite,
   fun a _ _ h => h (.atom a),
   h⟩

/-- **Hennessy-Milner iff**: under both forward and backward image-finiteness,
observer-indistinguishability and full bisimilarity coincide. -/
theorem indist_iff_fullBisim_imageFinite
    {R : Pat → Pat → Prop} {I : AtomSem}
    (hImageFinite : ∀ p : Pat, Set.Finite {q : Pat | R p q})
    (hPredFinite : ∀ p : Pat, Set.Finite {q : Pat | R q p})
    (p q : Pat) : indistObs R I p q ↔ FullBisimilar R I p q :=
  ⟨indist_implies_fullBisim_imageFinite hImageFinite hPredFinite,
   fullBisim_implies_indist⟩

/-- Under forward image-finiteness, indist implies (weak) bisimilarity. -/
theorem indist_implies_bisim_imageFinite
    {R : Pat → Pat → Prop} {I : AtomSem}
    (hImageFinite : ∀ p : Pat, Set.Finite {q : Pat | R p q})
    {p q : Pat} (h : indistObs R I p q) :
    Bisimilar R p q :=
  hm_converse_schema hImageFinite h

/-! ## Quotient and Measurement -/

/-- Measurement functions factor through observer-equivalence classes. -/
theorem measurement_factors_through_obsClass
    {R : Pat → Pat → Prop} {I : AtomSem}
    (mu : Pat → ℝ)
    (hCompat : ∀ p q, indistObs R I p q → mu p = mu q) :
    ∃ muQ : ObsClass R I → ℝ, ∀ p, muQ (Quotient.mk _ p) = mu p :=
  ⟨Quotient.lift mu (fun a b h => hCompat a b h), fun _ => rfl⟩

/-- The number of distinction classes is at most the number of states. -/
theorem obsClass_card_le [Fintype Pat] (R : Pat → Pat → Prop) (I : AtomSem)
    [DecidableRel (indistObs_setoid R I).r] :
    Fintype.card (Quotient (indistObs_setoid R I)) ≤ Fintype.card Pat :=
  Fintype.card_quotient_le _

end Mettapedia.OSLF.Framework.DistinctionGraph
