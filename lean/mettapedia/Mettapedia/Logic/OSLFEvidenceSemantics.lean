import Mettapedia.OSLF.Formula
import Mettapedia.Logic.EvidenceQuantale
import Mettapedia.Logic.PLNWorldModel
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# EvidenceQuantale Adapter for OSLF Semantics

This module is an **adapter layer**: it interprets OSLF formulas in the
canonical evidence carrier `EvidenceQuantale.Evidence`.

Ownership boundary:
- Canonical evidence semantics lives in `Mettapedia.Logic.EvidenceQuantale`
- This file only lifts that evidence algebra into OSLF formula interpretation

Evidence-valued formula interpretation uses Evidence's Frame (complete Heyting
algebra) structure:

- Evidence is a `Frame` (hence `HeytingAlgebra`, `CompleteLattice`)
- OSLF formulas map to Evidence values via lattice operations
- Threshold-Prop semantics (`sem`) is a corollary, not the foundation
- The threshold bridge is PARTIAL: it fails for disjunction/diamond because
  `τ ≤ x ⊔ y ⇏ τ ≤ x ∨ τ ≤ y` in Evidence's non-total order
  (this IS the Knuth-Skilling imprecision gate)

## Interpretation Table

| Formula   | Evidence semantics          |
|-----------|-----------------------------|
| ⊤         | ⊤ (top evidence)            |
| ⊥         | ⊥ (zero evidence)           |
| atom a    | I a p                       |
| φ ∧ ψ    | semE φ p ⊓ semE ψ p        |
| φ ∨ ψ    | semE φ p ⊔ semE ψ p        |
| φ → ψ    | semE φ p ⇨ semE ψ p        |
| ◇ φ      | ⨆ {q | R p q}, semE φ q    |
| □ φ      | ⨅ {q | R q p}, semE φ q    |

## References

- Meredith & Stay, "Operational Semantics in Logical Form"
- Knuth & Skilling, "Foundations of Inference" (totality axiom)
-/

namespace Mettapedia.Logic.OSLFEvidenceSemantics

open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel

open scoped ENNReal

/-! ## Evidence-Valued Atom Semantics -/

/-- Evidence-valued atom interpretation: maps atom names and patterns to Evidence. -/
abbrev EvidenceAtomSem := String → Pattern → Evidence

/-! ## Evidence-Valued Formula Semantics -/

/-- Evidence-valued denotational semantics of OSLF formulas.

Uses Evidence's Frame structure:
- `⊓` for conjunction (coordinatewise min)
- `⊔` for disjunction (coordinatewise max)
- `⇨` for Heyting implication (residuation)
- `⨆`/`⨅` for modalities over step-related states -/
noncomputable def semE (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) :
    OSLFFormula → Pattern → Evidence
  | .top, _ => ⊤
  | .bot, _ => ⊥
  | .atom a, p => I a p
  | .and φ ψ, p => semE R I φ p ⊓ semE R I ψ p
  | .or φ ψ, p => semE R I φ p ⊔ semE R I ψ p
  | .imp φ ψ, p => semE R I φ p ⇨ semE R I ψ p
  | .dia φ, p => ⨆ (q : {q // R p q}), semE R I φ q.val
  | .box φ, p => ⨅ (q : {q // R q p}), semE R I φ q.val

/-! ## Unfolding Lemmas -/

@[simp] theorem semE_top (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) (p : Pattern) :
    semE R I .top p = ⊤ := rfl

@[simp] theorem semE_bot (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) (p : Pattern) :
    semE R I .bot p = ⊥ := rfl

@[simp] theorem semE_atom (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) (a : String) (p : Pattern) :
    semE R I (.atom a) p = I a p := rfl

@[simp] theorem semE_and (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) (φ ψ : OSLFFormula) (p : Pattern) :
    semE R I (.and φ ψ) p = semE R I φ p ⊓ semE R I ψ p := rfl

@[simp] theorem semE_or (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) (φ ψ : OSLFFormula) (p : Pattern) :
    semE R I (.or φ ψ) p = semE R I φ p ⊔ semE R I ψ p := rfl

@[simp] theorem semE_imp (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) (φ ψ : OSLFFormula) (p : Pattern) :
    semE R I (.imp φ ψ) p = semE R I φ p ⇨ semE R I ψ p := rfl

@[simp] theorem semE_dia (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) (φ : OSLFFormula) (p : Pattern) :
    semE R I (.dia φ) p = ⨆ (q : {q // R p q}), semE R I φ q.val := rfl

@[simp] theorem semE_box (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem) (φ : OSLFFormula) (p : Pattern) :
    semE R I (.box φ) p = ⨅ (q : {q // R q p}), semE R I φ q.val := rfl

/-! ## Structural Monotonicity -/

/-- Conjunction projects to the left component. -/
theorem semE_and_le_left (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (φ ψ : OSLFFormula) (p : Pattern) :
    semE R I (.and φ ψ) p ≤ semE R I φ p :=
  inf_le_left

/-- Conjunction projects to the right component. -/
theorem semE_and_le_right (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (φ ψ : OSLFFormula) (p : Pattern) :
    semE R I (.and φ ψ) p ≤ semE R I ψ p :=
  inf_le_right

/-- Left disjunct injects into disjunction. -/
theorem semE_le_or_left (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (φ ψ : OSLFFormula) (p : Pattern) :
    semE R I φ p ≤ semE R I (.or φ ψ) p :=
  le_sup_left

/-- Right disjunct injects into disjunction. -/
theorem semE_le_or_right (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (φ ψ : OSLFFormula) (p : Pattern) :
    semE R I ψ p ≤ semE R I (.or φ ψ) p :=
  le_sup_right

/-- A step-successor's evidence injects into diamond. -/
theorem semE_dia_le (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (φ : OSLFFormula) (p q : Pattern) (h : R p q) :
    semE R I φ q ≤ semE R I (.dia φ) p :=
  le_iSup (fun (s : {s // R p s}) => semE R I φ s.val) ⟨q, h⟩

/-- Box projects to any predecessor. -/
theorem semE_box_le (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (φ : OSLFFormula) (p q : Pattern) (h : R q p) :
    semE R I (.box φ) p ≤ semE R I φ q :=
  iInf_le (fun (s : {s // R s p}) => semE R I φ s.val) ⟨q, h⟩

/-! ## Modus Ponens (Heyting) -/

/-- Heyting modus ponens: `semE (φ → ψ) p ⊓ semE φ p ≤ semE ψ p`. -/
theorem semE_imp_mp (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (φ ψ : OSLFFormula) (p : Pattern) :
    semE R I (.imp φ ψ) p ⊓ semE R I φ p ≤ semE R I ψ p := by
  simp only [semE_imp]
  exact himp_inf_le

/-! ## World-Model Connection -/

section WMConnection

variable {State : Type*} [EvidenceType State] [WorldModel State Pattern]

/-- Evidence atom semantics from a world-model state: the atom at pattern p
is the evidence extracted by querying `queryOfAtom a p`. -/
noncomputable def wmEvidenceAtomSem
    (W : State) (queryOfAtom : String → Pattern → Pattern) : EvidenceAtomSem :=
  fun a p => WorldModel.evidence W (queryOfAtom a p)

/-- WM revision lifts to evidence atoms: revising world states then
extracting atom evidence = extracting from each and combining. -/
theorem semE_wm_atom_revision
    (W₁ W₂ : State) (queryOfAtom : String → Pattern → Pattern)
    (R : Pattern → Pattern → Prop) (a : String) (p : Pattern) :
    semE R (wmEvidenceAtomSem (W₁ + W₂) queryOfAtom) (.atom a) p =
      semE R (wmEvidenceAtomSem W₁ queryOfAtom) (.atom a) p +
      semE R (wmEvidenceAtomSem W₂ queryOfAtom) (.atom a) p := by
  simp only [semE_atom, wmEvidenceAtomSem]
  exact WorldModel.evidence_add W₁ W₂ (queryOfAtom a p)

end WMConnection

/-! ## Threshold Bridge (Conjunctive Fragment)

The threshold bridge `τ ≤ semE R I φ p → sem R (threshI τ) φ p` works for
the conjunctive fragment (top, atom, and, box) but FAILS for the
disjunctive fragment (or, dia) because Evidence's order is non-total:
`τ ≤ x ⊔ y ⇏ τ ≤ x ∨ τ ≤ y`.

This is the formal expression of the Knuth-Skilling imprecision gate:
precise (Boolean) semantics can only be recovered on fragments where
the Heyting algebra happens to be Boolean. -/

/-- Threshold atom semantics: atom holds when evidence exceeds threshold. -/
noncomputable def threshAtomSem (I : EvidenceAtomSem) (τ : Evidence) :
    AtomSem :=
  fun a p => τ ≤ I a p

/-- Threshold bridge for atoms: direct by definition. -/
theorem threshold_atom (I : EvidenceAtomSem) (τ : Evidence) (R : Pattern → Pattern → Prop)
    (a : String) (p : Pattern) :
    τ ≤ semE R I (.atom a) p ↔ sem R (threshAtomSem I τ) (.atom a) p := by
  rfl

/-- Threshold bridge for conjunction. -/
theorem threshold_and (I : EvidenceAtomSem) (τ : Evidence) (R : Pattern → Pattern → Prop)
    (φ ψ : OSLFFormula) (p : Pattern)
    (hφ : τ ≤ semE R I φ p → sem R (threshAtomSem I τ) φ p)
    (hψ : τ ≤ semE R I ψ p → sem R (threshAtomSem I τ) ψ p) :
    τ ≤ semE R I (.and φ ψ) p → sem R (threshAtomSem I τ) (.and φ ψ) p := by
  intro h
  simp only [semE_and] at h
  exact ⟨hφ (le_trans h inf_le_left), hψ (le_trans h inf_le_right)⟩

/-- Threshold bridge FAILS for disjunction in general.

Counterexample: I "a" = (1,0), I "b" = (0,1) are incomparable in Evidence.
Their join (1,0) ⊔ (0,1) = (1,1), but τ = (1,1) exceeds neither component.
This is the imprecision gate in action: non-total order prevents Boolean
reduction of disjunction. -/
theorem threshold_or_counterexample :
    ¬ (∀ (I : EvidenceAtomSem) (τ : Evidence) (R : Pattern → Pattern → Prop)
       (φ ψ : OSLFFormula) (p : Pattern),
       τ ≤ semE R I (.or φ ψ) p →
       sem R (threshAtomSem I τ) (.or φ ψ) p) := by
  intro h
  -- I "a" = (1,0), I "b" = (0,1) are incomparable; τ = (1,1) = their join
  let p₀ : Pattern := .apply "x" []
  let I : EvidenceAtomSem := fun a _ =>
    if a == "a" then ⟨1, 0⟩ else ⟨0, 1⟩
  let τ₀ : Evidence := ⟨1, 1⟩
  let R₀ : Pattern → Pattern → Prop := fun _ _ => False
  have hle : τ₀ ≤ semE R₀ I (.or (.atom "a") (.atom "b")) p₀ := by
    simp only [semE_or, semE_atom]
    show (⟨1, 1⟩ : Evidence) ≤ (⟨1, 0⟩ : Evidence) ⊔ (⟨0, 1⟩ : Evidence)
    exact ⟨(@le_sup_left Evidence _ ⟨1, 0⟩ ⟨0, 1⟩).1, (@le_sup_right Evidence _ ⟨1, 0⟩ ⟨0, 1⟩).2⟩
  have habs := h I τ₀ R₀ (.atom "a") (.atom "b") p₀ hle
  simp only [sem, threshAtomSem] at habs
  have hnle : ¬ ((1 : ℝ≥0∞) ≤ (0 : ℝ≥0∞)) := by norm_num
  rcases habs with h1 | h2
  · exact hnle h1.2
  · exact hnle h2.1

/-! ### Complete Fragment Classification

The threshold bridge `τ ≤ semE ... → sem ...` works precisely for the
**conjunctive/universal fragment** {⊤, atom, ∧, →, □} and FAILS for the
**disjunctive/existential fragment** {∨, ◇}.

This is the formal expression of the Knuth-Skilling totality axiom:
point-valued (Boolean) semantics requires total order; Evidence's
non-total order forces Heyting default on disjunctive connectives. -/

/-- Threshold bridge for ⊤: always works (vacuously). -/
theorem threshold_top (I : EvidenceAtomSem) (τ : Evidence) (R : Pattern → Pattern → Prop)
    (p : Pattern) :
    τ ≤ semE R I .top p → sem R (threshAtomSem I τ) .top p := by
  intro _; trivial

/-- Threshold bridge for ⊥: works by absurdity (τ ≤ ⊥ is impossible for τ > 0). -/
theorem threshold_bot (I : EvidenceAtomSem) (τ : Evidence) (R : Pattern → Pattern → Prop)
    (p : Pattern) (hτ : ⊥ < τ) :
    τ ≤ semE R I .bot p → sem R (threshAtomSem I τ) .bot p := by
  intro h; exact absurd (lt_of_lt_of_le hτ h) (lt_irrefl _)

/-- Threshold bridge for implication (→): evidence-level modus ponens.

If `τ ≤ φ ⇨ ψ` and `τ ≤ φ` then `τ ≤ ψ`. The second hypothesis is at
the evidence level (not Prop level) because the reverse bridge
`sem (threshAtomSem I τ) φ p → τ ≤ semE R I φ p` fails for the
disjunctive fragment. -/
theorem threshold_imp (I : EvidenceAtomSem) (τ : Evidence) (R : Pattern → Pattern → Prop)
    (φ ψ : OSLFFormula) (p : Pattern)
    (hψ : τ ≤ semE R I ψ p → sem R (threshAtomSem I τ) ψ p) :
    τ ≤ semE R I (.imp φ ψ) p →
    τ ≤ semE R I φ p →
    sem R (threshAtomSem I τ) ψ p := by
  intro himp hφ
  apply hψ
  calc τ = τ ⊓ τ := (inf_idem _).symm
    _ ≤ (semE R I φ p ⇨ semE R I ψ p) ⊓ semE R I φ p := inf_le_inf himp hφ
    _ ≤ semE R I ψ p := himp_inf_le

/-- Threshold bridge for box (□): works because ⊓ distributes over threshold. -/
theorem threshold_box (I : EvidenceAtomSem) (τ : Evidence) (R : Pattern → Pattern → Prop)
    (φ : OSLFFormula) (p : Pattern)
    (hφ : ∀ q, R q p → τ ≤ semE R I φ q → sem R (threshAtomSem I τ) φ q) :
    τ ≤ semE R I (.box φ) p → sem R (threshAtomSem I τ) (.box φ) p := by
  intro h q hqp
  apply hφ q hqp
  exact le_trans h (semE_box_le R I φ p q hqp)

/-- Threshold bridge FAILS for diamond (◇) in general.

Same mechanism as `threshold_or_counterexample`: `τ ≤ ⨆ ... ⇏ ∃ ..., τ ≤ ...`
because Evidence is non-total. Two successors q₁, q₂ with incomparable evidence
(1,0) and (0,1) have supremum (1,1), but no single successor exceeds (1,1). -/
theorem threshold_dia_fails :
    ¬ (∀ (I : EvidenceAtomSem) (τ : Evidence) (R : Pattern → Pattern → Prop)
       (φ : OSLFFormula) (p : Pattern),
       τ ≤ semE R I (.dia φ) p →
       sem R (threshAtomSem I τ) (.dia φ) p) := by
  intro h
  let p₀ : Pattern := .apply "p" []
  let q₁ : Pattern := .apply "q1" []
  let q₂ : Pattern := .apply "q2" []
  let I : EvidenceAtomSem := fun _ q =>
    if q == q₁ then ⟨1, 0⟩ else ⟨0, 1⟩
  let τ₀ : Evidence := ⟨1, 1⟩
  let R₀ : Pattern → Pattern → Prop := fun p q => p = p₀ ∧ (q = q₁ ∨ q = q₂)
  -- τ₀ = (1,1) ≤ (1,0) ⊔ (0,1) ≤ ⨆ over {q₁, q₂} by le_iSup + sup_le
  have hle : τ₀ ≤ semE R₀ I (.dia (.atom "a")) p₀ := by
    simp only [semE_dia, semE_atom]
    have h1 := le_iSup (fun (q : {q // R₀ p₀ q}) => I "a" q.val) ⟨q₁, rfl, Or.inl rfl⟩
    have h2 := le_iSup (fun (q : {q // R₀ p₀ q}) => I "a" q.val) ⟨q₂, rfl, Or.inr rfl⟩
    refine le_trans ?_ (sup_le h1 h2)
    simp only [I, q₁, q₂, beq_iff_eq]
    exact ⟨le_sup_of_le_left (le_refl _), le_sup_of_le_right (le_refl _)⟩
  -- But no single successor has evidence ≥ (1,1)
  have habs := h I τ₀ R₀ (.atom "a") p₀ hle
  simp only [sem, threshAtomSem] at habs
  have hnle : ¬ ((1 : ℝ≥0∞) ≤ (0 : ℝ≥0∞)) := by norm_num
  rcases habs with ⟨q, ⟨_, hq⟩, hsat⟩
  rcases hq with rfl | rfl
  · exact hnle hsat.2
  · exact hnle hsat.1

/-! ## Totality Gate (Knuth-Skilling Projection Theorem)

Under total order (`∀ a b, a ≤ b ∨ b ≤ a`), the threshold bridge works for ALL
connectives — disjunction and diamond included. This is the formal expression of
the Knuth-Skilling totality axiom: adding totality to the Evidence algebra
recovers Boolean/classical semantics.

The projection theorem says: classical truth-conditional semantics (Montague) is
a SPECIAL CASE of evidential semantics, obtained by imposing totality. Without
totality, you get the strictly richer Heyting/evidential semantics. -/

/-- In a linearly ordered lattice, `τ ≤ a ⊔ b → τ ≤ a ∨ τ ≤ b`.
This is the lattice-level totality gate. -/
theorem le_sup_of_total {H : Type*} [SemilatticeSup H]
    (hTotal : ∀ a b : H, a ≤ b ∨ b ≤ a)
    {τ a b : H} (h : τ ≤ a ⊔ b) : τ ≤ a ∨ τ ≤ b := by
  rcases hTotal a b with hab | hba
  · right; exact le_trans h (sup_le hab (le_refl b))
  · left; exact le_trans h (sup_le (le_refl a) hba)

/-- Under totality, threshold bridge works for disjunction. -/
theorem threshold_or_total
    (hTotal : ∀ a b : Evidence, a ≤ b ∨ b ≤ a)
    (I : EvidenceAtomSem) (τ : Evidence) (R : Pattern → Pattern → Prop)
    (φ ψ : OSLFFormula) (p : Pattern)
    (hφ : τ ≤ semE R I φ p → sem R (threshAtomSem I τ) φ p)
    (hψ : τ ≤ semE R I ψ p → sem R (threshAtomSem I τ) ψ p) :
    τ ≤ semE R I (.or φ ψ) p → sem R (threshAtomSem I τ) (.or φ ψ) p := by
  intro h
  simp only [semE_or] at h
  rcases le_sup_of_total hTotal h with h1 | h2
  · exact Or.inl (hφ h1)
  · exact Or.inr (hψ h2)

/-- In a total order, `a ⊔ b < τ` from `a < τ` and `b < τ`. -/
private theorem sup_lt_of_lt_total {H : Type*} [SemilatticeSup H]
    (hTotal : ∀ a b : H, a ≤ b ∨ b ≤ a) {a b τ : H}
    (ha : a < τ) (hb : b < τ) : a ⊔ b < τ := by
  rcases hTotal a b with h | h
  · rwa [sup_eq_right.mpr h]
  · rwa [sup_eq_left.mpr h]

/-- In a total order, `Finset.sup'` of finitely many elements all `< τ` is `< τ`. -/
private theorem Finset.sup'_lt_total {H ι : Type*} [SemilatticeSup H]
    (hTotal : ∀ a b : H, a ≤ b ∨ b ≤ a)
    {s : Finset ι} (hs : s.Nonempty) {f : ι → H} {τ : H}
    (hlt : ∀ i ∈ s, f i < τ) : s.sup' hs f < τ := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    simp [Finset.sup'_singleton]; exact hlt a (Finset.mem_singleton_self a)
  | cons a s has hs ih =>
    rw [Finset.sup'_cons hs]
    exact sup_lt_of_lt_total hTotal
      (hlt a (Finset.mem_cons_self a _))
      (ih (fun i hi => hlt i (Finset.mem_cons_of_mem hi)))

/-- In a total order, `iSup` of finitely many elements all `< τ` is `< τ`.
Connects `Finset.sup'` on `Finset.univ` to `iSup` via `sup'_univ_eq_ciSup`. -/
private theorem iSup_lt_of_forall_lt_total {H : Type*} {ι : Type*}
    [CompleteLattice H] [Fintype ι] [Nonempty ι]
    (hTotal : ∀ a b : H, a ≤ b ∨ b ≤ a)
    {f : ι → H} {τ : H}
    (hlt : ∀ i, f i < τ) : iSup f < τ := by
  rw [← Finset.sup'_univ_eq_ciSup]
  exact Finset.sup'_lt_total hTotal Finset.univ_nonempty (fun i _ => hlt i)

/-- Under totality + finite branching, threshold bridge works for diamond.
Uses `iSup_lt_of_forall_lt_total`: in a total order over a finite set,
if every element is strictly below τ, then iSup < τ. -/
theorem threshold_dia_total
    (hTotal : ∀ a b : Evidence, a ≤ b ∨ b ≤ a)
    (I : EvidenceAtomSem) (τ : Evidence) (R : Pattern → Pattern → Prop)
    (φ : OSLFFormula) (p : Pattern)
    (hφ : ∀ q, R p q → τ ≤ semE R I φ q → sem R (threshAtomSem I τ) φ q)
    (hSucc : Set.Finite {q | R p q})
    (hNonempty : ∃ q, R p q) :
    τ ≤ semE R I (.dia φ) p → sem R (threshAtomSem I τ) (.dia φ) p := by
  intro h
  simp only [semE_dia] at h
  haveI : Nonempty {q // R p q} := by
    obtain ⟨q, hq⟩ := hNonempty; exact ⟨⟨q, hq⟩⟩
  haveI : Finite {q // R p q} := hSucc.to_subtype
  by_contra hc
  simp only [sem] at hc
  push_neg at hc
  have hno : ∀ q, R p q → ¬ (τ ≤ semE R I φ q) := by
    intro q hRq hle; exact hc q hRq (hφ q hRq hle)
  have hlt : ∀ (q : {q // R p q}), semE R I φ q.val < τ := by
    intro ⟨q, hRq⟩
    rcases hTotal τ (semE R I φ q) with h1 | h2
    · exact absurd h1 (hno q hRq)
    · exact lt_of_le_of_ne h2 (fun heq => hno q hRq (heq ▸ le_refl _))
  haveI : Fintype {q // R p q} := hSucc.fintype
  exact absurd (lt_of_le_of_lt h (iSup_lt_of_forall_lt_total hTotal hlt))
    (lt_irrefl _)

/-- Reverse threshold bridge: `sem (threshAtomSem I τ) φ p → τ ≤ semE R I φ p`.
Works for the imp-free fragment without totality. The reverse direction for
implication genuinely requires Booleanness (not just totality). -/
theorem threshold_reverse_atom (I : EvidenceAtomSem) (τ : Evidence)
    (R : Pattern → Pattern → Prop) (a : String) (p : Pattern) :
    sem R (threshAtomSem I τ) (.atom a) p → τ ≤ semE R I (.atom a) p := id

theorem threshold_reverse_and (I : EvidenceAtomSem) (τ : Evidence)
    (R : Pattern → Pattern → Prop) (φ ψ : OSLFFormula) (p : Pattern)
    (hφ : sem R (threshAtomSem I τ) φ p → τ ≤ semE R I φ p)
    (hψ : sem R (threshAtomSem I τ) ψ p → τ ≤ semE R I ψ p) :
    sem R (threshAtomSem I τ) (.and φ ψ) p → τ ≤ semE R I (.and φ ψ) p := by
  intro ⟨h1, h2⟩; exact le_inf (hφ h1) (hψ h2)

theorem threshold_reverse_or (I : EvidenceAtomSem) (τ : Evidence)
    (R : Pattern → Pattern → Prop) (φ ψ : OSLFFormula) (p : Pattern)
    (hφ : sem R (threshAtomSem I τ) φ p → τ ≤ semE R I φ p)
    (hψ : sem R (threshAtomSem I τ) ψ p → τ ≤ semE R I ψ p) :
    sem R (threshAtomSem I τ) (.or φ ψ) p → τ ≤ semE R I (.or φ ψ) p := by
  intro h
  rcases h with h1 | h2
  · exact le_trans (hφ h1) le_sup_left
  · exact le_trans (hψ h2) le_sup_right

/-! ## Scope of the Totality Projection Theorem

`threshold_dia_total` requires two side conditions:

1. **Finite branching** (`hSucc : Set.Finite {q | R p q}`): The successor set
   must be finite.  Without this, the sup of infinitely many values all `< τ`
   can still equal τ (e.g. sup of `{1 - 1/n}` = 1).

2. **Nonempty successors** (`hNonempty : ∃ q, R p q`): At deadlock states,
   `semE(◇φ, p) = ⊥` but `sem(◇φ, p)` requires a witness.  The bridge fails
   because the Prop-level diamond is existential while the Evidence-level
   diamond is a supremum (which can be ⊥ over the empty set).

Together with `threshold_atom`, `threshold_and`, `threshold_or_total`, and
`threshold_imp`, this covers the full OSLF formula language at states with
finite nonempty successor sets under totality. -/

/-- The threshold bridge for ◇ genuinely fails at deadlock states:
`⊥ ≤ semE(◇φ, p)` holds (empty sup = ⊥), but `sem(◇φ, p)` requires a
witness that doesn't exist. This shows `hNonempty` is necessary. -/
theorem threshold_dia_fails_at_deadlock :
    ∃ (I : EvidenceAtomSem) (R : Pattern → Pattern → Prop) (φ : OSLFFormula)
      (p : Pattern),
      (⊥ : Evidence) ≤ semE R I (.dia φ) p ∧
      ¬ sem R (threshAtomSem I ⊥) (.dia φ) p := by
  refine ⟨fun _ _ => ⊥, fun _ _ => False, .atom "a", .fvar "dead", bot_le, ?_⟩
  intro ⟨_, hR, _⟩; exact hR

/-! ## Reverse Threshold Bridge (Imp-Free Fragment)

The REVERSE direction `sem R (threshAtomSem I τ) φ p → τ ≤ semE R I φ p`
holds for the implication-free fragment WITHOUT totality or finite branching.
The existential witness in ◇ provides the evidence bound directly. -/

/-- An OSLF formula is implication-free (no `.imp` subformulas). -/
def impFree : OSLFFormula → Prop
  | .top | .bot | .atom _ => True
  | .and φ ψ | .or φ ψ => impFree φ ∧ impFree ψ
  | .imp _ _ => False
  | .dia φ | .box φ => impFree φ

/-- Reverse threshold bridge for ◇: no totality or finite branching needed.
The existential witness in `sem(◇φ)` provides the evidence bound. -/
theorem threshold_reverse_dia (I : EvidenceAtomSem) (τ : Evidence)
    (R : Pattern → Pattern → Prop) (φ : OSLFFormula) (p : Pattern)
    (hφ : ∀ q, R p q → sem R (threshAtomSem I τ) φ q → τ ≤ semE R I φ q) :
    sem R (threshAtomSem I τ) (.dia φ) p → τ ≤ semE R I (.dia φ) p := by
  intro ⟨q, hRq, hsat⟩
  simp only [semE_dia]
  exact le_trans (hφ q hRq hsat)
    (le_iSup (fun (q : {q // R p q}) => semE R I φ q.val) ⟨q, hRq⟩)

/-- Reverse threshold bridge for the full implication-free fragment.

For imp-free formulas, `sem R (threshAtomSem I τ) φ p → τ ≤ semE R I φ p`
holds unconditionally.  This is the converse of the forward bridge restricted
to the imp-free fragment; the forward direction for ∨/◇ needs totality, but
the reverse does not. -/
theorem threshold_reverse_impFree (I : EvidenceAtomSem) (τ : Evidence)
    (R : Pattern → Pattern → Prop) (φ : OSLFFormula) (hImpFree : impFree φ)
    (p : Pattern) :
    sem R (threshAtomSem I τ) φ p → τ ≤ semE R I φ p := by
  induction φ generalizing p with
  | top => intro _; exact le_top
  | bot => intro h; exact absurd h id
  | atom a => intro h; exact h
  | and φ ψ ih1 ih2 =>
    intro ⟨h1, h2⟩; exact le_inf (ih1 hImpFree.1 p h1) (ih2 hImpFree.2 p h2)
  | or φ ψ ih1 ih2 =>
    intro h; rcases h with h | h
    · exact le_trans (ih1 hImpFree.1 p h) le_sup_left
    · exact le_trans (ih2 hImpFree.2 p h) le_sup_right
  | imp _ _ => exact absurd hImpFree id
  | dia φ ih =>
    intro ⟨q, hRq, hsat⟩; simp only [semE_dia]
    exact le_trans (ih hImpFree q hsat)
      (le_iSup (fun (q : {q // R p q}) => semE R I φ q.val) ⟨q, hRq⟩)
  | box φ ih =>
    intro hbox; simp only [semE_box]
    exact le_iInf fun ⟨q, hRq⟩ => ih hImpFree q (hbox q hRq)

/-! ## Temporal Evidence Semantics

Temporal operators following Geisweiller & Yusuf, "Probabilistic Logic Networks
for Temporal and Procedural Reasoning" (LNCS 2023).  Temporal predicates are
regular predicates with a time dimension:

  P, Q, ... : Domain × Time → {True, False}

We embed temporal indices into patterns via a tagging constructor, keeping
Pattern as the universal query carrier.  Temporal operators are macros over
the existing evidence semantics — they shift the time index before evaluation.

### Operators (from Geisweiller & Yusuf §3.1)

- `Lag(P, T)  := λx,t. P(x, t - T)`  — bring past into present
- `Lead(P, T) := λx,t. P(x, t + T)`  — bring future into present
- `SequentialAnd(T, P, Q) := And(P, Lead(Q, T))`
- `PredictiveImplication(T, P, Q) := Imp(P, Lead(Q, T))`

### Key design: temporal patterns as tagged patterns

Rather than extending Pattern or OSLFFormula with a time type parameter
(which would require pervasive changes), we embed time into patterns:

  temporalPattern p t = Pattern.apply "⊛temporal" [p, Pattern.apply (toString t) []]

Old non-temporal Pattern queries are the special case `t = 0`. -/

section TemporalSemantics

/-- Embed a time index into a pattern.  Non-temporal patterns are `t = 0`. -/
def temporalPattern (p : Pattern) (t : Int) : Pattern :=
  Pattern.apply "⊛temporal" [p, Pattern.apply (toString t) []]

/-- Extract the spatial component from a temporal pattern at the same time. -/
theorem temporalPattern_injective_left {p₁ p₂ : Pattern} {t : Int}
    (h : temporalPattern p₁ t = temporalPattern p₂ t) : p₁ = p₂ := by
  simp [temporalPattern] at h
  exact h

/-- Same pattern at the same time gives the same temporal pattern. -/
@[simp] theorem temporalPattern_eq_iff {p₁ p₂ : Pattern} {t₁ t₂ : Int} :
    temporalPattern p₁ t₁ = temporalPattern p₂ t₂ ↔
    p₁ = p₂ ∧ toString t₁ = toString t₂ := by
  simp [temporalPattern]

/-- Temporal atom query: encode atom name + pattern + time into a WM query. -/
def temporalAtomQuery (baseAtomQuery : String → Pattern → Pattern)
    (a : String) (p : Pattern) (t : Int) : Pattern :=
  baseAtomQuery a (temporalPattern p t)

/-- Evidence-valued temporal atom semantics.  Evaluates an atom at a given
    time by embedding the time index into the query pattern. -/
noncomputable def temporalEvidenceAtomSem
    {State : Type*} [EvidenceType State] [WorldModel State Pattern]
    (W : State) (baseAtomQuery : String → Pattern → Pattern)
    (t : Int) : EvidenceAtomSem :=
  fun a p => WorldModel.evidence W (temporalAtomQuery baseAtomQuery a p t)

/-- Lag operator (Geisweiller & Yusuf §3.1):
    `Lag(I, T)` shifts atom evaluation backward by T time units.
    "Brings the past into the present." -/
noncomputable def lagAtomSem
    {State : Type*} [EvidenceType State] [WorldModel State Pattern]
    (W : State) (baseAtomQuery : String → Pattern → Pattern)
    (baseTime : Int) (lag : Int) : EvidenceAtomSem :=
  temporalEvidenceAtomSem W baseAtomQuery (baseTime - lag)

/-- Lead operator (Geisweiller & Yusuf §3.1):
    `Lead(I, T)` shifts atom evaluation forward by T time units.
    "Brings the future into the present." -/
noncomputable def leadAtomSem
    {State : Type*} [EvidenceType State] [WorldModel State Pattern]
    (W : State) (baseAtomQuery : String → Pattern → Pattern)
    (baseTime : Int) (lead : Int) : EvidenceAtomSem :=
  temporalEvidenceAtomSem W baseAtomQuery (baseTime + lead)

/-- Lead(Lag(P, T), T) ≡ P : shifting back then forward by T is identity. -/
theorem lagLeadIdentity
    {State : Type*} [EvidenceType State] [WorldModel State Pattern]
    (W : State) (baseAtomQuery : String → Pattern → Pattern)
    (baseTime : Int) (T : Int) :
    lagAtomSem W baseAtomQuery (baseTime + T) T =
    temporalEvidenceAtomSem W baseAtomQuery baseTime := by
  simp [lagAtomSem]

/-- SequentialAnd (Geisweiller & Yusuf §3.1):
    `SequentialAnd(T, φ, ψ)` = φ holds now AND ψ holds T time units later.
    Realized as conjunction with the second formula evaluated under Lead. -/
noncomputable def sequentialAndSemE
    {State : Type*} [EvidenceType State] [WorldModel State Pattern]
    (R : Pattern → Pattern → Prop)
    (W : State) (baseAtomQuery : String → Pattern → Pattern)
    (baseTime : Int) (T : Int)
    (φ ψ : OSLFFormula) (p : Pattern) : Evidence :=
  semE R (temporalEvidenceAtomSem W baseAtomQuery baseTime) φ p ⊓
  semE R (temporalEvidenceAtomSem W baseAtomQuery (baseTime + T)) ψ p

/-- PredictiveImplication (Geisweiller & Yusuf §3.1):
    `P ⇝ᵀ Q` = if P holds now then Q holds T time units later.
    Realized as implication with consequent evaluated under Lead. -/
noncomputable def predictiveImplicationSemE
    {State : Type*} [EvidenceType State] [WorldModel State Pattern]
    (R : Pattern → Pattern → Prop)
    (W : State) (baseAtomQuery : String → Pattern → Pattern)
    (baseTime : Int) (T : Int)
    (φ ψ : OSLFFormula) (p : Pattern) : Evidence :=
  semE R (temporalEvidenceAtomSem W baseAtomQuery baseTime) φ p ⇨
  semE R (temporalEvidenceAtomSem W baseAtomQuery (baseTime + T)) ψ p

/-- SequentialAnd is bounded by each component:
    `SequentialAnd(T, φ, ψ) ≤ semE(φ)` at the base time. -/
theorem sequentialAnd_le_left
    {State : Type*} [EvidenceType State] [WorldModel State Pattern]
    (R : Pattern → Pattern → Prop)
    (W : State) (baseAtomQuery : String → Pattern → Pattern)
    (baseTime : Int) (T : Int)
    (φ ψ : OSLFFormula) (p : Pattern) :
    sequentialAndSemE R W baseAtomQuery baseTime T φ ψ p ≤
    semE R (temporalEvidenceAtomSem W baseAtomQuery baseTime) φ p :=
  inf_le_left

/-- PredictiveImplication + antecedent evidence gives consequent evidence
    (modus ponens at the evidence level, using Heyting residuation). -/
theorem predictiveImplication_mp
    {State : Type*} [EvidenceType State] [WorldModel State Pattern]
    (R : Pattern → Pattern → Prop)
    (W : State) (baseAtomQuery : String → Pattern → Pattern)
    (baseTime : Int) (T : Int)
    (φ ψ : OSLFFormula) (p : Pattern) :
    semE R (temporalEvidenceAtomSem W baseAtomQuery baseTime) φ p ⊓
    predictiveImplicationSemE R W baseAtomQuery baseTime T φ ψ p ≤
    semE R (temporalEvidenceAtomSem W baseAtomQuery (baseTime + T)) ψ p :=
  inf_himp_le

/-- Temporal shifting rule (Geisweiller & Yusuf §3.2, rule S):
    The evidence of a proposition is preserved under time shift.
    Specifically, if φ is an atom, evidence is determined by the WM state
    at the shifted time — shifting merely changes WHICH time we look at,
    not the evidence structure. -/
theorem temporal_shift_atom
    {State : Type*} [EvidenceType State] [WorldModel State Pattern]
    (R : Pattern → Pattern → Prop)
    (W : State) (baseAtomQuery : String → Pattern → Pattern)
    (t : Int) (a : String) (p : Pattern) :
    semE R (temporalEvidenceAtomSem W baseAtomQuery t) (.atom a) p =
    WorldModel.evidence W (temporalAtomQuery baseAtomQuery a p t) := rfl

end TemporalSemantics

/-! ## Presupposition as Evidence Gating

Presuppositions are backgrounded content that must be satisfied for an assertion
to be felicitous (Strawson 1950, Heim 1983).  In evidence semantics, this is
naturally modeled using the tensor product (sequential composition):

  `presupGatedSemE(presup, assert, p) = E_presup(p) ⊗ E_assert(p)`

The tensor product is the right choice (vs. conjunction ⊓) because:
1. It represents independent, sequential composition of evidence
2. `⊗` distributes over `⨆` (quantale law), enabling presupposition
   projection through existential/diamond contexts
3. When presupposition evidence is `⊥` (unsatisfied), the tensor product
   collapses the whole sentence to `⊥`
4. When presupposition evidence is `one` (fully satisfied), tensor is
   transparent: `one ⊗ E_assert = E_assert`

### Projection Laws (van der Sandt 1992, Beaver 2001)

- **Negation projection**: `¬P` preserves the presupposition of P.
  "The king of France is NOT bald" still presupposes France has a king.

- **Conditional filtering**: In "If P then Q", presuppositions of Q are
  filtered by P.  Evidence version: presup(Q) is gated by presup(P→Q).

### References

- Strawson, "On Referring" (1950)
- Heim, "On the Projection Problem for Presuppositions" (1983)
- van der Sandt, "Presupposition Projection as Anaphora Resolution" (1992)
- Beaver, "Presupposition and Assertion in Dynamic Semantics" (2001)
-/

section Presupposition

/-- Presupposition-gated evidence: the total evidence of a presuppositional
    sentence is the tensor product of presupposition evidence and assertion evidence.

    Example: "The king of France is bald"
    - presup: ◇(is_king_of_france) — there exists a king of France
    - assert: is_bald — the referent is bald
    - gated evidence: E_presup ⊗ E_assert -/
noncomputable def presupGatedSemE (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (presup assert : OSLFFormula) (p : Pattern) : Evidence :=
  semE R I presup p * semE R I assert p

/-- When presupposition is fully satisfied (evidence = one), gating is transparent:
    `one ⊗ E_assert = E_assert`. -/
theorem presupGated_one_presup (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (presup assert : OSLFFormula) (p : Pattern)
    (h : semE R I presup p = Evidence.one) :
    presupGatedSemE R I presup assert p = semE R I assert p := by
  unfold presupGatedSemE
  rw [h, Evidence.one_tensor]

/-- When presupposition fails completely (evidence = ⊥), the gated evidence
    collapses to ⊥.  This captures presupposition failure. -/
theorem presupGated_bot_presup (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (presup assert : OSLFFormula) (p : Pattern)
    (h : semE R I presup p = ⊥) :
    presupGatedSemE R I presup assert p = ⊥ := by
  unfold presupGatedSemE
  rw [h]
  simp

/-- Gated evidence is bounded by assertion evidence (modulo presupposition).
    Since tensor components are multiplicative and evidence values are in ℝ≥0∞,
    `x * y ≤ y` when `x ≤ 1` (i.e., presupposition evidence is bounded). -/
theorem presupGated_le_assert_of_presup_le_one
    (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (presup assert : OSLFFormula) (p : Pattern)
    (hp : semE R I presup p ≤ Evidence.one) :
    presupGatedSemE R I presup assert p ≤ semE R I assert p := by
  unfold presupGatedSemE
  simp only [Evidence.le_def, Evidence.tensor_def, Evidence.one] at hp ⊢
  exact ⟨mul_le_of_le_one_left (zero_le _) hp.1, mul_le_of_le_one_left (zero_le _) hp.2⟩

/-- **Negation projection law**: Negation preserves presupposition.

    `presupGated(presup, ¬assert)` has the same presupposition component as
    `presupGated(presup, assert)`. We express this as: the presupposition
    evidence factor is identical regardless of whether the assertion is
    negated (negation is modeled as `assert → ⊥`). -/
theorem negation_preserves_presup (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (presup assert : OSLFFormula) (p : Pattern) :
    presupGatedSemE R I presup (.imp assert .bot) p =
    semE R I presup p * (semE R I assert p ⇨ ⊥) := by
  unfold presupGatedSemE
  simp [semE_imp, semE_bot]

/-- **Conditional filtering law**: In "If P then Q", the presupposition of Q
    is filtered through P.  At the evidence level, this means the presupposition
    evidence of Q is at least the implicational evidence P → presup(Q).

    Concretely: `semE(P → presupGated(presup_Q, Q)) ≥ semE(P → presup_Q) ⊓ semE(P → Q)`
    because the tensor factors can be separated under the Heyting residuation.

    We prove the simpler useful form: if P → presup(Q) is satisfied (≥ τ) and
    P → Q is satisfied (≥ τ), then P → presupGated(presup_Q, Q) is also
    supported at level τ ⊗ τ. -/
theorem conditional_filters_presup (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (antecedent presup_q assertion_q : OSLFFormula) (p : Pattern) (τ : Evidence)
    (h_presup : τ ≤ semE R I (.imp antecedent presup_q) p)
    (h_assert : τ ≤ semE R I (.imp antecedent assertion_q) p) :
    τ * τ ≤ semE R I (.imp antecedent presup_q) p *
             semE R I (.imp antecedent assertion_q) p := by
  exact mul_le_mul' h_presup h_assert

/-- Presupposition gating with shared presupposition distributes over conjunction:
    if the same presupposition gates both conjuncts, gating the conjunction is
    the same as conjoining the gated parts.

    `presupGated(π, φ₁ ∧ φ₂) = π ⊗ (semE(φ₁) ⊓ semE(φ₂))` -/
theorem presupGated_shared_and (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (presup assert₁ assert₂ : OSLFFormula) (p : Pattern) :
    presupGatedSemE R I presup (.and assert₁ assert₂) p =
    semE R I presup p * (semE R I assert₁ p ⊓ semE R I assert₂ p) := by
  unfold presupGatedSemE
  simp [semE_and]

/-- Presupposition gating monotonicity: stronger assertion gives stronger gated evidence. -/
theorem presupGated_mono_assert (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (presup assert₁ assert₂ : OSLFFormula) (p : Pattern)
    (h : semE R I assert₁ p ≤ semE R I assert₂ p) :
    presupGatedSemE R I presup assert₁ p ≤ presupGatedSemE R I presup assert₂ p := by
  unfold presupGatedSemE
  exact mul_le_mul_right h _

/-- Presupposition gating monotonicity: stronger presupposition gives stronger gated evidence. -/
theorem presupGated_mono_presup (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (presup₁ presup₂ assert : OSLFFormula) (p : Pattern)
    (h : semE R I presup₁ p ≤ semE R I presup₂ p) :
    presupGatedSemE R I presup₁ assert p ≤ presupGatedSemE R I presup₂ assert p := by
  unfold presupGatedSemE
  exact mul_le_mul_left h _

/-- Presupposition gating through diamond: if the presupposition and assertion
    hold at a successor, then the gated diamond holds.

    `◇(presupGated(presup, assert))` ≥ the gated value at any successor. -/
theorem presupGated_dia_le (R : Pattern → Pattern → Prop) (I : EvidenceAtomSem)
    (presup assert : OSLFFormula) (p q : Pattern) (hRpq : R p q) :
    presupGatedSemE R I presup assert q ≤
    ⨆ (s : {s // R p s}), presupGatedSemE R I presup assert s.val := by
  exact le_iSup (fun (s : {s // R p s}) => presupGatedSemE R I presup assert s.val) ⟨q, hRpq⟩

end Presupposition

end Mettapedia.Logic.OSLFEvidenceSemantics
