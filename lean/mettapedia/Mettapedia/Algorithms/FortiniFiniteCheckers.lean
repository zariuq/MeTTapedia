import Mettapedia.Logic.MarkovDeFinettiFortiniBridgeCore
import Mettapedia.Logic.MarkovExchangeability
import Mettapedia.Logic.Bridges.CheckerReflection
import Mathlib.Data.Fintype.EquivFin

/-!
# Markov de Finetti Fortini Bridge: Finite Checkers

Executable checker layer for the finite combinatorial obligations that appear in
the Fortini bridge crux:

- finite carrier cardinality compatibility (`s ≃ t` obstruction),
- candidate evidence-preserving map checks,
- candidate bijection + evidence checks that can be lifted to an equivalence.
-/

noncomputable section

namespace Mettapedia.Logic

namespace MarkovDeFinettiHard

open Mettapedia.Logic.MarkovExchangeability

section FinsetCard

variable {α : Type*}

/-- Boolean checker for cardinality compatibility of finite carriers. -/
def finsetSubtypeCardEqChecker (s t : Finset α) : Bool :=
  Mettapedia.Logic.Bridges.propChecker (s.card = t.card)

theorem finsetSubtypeCardEq_of_checker_true {s t : Finset α}
    (h : finsetSubtypeCardEqChecker s t = true) : s.card = t.card := by
  exact Mettapedia.Logic.Bridges.prop_of_checker_true (p := s.card = t.card) h

theorem finsetSubtypeCardNe_of_checker_false {s t : Finset α}
    (h : finsetSubtypeCardEqChecker s t = false) : s.card ≠ t.card := by
  exact Mettapedia.Logic.Bridges.not_prop_of_checker_false (p := s.card = t.card) h

theorem not_nonempty_equiv_of_finsetSubtypeCardEqChecker_false {s t : Finset α}
    (h : finsetSubtypeCardEqChecker s t = false) :
    ¬ Nonempty (s ≃ t) := by
  intro he
  have hcardSubtype : Fintype.card s = Fintype.card t := Fintype.card_eq.2 he
  have hcard : s.card = t.card := by simpa [Fintype.card_coe] using hcardSubtype
  exact (finsetSubtypeCardNe_of_checker_false (s := s) (t := t) h) hcard

theorem nonempty_equiv_of_finsetSubtypeCardEqChecker_true {s t : Finset α}
    (h : finsetSubtypeCardEqChecker s t = true) :
    Nonempty (s ≃ t) := by
  let hcard : s.card = t.card := finsetSubtypeCardEq_of_checker_true (s := s) (t := t) h
  have hcardSubtype : Fintype.card s = Fintype.card t := by
    simpa [Fintype.card_coe] using hcard
  exact ⟨Fintype.equivOfCardEq hcardSubtype⟩

theorem finsetSubtypeCardEqChecker_false_of_not_nonempty_equiv {s t : Finset α}
    (h : ¬ Nonempty (s ≃ t)) :
    finsetSubtypeCardEqChecker s t = false := by
  by_cases hchk : finsetSubtypeCardEqChecker s t = false
  · exact hchk
  · have htrue : finsetSubtypeCardEqChecker s t = true := by
      cases hval : finsetSubtypeCardEqChecker s t with
      | false => exact (hchk hval).elim
      | true => rfl
    exfalso
    exact h (nonempty_equiv_of_finsetSubtypeCardEqChecker_true (s := s) (t := t) htrue)

end FinsetCard

section EvidenceCheckers

variable {α : Type*} [DecidableEq α]
variable {n : ℕ}

/-- Checker that a candidate map preserves Markov evidence. -/
def evidencePreservingMapChecker
    (s t : Finset (Fin (n + 1) → α))
    (f : s → t) : Bool :=
  by
    classical
    exact Mettapedia.Logic.Bridges.propChecker
      (∀ xs : s, evidenceOf (n := n) xs.1 = evidenceOf (n := n) (f xs).1)

theorem evidencePreservingMap_of_checker_true
    {s t : Finset (Fin (n + 1) → α)} {f : s → t}
    (h : evidencePreservingMapChecker (n := n) s t f = true) :
    ∀ xs : s, evidenceOf (n := n) xs.1 = evidenceOf (n := n) (f xs).1 := by
  classical
  exact Mettapedia.Logic.Bridges.prop_of_checker_true
    (p := ∀ xs : s, evidenceOf (n := n) xs.1 = evidenceOf (n := n) (f xs).1) h

theorem not_evidencePreservingMap_of_checker_false
    {s t : Finset (Fin (n + 1) → α)} {f : s → t}
    (h : evidencePreservingMapChecker (n := n) s t f = false) :
    ¬ ∀ xs : s, evidenceOf (n := n) xs.1 = evidenceOf (n := n) (f xs).1 := by
  classical
  exact Mettapedia.Logic.Bridges.not_prop_of_checker_false
    (p := ∀ xs : s, evidenceOf (n := n) xs.1 = evidenceOf (n := n) (f xs).1) h

/-- Checker for "candidate map is bijective and evidence-preserving". -/
def evidencePreservingBijectiveMapChecker
    (s t : Finset (Fin (n + 1) → α))
    (f : s → t) : Bool :=
  by
    classical
    exact Mettapedia.Logic.Bridges.propChecker
      (Function.Bijective f ∧
        ∀ xs : s, evidenceOf (n := n) xs.1 = evidenceOf (n := n) (f xs).1)

theorem exists_equiv_and_evidence_of_bijectiveChecker_true
    {s t : Finset (Fin (n + 1) → α)} {f : s → t}
    (h : evidencePreservingBijectiveMapChecker (n := n) s t f = true) :
    ∃ e : s ≃ t,
      ∀ xs : s, evidenceOf (n := n) xs.1 = evidenceOf (n := n) (e xs).1 := by
  classical
  have hspec :
      Function.Bijective f ∧
        ∀ xs : s, evidenceOf (n := n) xs.1 = evidenceOf (n := n) (f xs).1 :=
    Mettapedia.Logic.Bridges.prop_of_checker_true
      (p := Function.Bijective f ∧
        ∀ xs : s, evidenceOf (n := n) xs.1 = evidenceOf (n := n) (f xs).1) h
  rcases hspec with ⟨hbij, hpres⟩
  refine ⟨Equiv.ofBijective f hbij, ?_⟩
  intro xs
  simpa using hpres xs

theorem bijectiveChecker_true_of_equiv_and_evidence
    {s t : Finset (Fin (n + 1) → α)} (e : s ≃ t)
    (hpres : ∀ xs : s, evidenceOf (n := n) xs.1 = evidenceOf (n := n) (e xs).1) :
    evidencePreservingBijectiveMapChecker (n := n) s t e = true := by
  classical
  refine Mettapedia.Logic.Bridges.checker_true_of_prop ?_
  exact ⟨e.bijective, hpres⟩

end EvidenceCheckers

section PrefixCarrierSpecialized

variable {k : ℕ}

/-- Cardinality-compatibility checker for two finite prefix carriers. -/
def prefixCarrierCardEqChecker
    (i₁ : Fin k) (S₁ : Finset ℕ) (v₁ : ℕ → Fin k)
    (i₂ : Fin k) (S₂ : Finset ℕ) (v₂ : ℕ → Fin k)
    (N : ℕ) : Bool :=
  finsetSubtypeCardEqChecker
    (rowVisitCylinderEventUpToPrefixCarrier (k := k) i₁ S₁ v₁ N)
    (rowVisitCylinderEventUpToPrefixCarrier (k := k) i₂ S₂ v₂ N)

theorem not_prefixCarrier_equiv_of_cardChecker_false
    (i₁ : Fin k) (S₁ : Finset ℕ) (v₁ : ℕ → Fin k)
    (i₂ : Fin k) (S₂ : Finset ℕ) (v₂ : ℕ → Fin k)
    (N : ℕ)
    (h :
      prefixCarrierCardEqChecker (k := k) i₁ S₁ v₁ i₂ S₂ v₂ N = false) :
    ¬ Nonempty (
      rowVisitCylinderEventUpToPrefixCarrier (k := k) i₁ S₁ v₁ N ≃
      rowVisitCylinderEventUpToPrefixCarrier (k := k) i₂ S₂ v₂ N) := by
  exact
    not_nonempty_equiv_of_finsetSubtypeCardEqChecker_false
      (s := rowVisitCylinderEventUpToPrefixCarrier (k := k) i₁ S₁ v₁ N)
      (t := rowVisitCylinderEventUpToPrefixCarrier (k := k) i₂ S₂ v₂ N) h

/-- Candidate-checker specialized to Fortini's evidence-preserving carrier witness. -/
def prefixCarrierEvidencePreservingBijectiveChecker
    (i₁ : Fin k) (S₁ : Finset ℕ) (v₁ : ℕ → Fin k)
    (i₂ : Fin k) (S₂ : Finset ℕ) (v₂ : ℕ → Fin k)
    (N : ℕ)
    (f :
      rowVisitCylinderEventUpToPrefixCarrier (k := k) i₁ S₁ v₁ N →
      rowVisitCylinderEventUpToPrefixCarrier (k := k) i₂ S₂ v₂ N) : Bool :=
  evidencePreservingBijectiveMapChecker (n := N)
    (rowVisitCylinderEventUpToPrefixCarrier (k := k) i₁ S₁ v₁ N)
    (rowVisitCylinderEventUpToPrefixCarrier (k := k) i₂ S₂ v₂ N) f

theorem exists_prefixCarrier_equiv_with_evidence_of_checker_true
    (i₁ : Fin k) (S₁ : Finset ℕ) (v₁ : ℕ → Fin k)
    (i₂ : Fin k) (S₂ : Finset ℕ) (v₂ : ℕ → Fin k)
    (N : ℕ)
    (f :
      rowVisitCylinderEventUpToPrefixCarrier (k := k) i₁ S₁ v₁ N →
      rowVisitCylinderEventUpToPrefixCarrier (k := k) i₂ S₂ v₂ N)
    (h :
      prefixCarrierEvidencePreservingBijectiveChecker
        (k := k) i₁ S₁ v₁ i₂ S₂ v₂ N f = true) :
    ∃ e :
      rowVisitCylinderEventUpToPrefixCarrier (k := k) i₁ S₁ v₁ N ≃
        rowVisitCylinderEventUpToPrefixCarrier (k := k) i₂ S₂ v₂ N,
      ∀ xs :
        rowVisitCylinderEventUpToPrefixCarrier (k := k) i₁ S₁ v₁ N,
        Mettapedia.Logic.MarkovExchangeability.evidenceOf (n := N) xs.1 =
          Mettapedia.Logic.MarkovExchangeability.evidenceOf (n := N) (e xs).1 := by
  simpa [prefixCarrierEvidencePreservingBijectiveChecker] using
    (exists_equiv_and_evidence_of_bijectiveChecker_true
      (n := N) (s := rowVisitCylinderEventUpToPrefixCarrier (k := k) i₁ S₁ v₁ N)
      (t := rowVisitCylinderEventUpToPrefixCarrier (k := k) i₂ S₂ v₂ N) (f := f) h)

/-- Convenience checker for the singleton-index carrier shape used in Fortini crux
counterexamples (`{n}` versus `{0}` at fixed anchor/value). -/
def rowVisitSingletonCarrierCardEqChecker
    (i a : Fin k) (n N : ℕ) : Bool :=
  prefixCarrierCardEqChecker (k := k)
    i ({n} : Finset ℕ) (fun m => if m = n then a else i)
    i ({0} : Finset ℕ) (fun m => if m = 0 then a else i)
    N

/-- Convenience checker for existence of an evidence-preserving singleton-carrier
equivalence (`{n}` versus `{0}`). -/
def rowVisitSingletonCarrierEvidenceEquivChecker
    (i a : Fin k) (n N : ℕ) : Bool :=
  by
    classical
    exact Mettapedia.Logic.Bridges.propChecker
      (∃ e :
          rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({n} : Finset ℕ)
            (fun m => if m = n then a else i) N ≃
            rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({0} : Finset ℕ)
              (fun m => if m = 0 then a else i) N,
        ∀ xs :
          rowVisitCylinderEventUpToPrefixCarrier (k := k) i ({n} : Finset ℕ)
            (fun m => if m = n then a else i) N,
          Mettapedia.Logic.MarkovExchangeability.evidenceOf (n := N) xs.1 =
            Mettapedia.Logic.MarkovExchangeability.evidenceOf (n := N) (e xs).1)

end PrefixCarrierSpecialized

end MarkovDeFinettiHard

end Mettapedia.Logic
