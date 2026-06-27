import Mettapedia.PLN.Bridges.HOL.DefinableCuts.Sugeno

namespace Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDefinableCuts

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.WithParams
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLCompletenessTightness
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLInheritanceBridge
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLQuantifierBridge
open Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLSimilarityBridge
open Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers
open Mettapedia.ProbabilityTheory.ImpreciseProbability.CredalSets

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## Cut-level saturated analogy transfer -/

/-- Canonical lower-endpoint transfer for saturated source-side analogy.

If the finite-vocabulary similarity cut for `p` and `q` is certainly saturated
over the extensional canonical family, and the full-inheritance cut from `q` to
`r` is certainly saturated, then the transferred full-inheritance cut from `p`
to `r` is certainly saturated as well. This is the credal/envelope-facing form
of the exact-threshold analogy-transfer theorem; it deliberately does not claim
soft similarity transfer below threshold `1`. -/
theorem predicateVocabularyFullInheritanceGeOneCut_lower_eq_one_of_source_similarity
    {T : ClosedTheorySet (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T)
    (σ : Ty Base)
    {Pred : Type w}
    (decode : Pred →
      UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    [Fintype Pred]
    (p q r : Pred)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hpE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).extent.ncard ≠ 0)
    (hpI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).intent.ncard ≠ 0)
    (hqE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).extent.ncard ≠ 0)
    (hqI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).intent.ncard ≠ 0)
    (hrI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning r).intent.ncard ≠ 0)
    (hSim0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateIffFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q)))
    (hQR0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode q) (decode r)))
    (hPR0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode r)))
    (hSimLower :
      ((predicateVocabularySimilarityGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode p q
        hObj hpE hqI hqE hpI hSim0).intervalOfConsistent
          (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1)
    (hQRLower :
      ((predicateVocabularyFullInheritanceGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode q r
        hObj hqE hrI hQR0).intervalOfConsistent
          (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1) :
    ((predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p r
      hObj hpE hrI hPR0).intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 := by
  let Csim :=
    predicateVocabularySimilarityGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hqE hpI hSim0
  let Cqr :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode q r
      hObj hqE hrI hQR0
  let Cpr :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p r
      hObj hpE hrI hPR0
  have hSimAll :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Csim.threshold ≤ Csim.score M :=
    (Csim.lower_eq_one_iff_forall_ge
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).1 hSimLower
  have hQRAll :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Cqr.threshold ≤ Cqr.score M :=
    (Cqr.lower_eq_one_iff_forall_ge
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).1 hQRLower
  exact
    (Cpr.lower_eq_one_iff_forall_ge
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).2 <|
      fun M => by
        letI := hObj M
        have hSimGe :
            1 ≤ predicateVocabularySimilarityStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p q := by
          simpa [Csim, predicateVocabularySimilarityGeOneCut] using hSimAll M
        have hSimLe :
            predicateVocabularySimilarityStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p q ≤ 1 :=
          predicateVocabularySimilarityStrength_le_one
            (Base := Base) (Const := WithParams Const) M.1 σ decode p q
        have hSimEq :
            predicateVocabularySimilarityStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p q = 1 :=
          le_antisymm hSimLe hSimGe
        have hQRGe :
            1 ≤ predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode q r := by
          simpa [Cqr, predicateVocabularyFullInheritanceGeOneCut] using hQRAll M
        have hQRLe :
            predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode q r ≤ 1 :=
          predicateVocabularyFullInheritanceStrength_le_one
            (Base := Base) (Const := WithParams Const) M.1 σ decode q r
        have hQREq :
            predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode q r = 1 :=
          le_antisymm hQRLe hQRGe
        have hPREq :
            predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p r = 1 :=
          predicateVocabularyFullInheritanceStrength_eq_one_of_source_similarity
            (Base := Base) (Const := WithParams Const) M.1 σ decode p q r
            (hpE M) (hpI M) (hqE M) (hqI M) (hrI M) hSimEq hQREq
        change 1 ≤ predicateVocabularyFullInheritanceStrength
          (Base := Base) (Const := WithParams Const) M.1 σ decode p r
        exact le_of_eq hPREq.symm

/-- Joint-cut version of saturated source-side analogy transfer.

This is the rule-facing use of `andCut`: the two premises "source-side
similarity is saturated" and "`q` fully inherits to `r`" are carried by one
certified conjunctive cut. The proof deliberately reuses the existing
source-side transfer theorem after unpacking the joint endpoint, so no parallel
analogy semantics is introduced. -/
theorem predicateVocabularyFullInheritanceGeOneCut_lower_eq_one_of_source_similarity_jointCut
    {T : ClosedTheorySet (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T)
    (σ : Ty Base)
    {Pred : Type w}
    (decode : Pred →
      UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    [Fintype Pred]
    (p q r : Pred)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hpE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).extent.ncard ≠ 0)
    (hpI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).intent.ncard ≠ 0)
    (hqE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).extent.ncard ≠ 0)
    (hqI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).intent.ncard ≠ 0)
    (hrI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning r).intent.ncard ≠ 0)
    (hSim0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateIffFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q)))
    (hQR0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode q) (decode r)))
    (hPR0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode r)))
    (hJointLower :
      (((predicateVocabularySimilarityGeOneCut
          (Base := Base) (Const := Const) (T := T) σ decode p q
          hObj hpE hqI hqE hpI hSim0).andCut
        (Base := Base) (Const := Const)
        (predicateVocabularyFullInheritanceGeOneCut
          (Base := Base) (Const := Const) (T := T) σ decode q r
          hObj hqE hrI hQR0)).intervalOfConsistent
            (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1) :
    ((predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p r
      hObj hpE hrI hPR0).intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 := by
  let Csim :=
    predicateVocabularySimilarityGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hqE hpI hSim0
  let Cqr :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode q r
      hObj hqE hrI hQR0
  have hBothAll :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Csim.threshold ≤ Csim.score M ∧ Cqr.threshold ≤ Cqr.score M :=
    (Csim.andCut_lower_eq_one_iff_forall_both_ge
      (Base := Base) (Const := Const) Cqr enum henum hCons hT0 hEM).1 hJointLower
  have hSimLower :
      (Csim.intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 :=
    (Csim.lower_eq_one_iff_forall_ge
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).2
      (fun M => (hBothAll M).1)
  have hQRLower :
      (Cqr.intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 :=
    (Cqr.lower_eq_one_iff_forall_ge
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).2
      (fun M => (hBothAll M).2)
  exact
    predicateVocabularyFullInheritanceGeOneCut_lower_eq_one_of_source_similarity
      (Base := Base) (Const := Const)
      enum henum hCons hT0 hEM σ decode p q r
      hObj hpE hpI hqE hqI hrI hSim0 hQR0 hPR0
      hSimLower hQRLower

/-- Rule-implication cut for saturated source-side analogy transfer.

Rather than taking the two saturated premises as global hypotheses, this
theorem packages the whole exact-threshold source-side analogy rule as one
certified implication cut:

`(similarity(p,q) = 1 ∧ inheritance(q,r) = 1) -> inheritance(p,r) = 1`.

The proof is pointwise over the canonical extensional theory-model family and
uses the existing full-inheritance source-similarity theorem, so this is a rule
gate over the established extensional/intensional machinery, not a duplicate
analogy semantics. -/
theorem predicateVocabularyFullInheritanceGeOneCut_sourceSimilarityRuleImpCut_lower_eq_one
    {T : ClosedTheorySet (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T)
    (σ : Ty Base)
    {Pred : Type w}
    (decode : Pred →
      UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    [Fintype Pred]
    (p q r : Pred)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hpE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).extent.ncard ≠ 0)
    (hpI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).intent.ncard ≠ 0)
    (hqE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).extent.ncard ≠ 0)
    (hqI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).intent.ncard ≠ 0)
    (hrI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning r).intent.ncard ≠ 0)
    (hSim0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateIffFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q)))
    (hQR0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode q) (decode r)))
    (hPR0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode r))) :
    ((((predicateVocabularySimilarityGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode p q
        hObj hpE hqI hqE hpI hSim0).andCut
      (Base := Base) (Const := Const)
      (predicateVocabularyFullInheritanceGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode q r
        hObj hqE hrI hQR0)).impCut
      (Base := Base) (Const := Const)
      (predicateVocabularyFullInheritanceGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode p r
        hObj hpE hrI hPR0)).intervalOfConsistent
          (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 := by
  let Csim :=
    predicateVocabularySimilarityGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hqE hpI hSim0
  let Cqr :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode q r
      hObj hqE hrI hQR0
  let Cpr :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p r
      hObj hpE hrI hPR0
  exact
    ((Csim.andCut (Base := Base) (Const := Const) Cqr).impCut_lower_eq_one_iff_forall_imp_ge
      (Base := Base) (Const := Const) Cpr enum henum hCons hT0 hEM).2 <|
      fun M hJoint => by
        letI := hObj M
        have hBoth :
            Csim.threshold ≤ Csim.score M ∧ Cqr.threshold ≤ Cqr.score M :=
          (Csim.andCut_ge_iff (Base := Base) (Const := Const) Cqr M).mp hJoint
        have hSimGe :
            1 ≤ predicateVocabularySimilarityStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p q := by
          simpa [Csim, predicateVocabularySimilarityGeOneCut] using hBoth.1
        have hSimLe :
            predicateVocabularySimilarityStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p q ≤ 1 :=
          predicateVocabularySimilarityStrength_le_one
            (Base := Base) (Const := WithParams Const) M.1 σ decode p q
        have hSimEq :
            predicateVocabularySimilarityStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p q = 1 :=
          le_antisymm hSimLe hSimGe
        have hQRGe :
            1 ≤ predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode q r := by
          simpa [Cqr, predicateVocabularyFullInheritanceGeOneCut] using hBoth.2
        have hQRLe :
            predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode q r ≤ 1 :=
          predicateVocabularyFullInheritanceStrength_le_one
            (Base := Base) (Const := WithParams Const) M.1 σ decode q r
        have hQREq :
            predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode q r = 1 :=
          le_antisymm hQRLe hQRGe
        have hPREq :
            predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p r = 1 :=
          predicateVocabularyFullInheritanceStrength_eq_one_of_source_similarity
            (Base := Base) (Const := WithParams Const) M.1 σ decode p q r
            (hpE M) (hpI M) (hqE M) (hqI M) (hrI M) hSimEq hQREq
        change 1 ≤ predicateVocabularyFullInheritanceStrength
          (Base := Base) (Const := WithParams Const) M.1 σ decode p r
        exact le_of_eq hPREq.symm

/-- Canonical lower-endpoint transfer for saturated target-side analogy. -/
theorem predicateVocabularyFullInheritanceGeOneCut_lower_eq_one_of_target_similarity
    {T : ClosedTheorySet (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T)
    (σ : Ty Base)
    {Pred : Type w}
    (decode : Pred →
      UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    [Fintype Pred]
    (p q r : Pred)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hpE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).extent.ncard ≠ 0)
    (hqE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).extent.ncard ≠ 0)
    (hqI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).intent.ncard ≠ 0)
    (hrE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning r).extent.ncard ≠ 0)
    (hrI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning r).intent.ncard ≠ 0)
    (hPQ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q)))
    (hSim0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateIffFormula
        (Base := Base) (Const := WithParams Const) σ (decode q) (decode r)))
    (hPR0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode r)))
    (hPQLower :
      ((predicateVocabularyFullInheritanceGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode p q
        hObj hpE hqI hPQ0).intervalOfConsistent
          (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1)
    (hSimLower :
      ((predicateVocabularySimilarityGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode q r
        hObj hqE hrI hrE hqI hSim0).intervalOfConsistent
          (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1) :
    ((predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p r
      hObj hpE hrI hPR0).intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 := by
  let Cpq :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hPQ0
  let Csim :=
    predicateVocabularySimilarityGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode q r
      hObj hqE hrI hrE hqI hSim0
  let Cpr :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p r
      hObj hpE hrI hPR0
  have hPQAll :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Cpq.threshold ≤ Cpq.score M :=
    (Cpq.lower_eq_one_iff_forall_ge
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).1 hPQLower
  have hSimAll :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Csim.threshold ≤ Csim.score M :=
    (Csim.lower_eq_one_iff_forall_ge
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).1 hSimLower
  exact
    (Cpr.lower_eq_one_iff_forall_ge
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).2 <|
      fun M => by
        letI := hObj M
        have hPQGe :
            1 ≤ predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p q := by
          simpa [Cpq, predicateVocabularyFullInheritanceGeOneCut] using hPQAll M
        have hPQLe :
            predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p q ≤ 1 :=
          predicateVocabularyFullInheritanceStrength_le_one
            (Base := Base) (Const := WithParams Const) M.1 σ decode p q
        have hPQEq :
            predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p q = 1 :=
          le_antisymm hPQLe hPQGe
        have hSimGe :
            1 ≤ predicateVocabularySimilarityStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode q r := by
          simpa [Csim, predicateVocabularySimilarityGeOneCut] using hSimAll M
        have hSimLe :
            predicateVocabularySimilarityStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode q r ≤ 1 :=
          predicateVocabularySimilarityStrength_le_one
            (Base := Base) (Const := WithParams Const) M.1 σ decode q r
        have hSimEq :
            predicateVocabularySimilarityStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode q r = 1 :=
          le_antisymm hSimLe hSimGe
        have hPREq :
            predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p r = 1 :=
          predicateVocabularyFullInheritanceStrength_eq_one_of_target_similarity
            (Base := Base) (Const := WithParams Const) M.1 σ decode p q r
            (hpE M) (hqI M) (hqE M) (hrE M) (hrI M) hPQEq hSimEq
        change 1 ≤ predicateVocabularyFullInheritanceStrength
          (Base := Base) (Const := WithParams Const) M.1 σ decode p r
        exact le_of_eq hPREq.symm

/-- Joint-cut version of saturated target-side analogy transfer.

This is the companion rule-facing use of `andCut`: the two premises "`p` fully
inherits to `q`" and "target-side similarity between `q` and `r` is saturated"
are carried by one certified conjunctive cut. As with the source-side version,
the proof unpacks the joint endpoint and reuses the existing target-side
transfer theorem. -/
theorem predicateVocabularyFullInheritanceGeOneCut_lower_eq_one_of_target_similarity_jointCut
    {T : ClosedTheorySet (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T)
    (σ : Ty Base)
    {Pred : Type w}
    (decode : Pred →
      UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    [Fintype Pred]
    (p q r : Pred)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hpE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).extent.ncard ≠ 0)
    (hqE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).extent.ncard ≠ 0)
    (hqI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).intent.ncard ≠ 0)
    (hrE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning r).extent.ncard ≠ 0)
    (hrI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning r).intent.ncard ≠ 0)
    (hPQ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q)))
    (hSim0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateIffFormula
        (Base := Base) (Const := WithParams Const) σ (decode q) (decode r)))
    (hPR0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode r)))
    (hJointLower :
      (((predicateVocabularyFullInheritanceGeOneCut
          (Base := Base) (Const := Const) (T := T) σ decode p q
          hObj hpE hqI hPQ0).andCut
        (Base := Base) (Const := Const)
        (predicateVocabularySimilarityGeOneCut
          (Base := Base) (Const := Const) (T := T) σ decode q r
          hObj hqE hrI hrE hqI hSim0)).intervalOfConsistent
            (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1) :
    ((predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p r
      hObj hpE hrI hPR0).intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 := by
  let Cpq :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hPQ0
  let Csim :=
    predicateVocabularySimilarityGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode q r
      hObj hqE hrI hrE hqI hSim0
  have hBothAll :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Cpq.threshold ≤ Cpq.score M ∧ Csim.threshold ≤ Csim.score M :=
    (Cpq.andCut_lower_eq_one_iff_forall_both_ge
      (Base := Base) (Const := Const) Csim enum henum hCons hT0 hEM).1 hJointLower
  have hPQLower :
      (Cpq.intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 :=
    (Cpq.lower_eq_one_iff_forall_ge
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).2
      (fun M => (hBothAll M).1)
  have hSimLower :
      (Csim.intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 :=
    (Csim.lower_eq_one_iff_forall_ge
      (Base := Base) (Const := Const) enum henum hCons hT0 hEM).2
      (fun M => (hBothAll M).2)
  exact
    predicateVocabularyFullInheritanceGeOneCut_lower_eq_one_of_target_similarity
      (Base := Base) (Const := Const)
      enum henum hCons hT0 hEM σ decode p q r
      hObj hpE hqE hqI hrE hrI hPQ0 hSim0 hPR0
      hPQLower hSimLower

/-- Rule-implication cut for saturated target-side analogy transfer.

This packages the exact-threshold target-side analogy rule as one certified
implication cut:

`(inheritance(p,q) = 1 ∧ similarity(q,r) = 1) -> inheritance(p,r) = 1`.

As with the source-side rule cut, the proof is pointwise over the canonical
extensional theory-model family and reuses the existing target-side transfer
theorem. -/
theorem predicateVocabularyFullInheritanceGeOneCut_targetSimilarityRuleImpCut_lower_eq_one
    {T : ClosedTheorySet (WithParams Const)}
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T)
    (σ : Ty Base)
    {Pred : Type w}
    (decode : Pred →
      UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    [Fintype Pred]
    (p q r : Pred)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hpE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).extent.ncard ≠ 0)
    (hqE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).extent.ncard ≠ 0)
    (hqI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).intent.ncard ≠ 0)
    (hrE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning r).extent.ncard ≠ 0)
    (hrI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning r).intent.ncard ≠ 0)
    (hPQ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q)))
    (hSim0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateIffFormula
        (Base := Base) (Const := WithParams Const) σ (decode q) (decode r)))
    (hPR0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode r))) :
    ((((predicateVocabularyFullInheritanceGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode p q
        hObj hpE hqI hPQ0).andCut
      (Base := Base) (Const := Const)
      (predicateVocabularySimilarityGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode q r
        hObj hqE hrI hrE hqI hSim0)).impCut
      (Base := Base) (Const := Const)
      (predicateVocabularyFullInheritanceGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode p r
        hObj hpE hrI hPR0)).intervalOfConsistent
          (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 := by
  let Cpq :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hPQ0
  let Csim :=
    predicateVocabularySimilarityGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode q r
      hObj hqE hrI hrE hqI hSim0
  let Cpr :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p r
      hObj hpE hrI hPR0
  exact
    ((Cpq.andCut (Base := Base) (Const := Const) Csim).impCut_lower_eq_one_iff_forall_imp_ge
      (Base := Base) (Const := Const) Cpr enum henum hCons hT0 hEM).2 <|
      fun M hJoint => by
        letI := hObj M
        have hBoth :
            Cpq.threshold ≤ Cpq.score M ∧ Csim.threshold ≤ Csim.score M :=
          (Cpq.andCut_ge_iff (Base := Base) (Const := Const) Csim M).mp hJoint
        have hPQGe :
            1 ≤ predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p q := by
          simpa [Cpq, predicateVocabularyFullInheritanceGeOneCut] using hBoth.1
        have hPQLe :
            predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p q ≤ 1 :=
          predicateVocabularyFullInheritanceStrength_le_one
            (Base := Base) (Const := WithParams Const) M.1 σ decode p q
        have hPQEq :
            predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p q = 1 :=
          le_antisymm hPQLe hPQGe
        have hSimGe :
            1 ≤ predicateVocabularySimilarityStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode q r := by
          simpa [Csim, predicateVocabularySimilarityGeOneCut] using hBoth.2
        have hSimLe :
            predicateVocabularySimilarityStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode q r ≤ 1 :=
          predicateVocabularySimilarityStrength_le_one
            (Base := Base) (Const := WithParams Const) M.1 σ decode q r
        have hSimEq :
            predicateVocabularySimilarityStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode q r = 1 :=
          le_antisymm hSimLe hSimGe
        have hPREq :
            predicateVocabularyFullInheritanceStrength
              (Base := Base) (Const := WithParams Const) M.1 σ decode p r = 1 :=
          predicateVocabularyFullInheritanceStrength_eq_one_of_target_similarity
            (Base := Base) (Const := WithParams Const) M.1 σ decode p q r
            (hpE M) (hqI M) (hqE M) (hrE M) (hrI M) hPQEq hSimEq
        change 1 ≤ predicateVocabularyFullInheritanceStrength
          (Base := Base) (Const := WithParams Const) M.1 σ decode p r
        exact le_of_eq hPREq.symm


end Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDefinableCuts
