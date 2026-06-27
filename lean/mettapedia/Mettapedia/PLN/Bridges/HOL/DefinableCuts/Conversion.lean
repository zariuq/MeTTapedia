import Mettapedia.PLN.Bridges.HOL.DefinableCuts.AnalogyTransfer

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

/-! ## Cut-level similarity / inheritance conversion -/

/-- Certified conversion from saturated predicate similarity to the forward
directed full-inheritance cut.

At threshold `1`, predicate similarity is represented by HOL predicate
equivalence, hence it entails the forward predicate-implication formula.  The
result is packaged as an implication cut so downstream PLN rule surfaces can
consume the conversion without duplicating the similarity semantics. -/
theorem predicateVocabularySimilarityGeOneCut_forwardInheritanceRuleImpCut_lower_eq_one
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
    (p q : Pred)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hpE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).extent.ncard ≠ 0)
    (hqI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).intent.ncard ≠ 0)
    (hqE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).extent.ncard ≠ 0)
    (hpI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).intent.ncard ≠ 0)
    (hSim0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateIffFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q)))
    (hPQ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q))) :
    (((predicateVocabularySimilarityGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hqE hpI hSim0).impCut
      (Base := Base) (Const := Const)
      (predicateVocabularyFullInheritanceGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode p q
        hObj hpE hqI hPQ0)).intervalOfConsistent
          (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 := by
  let Csim :=
    predicateVocabularySimilarityGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hqE hpI hSim0
  let Cpq :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hPQ0
  exact
    (Csim.impCut_lower_eq_one_iff_forall_imp_ge
      (Base := Base) (Const := Const) Cpq enum henum hCons hT0 hEM).2 <|
      fun M hSim => by
        have hIff : HenkinModel.models M.1 Csim.formula :=
          (Csim.represents_ge M).mpr hSim
        have hImp : HenkinModel.models M.1 Cpq.formula :=
          (HenkinModel.models_and M.1).mp hIff |>.1
        exact (Cpq.represents_ge M).mp hImp

/-- Certified conversion from saturated predicate similarity to the reverse
directed full-inheritance cut. -/
theorem predicateVocabularySimilarityGeOneCut_reverseInheritanceRuleImpCut_lower_eq_one
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
    (p q : Pred)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hpE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).extent.ncard ≠ 0)
    (hqI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).intent.ncard ≠ 0)
    (hqE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).extent.ncard ≠ 0)
    (hpI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).intent.ncard ≠ 0)
    (hSim0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateIffFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q)))
    (hQP0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode q) (decode p))) :
    (((predicateVocabularySimilarityGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hqE hpI hSim0).impCut
      (Base := Base) (Const := Const)
      (predicateVocabularyFullInheritanceGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode q p
        hObj hqE hpI hQP0)).intervalOfConsistent
          (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 := by
  let Csim :=
    predicateVocabularySimilarityGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hqE hpI hSim0
  let Cqp :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode q p
      hObj hqE hpI hQP0
  exact
    (Csim.impCut_lower_eq_one_iff_forall_imp_ge
      (Base := Base) (Const := Const) Cqp enum henum hCons hT0 hEM).2 <|
      fun M hSim => by
        have hIff : HenkinModel.models M.1 Csim.formula :=
          (Csim.represents_ge M).mpr hSim
        have hImp : HenkinModel.models M.1 Cqp.formula :=
          (HenkinModel.models_and M.1).mp hIff |>.2
        exact (Cqp.represents_ge M).mp hImp

/-- Certified conversion from mutual directed full inheritance to saturated
predicate similarity.

The premise is one conjunctive certified cut for the two directed inheritance
threshold events.  The conclusion is the existing finite-vocabulary similarity
cut, whose representing formula is the conjunction of those two predicate
implications. -/
theorem predicateVocabularySimilarityGeOneCut_of_mutualInheritanceRuleImpCut_lower_eq_one
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
    (p q : Pred)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hpE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).extent.ncard ≠ 0)
    (hqI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).intent.ncard ≠ 0)
    (hqE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).extent.ncard ≠ 0)
    (hpI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).intent.ncard ≠ 0)
    (hPQ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q)))
    (hQP0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode q) (decode p)))
    (hSim0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateIffFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q))) :
    ((((predicateVocabularyFullInheritanceGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode p q
        hObj hpE hqI hPQ0).andCut
      (Base := Base) (Const := Const)
      (predicateVocabularyFullInheritanceGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode q p
        hObj hqE hpI hQP0)).impCut
      (Base := Base) (Const := Const)
      (predicateVocabularySimilarityGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode p q
        hObj hpE hqI hqE hpI hSim0)).intervalOfConsistent
          (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 := by
  let Cpq :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hPQ0
  let Cqp :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode q p
      hObj hqE hpI hQP0
  let Csim :=
    predicateVocabularySimilarityGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hqE hpI hSim0
  exact
    ((Cpq.andCut (Base := Base) (Const := Const) Cqp).impCut_lower_eq_one_iff_forall_imp_ge
      (Base := Base) (Const := Const) Csim enum henum hCons hT0 hEM).2 <|
      fun M hJoint => by
        have hBoth :
            Cpq.threshold ≤ Cpq.score M ∧ Cqp.threshold ≤ Cqp.score M :=
          (Cpq.andCut_ge_iff (Base := Base) (Const := Const) Cqp M).mp hJoint
        have hPQModels : HenkinModel.models M.1 Cpq.formula :=
          (Cpq.represents_ge M).mpr hBoth.1
        have hQPModels : HenkinModel.models M.1 Cqp.formula :=
          (Cqp.represents_ge M).mpr hBoth.2
        have hIff : HenkinModel.models M.1 Csim.formula :=
          (HenkinModel.models_and M.1).mpr ⟨hPQModels, hQPModels⟩
        exact (Csim.represents_ge M).mp hIff

/-- Consumer form of saturated similarity-to-forward-inheritance conversion.

If the finite-vocabulary similarity cut is certainly saturated, then the
forward directed full-inheritance cut is certainly saturated.  This is the
exact-threshold, cut-level form of PLN's similarity-to-inheritance conversion;
it reuses the existing representing formula for similarity rather than defining
a parallel numeric conversion. -/
theorem predicateVocabularyFullInheritanceGeOneCut_forward_lower_eq_one_of_similarity
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
    (p q : Pred)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hpE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).extent.ncard ≠ 0)
    (hqI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).intent.ncard ≠ 0)
    (hqE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).extent.ncard ≠ 0)
    (hpI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).intent.ncard ≠ 0)
    (hSim0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateIffFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q)))
    (hPQ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q)))
    (hSimLower :
      ((predicateVocabularySimilarityGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode p q
        hObj hpE hqI hqE hpI hSim0).intervalOfConsistent
          (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1) :
    ((predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hPQ0).intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 := by
  let Csim :=
    predicateVocabularySimilarityGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hqE hpI hSim0
  let Cpq :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hPQ0
  have hRule :
      ((Csim.impCut (Base := Base) (Const := Const) Cpq).intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 :=
    predicateVocabularySimilarityGeOneCut_forwardInheritanceRuleImpCut_lower_eq_one
      (Base := Base) (Const := Const)
      enum henum hCons hT0 hEM σ decode p q
      hObj hpE hqI hqE hpI hSim0 hPQ0
  exact
    Csim.lower_eq_one_of_impCut_lower_eq_one_of_lower_eq_one
      (Base := Base) (Const := Const) Cpq enum henum hCons hT0 hEM hRule hSimLower

/-- Consumer form of saturated similarity-to-reverse-inheritance conversion. -/
theorem predicateVocabularyFullInheritanceGeOneCut_reverse_lower_eq_one_of_similarity
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
    (p q : Pred)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hpE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).extent.ncard ≠ 0)
    (hqI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).intent.ncard ≠ 0)
    (hqE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).extent.ncard ≠ 0)
    (hpI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).intent.ncard ≠ 0)
    (hSim0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateIffFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q)))
    (hQP0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode q) (decode p)))
    (hSimLower :
      ((predicateVocabularySimilarityGeOneCut
        (Base := Base) (Const := Const) (T := T) σ decode p q
        hObj hpE hqI hqE hpI hSim0).intervalOfConsistent
          (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1) :
    ((predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode q p
      hObj hqE hpI hQP0).intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 := by
  let Csim :=
    predicateVocabularySimilarityGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hqE hpI hSim0
  let Cqp :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode q p
      hObj hqE hpI hQP0
  have hRule :
      ((Csim.impCut (Base := Base) (Const := Const) Cqp).intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 :=
    predicateVocabularySimilarityGeOneCut_reverseInheritanceRuleImpCut_lower_eq_one
      (Base := Base) (Const := Const)
      enum henum hCons hT0 hEM σ decode p q
      hObj hpE hqI hqE hpI hSim0 hQP0
  exact
    Csim.lower_eq_one_of_impCut_lower_eq_one_of_lower_eq_one
      (Base := Base) (Const := Const) Cqp enum henum hCons hT0 hEM hRule hSimLower

/-- Consumer form of mutual-inheritance-to-similarity conversion.

If the two directed full-inheritance cuts are jointly certain, then the
finite-vocabulary similarity cut is certainly saturated.  This is the cut-level
`2inh2sim` endpoint theorem: below threshold `1` the soft formula remains a
semantic envelope, but the exact saturated rule is completeness-tight. -/
theorem predicateVocabularySimilarityGeOneCut_lower_eq_one_of_mutualInheritance_jointCut
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
    (p q : Pred)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hpE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).extent.ncard ≠ 0)
    (hqI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).intent.ncard ≠ 0)
    (hqE :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning q).extent.ncard ≠ 0)
    (hpI :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        ((predicateVocabularyInterpretation
          (Base := Base) (Const := WithParams Const) M.1 σ decode).meaning p).intent.ncard ≠ 0)
    (hPQ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q)))
    (hQP0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateImpFormula
        (Base := Base) (Const := WithParams Const) σ (decode q) (decode p)))
    (hSim0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateIffFormula
        (Base := Base) (Const := WithParams Const) σ (decode p) (decode q)))
    (hJointLower :
      (((predicateVocabularyFullInheritanceGeOneCut
          (Base := Base) (Const := Const) (T := T) σ decode p q
          hObj hpE hqI hPQ0).andCut
        (Base := Base) (Const := Const)
        (predicateVocabularyFullInheritanceGeOneCut
          (Base := Base) (Const := Const) (T := T) σ decode q p
          hObj hqE hpI hQP0)).intervalOfConsistent
            (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1) :
    ((predicateVocabularySimilarityGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hqE hpI hSim0).intervalOfConsistent
        (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 := by
  let Cpq :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hPQ0
  let Cqp :=
    predicateVocabularyFullInheritanceGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode q p
      hObj hqE hpI hQP0
  let Csim :=
    predicateVocabularySimilarityGeOneCut
      (Base := Base) (Const := Const) (T := T) σ decode p q
      hObj hpE hqI hqE hpI hSim0
  have hRule :
      (((Cpq.andCut (Base := Base) (Const := Const) Cqp).impCut
        (Base := Base) (Const := Const) Csim).intervalOfConsistent
          (Base := Base) (Const := Const) enum henum hCons hT0 hEM).lower = 1 :=
    predicateVocabularySimilarityGeOneCut_of_mutualInheritanceRuleImpCut_lower_eq_one
      (Base := Base) (Const := Const)
      enum henum hCons hT0 hEM σ decode p q
      hObj hpE hqI hqE hpI hPQ0 hQP0 hSim0
  exact
    (Cpq.andCut (Base := Base) (Const := Const) Cqp).lower_eq_one_of_impCut_lower_eq_one_of_lower_eq_one
      (Base := Base) (Const := Const) Csim enum henum hCons hT0 hEM hRule hJointLower

/-- Negative example discipline: a formula cannot represent a threshold event
if it is true in some model where the threshold fails. -/
theorem no_cut_representation_of_true_formula_below_threshold
    {T : ClosedTheorySet (WithParams Const)}
    {score : ExtensionalTheoryModel (Base := Base) (Const := Const) T → ℝ}
    {threshold : ℝ}
    {φ : ClosedFormula (WithParams Const)}
    (M : ExtensionalTheoryModel (Base := Base) (Const := Const) T)
    (hModels : HenkinModel.models M.1 φ)
    (hBelow : ¬ threshold ≤ score M) :
    ¬ ∃ _hφ0 : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) φ,
      ∀ N : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models N.1 φ ↔ threshold ≤ score N := by
  rintro ⟨_, hrepr⟩
  exact hBelow ((hrepr M).mp hModels)

/-- Negative example discipline: a formula cannot represent a threshold event
if it is false in some model where the threshold holds. -/
theorem no_cut_representation_of_false_formula_above_threshold
    {T : ClosedTheorySet (WithParams Const)}
    {score : ExtensionalTheoryModel (Base := Base) (Const := Const) T → ℝ}
    {threshold : ℝ}
    {φ : ClosedFormula (WithParams Const)}
    (M : ExtensionalTheoryModel (Base := Base) (Const := Const) T)
    (hNotModels : ¬ HenkinModel.models M.1 φ)
    (hAbove : threshold ≤ score M) :
    ¬ ∃ _hφ0 : ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) φ,
      ∀ N : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models N.1 φ ↔ threshold ≤ score N := by
  rintro ⟨_, hrepr⟩
  exact hNotModels ((hrepr M).mpr hAbove)


end Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDefinableCuts
