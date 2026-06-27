import Mettapedia.PLN.Bridges.HOL.DefinableCuts.Predicate

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

/-! ## QFM / fuzzy-quantifier cut instances -/

/-- At the strict finite-QFM endpoint, PLN-2008-style fuzzy `ForAll`
acceptance is a definable threshold event represented by the ordinary HOL
universal predicate formula.

This is deliberately the endpoint theorem, not the general fuzzy case:
arbitrary tolerance/capacity scores remain semantic numeric envelopes until
their threshold events are separately represented by closed HOL formulae. -/
noncomputable def predicateFuzzyForAllCrispEndpointGeOneCut
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hNonempty :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Nonempty (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (hPCL1 : params.PCL = 1)
    (hφ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p)) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M =>
      by
      classical
      letI := hObj M
      exact
      if fuzzyForAllHolds params
          (predicateCrispProfile
            (Base := Base) (Const := WithParams Const) M.1 σ p) then
        (1 : ℝ)
      else
        0
    threshold := 1
    formula := predicateForAllFormula
      (Base := Base) (Const := WithParams Const) σ p
    paramFree := hφ0
    represents_ge := by
      intro M
      classical
      letI := hObj M
      letI := hNonempty M
      constructor
      · intro hModels
        have hHolds :
            fuzzyForAllHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) :=
          (predicateFuzzyForAllHolds_iff_models_predicateForAllFormula_of_crisp_endpoint
            (Base := Base) (Const := WithParams Const) M.1 σ params p
            hε0 hPCL1).2 hModels
        change 1 ≤
          (if fuzzyForAllHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) then
            (1 : ℝ)
          else
            0)
        simp [hHolds]
      · intro hGe
        by_cases hHolds :
            fuzzyForAllHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p)
        · exact
            (predicateFuzzyForAllHolds_iff_models_predicateForAllFormula_of_crisp_endpoint
              (Base := Base) (Const := WithParams Const) M.1 σ params p
              hε0 hPCL1).1 hHolds
        · have hNoGe :
              ¬ 1 ≤
                (if fuzzyForAllHolds params
                    (predicateCrispProfile
                      (Base := Base) (Const := WithParams Const) M.1 σ p) then
                  (1 : ℝ)
                else
                  0) := by
            simp [hHolds]
          exact False.elim (hNoGe hGe) }

/-- Positive-threshold version of the strict finite-QFM `ForAll` endpoint cut.

The displayed QFM acceptance score here is Boolean-valued, so the general
Boolean-threshold transport applies.  This does not extend to fractional
near-one/counting scores without a separate threshold formula. -/
noncomputable def predicateFuzzyForAllCrispEndpointPositiveThresholdCut
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hNonempty :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Nonempty (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (hPCL1 : params.PCL = 1)
    (hφ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p))
    (theta : ℝ) (htheta_pos : 0 < theta) (htheta_le : theta ≤ 1) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  (predicateFuzzyForAllCrispEndpointGeOneCut
    (Base := Base) (Const := Const) (T := T)
    σ params p hObj hNonempty hε0 hPCL1 hφ0).booleanPositiveThreshold
    (Base := Base) (Const := Const) theta htheta_pos htheta_le rfl
    (by
      intro M
      classical
      letI := hObj M
      by_cases hHolds :
          fuzzyForAllHolds params
            (predicateCrispProfile
              (Base := Base) (Const := WithParams Const) M.1 σ p)
      · right
        change
          (if fuzzyForAllHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) then
            (1 : ℝ)
          else
            0) = 1
        simp [hHolds]
      · left
        change
          (if fuzzyForAllHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) then
            (1 : ℝ)
          else
            0) = 0
        simp [hHolds])

/-- The positive-threshold finite-QFM `ForAll` acceptance cut has exactly the
same formula-level credal interval as the endpoint-`1` acceptance cut.

The score threshold changes, but the already-proven Boolean transport keeps the
representing HOL formula fixed. -/
theorem predicateFuzzyForAllCrispEndpointPositiveThresholdCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hNonempty :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Nonempty (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (hPCL1 : params.PCL = 1)
    (hφ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p))
    (theta : ℝ) (htheta_pos : 0 < theta) (htheta_le : theta ≤ 1)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM =
      ExtensionalDefinableCut.intervalOfConsistent
        (Base := Base) (Const := Const)
        (predicateFuzzyForAllCrispEndpointGeOneCut
          (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0)
        enum henum hCons hT0 hEM := rfl

/-- Endpoint tightness for positive-threshold finite-QFM `ForAll`
acceptance: lower endpoint `1` is exactly provability of the HOL universal
predicate formula. -/
theorem predicateFuzzyForAllCrispEndpointPositiveThresholdCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hNonempty :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Nonempty (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (hPCL1 : params.PCL = 1)
    (hφ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p))
    (theta : ℝ) (htheta_pos : 0 < theta) (htheta_le : theta ≤ 1)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for positive-threshold finite-QFM `ForAll`
acceptance: upper endpoint `0` is exactly provability of the negated HOL
universal predicate formula. -/
theorem predicateFuzzyForAllCrispEndpointPositiveThresholdCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hNonempty :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Nonempty (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (hPCL1 : params.PCL = 1)
    (hφ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p))
    (theta : ℝ) (htheta_pos : 0 < theta) (htheta_le : theta ≤ 1)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) σ p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for positive-threshold finite-QFM `ForAll`
acceptance: the interval collapses exactly when the theory decides the HOL
universal predicate formula. -/
theorem predicateFuzzyForAllCrispEndpointPositiveThresholdCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hNonempty :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Nonempty (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (hPCL1 : params.PCL = 1)
    (hφ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p))
    (theta : ℝ) (htheta_pos : 0 < theta) (htheta_le : theta ≤ 1)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) σ p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateFuzzyForAllCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM

/-- Nonpositive-threshold boundary for the strict finite-QFM `ForAll`
acceptance score.

Since the acceptance score is Boolean-valued, thresholds `τ ≤ 0` are always
satisfied.  The representing formula is therefore a tautology over the HOL
universal-predicate formula. -/
noncomputable def predicateFuzzyForAllCrispEndpointNonpositiveThresholdTautologyCut
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hNonempty :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Nonempty (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (hPCL1 : params.PCL = 1)
    (hφ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p))
    (theta : ℝ) (htheta_nonpos : theta ≤ 0) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  (predicateFuzzyForAllCrispEndpointGeOneCut
    (Base := Base) (Const := Const) (T := T)
    σ params p hObj hNonempty hε0 hPCL1 hφ0).booleanNonpositiveThresholdTautology
    (Base := Base) (Const := Const) theta htheta_nonpos
    (by
      intro M
      classical
      letI := hObj M
      by_cases hHolds :
          fuzzyForAllHolds params
            (predicateCrispProfile
              (Base := Base) (Const := WithParams Const) M.1 σ p)
      · right
        change
          (if fuzzyForAllHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) then
            (1 : ℝ)
          else
            0) = 1
        simp [hHolds]
      · left
        change
          (if fuzzyForAllHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) then
            (1 : ℝ)
          else
            0) = 0
        simp [hHolds])

/-- At the strict finite-QFM endpoint, maximal existential-style near-one
score is also represented by the HOL universal predicate formula.

This is an intentionally clarifying theorem about the PLN-2008 QFM layer:
`fuzzyExistsScore` is the near-one mass, so threshold `1` says that every
admissible object is near-one. In the crisp endpoint this is HOL `ForAll`, not
ordinary logical `Exists`. -/
noncomputable def predicateFuzzyExistsScoreGeOneCut
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hNonempty :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Nonempty (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (hPCL1 : params.PCL = 1)
    (hφ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p)) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M =>
      letI := hObj M
      fuzzyExistsScore params
        (predicateCrispProfile
          (Base := Base) (Const := WithParams Const) M.1 σ p)
    threshold := 1
    formula := predicateForAllFormula
      (Base := Base) (Const := WithParams Const) σ p
    paramFree := hφ0
    represents_ge := by
      intro M
      letI := hObj M
      letI := hNonempty M
      constructor
      · intro hModels
        have hHolds :
            fuzzyForAllHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) :=
          (predicateFuzzyForAllHolds_iff_models_predicateForAllFormula_of_crisp_endpoint
            (Base := Base) (Const := WithParams Const) M.1 σ params p
            hε0 hPCL1).2 hModels
        unfold fuzzyForAllHolds at hHolds
        change 1 ≤
          fuzzyExistsScore params
            (predicateCrispProfile
              (Base := Base) (Const := WithParams Const) M.1 σ p)
        simpa [fuzzyExistsScore, hPCL1] using hHolds
      · intro hGe
        have hHolds :
            fuzzyForAllHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) := by
          unfold fuzzyForAllHolds
          simpa [fuzzyExistsScore, hPCL1] using hGe
        exact
          (predicateFuzzyForAllHolds_iff_models_predicateForAllFormula_of_crisp_endpoint
            (Base := Base) (Const := WithParams Const) M.1 σ params p
            hε0 hPCL1).1 hHolds }

/-- At the strict finite-QFM endpoint, PLN-2008-style fuzzy `ThereExists`
acceptance at threshold `1` is also represented by the HOL universal predicate
formula.

This is another clarifying cut certificate: the maximal-threshold QFM
existential-style check says that no admissible object is near-zero. For a crisp
profile at `epsilon = 0`, that is exactly universal HOL truth, not ordinary
logical existential truth. -/
noncomputable def predicateFuzzyThereExistsCrispEndpointGeOneCut
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hNonempty :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Nonempty (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (hPCL1 : params.PCL = 1)
    (hφ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p)) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M =>
      by
      classical
      letI := hObj M
      exact
      if fuzzyThereExistsHolds params
          (predicateCrispProfile
            (Base := Base) (Const := WithParams Const) M.1 σ p) then
        (1 : ℝ)
      else
        0
    threshold := 1
    formula := predicateForAllFormula
      (Base := Base) (Const := WithParams Const) σ p
    paramFree := hφ0
    represents_ge := by
      intro M
      classical
      letI := hObj M
      letI := hNonempty M
      constructor
      · intro hModels
        have hHolds :
            fuzzyThereExistsHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) :=
          (predicateFuzzyThereExistsHolds_iff_models_predicateForAllFormula_of_crisp_endpoint
            (Base := Base) (Const := WithParams Const) M.1 σ params p
            hε0 hPCL1).2 hModels
        change 1 ≤
          (if fuzzyThereExistsHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) then
            (1 : ℝ)
          else
            0)
        simp [hHolds]
      · intro hGe
        by_cases hHolds :
            fuzzyThereExistsHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p)
        · exact
            (predicateFuzzyThereExistsHolds_iff_models_predicateForAllFormula_of_crisp_endpoint
              (Base := Base) (Const := WithParams Const) M.1 σ params p
              hε0 hPCL1).1 hHolds
        · have hNoGe :
              ¬ 1 ≤
                (if fuzzyThereExistsHolds params
                    (predicateCrispProfile
                      (Base := Base) (Const := WithParams Const) M.1 σ p) then
                  (1 : ℝ)
                else
                  0) := by
            simp [hHolds]
          exact False.elim (hNoGe hGe) }

/-- Positive-threshold version of the strict finite-QFM `ThereExists`
acceptance cut.

As with the `ForAll` acceptance cut, this applies only to the Boolean endpoint
acceptance score.  It does not claim that arbitrary sub-endpoint QFM mass
thresholds are already HOL-definable. -/
noncomputable def predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hNonempty :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Nonempty (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (hPCL1 : params.PCL = 1)
    (hφ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p))
    (theta : ℝ) (htheta_pos : 0 < theta) (htheta_le : theta ≤ 1) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  (predicateFuzzyThereExistsCrispEndpointGeOneCut
    (Base := Base) (Const := Const) (T := T)
    σ params p hObj hNonempty hε0 hPCL1 hφ0).booleanPositiveThreshold
    (Base := Base) (Const := Const) theta htheta_pos htheta_le rfl
    (by
      intro M
      classical
      letI := hObj M
      by_cases hHolds :
          fuzzyThereExistsHolds params
            (predicateCrispProfile
              (Base := Base) (Const := WithParams Const) M.1 σ p)
      · right
        change
          (if fuzzyThereExistsHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) then
            (1 : ℝ)
          else
            0) = 1
        simp [hHolds]
      · left
        change
          (if fuzzyThereExistsHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) then
            (1 : ℝ)
          else
            0) = 0
        simp [hHolds])

/-- The positive-threshold finite-QFM `ThereExists` acceptance cut has exactly
the same formula-level credal interval as the endpoint-`1` acceptance cut.

At this strict endpoint `ThereExists` is still the PLN book's no-near-zero
acceptance predicate over a crisp profile, so the shared representing formula
is the HOL universal predicate formula. -/
theorem predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hNonempty :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Nonempty (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (hPCL1 : params.PCL = 1)
    (hφ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p))
    (theta : ℝ) (htheta_pos : 0 < theta) (htheta_le : theta ≤ 1)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM =
      ExtensionalDefinableCut.intervalOfConsistent
        (Base := Base) (Const := Const)
        (predicateFuzzyThereExistsCrispEndpointGeOneCut
          (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0)
        enum henum hCons hT0 hEM := rfl

/-- Endpoint tightness for positive-threshold finite-QFM `ThereExists`
acceptance: lower endpoint `1` is exactly provability of the HOL universal
predicate formula representing the endpoint acceptance event. -/
theorem predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hNonempty :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Nonempty (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (hPCL1 : params.PCL = 1)
    (hφ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p))
    (theta : ℝ) (htheta_pos : 0 < theta) (htheta_le : theta ≤ 1)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for positive-threshold finite-QFM `ThereExists`
acceptance: upper endpoint `0` is exactly provability of the negated HOL
universal predicate formula representing the endpoint acceptance event. -/
theorem predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hNonempty :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Nonempty (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (hPCL1 : params.PCL = 1)
    (hφ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p))
    (theta : ℝ) (htheta_pos : 0 < theta) (htheta_le : theta ≤ 1)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) σ p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for positive-threshold finite-QFM `ThereExists`
acceptance: the interval collapses exactly when the theory decides the HOL
universal predicate formula representing the endpoint acceptance event. -/
theorem predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hNonempty :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Nonempty (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (hPCL1 : params.PCL = 1)
    (hφ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p))
    (theta : ℝ) (htheta_pos : 0 < theta) (htheta_le : theta ≤ 1)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) σ p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateFuzzyThereExistsCrispEndpointPositiveThresholdCut
        (T := T) σ params p hObj hNonempty hε0 hPCL1 hφ0
        theta htheta_pos htheta_le)
      enum henum hCons hT0 hEM

/-- Nonpositive-threshold boundary for the strict finite-QFM `ThereExists`
acceptance score. -/
noncomputable def predicateFuzzyThereExistsCrispEndpointNonpositiveThresholdTautologyCut
    {T : ClosedTheorySet (WithParams Const)}
    (σ : Ty Base)
    (params : FuzzyQuantifierParams)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) σ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 σ))
    (hNonempty :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Nonempty (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 σ))
    (hε0 : params.ε = 0)
    (hPCL1 : params.PCL = 1)
    (hφ0 : ∀ (τ : Ty Base) (k : Nat), NoConstOccurrence (param τ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) σ p))
    (theta : ℝ) (htheta_nonpos : theta ≤ 0) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  (predicateFuzzyThereExistsCrispEndpointGeOneCut
    (Base := Base) (Const := Const) (T := T)
    σ params p hObj hNonempty hε0 hPCL1 hφ0).booleanNonpositiveThresholdTautology
    (Base := Base) (Const := Const) theta htheta_nonpos
    (by
      intro M
      classical
      letI := hObj M
      by_cases hHolds :
          fuzzyThereExistsHolds params
            (predicateCrispProfile
              (Base := Base) (Const := WithParams Const) M.1 σ p)
      · right
        change
          (if fuzzyThereExistsHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) then
            (1 : ℝ)
          else
            0) = 1
        simp [hHolds]
      · left
        change
          (if fuzzyThereExistsHolds params
              (predicateCrispProfile
                (Base := Base) (Const := WithParams Const) M.1 σ p) then
            (1 : ℝ)
          else
            0) = 0
        simp [hHolds])


end Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDefinableCuts
