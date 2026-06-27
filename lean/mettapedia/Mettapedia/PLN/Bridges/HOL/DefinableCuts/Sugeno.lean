import Mettapedia.PLN.Bridges.HOL.DefinableCuts.Bands

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

/-! ## Calibrated capacity / Sugeno cut instances -/

/-- A capacity-family calibration certificate for a HOL predicate.

The certificate says that, for every extensional theory model, the chosen
capacity on the predicate-object carrier makes Sugeno score `1` exactly the
closed HOL universal-predicate event. This is the intended seam for arbitrary
capacities: they may enter the proof-theoretic endpoint layer only after
supplying this representation proof. -/
structure PredicateSugenoOneCalibration
    (T : ClosedTheorySet (WithParams Const))
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau) where
  fintype :
    ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau)
  measurable :
    ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      MeasurableSpace (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau)
  capacity :
    ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      FuzzyCapacity (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau)
  represents_forall :
    ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      letI := fintype M
      letI := measurable M
      ((sugenoScoreInf (capacity M)
        (predicateCrispProfileInf
          (Base := Base) (Const := WithParams Const) M.1 tau p) :
        unitInterval) : ℝ) = 1 ↔
        HenkinModel.models M.1
          (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p)

/-- A calibrated capacity family yields a definable Sugeno endpoint cut.

This is the generic, non-laundering version of the counting-capacity cut below:
arbitrary capacities are allowed, but only through a calibration certificate
that identifies the endpoint event with a closed HOL formula. -/
noncomputable def predicateSugenoCalibratedCrispEndpointGeOneCut
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (C : PredicateSugenoOneCalibration
      (Base := Base) (Const := Const) T tau p)
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p)) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M =>
      letI := C.fintype M
      letI := C.measurable M
      ((sugenoScoreInf (C.capacity M)
        (predicateCrispProfileInf
          (Base := Base) (Const := WithParams Const) M.1 tau p) :
        unitInterval) : ℝ)
    threshold := 1
    formula := predicateForAllFormula
      (Base := Base) (Const := WithParams Const) tau p
    paramFree := hφ0
    represents_ge := by
      intro M
      letI := C.fintype M
      letI := C.measurable M
      constructor
      · intro hModels
        have hEq :
            ((sugenoScoreInf (C.capacity M)
              (predicateCrispProfileInf
                (Base := Base) (Const := WithParams Const) M.1 tau p) :
              unitInterval) : ℝ) = 1 :=
          (C.represents_forall M).2 hModels
        change 1 ≤
          ((sugenoScoreInf (C.capacity M)
            (predicateCrispProfileInf
              (Base := Base) (Const := WithParams Const) M.1 tau p) :
            unitInterval) : ℝ)
        exact le_of_eq hEq.symm
      · intro hGe
        have hLe :
            ((sugenoScoreInf (C.capacity M)
              (predicateCrispProfileInf
                (Base := Base) (Const := WithParams Const) M.1 tau p) :
              unitInterval) : ℝ) ≤ 1 :=
          unitInterval.le_one _
        have hEq :
            ((sugenoScoreInf (C.capacity M)
              (predicateCrispProfileInf
                (Base := Base) (Const := WithParams Const) M.1 tau p) :
              unitInterval) : ℝ) = 1 := by
          apply le_antisymm hLe
          simpa using hGe
        exact (C.represents_forall M).1 hEq }

/-- The calibrated Sugeno endpoint cut reads out through the existing HOL
formula interval for the representing universal-predicate formula. -/
theorem predicateSugenoCalibratedCrispEndpointGeOneCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (C : PredicateSugenoOneCalibration
      (Base := Base) (Const := Const) T tau p)
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCalibratedCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p C hφ0)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateForAllFormula
            (Base := Base) (Const := WithParams Const) tau p) := rfl

/-- Endpoint tightness for calibrated Sugeno endpoint cuts: lower endpoint `1`
is exactly provability of the HOL universal predicate formula. -/
theorem predicateSugenoCalibratedCrispEndpointGeOneCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (C : PredicateSugenoOneCalibration
      (Base := Base) (Const := Const) T tau p)
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCalibratedCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p C hφ0)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateSugenoCalibratedCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p C hφ0)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for calibrated Sugeno endpoint cuts: upper endpoint `0`
is exactly provability of the negated HOL universal predicate formula. -/
theorem predicateSugenoCalibratedCrispEndpointGeOneCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (C : PredicateSugenoOneCalibration
      (Base := Base) (Const := Const) T tau p)
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCalibratedCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p C hφ0)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateSugenoCalibratedCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p C hφ0)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for calibrated Sugeno endpoint cuts: the interval
collapses exactly when the theory decides the HOL universal predicate formula. -/
theorem predicateSugenoCalibratedCrispEndpointGeOneCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (C : PredicateSugenoOneCalibration
      (Base := Base) (Const := Const) T tau p)
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCalibratedCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p C hφ0)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateSugenoCalibratedCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p C hφ0)
      enum henum hCons hT0 hEM

/-- Normalized counting capacity supplies the first concrete Sugeno endpoint
calibration. -/
noncomputable def predicateSugenoCountingOneCalibration
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hNonempty :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Nonempty (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau)) :
    PredicateSugenoOneCalibration
      (Base := Base) (Const := Const) T tau p where
  fintype := hObj
  measurable := hMeasurable
  capacity := fun M => by
    letI := hObj M
    letI := hMeasurable M
    exact FuzzyCapacity.countingCapacity
      (U := (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
  represents_forall := by
    intro M
    letI := hObj M
    letI := hNonempty M
    letI := hMeasurable M
    exact
      predicateSugenoScoreInf_counting_eq_one_iff_models_predicateForAllFormula
        (Base := Base) (Const := WithParams Const) M.1 tau p

/-- Counting-capacity Sugeno aggregation of a HOL-induced crisp profile is a
definable endpoint cut represented by the HOL universal predicate formula.

This is the first arbitrary-domain capacity/Sugeno consumer of the definable-cut
layer. It is intentionally restricted to normalized counting capacity: arbitrary
capacities do not make `capacity(extension) = 1` equivalent to full extension
without an additional calibration theorem. -/
noncomputable def predicateSugenoCountingCrispEndpointGeOneCut
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hNonempty :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Nonempty (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p)) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M =>
      letI := hObj M
      letI := hMeasurable M
      ((sugenoScoreInf
        (FuzzyCapacity.countingCapacity
          (U := (PredicateObject
            (Base := Base) (Const := WithParams Const) M.1 tau)))
        (predicateCrispProfileInf
          (Base := Base) (Const := WithParams Const) M.1 tau p) :
        unitInterval) : ℝ)
    threshold := 1
    formula := predicateForAllFormula
      (Base := Base) (Const := WithParams Const) tau p
    paramFree := hφ0
    represents_ge := by
      intro M
      letI := hObj M
      letI := hNonempty M
      letI := hMeasurable M
      constructor
      · intro hModels
        have hEq :
            ((sugenoScoreInf
              (FuzzyCapacity.countingCapacity
                (U := (PredicateObject
                  (Base := Base) (Const := WithParams Const) M.1 tau)))
              (predicateCrispProfileInf
                (Base := Base) (Const := WithParams Const) M.1 tau p) :
              unitInterval) : ℝ) = 1 :=
          (predicateSugenoScoreInf_counting_eq_one_iff_models_predicateForAllFormula
            (Base := Base) (Const := WithParams Const) M.1 tau p).2 hModels
        change 1 ≤
          ((sugenoScoreInf
            (FuzzyCapacity.countingCapacity
              (U := (PredicateObject
                (Base := Base) (Const := WithParams Const) M.1 tau)))
            (predicateCrispProfileInf
              (Base := Base) (Const := WithParams Const) M.1 tau p) :
            unitInterval) : ℝ)
        exact le_of_eq hEq.symm
      · intro hGe
        have hLe :
            ((sugenoScoreInf
              (FuzzyCapacity.countingCapacity
                (U := (PredicateObject
                  (Base := Base) (Const := WithParams Const) M.1 tau)))
              (predicateCrispProfileInf
                (Base := Base) (Const := WithParams Const) M.1 tau p) :
              unitInterval) : ℝ) ≤ 1 :=
          unitInterval.le_one _
        have hEq :
            ((sugenoScoreInf
              (FuzzyCapacity.countingCapacity
                (U := (PredicateObject
                  (Base := Base) (Const := WithParams Const) M.1 tau)))
              (predicateCrispProfileInf
                (Base := Base) (Const := WithParams Const) M.1 tau p) :
              unitInterval) : ℝ) = 1 := by
          apply le_antisymm hLe
          simpa using hGe
        exact
          (predicateSugenoScoreInf_counting_eq_one_iff_models_predicateForAllFormula
            (Base := Base) (Const := WithParams Const) M.1 tau p).1 hEq }

/-- The counting-capacity Sugeno endpoint cut reads out through the existing
HOL formula interval for the representing universal-predicate formula. -/
theorem predicateSugenoCountingCrispEndpointGeOneCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hNonempty :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Nonempty (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p
        hObj hNonempty hMeasurable hφ0)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateForAllFormula
            (Base := Base) (Const := WithParams Const) tau p) := rfl

/-- Endpoint tightness for counting-capacity Sugeno endpoint cuts: lower
endpoint `1` is exactly provability of the HOL universal predicate formula. -/
theorem predicateSugenoCountingCrispEndpointGeOneCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hNonempty :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Nonempty (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p
        hObj hNonempty hMeasurable hφ0)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p
        hObj hNonempty hMeasurable hφ0)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for counting-capacity Sugeno endpoint cuts: upper
endpoint `0` is exactly provability of the negated HOL universal predicate
formula. -/
theorem predicateSugenoCountingCrispEndpointGeOneCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hNonempty :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Nonempty (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p
        hObj hNonempty hMeasurable hφ0)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p
        hObj hNonempty hMeasurable hφ0)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for counting-capacity Sugeno endpoint cuts: the
interval collapses exactly when the theory decides the HOL universal predicate
formula. -/
theorem predicateSugenoCountingCrispEndpointGeOneCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hNonempty :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Nonempty (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p
        hObj hNonempty hMeasurable hφ0)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCrispEndpointGeOneCut
        (Base := Base) (Const := Const) (T := T) tau p
        hObj hNonempty hMeasurable hφ0)
      enum henum hCons hT0 hEM

/-- Exact-denominator normalized-counting Sugeno cut for HOL-induced crisp
profiles.

For crisp HOL predicates, Sugeno aggregation against normalized counting
capacity is exactly the counting capacity of the predicate extension.  Thus
the same exact-denominator cardinality certificate used for counting capacity
also certifies the fractional Sugeno event `k / N ≤ Sugeno(counting, p)`.
This is still a counting-capacity result; arbitrary capacities require their
own threshold representation theorem. -/
noncomputable def predicateSugenoCountingCardinalityThresholdCut
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M =>
      letI := hObj M
      letI := hMeasurable M
      ((sugenoScoreInf
        (FuzzyCapacity.countingCapacity
          (U := PredicateObject
            (Base := Base) (Const := WithParams Const) M.1 tau))
        (predicateCrispProfileInf
          (Base := Base) (Const := WithParams Const) M.1 tau p) :
        unitInterval) : ℝ)
    threshold := (k : ℝ) / (N : ℝ)
    formula := χ
    paramFree := hχ0
    represents_ge := by
      intro M
      classical
      letI := hObj M
      letI := hMeasurable M
      have hScoreEq :
          ((sugenoScoreInf
            (FuzzyCapacity.countingCapacity
              (U := PredicateObject
                (Base := Base) (Const := WithParams Const) M.1 tau))
            (predicateCrispProfileInf
              (Base := Base) (Const := WithParams Const) M.1 tau p) :
            unitInterval) : ℝ) =
          (((FuzzyCapacity.countingCapacity
            (U := PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 tau))
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p) :
            unitInterval) : ℝ) := by
        rw [predicateSugenoScoreInf_eq_capacity_extension
          (Base := Base) (Const := WithParams Const) M.1 tau
          (FuzzyCapacity.countingCapacity
            (U := PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 tau)) p]
      constructor
      · intro hModels
        have hCount : k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard :=
          (hχRep M).1 hModels
        have hCap :
            (k : ℝ) / (N : ℝ) ≤
              (((FuzzyCapacity.countingCapacity
                (U := PredicateObject
                  (Base := Base) (Const := WithParams Const) M.1 tau))
                (predicateExtension
                  (Base := Base) (Const := WithParams Const) M.1 tau p) :
                unitInterval) : ℝ) :=
          (FuzzyCapacity.countingCapacity_ge_nat_div_iff_card_ge_of_card_eq
            (U := PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 tau)
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p)
            k N hNpos (hCardEq M)).2 hCount
        simpa [hScoreEq] using hCap
      · intro hGe
        apply (hχRep M).2
        have hCap :
            (k : ℝ) / (N : ℝ) ≤
              (((FuzzyCapacity.countingCapacity
                (U := PredicateObject
                  (Base := Base) (Const := WithParams Const) M.1 tau))
                (predicateExtension
                  (Base := Base) (Const := WithParams Const) M.1 tau p) :
                unitInterval) : ℝ) := by
          simpa [hScoreEq] using hGe
        exact
          (FuzzyCapacity.countingCapacity_ge_nat_div_iff_card_ge_of_card_eq
            (U := PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 tau)
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p)
            k N hNpos (hCardEq M)).1 hCap }

/-- The exact-denominator normalized-counting Sugeno cut reads out through the
existing HOL interval for the supplied cardinality-threshold formula. -/
theorem predicateSugenoCountingCardinalityThresholdCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM χ := rfl

/-- Endpoint tightness for the generic exact-denominator normalized-counting
Sugeno cardinality-threshold cut: lower endpoint `1` is exactly provability of
the supplied HOL cardinality formula. -/
theorem predicateSugenoCountingCardinalityThresholdCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T χ := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the generic exact-denominator normalized-counting
Sugeno cardinality-threshold cut: upper endpoint `0` is exactly provability of
the negated supplied HOL cardinality formula. -/
theorem predicateSugenoCountingCardinalityThresholdCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the generic exact-denominator
normalized-counting Sugeno cardinality-threshold cut: lower endpoint `0` is
exactly non-provability of the supplied HOL cardinality formula. -/
theorem predicateSugenoCountingCardinalityThresholdCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T χ := by
  exact
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the generic exact-denominator
normalized-counting Sugeno cardinality-threshold cut: upper endpoint `1` is
exactly non-provability of the negated supplied HOL cardinality formula. -/
theorem predicateSugenoCountingCardinalityThresholdCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ) := by
  exact
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the generic exact-denominator normalized-counting
Sugeno cardinality-threshold cut: the interval collapses exactly when the
theory decides the supplied HOL cardinality formula. -/
theorem predicateSugenoCountingCardinalityThresholdCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χ : ClosedFormula (WithParams Const))
    (hχ0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) χ)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χ ↔
          k ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T χ ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateSugenoCountingCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Concrete exact-denominator normalized-counting Sugeno cut for the HOL
existence formula `∃ x, p x`.

For HOL-induced crisp profiles, Sugeno/counting reduces to counting capacity;
this packages that reduction with the ordinary HOL existence formula at
threshold `1 / N`. This works at every HOL type because it does not rely on
object equality. -/
noncomputable def predicateSugenoCountingExistsExactThresholdCut
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  predicateSugenoCountingCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)
    tau p
    (predicateExistsFormula (Base := Base) (Const := WithParams Const) tau p)
    (fun ρ i =>
      noConstOccurrence_predicateExistsFormula
        (Base := Base) (Const := WithParams Const) tau p (hp0 ρ i))
    hObj hMeasurable 1 N hNpos hCardEq
    (fun M => by
      letI := hObj M
      exact
        models_predicateExistsFormula_iff_one_le_ncard_extension
          (Base := Base) (Const := WithParams Const) M.1 tau p)

/-- The concrete HOL-existence normalized-counting Sugeno cut reads out
through the existing HOL interval for `∃ x, p x`. -/
theorem predicateSugenoCountingExistsExactThresholdCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateExistsFormula
            (Base := Base) (Const := WithParams Const) tau p) := rfl

/-- Endpoint tightness for the HOL-existence normalized-counting Sugeno cut:
lower endpoint `1` is exactly provability of `∃ x, p x`. -/
theorem predicateSugenoCountingExistsExactThresholdCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateSugenoCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the HOL-existence normalized-counting Sugeno cut:
upper endpoint `0` is exactly provability of `¬ ∃ x, p x`. -/
theorem predicateSugenoCountingExistsExactThresholdCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateSugenoCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the HOL-existence normalized-counting
Sugeno cut: lower endpoint `0` is exactly non-provability of `∃ x, p x`. -/
theorem predicateSugenoCountingExistsExactThresholdCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p) := by
  simpa [predicateSugenoCountingExistsExactThresholdCut,
    predicateSugenoCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateSugenoCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the HOL-existence normalized-counting
Sugeno cut: upper endpoint `1` is exactly non-provability of `¬ ∃ x, p x`. -/
theorem predicateSugenoCountingExistsExactThresholdCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  simpa [predicateSugenoCountingExistsExactThresholdCut,
    predicateSugenoCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateSugenoCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the HOL-existence normalized-counting Sugeno cut:
the interval collapses exactly when the theory decides `∃ x, p x`. -/
theorem predicateSugenoCountingExistsExactThresholdCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateSugenoCountingExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Concrete exact-denominator normalized-counting Sugeno cut for the HOL
universal formula `∀ x, p x`.

For HOL-induced crisp profiles, Sugeno/counting reduces to counting capacity.
At the exact denominator threshold `N / N`, the numeric event is represented by
ordinary HOL universal truth under the explicit exact-carrier guards. -/
noncomputable def predicateSugenoCountingUniversalExactThresholdCut
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  predicateSugenoCountingCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)
    tau p
    (predicateForAllFormula (Base := Base) (Const := WithParams Const) tau p)
    (fun ρ i =>
      noConstOccurrence_predicateForAllFormula
        (Base := Base) (Const := WithParams Const) tau p (hp0 ρ i))
    hObj hMeasurable N N hNpos hCardEq
    (fun M => by
      letI := hObj M
      exact
        models_predicateForAllFormula_iff_card_le_ncard_extension_of_card_eq
          (Base := Base) (Const := WithParams Const) M.1 tau p N (hCardEq M))

/-- The concrete HOL-universal normalized-counting Sugeno cut reads out
through the existing HOL interval for `∀ x, p x`. -/
theorem predicateSugenoCountingUniversalExactThresholdCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateForAllFormula
            (Base := Base) (Const := WithParams Const) tau p) := rfl

/-- Endpoint tightness for the HOL-universal normalized-counting Sugeno cut:
lower endpoint `1` is exactly provability of `∀ x, p x`. -/
theorem predicateSugenoCountingUniversalExactThresholdCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) tau p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateSugenoCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the HOL-universal normalized-counting Sugeno cut:
upper endpoint `0` is exactly provability of `¬ ∀ x, p x`. -/
theorem predicateSugenoCountingUniversalExactThresholdCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateSugenoCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the HOL-universal normalized-counting
Sugeno cut: lower endpoint `0` is exactly non-provability of `∀ x, p x`. -/
theorem predicateSugenoCountingUniversalExactThresholdCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) tau p) := by
  simpa [predicateSugenoCountingUniversalExactThresholdCut,
    predicateSugenoCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateSugenoCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the HOL-universal normalized-counting
Sugeno cut: upper endpoint `1` is exactly non-provability of `¬ ∀ x, p x`. -/
theorem predicateSugenoCountingUniversalExactThresholdCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  simpa [predicateSugenoCountingUniversalExactThresholdCut,
    predicateSugenoCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateSugenoCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the HOL-universal normalized-counting Sugeno cut:
the interval collapses exactly when the theory decides `∀ x, p x`. -/
theorem predicateSugenoCountingUniversalExactThresholdCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) tau p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateForAllFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateSugenoCountingUniversalExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Concrete exact-denominator normalized-counting Sugeno cut for the
base-type HOL formula "at least two distinct witnesses satisfy `p`".

For HOL-induced crisp profiles, Sugeno/counting reduces to counting capacity;
this packages that reduction with the constructed base-type cardinality
formula at threshold `2 / N`. -/
noncomputable def predicateSugenoCountingAtLeastTwoBaseCut
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  predicateSugenoCountingCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)
    (.base b) p
    (predicateAtLeastTwoBaseFormula (Base := Base) (Const := WithParams Const) b p)
    (fun ρ i =>
      noConstOccurrence_predicateAtLeastTwoBaseFormula
        (Base := Base) (Const := WithParams Const) b p (hp0 ρ i))
    hObj hMeasurable 2 N hNpos hCardEq
    (fun M => by
      letI := hObj M
      exact
        models_predicateAtLeastTwoBaseFormula_iff_two_le_ncard_extension
          (Base := Base) (Const := WithParams Const) M.1 b p)

/-- The concrete base-type "at least two" normalized-counting Sugeno cut
reads out through the existing HOL interval for its representing formula. -/
theorem predicateSugenoCountingAtLeastTwoBaseCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateAtLeastTwoBaseFormula
            (Base := Base) (Const := WithParams Const) b p) := rfl

/-- Endpoint tightness for the concrete base-type "at least two"
normalized-counting Sugeno cut: lower endpoint `1` is exactly provability of
the constructed HOL cardinality formula. -/
theorem predicateSugenoCountingAtLeastTwoBaseCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the concrete base-type "at least two"
normalized-counting Sugeno cut: upper endpoint `0` is exactly provability of
the negated constructed HOL cardinality formula. -/
theorem predicateSugenoCountingAtLeastTwoBaseCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the concrete base-type "at least two"
normalized-counting Sugeno cut: lower endpoint `0` is exactly non-provability
of the constructed HOL cardinality formula. -/
theorem predicateSugenoCountingAtLeastTwoBaseCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p) := by
  simpa [predicateSugenoCountingAtLeastTwoBaseCut,
    predicateSugenoCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the concrete base-type "at least two"
normalized-counting Sugeno cut: upper endpoint `1` is exactly non-provability
of the negated constructed HOL cardinality formula. -/
theorem predicateSugenoCountingAtLeastTwoBaseCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  simpa [predicateSugenoCountingAtLeastTwoBaseCut,
    predicateSugenoCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the concrete base-type "at least two"
normalized-counting Sugeno cut: the interval collapses exactly when the theory
decides the constructed HOL cardinality formula. -/
theorem predicateSugenoCountingAtLeastTwoBaseCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Concrete exact-denominator normalized-counting Sugeno cut for the
base-type HOL formula "at least three distinct witnesses satisfy `p`".

For HOL-induced crisp profiles, Sugeno/counting reduces to counting capacity;
this packages that reduction with the constructed base-type cardinality
formula at threshold `3 / N`. -/
noncomputable def predicateSugenoCountingAtLeastThreeBaseCut
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  predicateSugenoCountingCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)
    (.base b) p
    (predicateAtLeastThreeBaseFormula (Base := Base) (Const := WithParams Const) b p)
    (fun ρ i =>
      noConstOccurrence_predicateAtLeastThreeBaseFormula
        (Base := Base) (Const := WithParams Const) b p (hp0 ρ i))
    hObj hMeasurable 3 N hNpos hCardEq
    (fun M => by
      letI := hObj M
      exact
        models_predicateAtLeastThreeBaseFormula_iff_three_le_ncard_extension
          (Base := Base) (Const := WithParams Const) M.1 b p)

/-- The concrete base-type "at least three" normalized-counting Sugeno cut
reads out through the existing HOL interval for its representing formula. -/
theorem predicateSugenoCountingAtLeastThreeBaseCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateAtLeastThreeBaseFormula
            (Base := Base) (Const := WithParams Const) b p) := rfl

/-- Endpoint tightness for the concrete base-type "at least three"
normalized-counting Sugeno cut: lower endpoint `1` is exactly provability of
the constructed HOL cardinality formula. -/
theorem predicateSugenoCountingAtLeastThreeBaseCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the concrete base-type "at least three"
normalized-counting Sugeno cut: upper endpoint `0` is exactly provability of
the negated constructed HOL cardinality formula. -/
theorem predicateSugenoCountingAtLeastThreeBaseCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the concrete base-type "at least three"
normalized-counting Sugeno cut: lower endpoint `0` is exactly non-provability
of the constructed HOL cardinality formula. -/
theorem predicateSugenoCountingAtLeastThreeBaseCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p) := by
  simpa [predicateSugenoCountingAtLeastThreeBaseCut,
    predicateSugenoCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the concrete base-type "at least three"
normalized-counting Sugeno cut: upper endpoint `1` is exactly non-provability
of the negated constructed HOL cardinality formula. -/
theorem predicateSugenoCountingAtLeastThreeBaseCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  simpa [predicateSugenoCountingAtLeastThreeBaseCut,
    predicateSugenoCountingCardinalityThresholdCut] using
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the concrete base-type "at least three"
normalized-counting Sugeno cut: the interval collapses exactly when the theory
decides the constructed HOL cardinality formula. -/
theorem predicateSugenoCountingAtLeastThreeBaseCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (b : Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) (.base b))
    (hp0 : ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) p)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)))
    (N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ bdy : Body Const, ∃ n, enum n = bdy)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateSugenoCountingAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM


end Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDefinableCuts
