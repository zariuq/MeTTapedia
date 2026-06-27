import Mettapedia.PLN.Bridges.HOL.DefinableCuts.Counting

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

/-! ### Concrete constructed finite-frequency bands -/

/-- Concrete all-HOL finite-frequency band cut for normalized counting
capacity.

Under an exact carrier-size guard `N`, this cut certifies the proper
nontrivial band `1 / N ≤ countingCapacity(ext p)` and
`1 / N ≤ 1 - countingCapacity(ext p)`: there is at least one witness for `p`,
and at least one admissible object does not satisfy `p`.  Unlike the
base-type two/three-witness cuts, this construction works at every HOL type
because neither side compares two objects by equality. -/
noncomputable def predicateCountingCapacityExistsAndExistsNotBandCut
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
  predicateCountingCapacityCardinalityBandCut
    (Base := Base) (Const := Const) (T := T)
    tau p
    (predicateExistsFormula
      (Base := Base) (Const := WithParams Const) tau p)
    (predicateExistsNotFormula
      (Base := Base) (Const := WithParams Const) tau p)
    (fun ρ i =>
      noConstOccurrence_predicateExistsFormula
        (Base := Base) (Const := WithParams Const) tau p (hp0 ρ i))
    (fun ρ i =>
      noConstOccurrence_predicateExistsNotFormula
        (Base := Base) (Const := WithParams Const) tau p (hp0 ρ i))
    hObj hMeasurable 1 1 N hNpos hCardEq
    (fun M => by
      letI := hObj M
      exact
        models_predicateExistsFormula_iff_one_le_ncard_extension
          (Base := Base) (Const := WithParams Const) M.1 tau p)
    (fun M => by
      letI := hObj M
      exact
        models_predicateExistsNotFormula_iff_ncard_extension_add_one_le
          (Base := Base) (Const := WithParams Const) M.1 tau p N
          (hCardEq M))

/-- The concrete all-HOL proper finite-frequency band event holds exactly when
there is at least one predicate witness and at least one non-witness. -/
theorem predicateCountingCapacityExistsAndExistsNotBandCut_ge_iff
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
    (M : ExtensionalTheoryModel (Base := Base) (Const := Const) T) :
    (predicateCountingCapacityExistsAndExistsNotBandCut
      (Base := Base) (Const := Const) (T := T)
      tau p hp0 hObj hMeasurable N hNpos hCardEq).threshold ≤
        (predicateCountingCapacityExistsAndExistsNotBandCut
          (Base := Base) (Const := Const) (T := T)
          tau p hp0 hObj hMeasurable N hNpos hCardEq).score M ↔
      1 ≤
          (predicateExtension
            (Base := Base) (Const := WithParams Const) M.1 tau p).ncard ∧
        (predicateExtension
            (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
          1 ≤ N := by
  exact
    predicateCountingCapacityCardinalityBandCut_ge_iff
      (Base := Base) (Const := Const) (T := T)
      tau p
      (predicateExistsFormula
        (Base := Base) (Const := WithParams Const) tau p)
      (predicateExistsNotFormula
        (Base := Base) (Const := WithParams Const) tau p)
      (fun ρ i =>
        noConstOccurrence_predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p (hp0 ρ i))
      (fun ρ i =>
        noConstOccurrence_predicateExistsNotFormula
          (Base := Base) (Const := WithParams Const) tau p (hp0 ρ i))
      hObj hMeasurable 1 1 N hNpos hCardEq
      (fun M => by
        letI := hObj M
        exact
          models_predicateExistsFormula_iff_one_le_ncard_extension
            (Base := Base) (Const := WithParams Const) M.1 tau p)
      (fun M => by
        letI := hObj M
        exact
          models_predicateExistsNotFormula_iff_ncard_extension_add_one_le
            (Base := Base) (Const := WithParams Const) M.1 tau p N
            (hCardEq M))
      M

/-- Numeric readout for the concrete all-HOL proper finite-frequency band:
under the exact carrier-size guard, the certified band event is exactly that
the normalized counting capacity of the predicate extension is strictly between
`0` and `1`. -/
theorem predicateCountingCapacityExistsAndExistsNotBandCut_ge_iff_countingCapacity_pos_and_lt_one
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
    (M : ExtensionalTheoryModel (Base := Base) (Const := Const) T) :
    (predicateCountingCapacityExistsAndExistsNotBandCut
      (Base := Base) (Const := Const) (T := T)
      tau p hp0 hObj hMeasurable N hNpos hCardEq).threshold ≤
        (predicateCountingCapacityExistsAndExistsNotBandCut
          (Base := Base) (Const := Const) (T := T)
          tau p hp0 hObj hMeasurable N hNpos hCardEq).score M ↔
      0 <
          ((FuzzyCapacity.countingCapacity
            (U := (PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 tau))
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p) :
            unitInterval) : ℝ) ∧
        ((FuzzyCapacity.countingCapacity
            (U := (PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 tau))
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p) :
            unitInterval) : ℝ) < 1 := by
  letI := hObj M
  letI := hMeasurable M
  rw [predicateCountingCapacityExistsAndExistsNotBandCut_ge_iff
    (Base := Base) (Const := Const) (T := T)
    tau p hp0 hObj hMeasurable N hNpos hCardEq M]
  exact
    (FuzzyCapacity.countingCapacity_pos_and_lt_one_iff_proper_cardinality_of_card_eq
      (U := (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
      (predicateExtension
        (Base := Base) (Const := WithParams Const) M.1 tau p)
      N hNpos (hCardEq M)).symm

/-- The concrete all-HOL proper finite-frequency band reads out through the
existing HOL interval for `∃ x, p x ∧ ∃ x, ¬ p x`. -/
theorem predicateCountingCapacityExistsAndExistsNotBandCut_intervalOfConsistent
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
      (predicateCountingCapacityExistsAndExistsNotBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (.and
            (predicateExistsFormula
              (Base := Base) (Const := WithParams Const) tau p)
            (predicateExistsNotFormula
              (Base := Base) (Const := WithParams Const) tau p)) := rfl

/-- Endpoint tightness for the concrete all-HOL proper finite-frequency band:
lower endpoint `1` is exactly provability of `∃ x, p x ∧ ∃ x, ¬ p x`. -/
theorem predicateCountingCapacityExistsAndExistsNotBandCut_lower_eq_one_iff_provable
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
      (predicateCountingCapacityExistsAndExistsNotBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.and
          (predicateExistsFormula
            (Base := Base) (Const := WithParams Const) tau p)
          (predicateExistsNotFormula
            (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsAndExistsNotBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the concrete all-HOL proper finite-frequency band:
upper endpoint `0` is exactly provability of the negation of
`∃ x, p x ∧ ∃ x, ¬ p x`. -/
theorem predicateCountingCapacityExistsAndExistsNotBandCut_upper_eq_zero_iff_provable_not
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
      (predicateCountingCapacityExistsAndExistsNotBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (.and
          (predicateExistsFormula
            (Base := Base) (Const := WithParams Const) tau p)
          (predicateExistsNotFormula
            (Base := Base) (Const := WithParams Const) tau p))) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsAndExistsNotBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the concrete all-HOL proper
finite-frequency band: lower endpoint `0` is exactly non-provability of the
conjunction of witness and non-witness existence. -/
theorem predicateCountingCapacityExistsAndExistsNotBandCut_lower_eq_zero_iff_not_provable
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
      (predicateCountingCapacityExistsAndExistsNotBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.and
          (predicateExistsFormula
            (Base := Base) (Const := WithParams Const) tau p)
          (predicateExistsNotFormula
            (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsAndExistsNotBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the concrete all-HOL proper
finite-frequency band: upper endpoint `1` is exactly non-provability of the
negation of the conjunction of witness and non-witness existence. -/
theorem predicateCountingCapacityExistsAndExistsNotBandCut_upper_eq_one_iff_not_provable_not
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
      (predicateCountingCapacityExistsAndExistsNotBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (.and
          (predicateExistsFormula
            (Base := Base) (Const := WithParams Const) tau p)
          (predicateExistsNotFormula
            (Base := Base) (Const := WithParams Const) tau p))) := by
  exact
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsAndExistsNotBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the concrete all-HOL proper finite-frequency
band: the interval collapses exactly when the theory decides the conjunction
of witness and non-witness existence. -/
theorem predicateCountingCapacityExistsAndExistsNotBandCut_width_eq_zero_iff_decides
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
      (predicateCountingCapacityExistsAndExistsNotBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.and
          (predicateExistsFormula
            (Base := Base) (Const := WithParams Const) tau p)
          (predicateExistsNotFormula
            (Base := Base) (Const := WithParams Const) tau p)) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (.and
          (predicateExistsFormula
            (Base := Base) (Const := WithParams Const) tau p)
          (predicateExistsNotFormula
            (Base := Base) (Const := WithParams Const) tau p))) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsAndExistsNotBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Concrete base-type finite-frequency band cut for normalized counting
capacity.

Under an exact carrier-size guard `N`, this cut certifies the band
`2 / N ≤ countingCapacity(ext p)` and
`1 / N ≤ 1 - countingCapacity(ext p)`: at least two witnesses satisfy `p`, and
at least one admissible base object does not.  The lower side uses the
constructed base-type HOL formula with equality; the complement side uses the
constructed non-witness formula. -/
noncomputable def predicateCountingCapacityTwoToAllButOneBaseBandCut
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
  predicateCountingCapacityCardinalityBandCut
    (Base := Base) (Const := Const) (T := T)
    (.base b) p
    (predicateAtLeastTwoBaseFormula
      (Base := Base) (Const := WithParams Const) b p)
    (predicateExistsNotFormula
      (Base := Base) (Const := WithParams Const) (.base b) p)
    (fun ρ i =>
      noConstOccurrence_predicateAtLeastTwoBaseFormula
        (Base := Base) (Const := WithParams Const) b p (hp0 ρ i))
    (fun ρ i =>
      noConstOccurrence_predicateExistsNotFormula
        (Base := Base) (Const := WithParams Const) (.base b) p (hp0 ρ i))
    hObj hMeasurable 2 1 N hNpos hCardEq
    (fun M => by
      letI := hObj M
      exact
        models_predicateAtLeastTwoBaseFormula_iff_two_le_ncard_extension
          (Base := Base) (Const := WithParams Const) M.1 b p)
    (fun M => by
      letI := hObj M
      exact
        models_predicateExistsNotFormula_iff_ncard_extension_add_one_le
          (Base := Base) (Const := WithParams Const) M.1 (.base b) p N
          (hCardEq M))

/-- The concrete base finite-frequency band event holds exactly when there are
at least two predicate witnesses and at least one non-witness. -/
theorem predicateCountingCapacityTwoToAllButOneBaseBandCut_ge_iff
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
    (M : ExtensionalTheoryModel (Base := Base) (Const := Const) T) :
    (predicateCountingCapacityTwoToAllButOneBaseBandCut
      (Base := Base) (Const := Const) (T := T)
      b p hp0 hObj hMeasurable N hNpos hCardEq).threshold ≤
        (predicateCountingCapacityTwoToAllButOneBaseBandCut
          (Base := Base) (Const := Const) (T := T)
          b p hp0 hObj hMeasurable N hNpos hCardEq).score M ↔
      2 ≤
          (predicateExtension
            (Base := Base) (Const := WithParams Const) M.1 (.base b) p).ncard ∧
        (predicateExtension
            (Base := Base) (Const := WithParams Const) M.1 (.base b) p).ncard +
          1 ≤ N := by
  exact
    predicateCountingCapacityCardinalityBandCut_ge_iff
      (Base := Base) (Const := Const) (T := T)
      (.base b) p
      (predicateAtLeastTwoBaseFormula
        (Base := Base) (Const := WithParams Const) b p)
      (predicateExistsNotFormula
        (Base := Base) (Const := WithParams Const) (.base b) p)
      (fun ρ i =>
        noConstOccurrence_predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p (hp0 ρ i))
      (fun ρ i =>
        noConstOccurrence_predicateExistsNotFormula
          (Base := Base) (Const := WithParams Const) (.base b) p (hp0 ρ i))
      hObj hMeasurable 2 1 N hNpos hCardEq
      (fun M => by
        letI := hObj M
        exact
          models_predicateAtLeastTwoBaseFormula_iff_two_le_ncard_extension
            (Base := Base) (Const := WithParams Const) M.1 b p)
      (fun M => by
        letI := hObj M
        exact
          models_predicateExistsNotFormula_iff_ncard_extension_add_one_le
            (Base := Base) (Const := WithParams Const) M.1 (.base b) p N
            (hCardEq M))
      M

/-- The concrete base finite-frequency band reads out through the existing HOL
interval for the conjunction of its two constructed cardinality formulas. -/
theorem predicateCountingCapacityTwoToAllButOneBaseBandCut_intervalOfConsistent
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
      (predicateCountingCapacityTwoToAllButOneBaseBandCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (.and
            (predicateAtLeastTwoBaseFormula
              (Base := Base) (Const := WithParams Const) b p)
            (predicateExistsNotFormula
              (Base := Base) (Const := WithParams Const) (.base b) p)) := rfl

/-- Endpoint tightness for the concrete base finite-frequency band: lower
endpoint `1` is exactly provability of the conjunction of its two constructed
cardinality formulas. -/
theorem predicateCountingCapacityTwoToAllButOneBaseBandCut_lower_eq_one_iff_provable
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
      (predicateCountingCapacityTwoToAllButOneBaseBandCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.and
          (predicateAtLeastTwoBaseFormula
            (Base := Base) (Const := WithParams Const) b p)
          (predicateExistsNotFormula
            (Base := Base) (Const := WithParams Const) (.base b) p)) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityTwoToAllButOneBaseBandCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the concrete base finite-frequency band: upper
endpoint `0` is exactly provability of the negation of the conjunction of its
two constructed cardinality formulas. -/
theorem predicateCountingCapacityTwoToAllButOneBaseBandCut_upper_eq_zero_iff_provable_not
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
      (predicateCountingCapacityTwoToAllButOneBaseBandCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (.and
          (predicateAtLeastTwoBaseFormula
            (Base := Base) (Const := WithParams Const) b p)
          (predicateExistsNotFormula
            (Base := Base) (Const := WithParams Const) (.base b) p))) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityTwoToAllButOneBaseBandCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the concrete base finite-frequency
band: lower endpoint `0` is exactly non-provability of the conjunction of its
two constructed cardinality formulas. -/
theorem predicateCountingCapacityTwoToAllButOneBaseBandCut_lower_eq_zero_iff_not_provable
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
      (predicateCountingCapacityTwoToAllButOneBaseBandCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.and
          (predicateAtLeastTwoBaseFormula
            (Base := Base) (Const := WithParams Const) b p)
          (predicateExistsNotFormula
            (Base := Base) (Const := WithParams Const) (.base b) p)) := by
  exact
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityTwoToAllButOneBaseBandCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the concrete base finite-frequency
band: upper endpoint `1` is exactly non-provability of the negation of the
conjunction of its two constructed cardinality formulas. -/
theorem predicateCountingCapacityTwoToAllButOneBaseBandCut_upper_eq_one_iff_not_provable_not
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
      (predicateCountingCapacityTwoToAllButOneBaseBandCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (.and
          (predicateAtLeastTwoBaseFormula
            (Base := Base) (Const := WithParams Const) b p)
          (predicateExistsNotFormula
            (Base := Base) (Const := WithParams Const) (.base b) p))) := by
  exact
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityTwoToAllButOneBaseBandCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the concrete base finite-frequency band: the
interval collapses exactly when the theory decides the conjunction of its two
constructed cardinality formulas. -/
theorem predicateCountingCapacityTwoToAllButOneBaseBandCut_width_eq_zero_iff_decides
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
      (predicateCountingCapacityTwoToAllButOneBaseBandCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.and
          (predicateAtLeastTwoBaseFormula
            (Base := Base) (Const := WithParams Const) b p)
          (predicateExistsNotFormula
            (Base := Base) (Const := WithParams Const) (.base b) p)) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (.and
          (predicateAtLeastTwoBaseFormula
            (Base := Base) (Const := WithParams Const) b p)
          (predicateExistsNotFormula
            (Base := Base) (Const := WithParams Const) (.base b) p))) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateCountingCapacityTwoToAllButOneBaseBandCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM


end Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDefinableCuts
