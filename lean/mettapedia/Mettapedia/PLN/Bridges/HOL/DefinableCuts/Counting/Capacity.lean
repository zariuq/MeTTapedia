import Mettapedia.PLN.Bridges.HOL.DefinableCuts.Counting.QFM

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

/-! ## Counting-capacity rational cuts -/

/-- On a finite carrier whose cardinality is exactly `N`, normalized counting
capacity is strictly positive exactly when the subset has at least one
element. -/
theorem FuzzyCapacity.countingCapacity_pos_iff_one_le_ncard_of_card_eq
    {U : Type u} [Fintype U] [MeasurableSpace U]
    (A : Set U) (N : Nat) (hNpos : 0 < N)
    (hCard : Fintype.card U = N) :
    0 <
        ((FuzzyCapacity.countingCapacity (U := U) A : unitInterval) : ℝ) ↔
      1 ≤ A.ncard := by
  classical
  haveI : Fintype A := Set.Finite.fintype (Set.toFinite A)
  have hUposNat : 0 < Fintype.card U := by
    simpa [hCard] using hNpos
  have hNposR : 0 < (N : ℝ) := by
    exact_mod_cast hNpos
  change 0 < ((FuzzyCapacity.countingValue (U := U) A : unitInterval) : ℝ) ↔
      1 ≤ A.ncard
  unfold FuzzyCapacity.countingValue
  have h0 : Fintype.card U ≠ 0 := Nat.ne_of_gt hUposNat
  simp [h0]
  have hFilterEq :
      Finset.univ.filter (fun a : U => a ∈ A) = A.toFinset := by
    ext a
    simp
  have hFilterCard :
      (Finset.univ.filter (fun a : U => a ∈ A)).card = A.ncard := by
    rw [hFilterEq, ← Set.ncard_eq_toFinset_card' A]
  rw [hFilterCard, hCard]
  constructor
  · intro hPos
    have hNumPos : 0 < (A.ncard : ℝ) :=
      (div_pos_iff_of_pos_right hNposR).mp hPos
    have hNatPos : 0 < A.ncard := by
      exact_mod_cast hNumPos
    exact Nat.succ_le_of_lt hNatPos
  · intro hOne
    have hNumPos : 0 < (A.ncard : ℝ) := by
      exact_mod_cast hOne
    exact (div_pos_iff_of_pos_right hNposR).mpr hNumPos

/-- On a finite carrier whose cardinality is exactly `N`, normalized counting
capacity is below `1` exactly when the subset misses at least one element. -/
theorem FuzzyCapacity.countingCapacity_lt_one_iff_ncard_add_one_le_of_card_eq
    {U : Type u} [Fintype U] [MeasurableSpace U]
    (A : Set U) (N : Nat) (hNpos : 0 < N)
    (hCard : Fintype.card U = N) :
    ((FuzzyCapacity.countingCapacity (U := U) A : unitInterval) : ℝ) < 1 ↔
      A.ncard + 1 ≤ N := by
  classical
  haveI : Fintype A := Set.Finite.fintype (Set.toFinite A)
  have hUposNat : 0 < Fintype.card U := by
    simpa [hCard] using hNpos
  have hNposR : 0 < (N : ℝ) := by
    exact_mod_cast hNpos
  change ((FuzzyCapacity.countingValue (U := U) A : unitInterval) : ℝ) < 1 ↔
      A.ncard + 1 ≤ N
  unfold FuzzyCapacity.countingValue
  have h0 : Fintype.card U ≠ 0 := Nat.ne_of_gt hUposNat
  simp [h0]
  have hFilterEq :
      Finset.univ.filter (fun a : U => a ∈ A) = A.toFinset := by
    ext a
    simp
  have hFilterCard :
      (Finset.univ.filter (fun a : U => a ∈ A)).card = A.ncard := by
    rw [hFilterEq, ← Set.ncard_eq_toFinset_card' A]
  rw [hFilterCard, hCard]
  constructor
  · intro hLt
    have hCast : (A.ncard : ℝ) < (N : ℝ) :=
      (div_lt_one hNposR).mp hLt
    have hNat : A.ncard < N := by
      exact_mod_cast hCast
    exact (Nat.lt_iff_add_one_le.mp hNat)
  · intro hAdd
    have hNat : A.ncard < N :=
      Nat.lt_iff_add_one_le.mpr hAdd
    have hCast : (A.ncard : ℝ) < (N : ℝ) := by
      exact_mod_cast hNat
    exact (div_lt_one hNposR).mpr hCast

/-- On an exact finite carrier, the strict open interval `0 < countingCapacity
A < 1` is exactly the proper-cardinality condition: at least one member and at
least one missing member. -/
theorem FuzzyCapacity.countingCapacity_pos_and_lt_one_iff_proper_cardinality_of_card_eq
    {U : Type u} [Fintype U] [MeasurableSpace U]
    (A : Set U) (N : Nat) (hNpos : 0 < N)
    (hCard : Fintype.card U = N) :
    0 <
          ((FuzzyCapacity.countingCapacity (U := U) A : unitInterval) : ℝ) ∧
        ((FuzzyCapacity.countingCapacity (U := U) A : unitInterval) : ℝ) < 1 ↔
      1 ≤ A.ncard ∧ A.ncard + 1 ≤ N := by
  rw [FuzzyCapacity.countingCapacity_pos_iff_one_le_ncard_of_card_eq
      (U := U) A N hNpos hCard,
    FuzzyCapacity.countingCapacity_lt_one_iff_ncard_add_one_le_of_card_eq
      (U := U) A N hNpos hCard]

/-- A nonempty predicate extension has normalized counting capacity at least
`1 / N` when the finite carrier has cardinality at most `N`.

This is the small but load-bearing arithmetic fact behind the first genuinely
fractional QFM/counting cut below.  The uniform carrier bound is essential: a
fixed positive threshold cannot represent nonempty existence over arbitrarily
large finite domains. -/
theorem predicateCountingCapacityExtension_ge_one_div_of_models_exists_of_card_le
    (M : HenkinModel.{u, v, w} Base Const)
    (tau : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M tau)]
    [MeasurableSpace (PredicateObject (Base := Base) (Const := Const) M tau)]
    (p : UnaryPredicate (Base := Base) (Const := Const) tau)
    (N : Nat) (hNpos : 0 < N)
    (hCard :
      Fintype.card (PredicateObject (Base := Base) (Const := Const) M tau) ≤ N)
    (hModels :
      HenkinModel.models M
        (predicateExistsFormula (Base := Base) (Const := Const) tau p)) :
    (1 : ℝ) / (N : ℝ) ≤
      ((FuzzyCapacity.countingCapacity
        (U := (PredicateObject (Base := Base) (Const := Const) M tau))
        (predicateExtension (Base := Base) (Const := Const) M tau p) :
          unitInterval) : ℝ) := by
    classical
    have hExtNonempty :
        (predicateExtension (Base := Base) (Const := Const) M tau p).Nonempty := by
      rcases
          (models_predicateExistsFormula_iff
            (Base := Base) (Const := Const) M tau p).1 hModels with
        ⟨x, hx⟩
      exact ⟨x, hx⟩
    exact
      (FuzzyCapacity.countingCapacity_ge_one_div_of_nonempty_of_card_le
        (U := (PredicateObject (Base := Base) (Const := Const) M tau))
        (predicateExtension (Base := Base) (Const := Const) M tau p)
        N hNpos hCard hExtNonempty)

/-- Guarded fractional counting-capacity cut for HOL existence.

For a fixed positive threshold `θ`, normalized counting capacity of a predicate
extension represents ordinary HOL `Exists` once every canonical carrier is
uniformly bounded by `N` and `θ ≤ 1/N`.  This is the first fractional
QFM/counting definable cut: unlike Boolean acceptance scores, the theorem needs
an explicit finite-carrier lower-bound hypothesis. -/
noncomputable def predicateCountingCapacityExistsPositiveThresholdCut
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCard :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) ≤ N)
    (theta : ℝ) (htheta_pos : 0 < theta)
    (htheta_le : theta ≤ (1 : ℝ) / (N : ℝ))
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateExistsFormula (Base := Base) (Const := WithParams Const) tau p)) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M =>
      letI := hObj M
      letI := hMeasurable M
      ((FuzzyCapacity.countingCapacity
        (U := (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
        (predicateExtension
          (Base := Base) (Const := WithParams Const) M.1 tau p) :
        unitInterval) : ℝ)
    threshold := theta
    formula := predicateExistsFormula
      (Base := Base) (Const := WithParams Const) tau p
    paramFree := hφ0
    represents_ge := by
      intro M
      classical
      letI := hObj M
      letI := hMeasurable M
      constructor
      · intro hModels
        exact le_trans htheta_le
          (predicateCountingCapacityExtension_ge_one_div_of_models_exists_of_card_le
            (Base := Base) (Const := WithParams Const) M.1 tau p
            N hNpos (hCard M) hModels)
      · intro hGe
        by_contra hNotModels
        have hExtEmpty :
            predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p = ∅ := by
          ext x
          constructor
          · intro hx
            have hPred :
                predicateHoldsAt
                  (Base := Base) (Const := WithParams Const) M.1 tau p x := by
              simpa [predicateExtension] using hx
            exact False.elim
              (hNotModels
                ((models_predicateExistsFormula_iff
                  (Base := Base) (Const := WithParams Const) M.1 tau p).2
                  ⟨x, hPred⟩))
          · intro hx
            simp at hx
        have hScore0 :
            ((FuzzyCapacity.countingCapacity
              (U := (PredicateObject
                (Base := Base) (Const := WithParams Const) M.1 tau))
              (predicateExtension
                (Base := Base) (Const := WithParams Const) M.1 tau p) :
              unitInterval) : ℝ) = 0 := by
          have hCap :
              FuzzyCapacity.countingCapacity
                (U := (PredicateObject
                  (Base := Base) (Const := WithParams Const) M.1 tau))
                (predicateExtension
                  (Base := Base) (Const := WithParams Const) M.1 tau p) =
                (0 : unitInterval) := by
            simp [FuzzyCapacity.countingCapacity, hExtEmpty,
              FuzzyCapacity.countingValue_empty
                (U := (PredicateObject
                  (Base := Base) (Const := WithParams Const) M.1 tau))]
          exact congrArg Subtype.val hCap
        have hNotGe : ¬ theta ≤
            ((FuzzyCapacity.countingCapacity
              (U := (PredicateObject
                (Base := Base) (Const := WithParams Const) M.1 tau))
              (predicateExtension
                (Base := Base) (Const := WithParams Const) M.1 tau p) :
              unitInterval) : ℝ) := by
          simpa [hScore0] using (not_le.mpr htheta_pos)
        exact hNotGe hGe }

/-- The guarded fractional counting-capacity cut has exactly the formula-level
credal interval of its representing HOL existence formula.

This is the readout that keeps the fractional cut tied to the sealed
formula-level completeness machinery: the numeric score is new, but the
interval is still the existing extensional HOL interval for the certified
threshold formula. -/
theorem predicateCountingCapacityExistsPositiveThresholdCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCard :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) ≤ N)
    (theta : ℝ) (htheta_pos : 0 < theta)
    (htheta_le : theta ≤ (1 : ℝ) / (N : ℝ))
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateExistsFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsPositiveThresholdCut
        (T := T) tau p hObj hMeasurable N hNpos hCard theta htheta_pos
        htheta_le hφ0)
      enum henum hCons hT0 hEM =
      extensionalTheoryCredalHOLFormulaIntervalOfConsistent
        (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
        (predicateExistsFormula (Base := Base) (Const := WithParams Const) tau p) := rfl

/-- Endpoint tightness for the guarded fractional counting-existence cut:
lower endpoint `1` is exactly provability of the representing HOL existence
formula. -/
theorem predicateCountingCapacityExistsPositiveThresholdCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCard :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) ≤ N)
    (theta : ℝ) (htheta_pos : 0 < theta)
    (htheta_le : theta ≤ (1 : ℝ) / (N : ℝ))
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateExistsFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsPositiveThresholdCut
        (T := T) tau p hObj hMeasurable N hNpos hCard theta htheta_pos
        htheta_le hφ0)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsFormula (Base := Base) (Const := WithParams Const) tau p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsPositiveThresholdCut
        (T := T) tau p hObj hMeasurable N hNpos hCard theta htheta_pos
        htheta_le hφ0)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the guarded fractional counting-existence cut:
upper endpoint `0` is exactly provability of the negation of the representing
HOL existence formula. -/
theorem predicateCountingCapacityExistsPositiveThresholdCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCard :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) ≤ N)
    (theta : ℝ) (htheta_pos : 0 < theta)
    (htheta_le : theta ≤ (1 : ℝ) / (N : ℝ))
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateExistsFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsPositiveThresholdCut
        (T := T) tau p hObj hMeasurable N hNpos hCard theta htheta_pos
        htheta_le hφ0)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsPositiveThresholdCut
        (T := T) tau p hObj hMeasurable N hNpos hCard theta htheta_pos
        htheta_le hφ0)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the guarded fractional
counting-existence cut: lower endpoint `0` is exactly non-provability of the
representing HOL existence formula. -/
theorem predicateCountingCapacityExistsPositiveThresholdCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCard :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) ≤ N)
    (theta : ℝ) (htheta_pos : 0 < theta)
    (htheta_le : theta ≤ (1 : ℝ) / (N : ℝ))
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateExistsFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsPositiveThresholdCut
        (T := T) tau p hObj hMeasurable N hNpos hCard theta htheta_pos
        htheta_le hφ0)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsFormula (Base := Base) (Const := WithParams Const) tau p) := by
  exact
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsPositiveThresholdCut
        (T := T) tau p hObj hMeasurable N hNpos hCard theta htheta_pos
        htheta_le hφ0)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the guarded fractional
counting-existence cut: upper endpoint `1` is exactly non-provability of the
negation of the representing HOL existence formula. -/
theorem predicateCountingCapacityExistsPositiveThresholdCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCard :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) ≤ N)
    (theta : ℝ) (htheta_pos : 0 < theta)
    (htheta_le : theta ≤ (1 : ℝ) / (N : ℝ))
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateExistsFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsPositiveThresholdCut
        (T := T) tau p hObj hMeasurable N hNpos hCard theta htheta_pos
        htheta_le hφ0)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsPositiveThresholdCut
        (T := T) tau p hObj hMeasurable N hNpos hCard theta htheta_pos
        htheta_le hφ0)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the guarded fractional counting-existence cut:
the certified fractional-counting interval collapses exactly when the theory
decides the representing HOL existence formula. -/
theorem predicateCountingCapacityExistsPositiveThresholdCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (N : Nat) (hNpos : 0 < N)
    (hCard :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) ≤ N)
    (theta : ℝ) (htheta_pos : 0 < theta)
    (htheta_le : theta ≤ (1 : ℝ) / (N : ℝ))
    (hφ0 : ∀ (ρ : Ty Base) (k : Nat), NoConstOccurrence (param ρ k)
      (predicateExistsFormula (Base := Base) (Const := WithParams Const) tau p))
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsPositiveThresholdCut
        (T := T) tau p hObj hMeasurable N hNpos hCard theta htheta_pos
        htheta_le hφ0)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsFormula (Base := Base) (Const := WithParams Const) tau p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsPositiveThresholdCut
        (T := T) tau p hObj hMeasurable N hNpos hCard theta htheta_pos
        htheta_le hφ0)
      enum henum hCons hT0 hEM

/-- Exact-denominator counting-capacity cut for the concrete HOL formula
`∃ x, p x`.

Under an exact carrier-size guard `N`, the formula represents
`1 / N ≤ countingCapacity(ext p)`: at least one admissible object lies in the
predicate extension. Unlike the base-type `at least two` and `at least three`
formulae, this construction works at every HOL type because it does not compare
objects by equality. -/
noncomputable def predicateCountingCapacityExistsExactThresholdCut
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
  { score := fun M =>
      letI := hObj M
      letI := hMeasurable M
      ((FuzzyCapacity.countingCapacity
        (U := (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
        (predicateExtension
          (Base := Base) (Const := WithParams Const) M.1 tau p) :
        unitInterval) : ℝ)
    threshold := ((1 : Nat) : ℝ) / (N : ℝ)
    formula := predicateExistsFormula
      (Base := Base) (Const := WithParams Const) tau p
    paramFree := fun ρ i =>
      noConstOccurrence_predicateExistsFormula
        (Base := Base) (Const := WithParams Const) tau p (hp0 ρ i)
    represents_ge := by
      intro M
      classical
      letI := hObj M
      letI := hMeasurable M
      constructor
      · intro hModels
        exact
          (FuzzyCapacity.countingCapacity_ge_nat_div_iff_card_ge_of_card_eq
            (U := (PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 tau))
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p)
            1 N hNpos (hCardEq M)).2
            ((models_predicateExistsFormula_iff_one_le_ncard_extension
              (Base := Base) (Const := WithParams Const) M.1 tau p).1 hModels)
      · intro hGe
        exact
          (models_predicateExistsFormula_iff_one_le_ncard_extension
            (Base := Base) (Const := WithParams Const) M.1 tau p).2
            ((FuzzyCapacity.countingCapacity_ge_nat_div_iff_card_ge_of_card_eq
              (U := (PredicateObject
                (Base := Base) (Const := WithParams Const) M.1 tau))
              (predicateExtension
                (Base := Base) (Const := WithParams Const) M.1 tau p)
              1 N hNpos (hCardEq M)).1 hGe) }

/-- The concrete exact-denominator existential counting cut reads out through
the existing HOL interval for `∃ x, p x`. -/
theorem predicateCountingCapacityExistsExactThresholdCut_intervalOfConsistent
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
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateExistsFormula
            (Base := Base) (Const := WithParams Const) tau p) := rfl

/-- Endpoint tightness for the concrete exact-denominator existential counting
cut: lower endpoint `1` is exactly provability of `∃ x, p x`. -/
theorem predicateCountingCapacityExistsExactThresholdCut_lower_eq_one_iff_provable
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
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the concrete exact-denominator existential counting
cut: upper endpoint `0` is exactly provability of `¬ ∃ x, p x`. -/
theorem predicateCountingCapacityExistsExactThresholdCut_upper_eq_zero_iff_provable_not
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
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the concrete exact-denominator
existential counting cut: lower endpoint `0` is exactly non-provability of
`∃ x, p x`. -/
theorem predicateCountingCapacityExistsExactThresholdCut_lower_eq_zero_iff_not_provable
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
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p) := by
  exact
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the concrete exact-denominator
existential counting cut: upper endpoint `1` is exactly non-provability of
`¬ ∃ x, p x`. -/
theorem predicateCountingCapacityExistsExactThresholdCut_upper_eq_one_iff_not_provable_not
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
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the concrete exact-denominator existential
counting cut: the interval collapses exactly when the theory decides
`∃ x, p x`. -/
theorem predicateCountingCapacityExistsExactThresholdCut_width_eq_zero_iff_decides
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
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsExactThresholdCut
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
      (predicateCountingCapacityExistsExactThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Exact rational counting-capacity cut from a cardinality-threshold
calibration formula.

If a param-free closed HOL formula `χ` represents "the predicate extension has
at least `k` elements" in every extensional theory model, and the carrier for
the predicate type has exactly `N` objects in every such model, then `χ`
represents the normalized counting-capacity threshold `k / N`.

This is deliberately a calibrated cut: this file does not invent a syntax for
"there are at least `k` distinct witnesses".  The caller must supply the
formula and the proof that it represents the cardinality event. -/
noncomputable def predicateCountingCapacityCardinalityThresholdCut
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
      ((FuzzyCapacity.countingCapacity
        (U := (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
        (predicateExtension
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
      constructor
      · intro hModels
        exact
          (FuzzyCapacity.countingCapacity_ge_nat_div_iff_card_ge_of_card_eq
            (U := (PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 tau))
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p)
            k N hNpos (hCardEq M)).2 ((hχRep M).1 hModels)
      · intro hGe
        exact (hχRep M).2
          ((FuzzyCapacity.countingCapacity_ge_nat_div_iff_card_ge_of_card_eq
            (U := (PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 tau))
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p)
            k N hNpos (hCardEq M)).1 hGe) }

/-- The calibrated cardinality-threshold counting cut reads out through the
existing HOL interval for its supplied representing formula. -/
theorem predicateCountingCapacityCardinalityThresholdCut_intervalOfConsistent
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
      (predicateCountingCapacityCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM χ := rfl

/-- Endpoint tightness for exact-denominator lower-cardinality counting cuts:
lower endpoint `1` is exactly provability of the supplied cardinality formula.
-/
theorem predicateCountingCapacityCardinalityThresholdCut_lower_eq_one_iff_provable
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
      (predicateCountingCapacityCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T χ := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for exact-denominator lower-cardinality counting cuts:
upper endpoint `0` is exactly provability of the negation of the supplied
cardinality formula. -/
theorem predicateCountingCapacityCardinalityThresholdCut_upper_eq_zero_iff_provable_not
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
      (predicateCountingCapacityCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for exact-denominator lower-cardinality
counting cuts: lower endpoint `0` is exactly non-provability of the supplied
cardinality formula. -/
theorem predicateCountingCapacityCardinalityThresholdCut_lower_eq_zero_iff_not_provable
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
      (predicateCountingCapacityCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T χ := by
  exact
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for exact-denominator lower-cardinality
counting cuts: upper endpoint `1` is exactly non-provability of the negation of
the supplied cardinality formula. -/
theorem predicateCountingCapacityCardinalityThresholdCut_upper_eq_one_iff_not_provable_not
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
      (predicateCountingCapacityCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ) := by
  exact
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for exact-denominator lower-cardinality counting cuts:
the certified interval collapses exactly when the theory decides the supplied
cardinality formula. -/
theorem predicateCountingCapacityCardinalityThresholdCut_width_eq_zero_iff_decides
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
      (predicateCountingCapacityCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T χ ∨
        ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Uniform exact-denominator counting-capacity cut for the concrete base-type
HOL formula "at least `k` distinct witnesses satisfy `p`".

This is the arbitrary-cardinality capstone for normalized counting capacity:
the constructed HOL formula supplies the representation proof required by the
generic cardinality-threshold cut.  It stays at base HOL types because equality
at higher types is extensional equivalence, while the normalized counting score
counts admissible objects. -/
noncomputable def predicateCountingCapacityAtLeastNBaseCut
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
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  predicateCountingCapacityCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)
    (.base b) p
    (predicateAtLeastNBaseFormula (Base := Base) (Const := WithParams Const) b p k)
    (fun ρ i =>
      noConstOccurrence_predicateAtLeastNBaseFormula
        (Base := Base) (Const := WithParams Const) b p (hp0 ρ i) k)
    hObj hMeasurable k N hNpos hCardEq
    (fun M => by
      letI := hObj M
      exact
        models_predicateAtLeastNBaseFormula_iff_k_le_ncard_extension
          (Base := Base) (Const := WithParams Const) M.1 b p k)

/-- Width-zero tightness for arbitrary base-type normalized counting-capacity
cuts.  This is the generic capstone behind the concrete "at least two" /
"at least three" witnesses: the certified interval collapses exactly when the
theory decides the constructed HOL cardinality formula. -/
theorem predicateCountingCapacityAtLeastNBaseCut_width_eq_zero_iff_decides
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
    (k N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 (.base b)) = N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (ρ : Ty Base) (i : Nat), NoConstOccurrence (param ρ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastNBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable k N hNpos hCardEq)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastNBaseFormula (Base := Base) (Const := WithParams Const) b p k) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastNBaseFormula
          (Base := Base) (Const := WithParams Const) b p k)) := by
  exact
    predicateCountingCapacityCardinalityThresholdCut_width_eq_zero_iff_decides
      (Base := Base) (Const := Const) (T := T)
      (.base b) p
      (predicateAtLeastNBaseFormula (Base := Base) (Const := WithParams Const) b p k)
      (fun ρ i =>
        noConstOccurrence_predicateAtLeastNBaseFormula
          (Base := Base) (Const := WithParams Const) b p (hp0 ρ i) k)
      hObj hMeasurable k N hNpos hCardEq
      (fun M => by
        letI := hObj M
        exact
          models_predicateAtLeastNBaseFormula_iff_k_le_ncard_extension
            (Base := Base) (Const := WithParams Const) M.1 b p k)
      enum henum hCons hT0 hEM

/-- Exact-denominator counting-capacity cut for the concrete base-type HOL
formula "at least two distinct witnesses satisfy `p`".

This is the first nontrivial cardinality-threshold cut whose representing
formula is constructed here rather than supplied by the caller.  It is
restricted to base HOL types because equality at higher types is extensional
equivalence, while the normalized counting score counts admissible objects. -/
noncomputable def predicateCountingCapacityAtLeastTwoBaseCut
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
  predicateCountingCapacityCardinalityThresholdCut
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

/-- The concrete base-type "at least two" counting cut reads out through the
existing HOL interval for its representing formula. -/
theorem predicateCountingCapacityAtLeastTwoBaseCut_intervalOfConsistent
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
      (predicateCountingCapacityAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateAtLeastTwoBaseFormula
            (Base := Base) (Const := WithParams Const) b p) := rfl

/-- Endpoint tightness for the concrete base-type "at least two" counting cut:
lower endpoint `1` is exactly provability of the constructed HOL cardinality
formula. -/
theorem predicateCountingCapacityAtLeastTwoBaseCut_lower_eq_one_iff_provable
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
      (predicateCountingCapacityAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the concrete base-type "at least two" counting cut:
upper endpoint `0` is exactly provability of the negation of the constructed
HOL cardinality formula. -/
theorem predicateCountingCapacityAtLeastTwoBaseCut_upper_eq_zero_iff_provable_not
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
      (predicateCountingCapacityAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the concrete base-type "at least two"
counting cut: lower endpoint `0` is exactly non-provability of the constructed
HOL cardinality formula. -/
theorem predicateCountingCapacityAtLeastTwoBaseCut_lower_eq_zero_iff_not_provable
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
      (predicateCountingCapacityAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p) := by
  exact
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the concrete base-type "at least two"
counting cut: upper endpoint `1` is exactly non-provability of the negation of
the constructed HOL cardinality formula. -/
theorem predicateCountingCapacityAtLeastTwoBaseCut_upper_eq_one_iff_not_provable_not
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
      (predicateCountingCapacityAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastTwoBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the concrete base-type "at least two" counting
cut: the interval collapses exactly when the theory decides the constructed
HOL cardinality formula. -/
theorem predicateCountingCapacityAtLeastTwoBaseCut_width_eq_zero_iff_decides
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
      (predicateCountingCapacityAtLeastTwoBaseCut
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
      (predicateCountingCapacityAtLeastTwoBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Exact-denominator counting-capacity cut for the concrete base-type HOL
formula "at least three distinct witnesses satisfy `p`".

This specializes the lower-cardinality threshold package at `k = 3` with a
constructed HOL formula and a theorem proving that the formula represents
`3 ≤ ncard(ext p)` in every canonical completion. -/
noncomputable def predicateCountingCapacityAtLeastThreeBaseCut
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
  predicateCountingCapacityCardinalityThresholdCut
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

/-- The concrete base-type "at least three" counting cut reads out through the
existing HOL interval for its representing formula. -/
theorem predicateCountingCapacityAtLeastThreeBaseCut_intervalOfConsistent
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
      (predicateCountingCapacityAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateAtLeastThreeBaseFormula
            (Base := Base) (Const := WithParams Const) b p) := rfl

/-- Endpoint tightness for the concrete base-type "at least three" counting
cut: lower endpoint `1` is exactly provability of the constructed HOL
cardinality formula. -/
theorem predicateCountingCapacityAtLeastThreeBaseCut_lower_eq_one_iff_provable
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
      (predicateCountingCapacityAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the concrete base-type "at least three" counting
cut: upper endpoint `0` is exactly provability of the negation of the
constructed HOL cardinality formula. -/
theorem predicateCountingCapacityAtLeastThreeBaseCut_upper_eq_zero_iff_provable_not
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
      (predicateCountingCapacityAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the concrete base-type "at least three"
counting cut: lower endpoint `0` is exactly non-provability of the constructed
HOL cardinality formula. -/
theorem predicateCountingCapacityAtLeastThreeBaseCut_lower_eq_zero_iff_not_provable
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
      (predicateCountingCapacityAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p) := by
  exact
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the concrete base-type "at least three"
counting cut: upper endpoint `1` is exactly non-provability of the negation of
the constructed HOL cardinality formula. -/
theorem predicateCountingCapacityAtLeastThreeBaseCut_upper_eq_one_iff_not_provable_not
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
      (predicateCountingCapacityAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateAtLeastThreeBaseFormula
          (Base := Base) (Const := WithParams Const) b p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the concrete base-type "at least three" counting
cut: the interval collapses exactly when the theory decides the constructed
HOL cardinality formula. -/
theorem predicateCountingCapacityAtLeastThreeBaseCut_width_eq_zero_iff_decides
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
      (predicateCountingCapacityAtLeastThreeBaseCut
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
      (predicateCountingCapacityAtLeastThreeBaseCut
        (Base := Base) (Const := Const) (T := T)
        b p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Exact rational complement-counting cut from an upper-cardinality calibration
formula.

If a param-free closed HOL formula `χ` represents
`ncard (ext p) + k ≤ N` in every extensional theory model, and the carrier for
the predicate type has exactly `N` objects in every such model, then `χ`
represents the complementary normalized counting-capacity threshold
`k / N ≤ 1 - countingCapacity(ext p)`.

This is the dual of `predicateCountingCapacityCardinalityThresholdCut`: it
certifies upper/absence-side rational events without pretending that Boolean
negation of a lower-cardinality formula is the same thing as a numeric
complement threshold. -/
noncomputable def predicateCountingCapacityComplementCardinalityThresholdCut
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
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            k ≤ N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  { score := fun M =>
      letI := hObj M
      letI := hMeasurable M
      1 - ((FuzzyCapacity.countingCapacity
        (U := (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
        (predicateExtension
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
      constructor
      · intro hModels
        exact
          (FuzzyCapacity.nat_div_le_one_sub_countingCapacity_iff_card_add_le_of_card_eq
            (U := (PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 tau))
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p)
            k N hNpos (hCardEq M)).2 ((hχRep M).1 hModels)
      · intro hGe
        exact (hχRep M).2
          ((FuzzyCapacity.nat_div_le_one_sub_countingCapacity_iff_card_add_le_of_card_eq
            (U := (PredicateObject
              (Base := Base) (Const := WithParams Const) M.1 tau))
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p)
            k N hNpos (hCardEq M)).1 hGe) }

/-- The calibrated complement-cardinality threshold cut reads out through the
existing HOL interval for its supplied upper-cardinality formula. -/
theorem predicateCountingCapacityComplementCardinalityThresholdCut_intervalOfConsistent
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
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            k ≤ N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityComplementCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM χ := rfl

/-- Endpoint tightness for exact-denominator complement-cardinality counting
cuts: lower endpoint `1` is exactly provability of the supplied
upper-cardinality formula. -/
theorem predicateCountingCapacityComplementCardinalityThresholdCut_lower_eq_one_iff_provable
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
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            k ≤ N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityComplementCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T χ := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityComplementCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for exact-denominator complement-cardinality counting
cuts: upper endpoint `0` is exactly provability of the negation of the supplied
upper-cardinality formula. -/
theorem predicateCountingCapacityComplementCardinalityThresholdCut_upper_eq_zero_iff_provable_not
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
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            k ≤ N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityComplementCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityComplementCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for exact-denominator complement-cardinality
counting cuts: lower endpoint `0` is exactly non-provability of the supplied
upper-cardinality formula. -/
theorem predicateCountingCapacityComplementCardinalityThresholdCut_lower_eq_zero_iff_not_provable
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
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            k ≤ N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityComplementCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T χ := by
  exact
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityComplementCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for exact-denominator complement-cardinality
counting cuts: upper endpoint `1` is exactly non-provability of the negation of
the supplied upper-cardinality formula. -/
theorem predicateCountingCapacityComplementCardinalityThresholdCut_upper_eq_one_iff_not_provable_not
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
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            k ≤ N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityComplementCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ) := by
  exact
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityComplementCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for exact-denominator complement-cardinality counting
cuts: the certified interval collapses exactly when the theory decides the
supplied upper-cardinality formula. -/
theorem predicateCountingCapacityComplementCardinalityThresholdCut_width_eq_zero_iff_decides
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
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            k ≤ N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityComplementCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T χ ∨
        ClosedTheorySet.Provable (Const := WithParams Const) T (.not χ) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateCountingCapacityComplementCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χ hχ0 hObj hMeasurable k N hNpos hCardEq hχRep)
      enum henum hCons hT0 hEM

/-- Exact-denominator complement counting-capacity cut for the concrete HOL
formula `∃ x, ¬ p x`.

Under an exact carrier-size guard `N`, the formula represents
`1 / N ≤ 1 - countingCapacity(ext p)`: there is at least one admissible object
outside the predicate extension.  Unlike the base-type `at least two`
cardinality formula, this construction works at every HOL type because it does
not compare two objects by equality. -/
noncomputable def predicateCountingCapacityExistsNotComplementCut
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
  predicateCountingCapacityComplementCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)
    tau p
    (predicateExistsNotFormula (Base := Base) (Const := WithParams Const) tau p)
    (fun ρ i =>
      noConstOccurrence_predicateExistsNotFormula
        (Base := Base) (Const := WithParams Const) tau p (hp0 ρ i))
    hObj hMeasurable 1 N hNpos hCardEq
    (fun M => by
      letI := hObj M
      exact
        models_predicateExistsNotFormula_iff_ncard_extension_add_one_le
          (Base := Base) (Const := WithParams Const) M.1 tau p N (hCardEq M))

/-- The concrete non-witness complement cut reads out through the existing HOL
interval for `∃ x, ¬ p x`. -/
theorem predicateCountingCapacityExistsNotComplementCut_intervalOfConsistent
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
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsNotComplementCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (predicateExistsNotFormula
            (Base := Base) (Const := WithParams Const) tau p) := rfl

/-- Endpoint tightness for the concrete non-witness complement cut: lower
endpoint `1` is exactly provability of `∃ x, ¬ p x`. -/
theorem predicateCountingCapacityExistsNotComplementCut_lower_eq_one_iff_provable
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
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsNotComplementCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsNotFormula
          (Base := Base) (Const := WithParams Const) tau p) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsNotComplementCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for the concrete non-witness complement cut: upper
endpoint `0` is exactly provability of `¬ ∃ x, ¬ p x`. -/
theorem predicateCountingCapacityExistsNotComplementCut_upper_eq_zero_iff_provable_not
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
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsNotComplementCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsNotFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsNotComplementCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for the concrete non-witness complement
cut: lower endpoint `0` is exactly non-provability of `∃ x, ¬ p x`. -/
theorem predicateCountingCapacityExistsNotComplementCut_lower_eq_zero_iff_not_provable
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
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsNotComplementCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsNotFormula
          (Base := Base) (Const := WithParams Const) tau p) := by
  exact
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsNotComplementCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for the concrete non-witness complement
cut: upper endpoint `1` is exactly non-provability of `¬ ∃ x, ¬ p x`. -/
theorem predicateCountingCapacityExistsNotComplementCut_upper_eq_one_iff_not_provable_not
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
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsNotComplementCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsNotFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsNotComplementCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for the concrete non-witness complement cut: the
interval collapses exactly when the theory decides `∃ x, ¬ p x`. -/
theorem predicateCountingCapacityExistsNotComplementCut_width_eq_zero_iff_decides
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
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsNotComplementCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (predicateExistsNotFormula
          (Base := Base) (Const := WithParams Const) tau p) ∨
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (predicateExistsNotFormula
          (Base := Base) (Const := WithParams Const) tau p)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateCountingCapacityExistsNotComplementCut
        (Base := Base) (Const := Const) (T := T)
        tau p hp0 hObj hMeasurable N hNpos hCardEq)
      enum henum hCons hT0 hEM

/-- Exact-denominator finite-frequency band cut for normalized counting
capacity.

The lower formula `χLower` represents `kLower ≤ ncard(ext p)`.  The upper-side
formula `χUpper` represents `ncard(ext p) + kMissing ≤ N`, i.e. enough
complement mass remains.  Their conjunction therefore represents the rational
band
`kLower / N ≤ countingCapacity(ext p)` and
`kMissing / N ≤ 1 - countingCapacity(ext p)`.

The result is deliberately built by composing the two existing calibrated cuts
through `andCut`: this is a consumer package over certified threshold events,
not a new interval semantics. -/
noncomputable def predicateCountingCapacityCardinalityBandCut
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χLower χUpper : ClosedFormula (WithParams Const))
    (hχLower0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χLower)
    (hχUpper0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χUpper)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (kLower kMissing N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχLowerRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χLower ↔
          kLower ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (hχUpperRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χUpper ↔
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            kMissing ≤ N) :
    ExtensionalDefinableCut (Base := Base) (Const := Const) T :=
  (predicateCountingCapacityCardinalityThresholdCut
    (Base := Base) (Const := Const) (T := T)
    tau p χLower hχLower0 hObj hMeasurable kLower N hNpos hCardEq
    hχLowerRep).andCut
      (Base := Base) (Const := Const)
      (predicateCountingCapacityComplementCardinalityThresholdCut
        (Base := Base) (Const := Const) (T := T)
        tau p χUpper hχUpper0 hObj hMeasurable kMissing N hNpos hCardEq
        hχUpperRep)

/-- The exact-denominator band cut is true in a canonical model exactly when
both finite-cardinality side conditions hold there. -/
theorem predicateCountingCapacityCardinalityBandCut_ge_iff
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χLower χUpper : ClosedFormula (WithParams Const))
    (hχLower0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χLower)
    (hχUpper0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χUpper)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (kLower kMissing N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχLowerRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χLower ↔
          kLower ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (hχUpperRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χUpper ↔
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            kMissing ≤ N)
    (M : ExtensionalTheoryModel (Base := Base) (Const := Const) T) :
    (predicateCountingCapacityCardinalityBandCut
      (Base := Base) (Const := Const) (T := T)
      tau p χLower χUpper hχLower0 hχUpper0 hObj hMeasurable
      kLower kMissing N hNpos hCardEq hχLowerRep hχUpperRep).threshold ≤
        (predicateCountingCapacityCardinalityBandCut
          (Base := Base) (Const := Const) (T := T)
          tau p χLower χUpper hχLower0 hχUpper0 hObj hMeasurable
          kLower kMissing N hNpos hCardEq hχLowerRep hχUpperRep).score M ↔
      kLower ≤
          (predicateExtension
            (Base := Base) (Const := WithParams Const) M.1 tau p).ncard ∧
        (predicateExtension
            (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
          kMissing ≤ N := by
  classical
  let CLower :=
    predicateCountingCapacityCardinalityThresholdCut
      (Base := Base) (Const := Const) (T := T)
      tau p χLower hχLower0 hObj hMeasurable kLower N hNpos hCardEq
      hχLowerRep
  let CUpper :=
    predicateCountingCapacityComplementCardinalityThresholdCut
      (Base := Base) (Const := Const) (T := T)
      tau p χUpper hχUpper0 hObj hMeasurable kMissing N hNpos hCardEq
      hχUpperRep
  change (CLower.andCut (Base := Base) (Const := Const) CUpper).threshold ≤
        (CLower.andCut (Base := Base) (Const := Const) CUpper).score M ↔
      kLower ≤
          (predicateExtension
            (Base := Base) (Const := WithParams Const) M.1 tau p).ncard ∧
        (predicateExtension
            (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
          kMissing ≤ N
  rw [ExtensionalDefinableCut.andCut_ge_iff]
  constructor
  · intro hBoth
    exact
      ⟨(hχLowerRep M).1 ((CLower.represents_ge M).2 hBoth.1),
        (hχUpperRep M).1 ((CUpper.represents_ge M).2 hBoth.2)⟩
  · intro hBoth
    exact
      ⟨(CLower.represents_ge M).1 ((hχLowerRep M).2 hBoth.1),
        (CUpper.represents_ge M).1 ((hχUpperRep M).2 hBoth.2)⟩

/-- The calibrated finite-frequency band cut reads out through the existing
HOL interval for the conjunction of its supplied lower and upper formulas. -/
theorem predicateCountingCapacityCardinalityBandCut_intervalOfConsistent
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χLower χUpper : ClosedFormula (WithParams Const))
    (hχLower0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χLower)
    (hχUpper0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χUpper)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (kLower kMissing N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχLowerRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χLower ↔
          kLower ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (hχUpperRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χUpper ↔
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            kMissing ≤ N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p χLower χUpper hχLower0 hχUpper0 hObj hMeasurable
        kLower kMissing N hNpos hCardEq hχLowerRep hχUpperRep)
      enum henum hCons hT0 hEM =
        extensionalTheoryCredalHOLFormulaIntervalOfConsistent
          (Base := Base) (Const := Const) T enum henum hCons hT0 hEM
          (.and χLower χUpper) := rfl

/-- Endpoint tightness for exact-denominator finite-frequency bands: lower
endpoint `1` is exactly provability of the supplied lower/upper cardinality
conjunction.

This theorem is deliberately a thin specialization of
`ExtensionalDefinableCut.lower_eq_one_iff_provable`; the mathematical content
is the already-certified `represents_ge` field of
`predicateCountingCapacityCardinalityBandCut`. -/
theorem predicateCountingCapacityCardinalityBandCut_lower_eq_one_iff_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χLower χUpper : ClosedFormula (WithParams Const))
    (hχLower0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χLower)
    (hχUpper0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χUpper)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (kLower kMissing N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχLowerRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χLower ↔
          kLower ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (hχUpperRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χUpper ↔
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            kMissing ≤ N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p χLower χUpper hχLower0 hχUpper0 hObj hMeasurable
        kLower kMissing N hNpos hCardEq hχLowerRep hχUpperRep)
      enum henum hCons hT0 hEM).lower = 1 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.and χLower χUpper) := by
  exact
    ExtensionalDefinableCut.lower_eq_one_iff_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p χLower χUpper hχLower0 hχUpper0 hObj hMeasurable
        kLower kMissing N hNpos hCardEq hχLowerRep hχUpperRep)
      enum henum hCons hT0 hEM

/-- Endpoint tightness for exact-denominator finite-frequency bands: upper
endpoint `0` is exactly provability of the negation of the supplied
lower/upper cardinality conjunction. -/
theorem predicateCountingCapacityCardinalityBandCut_upper_eq_zero_iff_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χLower χUpper : ClosedFormula (WithParams Const))
    (hχLower0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χLower)
    (hχUpper0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χUpper)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (kLower kMissing N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχLowerRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χLower ↔
          kLower ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (hχUpperRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χUpper ↔
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            kMissing ≤ N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p χLower χUpper hχLower0 hχUpper0 hObj hMeasurable
        kLower kMissing N hNpos hCardEq hχLowerRep hχUpperRep)
      enum henum hCons hT0 hEM).upper = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (.and χLower χUpper)) := by
  exact
    ExtensionalDefinableCut.upper_eq_zero_iff_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p χLower χUpper hχLower0 hχUpper0 hObj hMeasurable
        kLower kMissing N hNpos hCardEq hχLowerRep hχUpperRep)
      enum henum hCons hT0 hEM

/-- Open lower-endpoint tightness for exact-denominator finite-frequency
bands: lower endpoint `0` is exactly non-provability of the supplied
lower/upper cardinality conjunction. -/
theorem predicateCountingCapacityCardinalityBandCut_lower_eq_zero_iff_not_provable
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χLower χUpper : ClosedFormula (WithParams Const))
    (hχLower0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χLower)
    (hχUpper0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χUpper)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (kLower kMissing N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχLowerRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χLower ↔
          kLower ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (hχUpperRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χUpper ↔
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            kMissing ≤ N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p χLower χUpper hχLower0 hχUpper0 hObj hMeasurable
        kLower kMissing N hNpos hCardEq hχLowerRep hχUpperRep)
      enum henum hCons hT0 hEM).lower = 0 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.and χLower χUpper) := by
  exact
    ExtensionalDefinableCut.lower_eq_zero_iff_not_provable
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p χLower χUpper hχLower0 hχUpper0 hObj hMeasurable
        kLower kMissing N hNpos hCardEq hχLowerRep hχUpperRep)
      enum henum hCons hT0 hEM

/-- Open upper-endpoint tightness for exact-denominator finite-frequency
bands: upper endpoint `1` is exactly non-provability of the negation of the
supplied lower/upper cardinality conjunction. -/
theorem predicateCountingCapacityCardinalityBandCut_upper_eq_one_iff_not_provable_not
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χLower χUpper : ClosedFormula (WithParams Const))
    (hχLower0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χLower)
    (hχUpper0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χUpper)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (kLower kMissing N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχLowerRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χLower ↔
          kLower ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (hχUpperRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χUpper ↔
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            kMissing ≤ N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p χLower χUpper hχLower0 hχUpper0 hObj hMeasurable
        kLower kMissing N hNpos hCardEq hχLowerRep hχUpperRep)
      enum henum hCons hT0 hEM).upper = 1 ↔
      ¬ ClosedTheorySet.Provable (Const := WithParams Const) T
        (.not (.and χLower χUpper)) := by
  exact
    ExtensionalDefinableCut.upper_eq_one_iff_not_provable_not
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p χLower χUpper hχLower0 hχUpper0 hObj hMeasurable
        kLower kMissing N hNpos hCardEq hχLowerRep hχUpperRep)
      enum henum hCons hT0 hEM

/-- Width-zero tightness for exact-denominator finite-frequency bands: the
certified band interval collapses exactly when the theory decides the supplied
lower/upper cardinality conjunction. -/
theorem predicateCountingCapacityCardinalityBandCut_width_eq_zero_iff_decides
    {T : ClosedTheorySet (WithParams Const)}
    (tau : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := WithParams Const) tau)
    (χLower χUpper : ClosedFormula (WithParams Const))
    (hχLower0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χLower)
    (hχUpper0 : ∀ (ρ : Ty Base) (i : Nat),
      NoConstOccurrence (param ρ i) χUpper)
    (hObj : ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
      Fintype (PredicateObject
        (Base := Base) (Const := WithParams Const) M.1 tau))
    (hMeasurable :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        MeasurableSpace (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau))
    (kLower kMissing N : Nat) (hNpos : 0 < N)
    (hCardEq :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        Fintype.card (PredicateObject
          (Base := Base) (Const := WithParams Const) M.1 tau) = N)
    (hχLowerRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χLower ↔
          kLower ≤
            (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard)
    (hχUpperRep :
      ∀ M : ExtensionalTheoryModel (Base := Base) (Const := Const) T,
        HenkinModel.models M.1 χUpper ↔
          (predicateExtension
              (Base := Base) (Const := WithParams Const) M.1 tau p).ncard +
            kMissing ≤ N)
    (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : ClosedTheorySet.Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (i : Nat), NoConstOccurrence (param σ i) ψ)
    (hEM : ∀ ψ ∈ EMSchema Const, ψ ∈ T) :
    (ExtensionalDefinableCut.intervalOfConsistent
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p χLower χUpper hχLower0 hχUpper0 hObj hMeasurable
        kLower kMissing N hNpos hCardEq hχLowerRep hχUpperRep)
      enum henum hCons hT0 hEM).width = 0 ↔
      ClosedTheorySet.Provable (Const := WithParams Const) T
          (.and χLower χUpper) ∨
        ClosedTheorySet.Provable (Const := WithParams Const) T
          (.not (.and χLower χUpper)) := by
  exact
    ExtensionalDefinableCut.width_eq_zero_iff_decides
      (Base := Base) (Const := Const)
      (predicateCountingCapacityCardinalityBandCut
        (Base := Base) (Const := Const) (T := T)
        tau p χLower χUpper hχLower0 hχUpper0 hObj hMeasurable
        kLower kMissing N hNpos hCardEq hχLowerRep hχUpperRep)
      enum henum hCons hT0 hEM


end Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOLDefinableCuts
