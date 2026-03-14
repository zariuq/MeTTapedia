import Mathlib.Topology.UnitInterval
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Data.Fintype.Card

/-!
# Fuzzy Measure Core

Shared core for finite and arbitrary-domain fuzzy quantifier semantics.

This file introduces:

- Chapter-11 fuzzy quantifier parameters and proxy predicates
- `[0,1]`-valued profiles
- capacity-style fuzzy measures on crisp subsets
- normalized counting capacity as the finite-domain instance
- simple profile combinators used by both the finite and infinitary layers
-/

namespace Mettapedia.Logic.PLNFirstOrder

open Classical
open scoped unitInterval

/-- Chapter-11 fuzzy quantifier parameters for the arbitrary-domain fuzzy layer. -/
structure FuzzyQuantifierParamsInf where
  ε : ℝ
  LPC : ℝ
  UPC : ℝ
  PCL : ℝ
  hε : 0 ≤ ε ∧ ε ≤ 1
  hLPC : 0 ≤ LPC ∧ LPC ≤ 1
  hUPC : 0 ≤ UPC ∧ UPC ≤ 1
  hPCL : 0 ≤ PCL ∧ PCL ≤ 1
  hLPC_le_UPC : LPC ≤ UPC

/-- Numeric proxy for being "essentially true" (`≈ 1`). -/
def nearOneInf (p : FuzzyQuantifierParamsInf) (x : ℝ) : Prop :=
  1 - p.ε ≤ x ∧ x ≤ 1

/-- Numeric proxy for being "essentially false" (`≈ 0`). -/
def nearZeroInf (p : FuzzyQuantifierParamsInf) (x : ℝ) : Prop :=
  0 ≤ x ∧ x ≤ p.ε

/-- Duality at the proxy level: "near zero" in `x` is equivalent to
"near one" in `1 - x`. -/
theorem nearZeroInf_iff_nearOneInf_one_sub
    (p : FuzzyQuantifierParamsInf) (x : ℝ) :
    nearZeroInf p x ↔ nearOneInf p (1 - x) := by
  unfold nearZeroInf nearOneInf
  constructor
  · intro hx
    constructor <;> linarith [hx.1, hx.2]
  · intro hx
    constructor <;> linarith [hx.1, hx.2]

/-- Bundled fuzzy profile with values in the unit interval. -/
structure FuzzyProfile (U : Type*) where
  eval : U → I

namespace FuzzyProfile

variable {U : Type*}

instance : CoeFun (FuzzyProfile U) (fun _ => U → I) := ⟨FuzzyProfile.eval⟩

/-- Build a fuzzy profile from an `ℝ`-valued function together with pointwise `[0,1]` bounds. -/
def ofFn (f : U → ℝ) (hf : ∀ u, f u ∈ (I : Set ℝ)) : FuzzyProfile U :=
  ⟨fun u => ⟨f u, hf u⟩⟩

/-- Constant fuzzy profile. -/
def const (x : I) : FuzzyProfile U :=
  ⟨fun _ => x⟩

/-- Pointwise complement profile `u ↦ 1 - f u`. -/
def compl (f : FuzzyProfile U) : FuzzyProfile U :=
  ⟨fun u => ⟨1 - (f u : ℝ), by
      constructor
      · linarith [show (f u : ℝ) ≤ 1 from unitInterval.le_one (f u)]
      · linarith [show (0 : ℝ) ≤ f u from unitInterval.nonneg (f u)]⟩⟩

/-- Crisp indicator profile of a subset. -/
noncomputable def crispIndicator (A : Set U) : FuzzyProfile U :=
  ⟨fun u => if u ∈ A then (1 : I) else (0 : I)⟩

/-- Threshold cut `{u | t ≤ f u}`. -/
def thresholdCut (t : I) (f : FuzzyProfile U) : Set U :=
  {u | t ≤ f u}

@[simp] theorem ofFn_eval (f : U → ℝ) (hf : ∀ u, f u ∈ (I : Set ℝ)) (u : U) :
    ((ofFn f hf) u : ℝ) = f u := rfl

@[simp] theorem const_apply (x : I) (u : U) :
    const x u = x := rfl

@[simp] theorem compl_apply (f : FuzzyProfile U) (u : U) :
    ((compl f) u : ℝ) = 1 - (f u : ℝ) := rfl

@[simp] theorem crispIndicator_apply_mem (A : Set U) {u : U} (hu : u ∈ A) :
    crispIndicator A u = (1 : I) := by
  simp [crispIndicator, hu]

@[simp] theorem crispIndicator_apply_not_mem (A : Set U) {u : U} (hu : u ∉ A) :
    crispIndicator A u = (0 : I) := by
  simp [crispIndicator, hu]

@[simp] theorem thresholdCut_def (t : I) (f : FuzzyProfile U) :
    thresholdCut t f = {u | t ≤ f u} := rfl

end FuzzyProfile

/-- Capacity-style fuzzy measure on crisp subsets of a domain. -/
structure FuzzyCapacity (U : Type*) [MeasurableSpace U] where
  cap : Set U → I
  cap_empty : cap ∅ = 0
  mono : ∀ ⦃A B : Set U⦄, A ⊆ B → cap A ≤ cap B

namespace FuzzyCapacity

variable {U : Type*} [MeasurableSpace U]

instance : CoeFun (FuzzyCapacity U) (fun _ => Set U → I) := ⟨FuzzyCapacity.cap⟩

/-- Optional normalization predicate, separated from the core capacity structure
so the empty finite domain can still be modeled honestly. -/
def IsNormalized (ν : FuzzyCapacity U) : Prop :=
  ν Set.univ = 1

theorem cap_nonneg (ν : FuzzyCapacity U) (A : Set U) :
    0 ≤ (ν A : ℝ) :=
  unitInterval.nonneg (ν A)

theorem cap_le_one (ν : FuzzyCapacity U) (A : Set U) :
    (ν A : ℝ) ≤ 1 :=
  unitInterval.le_one (ν A)

theorem cap_empty_eq_zero (ν : FuzzyCapacity U) :
    ν ∅ = 0 :=
  ν.cap_empty

theorem cap_univ_le_one (ν : FuzzyCapacity U) :
    (ν Set.univ : ℝ) ≤ 1 :=
  cap_le_one ν Set.univ

section Counting

variable [Fintype U]

omit [MeasurableSpace U] in
/-- Cardinality monotonicity for finite subsets. -/
theorem card_set_mono {A B : Set U} (hAB : A ⊆ B) :
    Fintype.card A ≤ Fintype.card B := by
  classical
  refine Fintype.card_le_of_injective
    (fun x : A => (⟨x.1, hAB x.2⟩ : B)) ?_
  intro x y hxy
  cases x
  cases y
  simp at hxy
  simp [hxy]

/-- The normalized counting value of a finite subset. -/
noncomputable def countingValue (A : Set U) : I :=
  if h0 : Fintype.card U = 0 then
    (0 : I)
  else
    ⟨(Fintype.card A : ℝ) / (Fintype.card U : ℝ), by
      constructor
      · have hden_nonneg : 0 ≤ (Fintype.card U : ℝ) := by positivity
        positivity
      · have hden_pos_nat : 0 < Fintype.card U := Nat.pos_of_ne_zero h0
        have hden_pos : 0 < (Fintype.card U : ℝ) := by
          exact_mod_cast hden_pos_nat
        have hnum_le_nat : Fintype.card A ≤ Fintype.card U := by
          simpa using (Fintype.card_subtype_le (p := fun u => u ∈ A))
        have hnum_le : (Fintype.card A : ℝ) ≤ (Fintype.card U : ℝ) := by
          exact_mod_cast hnum_le_nat
        have hdiv' :
            (Fintype.card A : ℝ) / (Fintype.card U : ℝ) ≤
              (Fintype.card U : ℝ) / (Fintype.card U : ℝ) := by
          exact div_le_div_of_nonneg_right hnum_le (le_of_lt hden_pos)
        have hden_ne : (Fintype.card U : ℝ) ≠ 0 := ne_of_gt hden_pos
        simpa [hden_ne] using hdiv'⟩

omit [MeasurableSpace U] in
@[simp] theorem countingValue_empty :
    countingValue (U := U) (∅ : Set U) = 0 := by
  classical
  unfold countingValue
  by_cases h0 : Fintype.card U = 0
  · simp [h0]
  · simp [h0]

omit [MeasurableSpace U] in
theorem countingValue_mono {A B : Set U} (hAB : A ⊆ B) :
    countingValue (U := U) A ≤ countingValue (U := U) B := by
  classical
  unfold countingValue
  by_cases h0 : Fintype.card U = 0
  · simp [h0]
  · have hden_nonneg : 0 ≤ (Fintype.card U : ℝ) := by positivity
    have hcard : Fintype.card A ≤ Fintype.card B := card_set_mono hAB
    have hcard' : (Fintype.card A : ℝ) ≤ (Fintype.card B : ℝ) := by
      exact_mod_cast hcard
    simpa [Subtype.mk_le_mk, h0] using
      (div_le_div_of_nonneg_right hcard' hden_nonneg)

/-- Normalized counting capacity, which becomes a normalized capacity on nonempty finite domains. -/
noncomputable def countingCapacity : FuzzyCapacity U where
  cap := countingValue
  cap_empty := countingValue_empty (U := U)
  mono := by
    intro A B hAB
    exact countingValue_mono (U := U) hAB

theorem countingCapacity_isNormalized [Nonempty U] :
    IsNormalized (countingCapacity (U := U)) := by
  classical
  unfold IsNormalized countingCapacity
  change countingValue (U := U) Set.univ = (1 : I)
  have h0 : Fintype.card U ≠ 0 := by
    exact Nat.ne_of_gt (Fintype.card_pos_iff.mpr ‹Nonempty U›)
  unfold countingValue
  have hden_ne : (Fintype.card U : ℝ) ≠ 0 := by
    exact_mod_cast h0
  apply Subtype.ext
  simp [h0]
  have hfilter :
      @Finset.filter U (Membership.mem Set.univ) (fun a => propDecidable (a ∈ Set.univ))
          Finset.univ = (@Finset.univ U inferInstance) := by
    ext u
    simp
  calc
    ((@Finset.filter U (Membership.mem Set.univ) (fun a => propDecidable (a ∈ Set.univ))
        Finset.univ).card : ℝ) /
        (Fintype.card U : ℝ)
        = (Fintype.card U : ℝ) / (Fintype.card U : ℝ) := by
            rw [hfilter, Finset.card_univ]
    _ = 1 := by field_simp [hden_ne]

end Counting

end FuzzyCapacity

end Mettapedia.Logic.PLNFirstOrder
