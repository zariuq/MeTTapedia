import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Receipt
import Mathlib.Algebra.Order.Quantale

/-!
# Derived valuations of causal cost receipts

The runtime records only the free commutative-monoid signature measure.  An
additive effort-object interpretation or a multiplicative quantale
interpretation is constructed by folding weights assigned to ground signing
authorities.  Composition and location laws below are consequences of these
folds; they are not assumptions stored in a valuation interface.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

open scoped BigOperators

universe u v w x

namespace CostSig

/-- Universal additive interpretation of a signature multiset. -/
def additiveFold {Ground : Type u} {Delta : Type x} [AddCommMonoid Delta]
    (weight : Ground → Delta) (sig : CostSig Ground) : Delta :=
  (sig.map weight).sum

@[simp]
theorem additiveFold_zero {Ground : Type u} {Delta : Type x} [AddCommMonoid Delta]
    (weight : Ground → Delta) : additiveFold weight (0 : CostSig Ground) = 0 := by
  simp [additiveFold]

theorem additiveFold_add {Ground : Type u} {Delta : Type x} [AddCommMonoid Delta]
    (weight : Ground → Delta) (left right : CostSig Ground) :
    additiveFold weight (left + right) =
      additiveFold weight left + additiveFold weight right := by
  simp [additiveFold]

@[simp]
theorem additiveFold_singleton {Ground : Type u} {Delta : Type x} [AddCommMonoid Delta]
    (weight : Ground → Delta) (ground : Ground) :
    additiveFold weight ({ground} : CostSig Ground) = weight ground := by
  simp [additiveFold]

theorem additiveFold_finset_sum {Ground : Type u} {Delta : Type x}
    {Index : Type*} [DecidableEq Index] [AddCommMonoid Delta]
    (weight : Ground → Delta) (region : Finset Index)
    (value : Index → CostSig Ground) :
    additiveFold weight (∑ index ∈ region, value index) =
      ∑ index ∈ region, additiveFold weight (value index) := by
  induction region using Finset.induction with
  | empty => simp
  | @insert index region fresh ih =>
      simp [fresh, additiveFold_add, ih]

/-- Universal multiplicative interpretation of a signature multiset. -/
def multiplicativeFold {Ground : Type u} {Delta : Type x} [CommMonoid Delta]
    (weight : Ground → Delta) (sig : CostSig Ground) : Delta :=
  (sig.map weight).prod

@[simp]
theorem multiplicativeFold_zero {Ground : Type u} {Delta : Type x} [CommMonoid Delta]
    (weight : Ground → Delta) : multiplicativeFold weight (0 : CostSig Ground) = 1 := by
  simp [multiplicativeFold]

theorem multiplicativeFold_add {Ground : Type u} {Delta : Type x} [CommMonoid Delta]
    (weight : Ground → Delta) (left right : CostSig Ground) :
    multiplicativeFold weight (left + right) =
      multiplicativeFold weight left * multiplicativeFold weight right := by
  simp [multiplicativeFold]

@[simp]
theorem multiplicativeFold_singleton {Ground : Type u} {Delta : Type x} [CommMonoid Delta]
    (weight : Ground → Delta) (ground : Ground) :
    multiplicativeFold weight ({ground} : CostSig Ground) = weight ground := by
  simp [multiplicativeFold]

theorem multiplicativeFold_finset_sum {Ground : Type u} {Delta : Type x}
    {Index : Type*} [DecidableEq Index] [CommMonoid Delta]
    (weight : Ground → Delta) (region : Finset Index)
    (value : Index → CostSig Ground) :
    multiplicativeFold weight (∑ index ∈ region, value index) =
      ∏ index ∈ region, multiplicativeFold weight (value index) := by
  induction region using Finset.induction with
  | empty => simp
  | @insert index region fresh ih =>
      simp [fresh, multiplicativeFold_add, ih]

end CostSig

namespace CausalReceipt

variable {Event : Type w} {Other : Type*} {Ground : Type u} {Location : Type v}
    [Fintype Event] [Fintype Other]

/-- Parallel composition combines the complete raw measures. -/
theorem totalRawMeasure_parallel
    [DecidableEq Event] [DecidableEq Other]
    (left : CausalReceipt Event Ground Location)
    (right : CausalReceipt Other Ground Location) :
    (left.parallel right).totalRawMeasure =
      left.totalRawMeasure + right.totalRawMeasure := by
  simp [totalRawMeasure, rawMeasure, parallel]

/-- Sequential composition changes causal order but combines the same raw measures. -/
theorem totalRawMeasure_sequential
    [DecidableEq Event] [DecidableEq Other]
    (left : CausalReceipt Event Ground Location)
    (right : CausalReceipt Other Ground Location) :
    (left.sequential right).totalRawMeasure =
      left.totalRawMeasure + right.totalRawMeasure := by
  simp [totalRawMeasure, rawMeasure, sequential]

/-- Additive interpretation of a finite receipt region. -/
def additiveValue {Delta : Type x} [AddCommMonoid Delta] [DecidableEq Event]
    (receipt : CausalReceipt Event Ground Location) (weight : Ground → Delta)
    (region : Finset Event) : Delta :=
  CostSig.additiveFold weight (receipt.rawMeasure region)

/-- Additive interpretation of a complete finite receipt. -/
def totalAdditiveValue {Delta : Type x} [AddCommMonoid Delta]
    [DecidableEq Event]
    (receipt : CausalReceipt Event Ground Location) (weight : Ground → Delta) : Delta :=
  CostSig.additiveFold weight receipt.totalRawMeasure

/-- Multiplicative interpretation of a finite receipt region. -/
def multiplicativeValue {Delta : Type x} [CommMonoid Delta] [DecidableEq Event]
    (receipt : CausalReceipt Event Ground Location) (weight : Ground → Delta)
    (region : Finset Event) : Delta :=
  CostSig.multiplicativeFold weight (receipt.rawMeasure region)

/-- Multiplicative interpretation of a complete finite receipt. -/
def totalMultiplicativeValue {Delta : Type x} [CommMonoid Delta]
    [DecidableEq Event]
    (receipt : CausalReceipt Event Ground Location) (weight : Ground → Delta) : Delta :=
  CostSig.multiplicativeFold weight receipt.totalRawMeasure

/-- Additive valuations derive the parallel-composition law. -/
theorem totalAdditiveValue_parallel {Delta : Type x} [AddCommMonoid Delta]
    [DecidableEq Event] [DecidableEq Other]
    (left : CausalReceipt Event Ground Location)
    (right : CausalReceipt Other Ground Location) (weight : Ground → Delta) :
    (left.parallel right).totalAdditiveValue weight =
      left.totalAdditiveValue weight + right.totalAdditiveValue weight := by
  simp [totalAdditiveValue, totalRawMeasure_parallel, CostSig.additiveFold_add]

/-- Additive valuations derive the sequential-composition law. -/
theorem totalAdditiveValue_sequential {Delta : Type x} [AddCommMonoid Delta]
    [DecidableEq Event] [DecidableEq Other]
    (left : CausalReceipt Event Ground Location)
    (right : CausalReceipt Other Ground Location) (weight : Ground → Delta) :
    (left.sequential right).totalAdditiveValue weight =
      left.totalAdditiveValue weight + right.totalAdditiveValue weight := by
  simp [totalAdditiveValue, totalRawMeasure_sequential, CostSig.additiveFold_add]

/-- Multiplicative valuations derive the parallel-composition law. -/
theorem totalMultiplicativeValue_parallel {Delta : Type x} [CommMonoid Delta]
    [DecidableEq Event] [DecidableEq Other]
    (left : CausalReceipt Event Ground Location)
    (right : CausalReceipt Other Ground Location) (weight : Ground → Delta) :
    (left.parallel right).totalMultiplicativeValue weight =
      left.totalMultiplicativeValue weight * right.totalMultiplicativeValue weight := by
  simp [totalMultiplicativeValue, totalRawMeasure_parallel,
    CostSig.multiplicativeFold_add]

/-- Multiplicative valuations derive the sequential-composition law. -/
theorem totalMultiplicativeValue_sequential {Delta : Type x} [CommMonoid Delta]
    [DecidableEq Event] [DecidableEq Other]
    (left : CausalReceipt Event Ground Location)
    (right : CausalReceipt Other Ground Location) (weight : Ground → Delta) :
    (left.sequential right).totalMultiplicativeValue weight =
      left.totalMultiplicativeValue weight * right.totalMultiplicativeValue weight := by
  simp [totalMultiplicativeValue, totalRawMeasure_sequential,
    CostSig.multiplicativeFold_add]

/-- The additive universal fold commutes with per-location restriction. -/
theorem additive_restriction_gluing {Delta : Type x} [AddCommMonoid Delta]
    [DecidableEq Event] [DecidableEq Location]
    (receipt : CausalReceipt Event Ground Location) (weight : Ground → Delta)
    (location : Location) (region : Finset Event) :
    CostSig.additiveFold weight (receipt.rawMeasureAt location region) =
      ∑ event ∈ region,
        CostSig.additiveFold weight ((receipt.label event).rawSpendAt location) := by
  induction region using Finset.induction with
  | empty => simp [rawMeasureAt]
  | @insert event region hnotmem ih =>
      rw [rawMeasureAt, Finset.sum_insert hnotmem, CostSig.additiveFold_add,
        Finset.sum_insert hnotmem]
      congr 1

/-- The multiplicative universal fold commutes with per-location restriction. -/
theorem multiplicative_restriction_gluing {Delta : Type x} [CommMonoid Delta]
    [DecidableEq Event] [DecidableEq Location]
    (receipt : CausalReceipt Event Ground Location) (weight : Ground → Delta)
    (location : Location) (region : Finset Event) :
    CostSig.multiplicativeFold weight (receipt.rawMeasureAt location region) =
      ∏ event ∈ region,
        CostSig.multiplicativeFold weight ((receipt.label event).rawSpendAt location) := by
  induction region using Finset.induction with
  | empty => simp [rawMeasureAt]
  | @insert event region hnotmem ih =>
      rw [rawMeasureAt, Finset.sum_insert hnotmem, CostSig.multiplicativeFold_add,
        Finset.prod_insert hnotmem]
      congr 1

/-- All local additive interpretations glue to the global interpretation.
Repeated contributions at one location retain their multiplicity before the
finite location sum is taken. -/
theorem additive_global_gluing {Delta : Type x} [AddCommMonoid Delta]
    [DecidableEq Event] [Fintype Location] [DecidableEq Location]
    (receipt : CausalReceipt Event Ground Location) (weight : Ground → Delta)
    (region : Finset Event) :
    (∑ location : Location,
      CostSig.additiveFold weight (receipt.rawMeasureAt location region)) =
      CostSig.additiveFold weight (receipt.rawMeasure region) := by
  calc
    (∑ location : Location,
        CostSig.additiveFold weight (receipt.rawMeasureAt location region)) =
        CostSig.additiveFold weight
          (∑ location : Location, receipt.rawMeasureAt location region) := by
      symm
      simpa using CostSig.additiveFold_finset_sum weight Finset.univ
        (fun location : Location => receipt.rawMeasureAt location region)
    _ = CostSig.additiveFold weight (receipt.rawMeasure region) := by
      rw [receipt.sum_rawMeasureAt_eq_rawMeasure]

/-- All local multiplicative interpretations glue to the global
interpretation over the same operational receipt. -/
theorem multiplicative_global_gluing {Delta : Type x} [CommMonoid Delta]
    [DecidableEq Event] [Fintype Location] [DecidableEq Location]
    (receipt : CausalReceipt Event Ground Location) (weight : Ground → Delta)
    (region : Finset Event) :
    (∏ location : Location,
      CostSig.multiplicativeFold weight (receipt.rawMeasureAt location region)) =
      CostSig.multiplicativeFold weight (receipt.rawMeasure region) := by
  calc
    (∏ location : Location,
        CostSig.multiplicativeFold weight (receipt.rawMeasureAt location region)) =
        CostSig.multiplicativeFold weight
          (∑ location : Location, receipt.rawMeasureAt location region) := by
      symm
      simpa using CostSig.multiplicativeFold_finset_sum weight Finset.univ
        (fun location : Location => receipt.rawMeasureAt location region)
    _ = CostSig.multiplicativeFold weight (receipt.rawMeasure region) := by
      rw [receipt.sum_rawMeasureAt_eq_rawMeasure]

/-- Finite-support additive gluing works for opaque, potentially infinite
location types such as rho names. -/
theorem additive_fundingSupport_gluing
    {Delta : Type x} [AddCommMonoid Delta]
    [DecidableEq Event] [DecidableEq Location]
    (receipt : CausalReceipt Event Ground Location) (weight : Ground → Delta)
    (region : Finset Event) :
    (∑ location ∈ receipt.fundingLocations region,
      CostSig.additiveFold weight (receipt.rawMeasureAt location region)) =
      CostSig.additiveFold weight (receipt.rawMeasure region) := by
  calc
    (∑ location ∈ receipt.fundingLocations region,
        CostSig.additiveFold weight (receipt.rawMeasureAt location region)) =
        CostSig.additiveFold weight
          (∑ location ∈ receipt.fundingLocations region,
            receipt.rawMeasureAt location region) := by
      symm
      exact CostSig.additiveFold_finset_sum weight
        (receipt.fundingLocations region)
        (fun location => receipt.rawMeasureAt location region)
    _ = CostSig.additiveFold weight (receipt.rawMeasure region) := by
      rw [receipt.sum_rawMeasureAt_fundingLocations_eq_rawMeasure]

/-- Finite-support multiplicative gluing uses the same located receipt. -/
theorem multiplicative_fundingSupport_gluing
    {Delta : Type x} [CommMonoid Delta]
    [DecidableEq Event] [DecidableEq Location]
    (receipt : CausalReceipt Event Ground Location) (weight : Ground → Delta)
    (region : Finset Event) :
    (∏ location ∈ receipt.fundingLocations region,
      CostSig.multiplicativeFold weight (receipt.rawMeasureAt location region)) =
      CostSig.multiplicativeFold weight (receipt.rawMeasure region) := by
  calc
    (∏ location ∈ receipt.fundingLocations region,
        CostSig.multiplicativeFold weight (receipt.rawMeasureAt location region)) =
        CostSig.multiplicativeFold weight
          (∑ location ∈ receipt.fundingLocations region,
            receipt.rawMeasureAt location region) := by
      symm
      exact CostSig.multiplicativeFold_finset_sum weight
        (receipt.fundingLocations region)
        (fun location => receipt.rawMeasureAt location region)
    _ = CostSig.multiplicativeFold weight (receipt.rawMeasure region) := by
      rw [receipt.sum_rawMeasureAt_fundingLocations_eq_rawMeasure]

/-- Additive interpreted totals are invariant under event-identity relabeling. -/
theorem totalAdditiveValue_relabel {OtherId : Type*} {Delta : Type x}
    [AddCommMonoid Delta] [DecidableEq Event]
    [Fintype OtherId] [DecidableEq OtherId]
    (receipt : CausalReceipt Event Ground Location) (ids : Event ≃ OtherId)
    (weight : Ground → Delta) :
    (receipt.relabel ids).totalAdditiveValue weight =
      receipt.totalAdditiveValue weight := by
  simp [totalAdditiveValue, totalRawMeasure_relabel]

/-- Multiplicative interpreted totals are invariant under event-identity relabeling. -/
theorem totalMultiplicativeValue_relabel {OtherId : Type*} {Delta : Type x}
    [CommMonoid Delta] [DecidableEq Event]
    [Fintype OtherId] [DecidableEq OtherId]
    (receipt : CausalReceipt Event Ground Location) (ids : Event ≃ OtherId)
    (weight : Ground → Delta) :
    (receipt.relabel ids).totalMultiplicativeValue weight =
      receipt.totalMultiplicativeValue weight := by
  simp [totalMultiplicativeValue, totalRawMeasure_relabel]

/-! ### Downstream effort-object and quantale readings -/

/-- Remaining effort-object budget after interpreting the complete receipt. -/
def remainingBudget {Delta : Type x} [AddCommGroup Delta]
    [DecidableEq Event]
    (receipt : CausalReceipt Event Ground Location) (weight : Ground → Delta)
    (initial : Delta) : Delta :=
  initial - receipt.totalAdditiveValue weight

/-- Eventwise quantale total.  Completeness and distributivity belong to the
target interpretation; the operational receipt itself remains signature-valued. -/
def totalQuantaleValue {Delta : Type x} [CommMonoid Delta]
    [CompleteLattice Delta] [IsQuantale Delta]
    [DecidableEq Event]
    (receipt : CausalReceipt Event Ground Location) (weight : Ground → Delta) : Delta :=
  receipt.totalMultiplicativeValue weight

/-- Quantale totals inherit parallel compositionality from the universal fold. -/
theorem totalQuantaleValue_parallel {Delta : Type x} [CommMonoid Delta]
    [CompleteLattice Delta] [IsQuantale Delta]
    [DecidableEq Event] [DecidableEq Other]
    (left : CausalReceipt Event Ground Location)
    (right : CausalReceipt Other Ground Location) (weight : Ground → Delta) :
    (left.parallel right).totalQuantaleValue weight =
      left.totalQuantaleValue weight * right.totalQuantaleValue weight :=
  left.totalMultiplicativeValue_parallel right weight

/-- Quantale totals inherit sequential compositionality from the universal fold. -/
theorem totalQuantaleValue_sequential {Delta : Type x} [CommMonoid Delta]
    [CompleteLattice Delta] [IsQuantale Delta]
    [DecidableEq Event] [DecidableEq Other]
    (left : CausalReceipt Event Ground Location)
    (right : CausalReceipt Other Ground Location) (weight : Ground → Delta) :
    (left.sequential right).totalQuantaleValue weight =
      left.totalQuantaleValue weight * right.totalQuantaleValue weight :=
  left.totalMultiplicativeValue_sequential right weight

end CausalReceipt

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
