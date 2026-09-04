import Mettapedia.CategoryTheory.GlobularSet

/-!
# Local truncation certificates in an unbounded globular tower

A thin comparison layer is a local theorem, not a global ceiling on higher
cells.  This module makes that distinction precise for globular sets.

At one boundary dimension, local thinness is equivalent to saying that every
proposition-valued observer is invariant on parallel cells.  A checked local
thinness certificate therefore licenses erasure of an inhabited boundary
fibre to `Unit`, with every observer factoring through that erasure.

The construction `ThinBelowThickNext` supplies the negative control: for every
finite horizon there is a globular tower that is locally thin at every lower
dimension and has two distinct parallel cells immediately above the horizon.
Thus no finite collection of thinness results proves a global truncation.

This is deliberately a theorem about the raw globular boundary shape.  It
does not claim to construct a weak omega-category, its compositions, or its
coherences.  Those structures must be supplied by the selected higher
categorical semantics.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.Higher

namespace GlobularSet

universe u v

/-- Local thinness at every boundary dimension strictly below a finite
horizon. -/
def ThinBelow (tower : GlobularSet.{u}) (horizon : Nat) : Prop :=
  ∀ dimension, dimension < horizon → tower.LocallyThinAt dimension

/-- An observer cannot distinguish any two parallel cells in one fixed
boundary fibre. -/
def ObserverErasureSafe (tower : GlobularSet.{u}) (dimension : Nat)
    (sourceCell targetCell : tower.Cell dimension) {Result : Type v}
    (observe : tower.BoundaryFiber dimension sourceCell targetCell → Result) :
    Prop :=
  ∀ first second, observe first = observe second

/-- Thinness makes every observer of every parallel-cell fibre insensitive to
cell identity. -/
theorem observerErasureSafe_of_locallyThinAt
    (tower : GlobularSet.{u}) (dimension : Nat)
    (thin : tower.LocallyThinAt dimension)
    (sourceCell targetCell : tower.Cell dimension)
    {Result : Type v}
    (observe : tower.BoundaryFiber dimension sourceCell targetCell → Result) :
    tower.ObserverErasureSafe dimension sourceCell targetCell observe := by
  intro first second
  exact congrArg observe ((thin sourceCell targetCell).allEq first second)

/-- Proposition-valued consumers already form a complete discriminator:
local thinness holds exactly when all of them are erasure-safe. -/
theorem locallyThinAt_iff_every_propObserver_erasureSafe
    (tower : GlobularSet.{u}) (dimension : Nat) :
    tower.LocallyThinAt dimension ↔
      ∀ sourceCell targetCell
        (observe : tower.BoundaryFiber dimension sourceCell targetCell → Prop),
        tower.ObserverErasureSafe dimension sourceCell targetCell observe := by
  constructor
  · intro thin sourceCell targetCell observe
    exact tower.observerErasureSafe_of_locallyThinAt dimension thin
      sourceCell targetCell observe
  · intro everyObserver sourceCell targetCell
    constructor
    intro first second
    let identifiesFirst :
        tower.BoundaryFiber dimension sourceCell targetCell → Prop :=
      fun cell => cell = first
    have invariant := everyObserver sourceCell targetCell identifiesFirst
      first second
    have secondEqualsFirst : second = first := by
      exact Eq.mp invariant rfl
    exact secondEqualsFirst.symm

/-- A proof-carrying license to use the thin representation at one selected
cell dimension. -/
structure LocalTruncationCertificate (tower : GlobularSet.{u})
    (dimension : Nat) : Prop where
  thin : tower.LocallyThinAt dimension

namespace LocalTruncationCertificate

/-- The optimized representation forgets which parallel cell was supplied. -/
def erase {tower : GlobularSet.{u}} {dimension : Nat}
    (_certificate : tower.LocalTruncationCertificate dimension)
    {sourceCell targetCell : tower.Cell dimension}
    (_cell : tower.BoundaryFiber dimension sourceCell targetCell) : Unit :=
  ()

/-- Recover an observer result from the erased representation by choosing any
inhabitant of the certified-thin fibre. -/
def readout {tower : GlobularSet.{u}} {dimension : Nat}
    (_certificate : tower.LocalTruncationCertificate dimension)
    {sourceCell targetCell : tower.Cell dimension}
    (anchor : tower.BoundaryFiber dimension sourceCell targetCell)
    {Result : Type v}
    (observe : tower.BoundaryFiber dimension sourceCell targetCell → Result) :
    Unit → Result :=
  fun _ => observe anchor

/-- Every observer on an inhabited certified-thin boundary fibre factors
through the `Unit` erasure. -/
theorem observer_factorization
    {tower : GlobularSet.{u}} {dimension : Nat}
    (certificate : tower.LocalTruncationCertificate dimension)
    {sourceCell targetCell : tower.Cell dimension}
    (anchor : tower.BoundaryFiber dimension sourceCell targetCell)
    {Result : Type v}
    (observe : tower.BoundaryFiber dimension sourceCell targetCell → Result) :
    observe = certificate.readout anchor observe ∘ certificate.erase := by
  funext cell
  exact congrArg observe
    ((certificate.thin sourceCell targetCell).allEq cell anchor)

end LocalTruncationCertificate

/-- A genuinely distinguishing consumer at one boundary dimension. -/
def HasDistinguishingObserverAt (tower : GlobularSet.{u})
    (dimension : Nat) : Prop :=
  ∃ sourceCell targetCell,
    ∃ (observe : tower.BoundaryFiber dimension sourceCell targetCell → Prop)
      (first second : tower.BoundaryFiber dimension sourceCell targetCell),
      observe first ≠ observe second

/-- Distinct parallel cells always have a proposition-valued consumer that
distinguishes them. -/
theorem hasDistinguishingObserverAt_of_hasDistinctParallelAt
    (tower : GlobularSet.{u}) (dimension : Nat)
    (distinct : tower.HasDistinctParallelAt dimension) :
    tower.HasDistinguishingObserverAt dimension := by
  obtain ⟨sourceCell, targetCell, first, second, different⟩ := distinct
  let identifiesFirst :
      tower.BoundaryFiber dimension sourceCell targetCell → Prop :=
    fun cell => cell = first
  refine ⟨sourceCell, targetCell, identifiesFirst, first, second, ?_⟩
  intro equalResults
  have secondEqualsFirst : second = first := Eq.mp equalResults rfl
  exact different secondEqualsFirst.symm

/-- A distinguishing consumer is exactly a failure of the proposed erasure
for that consumer. -/
theorem not_observerErasureSafe_of_distinguishes
    (tower : GlobularSet.{u}) (dimension : Nat)
    (sourceCell targetCell : tower.Cell dimension)
    (observe : tower.BoundaryFiber dimension sourceCell targetCell → Prop)
    (first second : tower.BoundaryFiber dimension sourceCell targetCell)
    (distinguishes : observe first ≠ observe second) :
    ¬ tower.ObserverErasureSafe dimension sourceCell targetCell observe := by
  intro safe
  exact distinguishes (safe first second)

end GlobularSet

/-! ## A thin finite prefix with a thick next dimension -/

namespace ThinBelowThickNext

/-- Boolean labels forced to `false` through the chosen horizon.  Above the
horizon both labels are available. -/
def Cell (horizon dimension : Nat) : Type :=
  { label : Bool // dimension ≤ horizon → label = false }

/-- Common source and target map.  At and below the horizon it returns the
unique low-dimensional label; above the horizon it retains the label. -/
def boundary (horizon dimension : Nat) :
    Cell horizon (dimension + 1) → Cell horizon dimension :=
  fun cell =>
    if low : dimension ≤ horizon then
      ⟨false, fun _ => rfl⟩
    else
      ⟨cell.1, fun atMostHorizon => (low atMostHorizon).elim⟩

/-- An unbounded globular tower with coincident source and target maps. -/
def tower (horizon : Nat) : GlobularSet where
  Cell := Cell horizon
  source := boundary horizon
  target := boundary horizon
  source_source := by
    intro _dimension _cell
    rfl
  target_source := by
    intro _dimension _cell
    rfl

/-- At or below the horizon, the label constraint leaves one cell. -/
theorem cell_subsingleton (horizon dimension : Nat)
    (bounded : dimension ≤ horizon) :
    Subsingleton (Cell horizon dimension) where
  allEq := by
    intro first second
    apply Subtype.ext
    exact (first.2 bounded).trans (second.2 bounded).symm

/-- If the next cell dimension is still below the horizon, its parallel
fibres are subsingletons. -/
theorem locallyThinAt_of_succ_le (horizon dimension : Nat)
    (bounded : dimension + 1 ≤ horizon) :
    (tower horizon).LocallyThinAt dimension := by
  intro sourceCell targetCell
  constructor
  intro first second
  apply Subtype.ext
  exact (cell_subsingleton horizon (dimension + 1) bounded).allEq
    first.1 second.1

/-- Every boundary dimension strictly below the horizon is locally thin. -/
theorem thinBelow (horizon : Nat) :
    (tower horizon).ThinBelow horizon := by
  intro dimension below
  exact locallyThinAt_of_succ_le horizon dimension (by omega)

/-- The unique cell at the horizon. -/
def horizonCell (horizon : Nat) : Cell horizon horizon :=
  ⟨false, fun _ => rfl⟩

/-- First cell immediately above the horizon. -/
def falseNextCell (horizon : Nat) : Cell horizon (horizon + 1) :=
  ⟨false, fun impossible => by omega⟩

/-- Distinct second cell immediately above the horizon. -/
def trueNextCell (horizon : Nat) : Cell horizon (horizon + 1) :=
  ⟨true, fun impossible => by omega⟩

def falseNextInFiber (horizon : Nat) :
    (tower horizon).BoundaryFiber horizon
      (horizonCell horizon) (horizonCell horizon) := by
  refine ⟨falseNextCell horizon, ?_⟩
  simp [tower, boundary, horizonCell]

def trueNextInFiber (horizon : Nat) :
    (tower horizon).BoundaryFiber horizon
      (horizonCell horizon) (horizonCell horizon) := by
  refine ⟨trueNextCell horizon, ?_⟩
  simp [tower, boundary, horizonCell]

/-- The two cells immediately above the horizon are distinct. -/
theorem nextCells_distinct (horizon : Nat) :
    falseNextInFiber horizon ≠ trueNextInFiber horizon := by
  intro equality
  have labelEquality := congrArg (fun cell => cell.1.1) equality
  exact Bool.false_ne_true labelEquality

/-- The first unlicensed dimension has genuinely distinct parallel cells. -/
theorem hasDistinctParallelAt_horizon (horizon : Nat) :
    (tower horizon).HasDistinctParallelAt horizon :=
  ⟨horizonCell horizon, horizonCell horizon,
    falseNextInFiber horizon, trueNextInFiber horizon,
    nextCells_distinct horizon⟩

/-- Consequently the tower is not locally thin at the horizon itself. -/
theorem not_locallyThinAt_horizon (horizon : Nat) :
    ¬ (tower horizon).LocallyThinAt horizon :=
  (tower horizon).not_locallyThinAt_of_hasDistinctParallelAt horizon
    (hasDistinctParallelAt_horizon horizon)

/-- The tower remains inhabited in every dimension. -/
theorem cell_nonempty (horizon dimension : Nat) :
    Nonempty (Cell horizon dimension) :=
  ⟨⟨false, fun _ => rfl⟩⟩

end ThinBelowThickNext

/-! ## No finite observation proves a global cutoff -/

/-- At every finite horizon, thinness throughout the lower prefix is
compatible with a distinguishing higher-cell observer at the next level. -/
theorem finiteThinPrefix_does_not_force_nextThinness (horizon : Nat) :
    ∃ tower : GlobularSet.{0},
      tower.ThinBelow horizon ∧
        tower.HasDistinctParallelAt horizon ∧
        tower.HasDistinguishingObserverAt horizon := by
  let tower := ThinBelowThickNext.tower horizon
  have distinct : tower.HasDistinctParallelAt horizon :=
    ThinBelowThickNext.hasDistinctParallelAt_horizon horizon
  exact ⟨tower, ThinBelowThickNext.thinBelow horizon, distinct,
    tower.hasDistinguishingObserverAt_of_hasDistinctParallelAt
      horizon distinct⟩

/-- Therefore no proposed finite horizon can make thinness of its whole lower
prefix entail thinness at the next boundary dimension for every globular
tower. -/
theorem no_global_cell_cutoff_from_finite_thin_prefix :
    ¬ ∃ horizon : Nat, ∀ tower : GlobularSet.{0},
      tower.ThinBelow horizon → tower.LocallyThinAt horizon := by
  rintro ⟨horizon, purportedCutoff⟩
  obtain ⟨tower, thinPrefix, distinct, _observer⟩ :=
    finiteThinPrefix_does_not_force_nextThinness horizon
  exact tower.not_locallyThinAt_of_hasDistinctParallelAt horizon distinct
    (purportedCutoff tower thinPrefix)

end Mettapedia.CategoryTheory.Higher
