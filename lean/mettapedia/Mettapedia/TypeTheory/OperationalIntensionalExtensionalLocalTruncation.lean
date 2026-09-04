import Mettapedia.CategoryTheory.GlobularLocalTruncation
import Mettapedia.TypeTheory.OperationalIntensionalExtensionalLocallyThinModeTheory

/-!
# The local truncation certificate of the O/I/E comparison sector

The locally thin operational/intensional/extensional mode bicategory supplies
a concrete optimization certificate for its selected two-cell layer.  This
module places the operational-to-extensional hom sector in a globular tower
and connects that certificate to the generic observer-erasure theorem.

The tower is only the strict globular shadow of the selected locally thin
bicategory.  Its higher cells are identities.  This is an implementation
profile for the current core, not evidence that every future extension of
Prime is globally truncated.  The arbitrary-horizon countermodel from
`GlobularLocalTruncation` is carried alongside the certificate to make that
boundary formal.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory
namespace OperationalIntensionalExtensionalLocalTruncation

open Mettapedia.CategoryTheory.Higher
open Mettapedia.TypeTheory.LocallyThinWhiskeredCellBicategory
open OperationalIntensionalExtensionalTwoComputad
open OperationalIntensionalExtensionalLocallyThinModeTheory

/-- Modalities in the selected operational-to-extensional hom sector. -/
abbrev SectorPath : Type :=
  ModePath Mode.operational Mode.extensional

/-- Reflected two-cells between parallel paths in that sector, with both
boundaries retained as data. -/
abbrev SectorTwoCell : Type :=
  Σ first : SectorPath, Σ second : SectorPath,
    ThinCell (B := FreeModeBicategory) CellGenerator first second

/-- The globular cells of the strict sector shadow.  Dimensions above two
reuse the selected two-cell as its unique iterated identity. -/
def Cell : Nat → Type
  | 0 => Unit
  | 1 => SectorPath
  | _ + 2 => SectorTwoCell

/-- Globular source map for the sector shadow. -/
def source : (dimension : Nat) → Cell (dimension + 1) → Cell dimension
  | 0, _path => ()
  | 1, cell => cell.1
  | _ + 2, cell => cell

/-- Globular target map for the sector shadow. -/
def target : (dimension : Nat) → Cell (dimension + 1) → Cell dimension
  | 0, _path => ()
  | 1, cell => cell.2.1
  | _ + 2, cell => cell

/-- The strict globular shadow of the current locally thin comparison
sector. -/
def tower : GlobularSet where
  Cell := Cell
  source := source
  target := target
  source_source := by
    intro dimension cell
    cases dimension with
    | zero => rfl
    | succ dimension =>
        cases dimension <;> rfl
  target_source := by
    intro dimension cell
    cases dimension with
    | zero => rfl
    | succ dimension =>
        cases dimension <;> rfl

/-- Parallel reflected two-cells are propositionally unique after their path
boundaries are fixed. -/
theorem locallyThinAt_twoCells : tower.LocallyThinAt 1 := by
  intro firstPath secondPath
  constructor
  rintro ⟨⟨firstA, secondA, cellA⟩, sourceA, targetA⟩
    ⟨⟨firstB, secondB, cellB⟩, sourceB, targetB⟩
  apply Subtype.ext
  change (⟨firstA, secondA, cellA⟩ : SectorTwoCell) =
    ⟨firstB, secondB, cellB⟩
  change firstA = firstPath at sourceA
  change secondA = secondPath at targetA
  change firstB = firstPath at sourceB
  change secondB = secondPath at targetB
  subst firstA
  subst secondA
  subst firstB
  subst secondB
  have cellsEqual : cellA = cellB := Subsingleton.elim _ _
  subst cellsEqual
  rfl

/-- The current core therefore carries an explicit local two-cell truncation
certificate. -/
def twoCellCertificate : tower.LocalTruncationCertificate 1 where
  thin := locallyThinAt_twoCells

/-- The authored comparison between evidence-then-readout and direct
observation, as an element of the selected boundary fibre. -/
def factorForwardInFiber :
    tower.BoundaryFiber 1 evidenceReadoutPath observePath := by
  refine ⟨⟨evidenceReadoutPath, observePath,
    ofAuthored (B := FreeModeBicategory) CellGenerator.factorForward⟩, ?_⟩
  exact ⟨rfl, rfl⟩

/-- Every consumer of this reflected comparison factors through the thin
`Unit` representation.  The consumer's result type remains unrestricted. -/
theorem factorForward_observer_factorization {Result : Type}
    (observeComparison :
      tower.BoundaryFiber 1 evidenceReadoutPath observePath → Result) :
    observeComparison =
      twoCellCertificate.readout factorForwardInFiber observeComparison ∘
        twoCellCertificate.erase :=
  twoCellCertificate.observer_factorization
    factorForwardInFiber observeComparison

/-- The local core certificate and the absence of any universal finite cutoff
are simultaneously true.  Optimizing this sector therefore does not limit
the cell height of future languages or models. -/
theorem local_core_thinness_without_global_cutoff :
    Nonempty (tower.LocalTruncationCertificate 1) ∧
      ¬ ∃ horizon : Nat, ∀ candidate : GlobularSet.{0},
        candidate.ThinBelow horizon → candidate.LocallyThinAt horizon :=
  ⟨⟨twoCellCertificate⟩,
    Mettapedia.CategoryTheory.Higher.no_global_cell_cutoff_from_finite_thin_prefix⟩

/-- Raw comparison history remains distinguishable even though the reflected
semantic comparison admits local erasure. -/
theorem local_erasure_coexists_with_raw_history :
    Nonempty (tower.LocalTruncationCertificate 1) ∧
      rawFactorRoundTrip ≠ rawFactorIdentity :=
  ⟨⟨twoCellCertificate⟩, raw_factor_history_distinct⟩

end OperationalIntensionalExtensionalLocalTruncation
end Mettapedia.TypeTheory
