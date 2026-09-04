import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mettapedia.TypeTheory.FreeWhiskeredCellCoherenceObservation
import Mettapedia.TypeTheory.LocallyThinWhiskeredCellBicategory
import Mettapedia.TypeTheory.OperationalIntensionalExtensionalTwoComputad

/-!
# The locally thin operational/intensional/extensional mode bicategory

The operational/intensional/extensional two-computad is instantiated in the
generic locally thin extension.  The result is an actual bicategory with the
six selected modalities, all eight authored comparison generators, three
bicategorical adjunctions, and the factorization isomorphism.

This is the coherent `M1` candidate.  It deliberately separates construction
from semantic factorization.  The raw mixed cells have a canonical
interpretation in `Cat`, but that interpretation descends to the locally thin
cell fibre exactly when it is fibre-invariant.  One factorization round-trip is
proved invariant here; global invariance and the descended pseudofunctor are
proved in `OperationalIntensionalExtensionalSemanticThinness` so that the
construction and its semantic qualification remain separate dependencies.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory
namespace OperationalIntensionalExtensionalLocallyThinModeTheory

open CategoryTheory CategoryTheory.Bicategory
open FreeWhiskeredCell
open FreeWhiskeredCell.CoherenceObservation
open LocallyThinCellReflection
open LocallyThinWhiskeredCellBicategory
open OperationalIntensionalExtensionalModes
open OperationalIntensionalExtensionalTwoComputad

universe u

/-! ## Modes and modalities -/

/-- The locally thin extension of the free mode bicategory by the eight
authored comparison generators. -/
abbrev ThinMode :=
  LocallyThinWhiskeredCellBicategory.Extension
    FreeModeBicategory CellGenerator

def operational : ThinMode := ⟨Mode.operational⟩
def intensional : ThinMode := ⟨Mode.intensional⟩
def extensional : ThinMode := ⟨Mode.extensional⟩

def evidence : operational ⟶ intensional := ⟨evidencePath⟩
def forgetEvidence : intensional ⟶ operational := ⟨forgetEvidencePath⟩
def readout : intensional ⟶ extensional := ⟨readoutPath⟩
def discrete : extensional ⟶ intensional := ⟨discretePath⟩
def points : intensional ⟶ extensional := ⟨pointsPath⟩
def observe : operational ⟶ extensional := ⟨observePath⟩

def evidenceReadout : operational ⟶ extensional :=
  evidence ≫ readout

/-! ## Authored cells, adjunctions, and factorization -/

def operationalUnit : 𝟙 operational ⟶ evidence ≫ forgetEvidence :=
  ofAuthored (B := FreeModeBicategory) CellGenerator.operationalUnit

def operationalCounit : forgetEvidence ≫ evidence ⟶ 𝟙 intensional :=
  ofAuthored (B := FreeModeBicategory) CellGenerator.operationalCounit

def readoutUnit : 𝟙 intensional ⟶ readout ≫ discrete :=
  ofAuthored (B := FreeModeBicategory) CellGenerator.readoutUnit

def readoutCounit : discrete ≫ readout ⟶ 𝟙 extensional :=
  ofAuthored (B := FreeModeBicategory) CellGenerator.readoutCounit

def discreteUnit : 𝟙 extensional ⟶ discrete ≫ points :=
  ofAuthored (B := FreeModeBicategory) CellGenerator.discreteUnit

def discreteCounit : points ≫ discrete ⟶ 𝟙 intensional :=
  ofAuthored (B := FreeModeBicategory) CellGenerator.discreteCounit

def factorForward : evidenceReadout ⟶ observe :=
  ofAuthored (B := FreeModeBicategory) CellGenerator.factorForward

def factorBackward : observe ⟶ evidenceReadout :=
  ofAuthored (B := FreeModeBicategory) CellGenerator.factorBackward

/-- The operational/intensional pair is an adjunction in the selected locally
thin bicategory. -/
def operationalAdjunction : evidence ⊣ forgetEvidence where
  unit := operationalUnit
  counit := operationalCounit
  left_triangle := Subsingleton.elim _ _
  right_triangle := Subsingleton.elim _ _

/-- Extensional readout is left adjoint to the discrete embedding. -/
def readoutAdjunction : readout ⊣ discrete where
  unit := readoutUnit
  counit := readoutCounit
  left_triangle := Subsingleton.elim _ _
  right_triangle := Subsingleton.elim _ _

/-- The discrete embedding is left adjoint to the points/readout modality. -/
def discretePointsAdjunction : discrete ⊣ points where
  unit := discreteUnit
  counit := discreteCounit
  left_triangle := Subsingleton.elim _ _
  right_triangle := Subsingleton.elim _ _

/-- The two operational-to-extensional routes are isomorphic in the locally
thin mode bicategory. -/
def factorIso : evidenceReadout ≅ observe where
  hom := factorForward
  inv := factorBackward
  hom_inv_id := Subsingleton.elim _ _
  inv_hom_id := Subsingleton.elim _ _

theorem factor_roundTrip_is_identity :
    factorForward ≫ factorBackward = 𝟙 evidenceReadout :=
  Subsingleton.elim _ _

theorem factor_inverseRoundTrip_is_identity :
    factorBackward ≫ factorForward = 𝟙 observe :=
  Subsingleton.elim _ _

/-! ## Raw mixed semantics and the exact descent gate -/

/-- Interpret a structural base cell by the free semantic pseudofunctor and
an authored generator by its independently checked natural transformation. -/
def mixedSemanticAlgebra :
    FreeWhiskeredCell.Algebra (oneCellBase FreeModeBicategory)
      (ExtendedGenerator CellGenerator) SemanticCell.{u} where
  onRefl := fun path => 𝟙 (semanticPseudofunctor.{u}.map path)
  onGenerator := by
    intro source target first second generator
    cases generator with
    | structural structural =>
        exact semanticPseudofunctor.{u}.map₂ structural
    | authored authored =>
        exact interpretGenerator.{u} authored
  onVertical := fun earlier later => earlier ≫ later
  onWhiskerLeft := @fun _source _middle _target prior _first _second cell =>
    semanticPseudofunctor.{u}.map prior ◁ cell
  onWhiskerRight := @fun _source _middle _target _first _second suffix cell =>
    cell ▷ semanticPseudofunctor.{u}.map suffix

/-- The canonical `Cat` meaning of every raw structural/authored cell. -/
def interpretMixedCell
    {source target : Mode} {first second : ModePath source target} :
    RawGeneratedCell (B := FreeModeBicategory)
      CellGenerator first second → SemanticCell.{u} first second :=
  mixedSemanticAlgebra.{u}.fold

/-- The exact condition under which raw mixed semantics descends to one
locally thin parallel-cell fibre. -/
def SemanticFibreInvariant
    {source target : Mode} (first second : ModePath source target) : Prop :=
  FibreInvariant
    (@interpretMixedCell.{u} source target first second)

/-- Semantic descent through a selected thin fibre is equivalent to semantic
proof irrelevance on the corresponding raw mixed fibre. -/
theorem semantic_factors_through_thin_iff
    {source target : Mode} (first second : ModePath source target) :
    FactorsThrough (@interpretMixedCell.{u} source target first second) ↔
      SemanticFibreInvariant.{u} first second :=
  factorsThrough_iff_fibreInvariant _

/-! ## A proved local semantic coherence and a raw-history negative control -/

def rawFactorForward :
    RawGeneratedCell (B := FreeModeBicategory)
      CellGenerator evidenceReadoutPath observePath :=
  .generator (.authored .factorForward)

def rawFactorBackward :
    RawGeneratedCell (B := FreeModeBicategory)
      CellGenerator observePath evidenceReadoutPath :=
  .generator (.authored .factorBackward)

def rawFactorRoundTrip :
    RawGeneratedCell (B := FreeModeBicategory)
      CellGenerator evidenceReadoutPath evidenceReadoutPath :=
  .vertical rawFactorForward rawFactorBackward

def rawFactorIdentity :
    RawGeneratedCell (B := FreeModeBicategory)
      CellGenerator evidenceReadoutPath evidenceReadoutPath :=
  FreeWhiskeredCell.Cell.refl
    (base := oneCellBase FreeModeBicategory)
    (Generator := ExtendedGenerator CellGenerator) evidenceReadoutPath

theorem raw_factor_history_distinct :
    rawFactorRoundTrip ≠ rawFactorIdentity := by
  intro equality
  have shapeEquality := congrArg rawShape equality
  simp [rawFactorRoundTrip, rawFactorForward, rawFactorBackward,
    rawFactorIdentity, rawShape] at shapeEquality

/-- Construction-history observation correctly refuses the locally thin
quotient on this raw fibre. -/
def rawShapeDiscriminator :
    Discriminator
      (RawGeneratedCell (B := FreeModeBicategory)
        CellGenerator evidenceReadoutPath evidenceReadoutPath)
      RawShape where
  left := rawFactorRoundTrip
  right := rawFactorIdentity
  observe := rawShape
  separates := by
    simp [rawFactorRoundTrip, rawFactorForward, rawFactorBackward,
      rawFactorIdentity, rawShape]

theorem raw_shape_does_not_factor_through_thin :
    ¬ FactorsThrough
      (rawShape :
        RawGeneratedCell (B := FreeModeBicategory)
          CellGenerator evidenceReadoutPath
          evidenceReadoutPath → RawShape) :=
  rawShapeDiscriminator.not_factorsThrough

/-- The independent categorical semantics validates erasure of this specific
factorization round-trip history. -/
theorem semantic_factor_history_identified :
    interpretMixedCell.{u} rawFactorRoundTrip =
      interpretMixedCell.{u} rawFactorIdentity := by
  change
    (Cat.Hom.isoMk observationFactors.{u}).hom ≫
        (Cat.Hom.isoMk observationFactors.{u}).inv =
      𝟙 ((evidenceCompletion.{u} ⋙ routeQuotient.{u}).toCatHom)
  exact (Cat.Hom.isoMk observationFactors.{u}).hom_inv_id

/-! ## Connected boundary -/

/-- The locally thin candidate is a genuine bicategory containing the three
adjunctions and factor isomorphism, while this construction module exposes
semantic descent as an explicit fibre-invariance obligation. -/
theorem locally_thin_mode_boundary :
    Quiver.IsThin (operational ⟶ extensional) ∧
      Nonempty (evidence ⊣ forgetEvidence) ∧
      Nonempty (readout ⊣ discrete) ∧
      Nonempty (discrete ⊣ points) ∧
      Nonempty (evidenceReadout ≅ observe) ∧
      interpretMixedCell.{u} rawFactorRoundTrip =
        interpretMixedCell.{u} rawFactorIdentity :=
  ⟨inferInstance,
    ⟨operationalAdjunction⟩,
    ⟨readoutAdjunction⟩,
    ⟨discretePointsAdjunction⟩,
    ⟨factorIso⟩,
    semantic_factor_history_identified⟩

/-! ## Axiom audit -/

#print axioms operationalAdjunction
#print axioms readoutAdjunction
#print axioms discretePointsAdjunction
#print axioms factorIso
#print axioms factor_roundTrip_is_identity
#print axioms semantic_factors_through_thin_iff
#print axioms raw_factor_history_distinct
#print axioms raw_shape_does_not_factor_through_thin
#print axioms semantic_factor_history_identified
#print axioms locally_thin_mode_boundary

end OperationalIntensionalExtensionalLocallyThinModeTheory
end Mettapedia.TypeTheory
