import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat
import Mathlib.CategoryTheory.Bicategory.Free
import Mathlib.CategoryTheory.PathCategory.Basic
import Mettapedia.TypeTheory.FreeWhiskeredCell
import Mettapedia.TypeTheory.ModalCwF
import Mettapedia.TypeTheory.OperationalIntensionalExtensionalModes

/-!
# The operational / intensional / extensional mode two-computad

This module separates three layers that a multimodal dependent type theory
must not conflate:

1. a quiver of three modes and six generating modalities;
2. the free bicategory of modality paths and structural coherence cells;
3. authored two-generators for the three adjunctions and the commuting
   observation comparison.

The authored cells freely generate raw whiskered cells.  They have a
non-degenerate interpretation in the bicategory `Cat`, using the concrete
semantic categories and adjunctions from
`OperationalIntensionalExtensionalModes`.  The bare free bicategory cannot
manufacture either an adjunction unit or the commuting comparison: a proved
generator-count invariant rules both out.  Thus the two-dimensional data is
real additional structure, not a relabeling of bicategorical coherence.

The ordinary `ModeTheory` used by `ModalCwF` is recovered as the free path
category of the same mode quiver.  It retains modality paths but deliberately
forgets authored two-cells.  Consequently it is an honest one-dimensional
shadow, not yet the full MTT mode theory.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory
namespace OperationalIntensionalExtensionalTwoComputad

open CategoryTheory CategoryTheory.Bicategory
open OperationalIntensionalExtensionalModes

universe u

/-! ## Modes and generating modalities -/

/-- The three semantic roles. -/
inductive Mode : Type
  | operational
  | intensional
  | extensional
  deriving DecidableEq, Repr

/-- Six primitive directed modalities.  `readout` and `points` have the same
endpoints but different semantic meanings, so they remain distinct arrows. -/
inductive Modality : Mode → Mode → Type
  | evidence : Modality .operational .intensional
  | forgetEvidence : Modality .intensional .operational
  | readout : Modality .intensional .extensional
  | discrete : Modality .extensional .intensional
  | points : Modality .intensional .extensional
  | observe : Modality .operational .extensional

instance : Quiver Mode where
  Hom := Modality

/-- The free category of finite modality paths is the exact one-dimensional
mode theory currently consumed by `ModalCwF`. -/
def pathModeTheory : ModeTheory where
  Mode := Paths Mode
  Hom := fun source target => source ⟶ target
  id := fun mode => 𝟙 mode
  comp := fun earlier later => earlier ≫ later
  id_comp := by simp
  comp_id := by simp
  comp_assoc := by simp

/-- The composite route through the intensional mode and the direct
operational observation are distinct in the one-dimensional shadow. -/
theorem path_shadow_does_not_commute_on_the_nose :
    (Quiver.Path.comp
        (Quiver.Hom.toPath Modality.evidence :
          Quiver.Path Mode.operational Mode.intensional)
        (Quiver.Hom.toPath Modality.readout :
          Quiver.Path Mode.intensional Mode.extensional)) ≠
      (Quiver.Hom.toPath Modality.observe :
        Quiver.Path Mode.operational Mode.extensional) := by
  intro equality
  have lengths := congrArg Quiver.Path.length equality
  simp at lengths

/-! ## Free bicategorical modality paths -/

/-- The free bicategory contains only structural unitors and associators as
two-cells. -/
abbrev FreeModeBicategory := FreeBicategory Mode

/-- One-cells of the free mode bicategory, named explicitly to avoid
confusing the original modality quiver with the freely generated quiver. -/
abbrev ModePath (source target : Mode) :=
  FreeBicategory.Hom (B := Mode) source target

/-- Each parallel-path collection carries the hom-category structure of the
free bicategory.  Naming the instance avoids ambiguity with the original
quiver on `Mode`. -/
instance modePathCategory (source target : Mode) :
    Category (ModePath source target) :=
  FreeBicategory.homCategory (B := Mode) source target

def evidencePath : ModePath .operational .intensional :=
  FreeBicategory.Hom.of (B := Mode) Modality.evidence

def forgetEvidencePath : ModePath .intensional .operational :=
  FreeBicategory.Hom.of (B := Mode) Modality.forgetEvidence

def readoutPath : ModePath .intensional .extensional :=
  FreeBicategory.Hom.of (B := Mode) Modality.readout

def discretePath : ModePath .extensional .intensional :=
  FreeBicategory.Hom.of (B := Mode) Modality.discrete

def pointsPath : ModePath .intensional .extensional :=
  FreeBicategory.Hom.of (B := Mode) Modality.points

def observePath : ModePath .operational .extensional :=
  FreeBicategory.Hom.of (B := Mode) Modality.observe

def evidenceForgetPath : ModePath .operational .operational :=
  FreeBicategory.Hom.comp evidencePath forgetEvidencePath

def forgetEvidenceEvidencePath : ModePath .intensional .intensional :=
  FreeBicategory.Hom.comp forgetEvidencePath evidencePath

def readoutDiscretePath : ModePath .intensional .intensional :=
  FreeBicategory.Hom.comp readoutPath discretePath

def discreteReadoutPath : ModePath .extensional .extensional :=
  FreeBicategory.Hom.comp discretePath readoutPath

def discretePointsPath : ModePath .extensional .extensional :=
  FreeBicategory.Hom.comp discretePath pointsPath

def pointsDiscretePath : ModePath .intensional .intensional :=
  FreeBicategory.Hom.comp pointsPath discretePath

def evidenceReadoutPath : ModePath .operational .extensional :=
  FreeBicategory.Hom.comp evidencePath readoutPath

/-! ## A semantic pseudofunctor into `Cat` -/

/-- Interpret each mode as its concrete semantic category and each primitive
modality as its already-verified functor. -/
def semanticPrefunctor : Mode ⥤q Cat.{u, u + 1} where
  obj
    | .operational => Cat.of DynSys.{u}
    | .intensional => Cat.of RouteType.{u}
    | .extensional => Cat.of ExtType.{u}
  map := fun {_source _target} modality =>
    match modality with
    | .evidence => evidenceCompletion.{u}.toCatHom
    | .forgetEvidence => forgetReflexivity.{u}.toCatHom
    | .readout => routeQuotient.{u}.toCatHom
    | .discrete => discreteOn.{u}.toCatHom
    | .points => pointsOf.{u}.toCatHom
    | .observe => dynQuotient.{u}.toCatHom

/-- Structural extension of the semantic assignment to every free modality
path and every bicategorical coherence cell. -/
def semanticPseudofunctor :
    FreeModeBicategory ⥤ᵖ Cat.{u, u + 1} :=
  FreeBicategory.lift semanticPrefunctor

@[simp] theorem semantic_evidencePath :
    semanticPseudofunctor.{u}.map evidencePath =
      evidenceCompletion.{u}.toCatHom := rfl

@[simp] theorem semantic_forgetEvidencePath :
    semanticPseudofunctor.{u}.map forgetEvidencePath =
      forgetReflexivity.{u}.toCatHom := rfl

@[simp] theorem semantic_readoutPath :
    semanticPseudofunctor.{u}.map readoutPath =
      routeQuotient.{u}.toCatHom := rfl

@[simp] theorem semantic_discretePath :
    semanticPseudofunctor.{u}.map discretePath =
      discreteOn.{u}.toCatHom := rfl

@[simp] theorem semantic_pointsPath :
    semanticPseudofunctor.{u}.map pointsPath =
      pointsOf.{u}.toCatHom := rfl

@[simp] theorem semantic_observePath :
    semanticPseudofunctor.{u}.map observePath =
      dynQuotient.{u}.toCatHom := rfl

@[simp] theorem semantic_evidenceReadoutPath :
    semanticPseudofunctor.{u}.map evidenceReadoutPath =
      (evidenceCompletion.{u} ⋙ routeQuotient.{u}).toCatHom := rfl

/-! ## Negative theorem for the bare free bicategory -/

/-- Number of primitive modalities in a free one-cell. -/
def generatorCount : {source target : Mode} →
    ModePath source target → Nat
  | _, _, .of _ => 1
  | _, _, .id _ => 0
  | _, _, .comp earlier later =>
      generatorCount earlier + generatorCount later

@[simp] theorem generatorCount_id (mode : Mode) :
    generatorCount (FreeBicategory.Hom.id mode) = 0 := rfl

@[simp] theorem generatorCount_comp
    {source middle target : Mode}
    (earlier : ModePath source middle) (later : ModePath middle target) :
    generatorCount (FreeBicategory.Hom.comp earlier later) =
      generatorCount earlier + generatorCount later := rfl

/-- Every structural coherence cell in the bare free bicategory preserves
the number of primitive modalities. -/
theorem raw_coherence_preserves_generatorCount
    {source target : Mode}
    {first second : ModePath source target}
    (cell : FreeBicategory.Hom₂ first second) :
    generatorCount first = generatorCount second := by
  induction cell with
  | id => rfl
  | vcomp _ _ earlier later => exact earlier.trans later
  | whisker_left prior _ inductionHypothesis =>
      change generatorCount prior + generatorCount _ =
        generatorCount prior + generatorCount _
      exact congrArg (fun count => generatorCount prior + count)
        inductionHypothesis
  | whisker_right suffix _ inductionHypothesis =>
      change generatorCount _ + generatorCount suffix =
        generatorCount _ + generatorCount suffix
      exact congrArg (fun count => count + generatorCount suffix)
        inductionHypothesis
  | associator first middle last =>
      exact Nat.add_assoc (generatorCount first)
        (generatorCount middle) (generatorCount last)
  | associator_inv first middle last =>
      exact (Nat.add_assoc (generatorCount first)
        (generatorCount middle) (generatorCount last)).symm
  | right_unitor path => exact Nat.add_zero (generatorCount path)
  | right_unitor_inv path => exact (Nat.add_zero (generatorCount path)).symm
  | left_unitor path => exact Nat.zero_add (generatorCount path)
  | left_unitor_inv path => exact (Nat.zero_add (generatorCount path)).symm

/-- The generator-count invariant descends through the coherence quotient. -/
theorem coherence_preserves_generatorCount
    {source target : Mode}
    {first second : ModePath source target}
    (cell : first ⟶ second) :
    generatorCount first = generatorCount second := by
  induction cell using Quot.inductionOn with
  | _ representative =>
      exact raw_coherence_preserves_generatorCount representative

/-- Structural bicategorical coherence alone cannot identify the two-step
factorization with the direct observation modality. -/
theorem no_bare_factor_cell :
    IsEmpty (evidenceReadoutPath ⟶ observePath) :=
  ⟨fun cell => by
    have countEquality := coherence_preserves_generatorCount cell
    simp [evidenceReadoutPath, evidencePath, readoutPath, observePath,
      generatorCount] at countEquality⟩

/-- Nor can the bare free bicategory synthesize the unit of the operational
evidence adjunction. -/
theorem no_bare_operational_unit :
    IsEmpty
      ((FreeBicategory.Hom.id Mode.operational) ⟶
        evidenceForgetPath) :=
  ⟨fun cell => by
    have countEquality := coherence_preserves_generatorCount cell
    simp [evidenceForgetPath, evidencePath, forgetEvidencePath,
      generatorCount] at countEquality⟩

/-! ## Authored two-generators -/

/-- The raw one-dimensional boundary used by the free whiskered-cell
construction. -/
def modeCellBase : FreeWhiskeredCell.Base where
  Object := Mode
  Hom := ModePath
  compose := FreeBicategory.Hom.comp

/-- Authored two-generators: units and counits for all three adjunctions,
plus both directions of the commuting observation comparison. -/
inductive CellGenerator :
    {source target : modeCellBase.Object} →
      modeCellBase.Hom source target →
      modeCellBase.Hom source target → Type
  | operationalUnit :
      CellGenerator (FreeBicategory.Hom.id Mode.operational)
        evidenceForgetPath
  | operationalCounit :
      CellGenerator forgetEvidenceEvidencePath
        (FreeBicategory.Hom.id Mode.intensional)
  | readoutUnit :
      CellGenerator (FreeBicategory.Hom.id Mode.intensional)
        readoutDiscretePath
  | readoutCounit :
      CellGenerator discreteReadoutPath
        (FreeBicategory.Hom.id Mode.extensional)
  | discreteUnit :
      CellGenerator (FreeBicategory.Hom.id Mode.extensional)
        discretePointsPath
  | discreteCounit :
      CellGenerator pointsDiscretePath
        (FreeBicategory.Hom.id Mode.intensional)
  | factorForward :
      CellGenerator evidenceReadoutPath observePath
  | factorBackward :
      CellGenerator observePath evidenceReadoutPath

/-- Raw authored cells retain their constructor history. -/
abbrev ModeCell {source target : Mode}
    (first second : ModePath source target) :=
  FreeWhiskeredCell.Cell modeCellBase CellGenerator first second

/-! ## Interpretation of authored cells in `Cat` -/

/-- Semantic two-cells between interpretations of parallel modality paths. -/
abbrev SemanticCell {source target : Mode}
    (first second : ModePath source target) :=
  semanticPseudofunctor.{u}.map first ⟶
    semanticPseudofunctor.{u}.map second

/-- Interpret each authored generator using the independently proved
adjunctions and commuting natural isomorphism. -/
def interpretGenerator :
    {source target : Mode} →
    {first second : ModePath source target} →
      CellGenerator first second → SemanticCell.{u} first second
  | _, _, _, _, .operationalUnit => operationalEvidence.{u}.toCat.unit
  | _, _, _, _, .operationalCounit => operationalEvidence.{u}.toCat.counit
  | _, _, _, _, .readoutUnit => extensionalReadout.{u}.toCat.unit
  | _, _, _, _, .readoutCounit => extensionalReadout.{u}.toCat.counit
  | _, _, _, _, .discreteUnit => discretePoints.{u}.toCat.unit
  | _, _, _, _, .discreteCounit => discretePoints.{u}.toCat.counit
  | _, _, _, _, .factorForward =>
      (Cat.Hom.isoMk observationFactors.{u}).hom
  | _, _, _, _, .factorBackward =>
      (Cat.Hom.isoMk observationFactors.{u}).inv

/-- The semantic algebra for arbitrary raw whiskered cells. -/
def semanticCellAlgebra :
    FreeWhiskeredCell.Algebra modeCellBase CellGenerator SemanticCell.{u} where
  onRefl := fun path => 𝟙 (semanticPseudofunctor.{u}.map path)
  onGenerator := interpretGenerator
  onVertical := fun earlier later => earlier ≫ later
  onWhiskerLeft := @fun _source _middle _target prior _first _second cell =>
    semanticPseudofunctor.{u}.map prior ◁ cell
  onWhiskerRight := @fun _source _middle _target _first _second suffix cell =>
    cell ▷ semanticPseudofunctor.{u}.map suffix

/-- Canonical semantic interpretation of every raw authored cell. -/
def interpretCell
    {source target : Mode}
    {first second : ModePath source target} :
    ModeCell first second → SemanticCell.{u} first second :=
  semanticCellAlgebra.{u}.fold

/-- The authored forward comparison cell. -/
def factorCell : ModeCell evidenceReadoutPath observePath :=
  .generator .factorForward

/-- The authored unit cell for free evidence completion. -/
def operationalUnitCell :
    ModeCell (FreeBicategory.Hom.id Mode.operational)
      evidenceForgetPath :=
  .generator .operationalUnit

/-- The authored inverse comparison cell. -/
def factorCellInverse : ModeCell observePath evidenceReadoutPath :=
  .generator .factorBackward

/-- Raw syntax remembers that the round trip used two authored cells. -/
def factorRoundTrip :
    ModeCell evidenceReadoutPath evidenceReadoutPath :=
  .vertical factorCell factorCellInverse

theorem factorRoundTrip_not_reflexive :
    factorRoundTrip ≠
      FreeWhiskeredCell.Cell.refl (base := modeCellBase)
        (Generator := CellGenerator) evidenceReadoutPath := by
  intro equality
  cases equality

@[simp] theorem interpret_factorCell :
    interpretCell.{u} factorCell =
      (Cat.Hom.isoMk observationFactors.{u}).hom := by
  simp [interpretCell, factorCell, semanticCellAlgebra,
    interpretGenerator]

@[simp] theorem interpret_operationalUnitCell :
    interpretCell.{u} operationalUnitCell =
      operationalEvidence.{u}.toCat.unit := by
  simp [interpretCell, operationalUnitCell, semanticCellAlgebra,
    interpretGenerator]

@[simp] theorem interpret_factorCellInverse :
    interpretCell.{u} factorCellInverse =
      (Cat.Hom.isoMk observationFactors.{u}).inv := by
  simp [interpretCell, factorCellInverse, semanticCellAlgebra,
    interpretGenerator]

/-- Semantics validates the authored comparison as an isomorphism while the
raw syntax continues to retain the two-step receipt. -/
theorem interpret_factorRoundTrip :
    interpretCell.{u} factorRoundTrip =
      𝟙 (semanticPseudofunctor.{u}.map
        evidenceReadoutPath) := by
  change
    (Cat.Hom.isoMk observationFactors.{u}).hom ≫
        (Cat.Hom.isoMk observationFactors.{u}).inv =
      𝟙 ((evidenceCompletion.{u} ⋙ routeQuotient.{u}).toCatHom)
  exact (Cat.Hom.isoMk observationFactors.{u}).hom_inv_id

/-! ## Structural universality -/

/-- Once the eight generator meanings and structural operations are fixed,
the interpretation of every raw mode cell is unique. -/
theorem semantic_interpretation_unique
    (extension : FreeWhiskeredCell.Extension semanticCellAlgebra.{u}) :
    ∀ {source target : Mode}
      {first second : ModePath source target}
      (cell : ModeCell first second),
      extension.onCell cell = interpretCell.{u} cell :=
  FreeWhiskeredCell.Extension.onCell_unique extension

/-! ## Axiom audit -/

#print axioms path_shadow_does_not_commute_on_the_nose
#print axioms no_bare_factor_cell
#print axioms no_bare_operational_unit
#print axioms interpret_operationalUnitCell
#print axioms factorRoundTrip_not_reflexive
#print axioms interpret_factorRoundTrip
#print axioms semantic_interpretation_unique

end OperationalIntensionalExtensionalTwoComputad
end Mettapedia.TypeTheory
