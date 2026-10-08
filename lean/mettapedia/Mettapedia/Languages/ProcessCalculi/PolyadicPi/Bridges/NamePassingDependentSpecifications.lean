import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentEvidence
import Mettapedia.TypeTheory.DisplayedPresheafEvidenceUniversal
import Mettapedia.TypeTheory.DisplayedPresheafPiSubstitution
import Mettapedia.TypeTheory.DisplayedPresheafClassifier

/-!
# Universal dependent specifications at the actual compiler interface

Every coherent target specification is reached by a unique evidence map
precisely when its compiler pullback is justified by the source family.
The map computes on supplied certificates and composes through subsequent
native transports. Public-return claims use the existing execution
comparison; the hom-set universal property does not manufacture them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentSpecifications

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafSliceSubstitution
open DisplayedPresheafEvidenceTransport DisplayedPresheafEvidenceUniversal
open NamePassingDependentEvidence NamePassingObserverAdequacy

/-- Quantification ranges over every coherent target family, rather than
only the storage representation of an individual source certificate. -/
def specificationEquiv (A : DisplayedFamily sourcePrograms)
    (B : DisplayedFamily compiledPrograms) :
    (compiledFamily A ⟶ B) ≃ (A ⟶ reindexDisplayed compilerMap B) :=
  DisplayedPresheafEvidenceUniversal.specificationEquiv compilerMap A B

def realize {A : DisplayedFamily sourcePrograms} {B : DisplayedFamily compiledPrograms}
    (body : A ⟶ reindexDisplayed compilerMap B) : compiledFamily A ⟶ B :=
  descend compilerMap body

theorem realization_computes {A : DisplayedFamily sourcePrograms}
    {B : DisplayedFamily compiledPrograms} (body : A ⟶ reindexDisplayed compilerMap B)
    (point : sourcePrograms.Elements) (evidence : A.obj point) :
    (realize body).app (compilerMap.mapElements.obj point)
        ((carry A).app point evidence) = body.app point evidence :=
  descend_unit compilerMap body point evidence

theorem realization_unique {A : DisplayedFamily sourcePrograms}
    {B : DisplayedFamily compiledPrograms} (body : A ⟶ reindexDisplayed compilerMap B)
    (target : compiledFamily A ⟶ B)
    (computes : carry A ≫ (reindexFunctor compilerMap).map target = body) :
    target = realize body := descend_unique compilerMap body target computes

theorem specification_exists_iff (A : DisplayedFamily sourcePrograms)
    (B : DisplayedFamily compiledPrograms) :
    Nonempty (compiledFamily A ⟶ B) ↔ Nonempty (A ⟶ reindexDisplayed compilerMap B) :=
  DisplayedPresheafEvidenceUniversal.specification_exists_iff compilerMap A B

theorem realization_naturality {A : DisplayedFamily sourcePrograms}
    {B D : DisplayedFamily compiledPrograms}
    (body : A ⟶ reindexDisplayed compilerMap B) (changeEvidence : B ⟶ D) :
    realize (body ≫ (reindexFunctor compilerMap).map changeEvidence) =
      realize body ≫ changeEvidence := descend_naturality compilerMap body changeEvidence

/-- The specification witness is supplied together with a real public
execution of the emitted program, under the source return hypothesis. -/
theorem realization_and_public_execution {A : DisplayedFamily sourcePrograms}
    {B : DisplayedFamily compiledPrograms} (body : A ⟶ reindexDisplayed compilerMap B)
    (point : sourcePrograms.Elements) (evidence : A.obj point)
    (returned : MayReturn point.2) :
    (realize body).app (compilerMap.mapElements.obj point)
        ((carry A).app point evidence) = body.app point evidence ∧
      ProtocolMayReturn (compilerMap.app point.1 point.2) :=
  ⟨realization_computes body point evidence,
    receipt_public_return A (compilerMap.mapElements.obj point)
      ((carry A).app point evidence) returned⟩

/-- Source and target validity agree at every supplied receipt, including
receipts not presented syntactically as applications of `carry`. -/
theorem arbitrary_receipt_execution (A : DisplayedFamily sourcePrograms)
    (point : compiledPrograms.Elements) (receipt : (compiledFamily A).obj point) :
    MayReturn receipt.val.1 ↔ ProtocolMayReturn point.2 :=
  receipt_public_return_iff A point receipt

/-- The compiler is a map inside this one native topos. Its pullback has
both quantifier adjoints on the actual proof-valued family categories. -/
noncomputable def nativeAdjoints :
    (transportFunctor compilerMap ⊣ reindexFunctor compilerMap) ×
      (reindexFunctor compilerMap ⊣ compilerMap.mapElements.ran) :=
  familyAdjointTriple compilerMap

/-- Native dependent products substitute through compilation using the
same formation comparison as the shared presheaf CwF. -/
noncomputable def functionSubstitution (A : DisplayedFamily compiledPrograms)
    (B : DisplayedFamily (totalSpace A)) :
    DisplayedPresheafPi.piDisplayed (reindexDisplayed compilerMap A)
        (reindexDisplayed (totalReindexMap compilerMap A) B) ≅
      reindexDisplayed compilerMap (DisplayedPresheafPi.piDisplayed A B) :=
  DisplayedPresheafPiSubstitution.piSubstitutionIso compilerMap A B

theorem pairSubstitution (A : DisplayedFamily compiledPrograms)
    (B : DisplayedFamily (totalSpace A)) :
    reindexDisplayed compilerMap (DisplayedPresheafSigma.sigmaDisplayed A B) =
      DisplayedPresheafSigma.sigmaDisplayed (reindexDisplayed compilerMap A)
        (reindexDisplayed (totalReindexMap compilerMap A) B) :=
  DisplayedPresheafSigma.sigmaDisplayed_reindex compilerMap A B

theorem propositionSubstitution :
    reindexDisplayed compilerMap (DisplayedPresheafClassifier.propositions compiledPrograms) =
      DisplayedPresheafClassifier.propositions sourcePrograms :=
  DisplayedPresheafClassifier.propositions_substitution compilerMap

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentSpecifications
