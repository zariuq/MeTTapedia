import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingObserverFunctor
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingObserverAdequacy
import Mettapedia.TypeTheory.DisplayedPresheafEvidenceCoherence
import Mettapedia.TypeTheory.PresheafDependentIdentity

/-!
# Proof-retaining native families at the name-passing compiler interface

The actual context-natural compiler induces dependent-sum transport of any
coherent certificate family. Its total context is naturally isomorphic to
the original program-and-certificate context, with projection equal to
compilation. Public-return validity is checked by executing the emitted rho
program through the established spine. This interface does not identify the
observer-context category with a variable-substitution classifying theory.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentEvidence

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafEvidenceTransport
open NamePassingLambda NamePassingContexts NamePassingObserverFunctor
open NamePassingObserverAdequacy

abbrev ContextCategory := SourceScopeᵒᵖ

def sourcePrograms : ContextCategoryᵒᵖ ⥤ Type :=
  (opOpEquivalence SourceScope).functor ⋙ sourceInterpretation

def compiledPrograms : ContextCategoryᵒᵖ ⥤ Type :=
  (opOpEquivalence SourceScope).functor ⋙ translation ⋙ protocolInterpretation

def compilerMap : sourcePrograms ⟶ compiledPrograms :=
  Functor.whiskerLeft (opOpEquivalence SourceScope).functor compilation

def compiledFamily (A : DisplayedFamily sourcePrograms) : DisplayedFamily compiledPrograms :=
  transport compilerMap A

def carry (A : DisplayedFamily sourcePrograms) :
    A ⟶ reindexDisplayed compilerMap (compiledFamily A) := unit compilerMap A

theorem carry_injective (A : DisplayedFamily sourcePrograms) (point : sourcePrograms.Elements) :
    Function.Injective ((carry A).app point) := unit_injective compilerMap A point

def programAndCertificateIso (A : DisplayedFamily sourcePrograms) :
    totalSpace (compiledFamily A) ≅ totalSpace A := totalIso compilerMap A

theorem programAndCertificate_projection (A : DisplayedFamily sourcePrograms) :
    (programAndCertificateIso A).hom ≫ totalProjection A ≫ compilerMap =
      totalProjection (compiledFamily A) := totalIso_projection compilerMap A

/-- The original source program and its supplied certificate are recovered
from a transported receipt without proof search or a choice of origin. -/
theorem supplied_certificate_retained (A : DisplayedFamily sourcePrograms)
    (point : sourcePrograms.Elements) (evidence : A.obj point) :
    ((carry A).app point evidence).val = ⟨point.2, evidence⟩ := rfl

/-- Any actual ordered-premise readout of the supplied certificate is
retained literally. The readout need not factor through program behavior. -/
theorem ordered_uses_retained (A : DisplayedFamily sourcePrograms)
    (point : sourcePrograms.Elements) (evidence : A.obj point)
    {Use : Type} (uses : A.obj point → List Use) :
    uses ((carry A).app point evidence).val.2 = uses evidence := rfl

/-- A valid public-return certificate of the retained source certifies the
actual target execution, through the independently checked compiler theorem. -/
theorem receipt_public_return (A : DisplayedFamily sourcePrograms)
    (point : compiledPrograms.Elements) (receipt : (compiledFamily A).obj point)
    (returned : MayReturn receipt.val.1) : ProtocolMayReturn point.2 := by
  have emitted := receipt.property
  dsimp [totalProjection, compilerMap, compilation] at emitted
  exact (congrArg (fun component => ProtocolMayReturn component) emitted).mp
    ((mayReturn_iff receipt.val.1).mp returned)

theorem receipt_public_return_iff (A : DisplayedFamily sourcePrograms)
    (point : compiledPrograms.Elements) (receipt : (compiledFamily A).obj point) :
    MayReturn receipt.val.1 ↔ ProtocolMayReturn point.2 := by
  have emitted := receipt.property
  dsimp [totalProjection, compilerMap, compilation] at emitted
  exact (mayReturn_iff receipt.val.1).trans
    (iff_of_eq (congrArg (fun component => ProtocolMayReturn component) emitted))

/-- Actual native dependent abstraction/application over the compiled
certificate family returns the same receipt and therefore the same proof. -/
noncomputable def applyCertificateIdentity (A : DisplayedFamily sourcePrograms)
    (world : ContextCategoryᵒᵖ) (value : (totalSpace (compiledFamily A)).obj world) :
    (totalSpace (compiledFamily A)).obj world :=
  let f := totalProjection (compiledFamily A)
  (pullback.fst f f).app world
    ((PresheafDependentAdjunction.evaluation f ((Over.pullback f).obj (Over.mk f))).left.app world
      (((Over.pullback f).map (PresheafDependentIdentity.identityFunction f)).left.app world
        ((PresheafDependentIdentity.argumentMap f).app world value)))

theorem applyCertificateIdentity_retains (A : DisplayedFamily sourcePrograms)
    (world : ContextCategoryᵒᵖ) (value : (totalSpace (compiledFamily A)).obj world) :
    applyCertificateIdentity A world value = value :=
  PresheafDependentIdentity.identity_retains_value (totalProjection (compiledFamily A)) world value

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentEvidence
