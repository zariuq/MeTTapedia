import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedIndexedEvidence
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentSpecifications
import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableIndexedForgetSubstitution

/-!
# Generated terms for independently supplied compiler specifications

An authored source certificate implementation determines a map of complete
program-and-certificate values. The generated term composes that original
map with the actual receipt's forgetful substitution. Its native output is
the same whole target certificate as universal sum elimination, at every
represented observation world and along every future contextual arrow.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedIndexedSpecifications

open _root_.CategoryTheory Opposite
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafSlice
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open ContextualModelTelescopes NativeLocalTypeFormers
open RepresentableIndexedDeclarations
open NamePassingDependentEvidence NamePassingDependentSpecifications
open NamePassingGeneratedIndexedEvidence

noncomputable section

variable {A : DisplayedFamily sourcePrograms} {B : DisplayedFamily compiledPrograms}

def specificationMap (body : A ⟶ reindexDisplayed compilerMap B) :
    totalSpace A ⟶ totalSpace B :=
  DisplayedPresheafEvidenceUniversal.evidenceTotalMap compilerMap body

theorem specification_projection (body : A ⟶ reindexDisplayed compilerMap B) :
    specificationMap body ≫ totalProjection B = receiptMap A :=
  DisplayedPresheafEvidenceUniversal.evidenceTotalMap_projection compilerMap body

def specificationArrow (body : A ⟶ reindexDisplayed compilerMap B) :
    (indexed A).source ⟶ (PresheafReadout.indexed (totalProjection B)).source :=
  ⟨specificationMap body⟩

def specificationTerm (body : A ⟶ reindexDisplayed compilerMap B) : TermExpr (symbols Base) 2 :=
  forgetArrowTerm (indexed A) (specificationArrow body)

def specificationTermFormed (body : A ⟶ reindexDisplayed compilerMap B) :
    Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Derivation (signature Base)
      (.term (fibreContext (indexed A)) (specificationTerm body)
        (objectType (PresheafReadout.indexed (totalProjection B)).source 2)) :=
  forgetArrowFormed (indexed A) (specificationArrow body)

def specificationValue (body : A ⟶ reindexDisplayed compilerMap B) :
    NativeValue (fibreScope (indexed A)).1 :=
  Value.substitute (K := (NativeModel Base).toCwf)
    (⟨RepresentableDeclarations.arrowMeaning ⟨(indexed A).source,
        (PresheafReadout.indexed (totalProjection B)).source,
        specificationArrow body⟩,
      RepresentableDeclarations.arrowValue ⟨(indexed A).source,
        (PresheafReadout.indexed (totalProjection B)).source,
        specificationArrow body⟩⟩ : NativeValue (objectScope (indexed A).source).1)
    (forgetMap (indexed A))

theorem generated_specification_read (body : A ⟶ reindexDisplayed compilerMap B) :
    (model Base).evaluateTerm (fibreScope (indexed A)) (specificationTerm body) =
      some (specificationValue body) := forget_arrow_read (indexed A) (specificationArrow body)

theorem complete_specification_section (body : A ⟶ reindexDisplayed compilerMap B)
    (point : compiledPrograms.Elements) (supplied : NativeReceipt A point) :
    ((specificationValue body).2.val
      ⟨op (PresheafReadout.worldObject point.1.unop),
        ⟨PresheafReadout.argument (receiptMap A) point.1.unop point.2, supplied⟩⟩).down =
      (decode (indexed A) (op (PresheafReadout.worldObject point.1.unop))
        (PresheafReadout.argument (receiptMap A) point.1.unop point.2) supplied).val.down ≫
          specificationMap body := rfl

abbrev NativeSpecification (B : DisplayedFamily compiledPrograms) (point : compiledPrograms.Elements) :=
  PresheafReadout.NativeFibre (totalProjection B) point.1.unop point.2

def specificationEquiv (B : DisplayedFamily compiledPrograms) (point : compiledPrograms.Elements) :
    NativeSpecification B point ≃ B.obj point :=
  (PresheafReadout.pointFibreEquiv (totalProjection B) point.1.unop point.2).trans
    (projectionFibreEquiv B point).symm

/-- This value uses the independently authored source implementation map.
The comparison with universal elimination is proved below. -/
def applySpecification (body : A ⟶ reindexDisplayed compilerMap B)
    (point : compiledPrograms.Elements) (supplied : NativeReceipt A point) :
    NativeSpecification B point :=
  PresheafReadout.encodePoint (totalProjection B) point.1.unop point.2
    ((specificationMap body).app point.1 (receiptEquiv A point supplied).val) (by
      have commutes := congrArg
        (fun arrow : totalSpace A ⟶ compiledPrograms =>
          (show compiledPrograms.obj point.1 from
            arrow.app point.1 (receiptEquiv A point supplied).val)) (specification_projection body)
      exact commutes.trans (receiptEquiv A point supplied).property)

theorem specification_current_read (body : A ⟶ reindexDisplayed compilerMap B)
    (point : compiledPrograms.Elements) (supplied : NativeReceipt A point) :
    specificationEquiv B point (applySpecification body point supplied) =
      (realize body).app point (receiptEquiv A point supplied) := by
  change (projectionFibreEquiv B point).symm
      (PresheafReadout.decodePoint (totalProjection B) point.1.unop point.2
        (applySpecification body point supplied)) = _
  rw [applySpecification, PresheafReadout.decode_encode]
  rfl

theorem generated_term_complete_current (body : A ⟶ reindexDisplayed compilerMap B)
    (point : compiledPrograms.Elements) (supplied : NativeReceipt A point) :
    yonedaEquiv (((specificationValue body).2.val
      ⟨op (PresheafReadout.worldObject point.1.unop),
        ⟨PresheafReadout.argument (receiptMap A) point.1.unop point.2, supplied⟩⟩).down) =
      (specificationMap body).app point.1 (receiptEquiv A point supplied).val := by
  rw [complete_specification_section, complete_section_read, yonedaEquiv_comp]
  exact congrArg (fun value : (totalSpace A).obj point.1 =>
    (show (totalSpace B).obj point.1 from (specificationMap body).app point.1 value))
      (yonedaEquiv.apply_symm_apply (receiptEquiv A point supplied).val)

/-- The parsed generated term returns the target program together with
the complete universal specification witness, not only its support. -/
theorem generated_term_universal_readout (body : A ⟶ reindexDisplayed compilerMap B)
    (point : compiledPrograms.Elements) (supplied : NativeReceipt A point) :
    yonedaEquiv (((specificationValue body).2.val
      ⟨op (PresheafReadout.worldObject point.1.unop),
        ⟨PresheafReadout.argument (receiptMap A) point.1.unop point.2, supplied⟩⟩).down) =
      (⟨point.2, (realize body).app point (receiptEquiv A point supplied)⟩ :
        (totalSpace B).obj point.1) := by
  have recovered := congrArg Subtype.val
    ((projectionFibreEquiv B point).apply_symm_apply
      (PresheafReadout.decodePoint (totalProjection B) point.1.unop point.2
        (applySpecification body point supplied)))
  change (⟨point.2, specificationEquiv B point (applySpecification body point supplied)⟩ :
      (totalSpace B).obj point.1) = _ at recovered
  rw [specification_current_read, applySpecification, PresheafReadout.decode_encode] at recovered
  exact (generated_term_complete_current body point supplied).trans recovered.symm

theorem generated_receipt_specification_unique (body : A ⟶ reindexDisplayed compilerMap B)
    (target : compiledFamily A ⟶ B)
    (computes : ∀ (point : sourcePrograms.Elements) (evidence : A.obj point),
      target.app (compilerMap.mapElements.obj point)
        (receiptEquiv A (compilerMap.mapElements.obj point) (suppliedReceipt A point evidence)) =
          body.app point evidence) : target = realize body := by
  apply realization_unique body target
  ext point evidence
  have read := computes point evidence
  rw [supplied_receipt_read] at read
  exact read

theorem supplied_specification_computes (body : A ⟶ reindexDisplayed compilerMap B)
    (point : sourcePrograms.Elements) (evidence : A.obj point) :
    specificationEquiv B (compilerMap.mapElements.obj point)
      (applySpecification body (compilerMap.mapElements.obj point) (suppliedReceipt A point evidence)) =
        body.app point evidence := by
  rw [specification_current_read, supplied_receipt_read]
  exact realization_computes body point evidence

theorem specification_future_read (body : A ⟶ reindexDisplayed compilerMap B)
    {point future : compiledPrograms.Elements} (before : point ⟶ future)
    (supplied : NativeReceipt A point) :
    specificationEquiv B future (applySpecification body future (restrictReceipt A before supplied)) =
      B.map before (specificationEquiv B point (applySpecification body point supplied)) := by
  rw [specification_current_read, restriction_read, specification_current_read]
  exact (realize body).naturality_apply before _

theorem supplied_complete_value (body : A ⟶ reindexDisplayed compilerMap B)
    (point : sourcePrograms.Elements) (evidence : A.obj point) :
    (specificationMap body).app point.1 ⟨point.2, evidence⟩ =
      (⟨compilerMap.app point.1 point.2, body.app point evidence⟩ : (totalSpace B).obj point.1) := rfl

end

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedIndexedSpecifications
