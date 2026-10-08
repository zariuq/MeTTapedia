import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentEvidence
import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableIndexedPresheafRestriction
import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableIndexedSubstitution

/-!
# Generated dependent types for actual compiler receipts

The original map sends a complete source program-and-certificate value to
its actual compiled program. Its independently generated indexed type
recovers exactly the existing dependent-sum receipt. Yoneda recovery keeps
the entire coherent section, including the certificate's contextual action.

The generated model is over the explicitly lifted category of presheaves.
The comparison at represented observation worlds does not identify the two
ambient presheaf toposes or add dependent constructs to the lambda compiler.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedIndexedEvidence

open _root_.CategoryTheory Opposite
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open RepresentableIndexedDeclarations
open NamePassingDependentEvidence

noncomputable section

abbrev Base := PresheafReadout.Base ContextCategory

def receiptMap (A : DisplayedFamily sourcePrograms) : totalSpace A ⟶ compiledPrograms :=
  totalProjection A ≫ compilerMap

abbrev indexed (A : DisplayedFamily sourcePrograms) := PresheafReadout.indexed (receiptMap A)

abbrev NativeReceipt (A : DisplayedFamily sourcePrograms) (point : compiledPrograms.Elements) :=
  PresheafReadout.NativeFibre (receiptMap A) point.1.unop point.2

def receiptEquiv (A : DisplayedFamily sourcePrograms) (point : compiledPrograms.Elements) :
    NativeReceipt A point ≃ (compiledFamily A).obj point :=
  PresheafReadout.pointFibreEquiv (receiptMap A) point.1.unop point.2

def encodeReceipt (A : DisplayedFamily sourcePrograms) (point : compiledPrograms.Elements)
    (receipt : (compiledFamily A).obj point) : NativeReceipt A point :=
  PresheafReadout.encodePoint (receiptMap A) point.1.unop point.2 receipt.val receipt.property

theorem decode_encode (A : DisplayedFamily sourcePrograms) (point : compiledPrograms.Elements)
    (receipt : (compiledFamily A).obj point) :
    receiptEquiv A point (encodeReceipt A point receipt) = receipt :=
  PresheafReadout.decode_encode (receiptMap A) point.1.unop point.2 receipt.val receipt.property

theorem encode_decode (A : DisplayedFamily sourcePrograms) (point : compiledPrograms.Elements)
    (supplied : NativeReceipt A point) :
    encodeReceipt A point (receiptEquiv A point supplied) = supplied :=
  PresheafReadout.encode_decode (receiptMap A) point.1.unop point.2 supplied

def generatedType (A : DisplayedFamily sourcePrograms) :
    Derivation (signature Base) (.type (objectContext (indexed A).target)
      (fibreType (indexed A) (.var 0))) := genericFibreFormed (indexed A)

theorem generated_type_read (A : DisplayedFamily sourcePrograms) :
    (model Base).evaluateType (objectScope (indexed A).target) (fibreType (indexed A) (.var 0)) =
      some (fibreMeaning (indexed A)) := generic_fibre_read (indexed A)

theorem generated_forget_read (A : DisplayedFamily sourcePrograms) :
    (model Base).evaluateTerm (fibreScope (indexed A)) (genericForget (indexed A)) =
      some ⟨forgetType (indexed A), forgetValue (indexed A)⟩ := generic_forget_read (indexed A)

def suppliedReceipt (A : DisplayedFamily sourcePrograms) (point : sourcePrograms.Elements)
    (evidence : A.obj point) : NativeReceipt A (compilerMap.mapElements.obj point) :=
  encodeReceipt A (compilerMap.mapElements.obj point) ((carry A).app point evidence)

theorem supplied_receipt_read (A : DisplayedFamily sourcePrograms) (point : sourcePrograms.Elements)
    (evidence : A.obj point) :
    receiptEquiv A (compilerMap.mapElements.obj point) (suppliedReceipt A point evidence) =
      (carry A).app point evidence := decode_encode A _ _

theorem supplied_receipt_injective (A : DisplayedFamily sourcePrograms)
    (point : sourcePrograms.Elements) : Function.Injective (suppliedReceipt A point) := by
  intro first second same
  apply carry_injective A point
  have recovered := congrArg (receiptEquiv A (compilerMap.mapElements.obj point)) same
  rw [supplied_receipt_read, supplied_receipt_read] at recovered
  exact recovered

theorem complete_section_read (A : DisplayedFamily sourcePrograms) (point : compiledPrograms.Elements)
    (supplied : NativeReceipt A point) :
    (decode (indexed A) (op (PresheafReadout.worldObject point.1.unop))
      (PresheafReadout.argument (receiptMap A) point.1.unop point.2) supplied).val.down =
        yonedaEquiv.symm (receiptEquiv A point supplied).val :=
  PresheafReadout.complete_section_recovery (receiptMap A) point.1.unop point.2 supplied

theorem complete_future_read (A : DisplayedFamily sourcePrograms)
    {point future : compiledPrograms.Elements} (before : point ⟶ future)
    (supplied : NativeReceipt A point) :
    ((decode (indexed A) (op (PresheafReadout.worldObject point.1.unop))
      (PresheafReadout.argument (receiptMap A) point.1.unop point.2) supplied).val.down.app future.1)
        before.val.unop = (totalSpace A).map before.val (receiptEquiv A point supplied).val :=
  PresheafReadout.complete_future_readout (receiptMap A) point.1.unop future.1.unop
    before.val.unop point.2 supplied

/-- Restriction is the original dependent receipt action, reconstructed
as a complete generated fibre value at the next represented world. -/
def restrictReceipt (A : DisplayedFamily sourcePrograms)
    {point future : compiledPrograms.Elements} (before : point ⟶ future)
    (supplied : NativeReceipt A point) : NativeReceipt A future :=
  encodeReceipt A future ((compiledFamily A).map before (receiptEquiv A point supplied))

theorem restriction_read (A : DisplayedFamily sourcePrograms)
    {point future : compiledPrograms.Elements} (before : point ⟶ future)
    (supplied : NativeReceipt A point) :
    receiptEquiv A future (restrictReceipt A before supplied) =
      (compiledFamily A).map before (receiptEquiv A point supplied) := decode_encode A _ _

theorem restriction_identity (A : DisplayedFamily sourcePrograms) (point : compiledPrograms.Elements)
    (supplied : NativeReceipt A point) : restrictReceipt A (𝟙 point) supplied = supplied := by
  apply (receiptEquiv A point).injective
  rw [restriction_read]
  exact (compiledFamily A).map_id_apply point _

theorem restriction_composition (A : DisplayedFamily sourcePrograms)
    {point middle final : compiledPrograms.Elements} (first : point ⟶ middle)
    (second : middle ⟶ final) (supplied : NativeReceipt A point) :
    restrictReceipt A (first ≫ second) supplied =
      restrictReceipt A second (restrictReceipt A first supplied) := by
  apply (receiptEquiv A final).injective
  rw [restriction_read, restriction_read, restriction_read]
  exact (compiledFamily A).map_comp_apply first second _

def futurePoint (point : compiledPrograms.Elements) {future : ContextCategoryᵒᵖ}
    (before : point.1 ⟶ future) : compiledPrograms.Elements :=
  ⟨future, (show compiledPrograms.obj future from compiledPrograms.map before point.2)⟩

def futureArrow (point : compiledPrograms.Elements) {future : ContextCategoryᵒᵖ}
    (before : point.1 ⟶ future) : point ⟶ futurePoint point before :=
  CategoryOfElements.homMk point (futurePoint point before) before rfl

/-- On the canonical category-of-elements lift, the receipt restriction
is exactly the generated native family's own dependent reindexing action. -/
theorem restriction_is_native_action (A : DisplayedFamily sourcePrograms)
    (point : compiledPrograms.Elements) {future : ContextCategoryᵒᵖ}
    (before : point.1 ⟶ future) (supplied : NativeReceipt A point) :
    restrictReceipt A (futureArrow point before) supplied =
      PresheafReadout.restrict (receiptMap A) before.unop point.2 supplied := by
  apply (receiptEquiv A (futurePoint point before)).injective
  rw [restriction_read]
  apply Subtype.ext
  change (totalSpace A).map before (receiptEquiv A point supplied).val =
    (PresheafReadout.decodePoint (receiptMap A) future.unop
      (compiledPrograms.map before point.2)
      (PresheafReadout.restrict (receiptMap A) before.unop point.2 supplied)).val
  exact (PresheafReadout.restrict_decode (receiptMap A) before.unop point.2 supplied).symm

/-- Independently formed raw substitution along the original compiler
pulls back the actual generated certificate family. -/
theorem generated_compiler_substitution (A : DisplayedFamily sourcePrograms) :
    (model Base).evaluateType (objectScope (PresheafReadout.indexed compilerMap).source)
      ((fibreType (indexed A) (.var 0)).substitute
        (originalSubstitution (PresheafReadout.indexed compilerMap).arrow)) =
      some ((fibreMeaning (indexed A)).reindex
        (originalMap (PresheafReadout.indexed compilerMap).arrow)) :=
  complete_indexed_family_substitution (indexed A) (PresheafReadout.indexed compilerMap).arrow

end

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedIndexedEvidence
