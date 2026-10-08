import Mettapedia.TypeTheory.JudgmentPresheafEvidence
import Mettapedia.TypeTheory.JudgmentPresentationControls
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Contextual proof interpretation and literal receipt readouts

One contextual model retains proof trees, while another reads their ordered
leaf labels. Their transition is the derived initial interpreter, rather
than an unrelated assignment of values. Native compiler receipts retain two
different trees at the same emitted program; the ordered readout continues
to distinguish them even when a premise-dropping translation would not.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.JudgmentPresheafEvidenceControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open JudgmentDerivation JudgmentPresentationControls JudgmentPresheafEvidence
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafEvidenceTransport

abbrev Worlds := WalkingParallelPair

def programs : Worldsᵒᵖ ⥤ Type := (Functor.const _).obj Nat

/-- The carriers change from actual trees to ordered ledgers. -/
def modelDiagram : Worlds ⥤ Algebra source :=
  parallelPair (interpretation ledger) (interpretation ledger)

def models : programs.Elements ⥤ Algebra source :=
  CategoryOfElements.π programs ⋙ walkingParallelPairOpEquiv.inverse ⋙ modelDiagram

def upper : programs.Elements := ⟨Opposite.op .one, (7 : Nat)⟩
def lower : programs.Elements := ⟨Opposite.op .zero, (7 : Nat)⟩

def route : upper ⟶ lower :=
  ⟨(show (.zero : Worlds) ⟶ .one from WalkingParallelPairHom.left).op, rfl⟩

theorem upper_interpretation (first second : Bool) :
    (interpretationMap models .unit).app upper (fork first second) = fork first second :=
  interpret_generated _

theorem lower_interpretation (first second : Bool) :
    (interpretationMap models .unit).app lower (fork first second) = [first, second] := rfl

/-- A real context arrow computes the ledger from the supplied proof tree. -/
theorem context_arrow_computes (first second : Bool) :
    (evidenceFamily models .unit).map route (fork first second) = [first, second] := rfl

theorem generated_section_is_coherent (first second : Bool) :
    (evidenceFamily models .unit).map route
        ((interpretedSection models (fork first second)).val upper) =
      (interpretedSection models (fork first second)).val lower :=
  (interpretedSection models (fork first second)).property route

/-- A noninjective program map has a native dependent-sum receipt; no raw
proof translation is substituted for its origin-retaining action. -/
def programMap : programs ⟶ programs where
  app _ := TypeCat.ofHom (fun program : Nat => program % 2)

def emitted : programs.Elements := programMap.mapElements.obj lower

def receipt (first second : Bool) :
    (transport programMap (derivationFamily (S := source) programs PUnit.unit)).obj emitted :=
  (unit programMap (derivationFamily (S := source) programs PUnit.unit)).app lower (fork first second)

theorem receipts_distinct : receipt false false ≠ receipt false true := by
  intro equal
  exact supplied_proofs_distinct
    (unit_injective programMap (derivationFamily (S := source) programs PUnit.unit) lower equal)

theorem receipt_readout (first second : Bool) :
    (receiptReadout programMap models .unit).app emitted (receipt first second) =
      [first, second] :=
  receiptReadout_computes programMap models lower (fork first second)

theorem receipt_readouts_distinguish :
    (receiptReadout programMap models .unit).app emitted (receipt false false) ≠
      (receiptReadout programMap models .unit).app emitted (receipt false true) := by
  change ([false, false] : List Bool) ≠ [false, true]
  decide

/-- A source premise-dropping translation is lossy, while the native
receipt's certified ordered readout keeps the source distinction. -/
theorem lossy_translation_and_retained_receipts :
    firstPremise.translate (fork false false) = firstPremise.translate (fork false true) ∧
      receipt false false ≠ receipt false true :=
  ⟨translation_omits_second_premise, receipts_distinct⟩

end Mettapedia.TypeTheory.JudgmentPresheafEvidenceControls
