import Mettapedia.TypeTheory.DisplayedPresheafRefinementTransport
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentRuntimeEvidence

/-!
# Native refinement certificates on actual compiled execution prefixes

A predicate-respecting implementation into an independently supplied target
family extends to the actual compiler's origin-retaining refinement receipt.
Every supplied core-rho prefix keeps the selected initial witness, its
predicate membership, the computed target refinement and the exact operational
history. The native certificate describes the supplied initial program.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRefinementEvidence

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafRefinementTransport
open NamePassingDependentEvidence NamePassingDependentRuntimeEvidence
open NamePassingUnaryForward NamePassingEnvironmentEquationsNative

variable (A : DisplayedFamily sourcePrograms) (B : DisplayedFamily compiledPrograms)
variable (body : A ⟶ reindexDisplayed compilerMap B)
variable (sourcePredicate : Subfunctor (totalSpace A))
variable (targetPredicate : Subfunctor (totalSpace B))
variable (respects : sourcePredicate ≤ targetPredicate.preimage
  (DisplayedPresheafEvidenceUniversal.evidenceTotalMap compilerMap body))

/-- This is the actual runtime receipt for the two refined families and
the earned predicate-respecting source implementation. -/
abbrev RuntimeReceipt (point : sourcePrograms.Elements)
    (selected : (Refinement.displayed A sourcePredicate).obj point)
    (world : NamePassingSpine.World (scope point)) (code : RhoUnaryCode.Code 0)
    {final : RhoUnaryReadback.TargetProcess}
    (actual : ExecutionPath RhoUnaryReadback.Target
      (RhoUnaryReadback.runtimeProcess code world.available) final) :=
  NamePassingDependentRuntimeEvidence.Receipt
    (Refinement.displayed A sourcePredicate) (Refinement.displayed B targetPredicate)
    (liftSource compilerMap body sourcePredicate targetPredicate respects)
    point selected world code actual

/-- The real compiler equation and any supplied target execution prefix
produce a native refinement receipt with that exact operational endpoint. -/
theorem retain_refined_prefix (point : sourcePrograms.Elements)
    (selected : (Refinement.displayed A sourcePredicate).obj point)
    (world : NamePassingSpine.World (scope point)) (code : RhoUnaryCode.Code 0)
    (compiled : NamePassingRho.compile point.2 (references (scope point)) .zero
      world.world = some code) {final : RhoUnaryReadback.TargetProcess}
    (actual : ExecutionPath RhoUnaryReadback.Target
      (RhoUnaryReadback.runtimeProcess code world.available) final) :
    Nonempty (RuntimeReceipt A B body sourcePredicate targetPredicate respects
      point selected world code actual) :=
  retain_prefix _ _ (liftSource compilerMap body sourcePredicate targetPredicate respects)
    point selected world code compiled actual

variable {A B body sourcePredicate targetPredicate respects}
variable {point : sourcePrograms.Elements}
variable {selected : (Refinement.displayed A sourcePredicate).obj point}
variable {world : NamePassingSpine.World (scope point)} {code : RhoUnaryCode.Code 0}
variable {final : RhoUnaryReadback.TargetProcess}
variable {actual : ExecutionPath RhoUnaryReadback.Target
  (RhoUnaryReadback.runtimeProcess code world.available) final}

/-- The sum/refinement comparison applies to the native certificate
stored with this execution prefix. -/
def RuntimeReceipt.selectedReceipt
    (receipt : RuntimeReceipt A B body sourcePredicate targetPredicate respects
      point selected world code actual) :
    (Refinement.displayed (compiledFamily A)
      (receiptPredicate compilerMap A sourcePredicate)).obj
        (compilerMap.mapElements.obj point) :=
  (transportIso compilerMap A sourcePredicate).hom.app
    (compilerMap.mapElements.obj point) receipt.nativeCertificate

theorem RuntimeReceipt.selectedReceipt_origin
    (receipt : RuntimeReceipt A B body sourcePredicate targetPredicate respects
      point selected world code actual) :
    receipt.selectedReceipt.val.val.1 = point.2 := by
  simp only [RuntimeReceipt.selectedReceipt, receipt.carried]
  rfl

theorem RuntimeReceipt.selectedReceipt_witness
    (receipt : RuntimeReceipt A B body sourcePredicate targetPredicate respects
      point selected world code actual) :
    HEq receipt.selectedReceipt.val.val.2 selected.val := by
  have pair : receipt.selectedReceipt.val.val = ⟨point.2, selected.val⟩ := by
    change (⟨receipt.nativeCertificate.val.1, receipt.nativeCertificate.val.2.val⟩ :
      (totalSpace A).obj point.1) = _
    rw [receipt.carried]
    rfl
  exact (Sigma.mk.inj_iff.mp pair).2

/-- Universal elimination computes the supplied target implementation,
while target predicate membership is part of the stored specification. -/
theorem RuntimeReceipt.specification_value
    (receipt : RuntimeReceipt A B body sourcePredicate targetPredicate respects
      point selected world code actual) :
    receipt.specification.val = body.app point selected.val := by
  rw [receipt.computed]
  rfl

theorem RuntimeReceipt.specification_membership
    (receipt : RuntimeReceipt A B body sourcePredicate targetPredicate respects
      point selected world code actual) :
    (⟨(compilerMap.mapElements.obj point).2, receipt.specification.val⟩ :
      (totalSpace B).obj point.1) ∈ targetPredicate.obj point.1 :=
  receipt.specification.property

/-- The original selected witness remains paired with the complete
reflected history; no current-state refinement is inferred from it. -/
theorem RuntimeReceipt.initial_membership
    (receipt : RuntimeReceipt A B body sourcePredicate targetPredicate respects
      point selected world code actual) :
    (⟨point.2, receipt.history.2.val⟩ : (totalSpace A).obj point.1) ∈
      sourcePredicate.obj point.1 := receipt.history.2.property

theorem RuntimeReceipt.ordered_uses
    (receipt : RuntimeReceipt A B body sourcePredicate targetPredicate respects
      point selected world code actual) {Use : Type} (uses : A.obj point → List Use) :
    uses receipt.history.2.val = uses selected.val := rfl

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRefinementEvidence
