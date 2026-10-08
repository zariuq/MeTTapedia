import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalPartnerObservations
import Mettapedia.CategoryTheory.FiniteActionTreeAssays

/-!
# Future re-assay of complete closed COMM partner interactions

Readouts are supplied independently of the reduction relation. At every reached
state they must agree, and every actual reaction under every supplied parallel
partner must be matched. The actual coloured cofree observation has exactly this
kernel. Addressed reaction occurrences remain beside their target observations;
equal coloured endpoints do not identify their origins.

The interaction profile is closed COMM. No RUN rule or arbitrary quotation and
binding congruence is added here. A supplied assay is not automatically a
structural instrument kit; grammar, equation and runtime admission are separate.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalPartnerAssays

open Mettapedia.CategoryTheory
open CanonicalBag CanonicalReaction CanonicalPartnerCoalgebra CanonicalPartnerObservations

variable {Colours : Type}

def Admitted (readout : Bag → Colours) (relation : Bag → Bag → Prop) : Prop :=
  ∀ source other, relation source other →
    readout source = readout other ∧ ∀ partner,
      (∀ target, Reaction (append source partner) target →
        ∃ matched, Reaction (append other partner) matched ∧ relation target matched) ∧
      (∀ target, Reaction (append other partner) target →
        ∃ matched, Reaction (append source partner) matched ∧ relation matched target)

def Bisimilar (readout : Bag → Colours) (source other : Bag) : Prop :=
  ∃ relation, Admitted readout relation ∧ relation source other

theorem admitted_iff_complete_matching (readout : Bag → Colours)
    (relation : Bag → Bag → Prop) :
    Admitted readout relation ↔
      FiniteActionTreeAssays.Admitted successors successors readout readout relation := by
  constructor
  · intro admitted source other held
    refine ⟨(admitted source other held).1, fun partner => ⟨?_, ?_⟩⟩
    · intro target member
      obtain ⟨matched, reaction, related⟩ :=
        ((admitted source other held).2 partner).1 target
          ((mem_successors_iff_reaction source partner target).1 member)
      exact ⟨matched, (mem_successors_iff_reaction other partner matched).2 reaction, related⟩
    · intro target member
      obtain ⟨matched, reaction, related⟩ :=
        ((admitted source other held).2 partner).2 target
          ((mem_successors_iff_reaction other partner target).1 member)
      exact ⟨matched, (mem_successors_iff_reaction source partner matched).2 reaction, related⟩
  · intro admitted source other held
    refine ⟨(admitted source other held).1, fun partner => ⟨?_, ?_⟩⟩
    · intro target reaction
      obtain ⟨matched, member, related⟩ := ((admitted source other held).2 partner).1 target
        ((mem_successors_iff_reaction source partner target).2 reaction)
      exact ⟨matched, (mem_successors_iff_reaction other partner matched).1 member, related⟩
    · intro target reaction
      obtain ⟨matched, member, related⟩ := ((admitted source other held).2 partner).2 target
        ((mem_successors_iff_reaction other partner target).2 reaction)
      exact ⟨matched, (mem_successors_iff_reaction source partner matched).1 member, related⟩

theorem future_assay_iff_bisimilar (readout : Bag → Colours) (source other : Bag) :
    certificateObservation Colours readout source = certificateObservation Colours readout other ↔
      Bisimilar readout source other := by
  change FiniteActionTreeAssays.observe successors readout source =
    FiniteActionTreeAssays.observe successors readout other ↔ _
  rw [FiniteActionTreeAssays.observation_eq_iff_bisimilar]
  constructor
  · rintro ⟨relation, admitted, held⟩
    exact ⟨relation, (admitted_iff_complete_matching readout relation).2 admitted, held⟩
  · rintro ⟨relation, admitted, held⟩
    exact ⟨relation, (admitted_iff_complete_matching readout relation).1 admitted, held⟩

theorem root_agreement (readout : Bag → Colours) {source other : Bag}
    (related : Bisimilar readout source other) : readout source = readout other := by
  obtain ⟨relation, admitted, held⟩ := related
  exact (admitted source other held).1

theorem interaction_of_assay (readout : Bag → Colours) {source other : Bag}
    (related : Bisimilar readout source other) :
    CanonicalPartnerObservations.Bisimilar source other := by
  obtain ⟨relation, admitted, held⟩ := related
  exact ⟨relation, fun first second paired => (admitted first second paired).2, held⟩

theorem weaken (readout : Bag → Colours) {Other : Type} (mapping : Colours → Other)
    {source other : Bag} (related : Bisimilar readout source other) :
    Bisimilar (mapping ∘ readout) source other := by
  obtain ⟨relation, admitted, held⟩ := related
  refine ⟨relation, ?_, held⟩
  intro first second paired
  exact ⟨congrArg mapping ((admitted first second paired).1),
    (admitted first second paired).2⟩

structure AssayedReceipt (readout : Bag → Colours) (source partner : Bag) where
  occurrence : Receipt source partner
  targetObservation : FiniteActionTree.Tree Bag Colours
  checked : targetObservation = certificateObservation Colours readout occurrence.target

def assayReceipt (readout : Bag → Colours) (source partner : Bag)
    (receipt : Receipt source partner) : AssayedReceipt readout source partner :=
  ⟨receipt, certificateObservation Colours readout receipt.target, rfl⟩

theorem supplied_occurrence_retained (readout : Bag → Colours) (source partner : Bag)
    (receipt : Receipt source partner) :
    (assayReceipt readout source partner receipt).occurrence = receipt := rfl

theorem AssayedReceipt.target_root {readout : Bag → Colours} {source partner : Bag}
    (receipt : AssayedReceipt readout source partner) :
    FiniteActionTree.Tree.root receipt.targetObservation = readout receipt.occurrence.target := by
  rw [receipt.checked, certificate_root]

theorem AssayedReceipt.successor {readout : Bag → Colours} {source partner : Bag}
    (receipt : AssayedReceipt readout source partner) :
    receipt.targetObservation ∈
      FiniteActionTree.Tree.step (certificateObservation Colours readout source) partner := by
  rw [receipt.checked, certificate_successors, FinitePowerset.mem_map]
  exact ⟨receipt.occurrence.target, receipt_member source partner receipt.occurrence, rfl⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalPartnerAssays
