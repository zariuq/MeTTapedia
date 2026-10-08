import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalPartnerObservations
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionControls

/-!
# Actual partner synchronization and occurrence-sensitive controls

The existing waiting-input separator is read through the complete new
coalgebra and final observations. Duplicate output occurrences retain two
different addressed receipts while contributing the same canonical target.
Coloured cofree observations preserve the complete target inventory and the
authored bound-name substitution result; neither final nor coloured endpoint
observations recover a firing history.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalPartnerControls

open _root_.CategoryTheory
open Mettapedia.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open CanonicalBag CanonicalReaction CanonicalReactionOccurrences
open CanonicalPartnerCoalgebra CanonicalPartnerObservations
open LanguageDefGSLT HennessyMilnerRho
open LanguageDefRewriteSystem

theorem actual_partner_synchronization :
    fromProcess closedCommTarget ∈ successors
      (fromProcess ParallelContextAdequacy.waitingInput)
      (fromProcess ParallelContextAdequacy.outputPartner) :=
  (mem_successors_iff_public _ _ _).2 ParallelContextAdequacy.partner_step

theorem inert_partner_cut :
    successors (fromProcess closedNil)
      (fromProcess ParallelContextAdequacy.outputPartner) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro target member
  have step := (mem_successors_iff_public closedNil
    ParallelContextAdequacy.outputPartner (toProcess target)).1
      (by simpa only [fromProcess_toProcess] using member)
  exact ParallelContextAdequacy.no_step_of_successors_nil
    ParallelContextAdequacy.nilPartner_successors (toProcess target) step

/-- The old bare-reduction separator survives the whole final-observation bridge. -/
theorem reductions_cannot_replace_partners :
    (HennessyMilnerInstance.rhoSystem PEmpty.{1} (fun atom => atom.elim)).Bisimilar
        ParallelContextAdequacy.waitingInput closedNil ∧
      observe (fromProcess ParallelContextAdequacy.waitingInput) ≠
        observe (fromProcess closedNil) := by
  refine ⟨ParallelContextAdequacy.waitingInput_reduction_bisimilar_nil, ?_⟩
  intro same
  exact ParallelContextAdequacy.waitingInput_not_partner_bisimilar_nil
    ((public_bisimilar_iff_final_observation _ _).2 same)

abbrev first : Receipt CanonicalReactionControls.rule.redex CanonicalReactionControls.oneOutput :=
  CanonicalReactionControls.first

abbrev second : Receipt CanonicalReactionControls.rule.redex CanonicalReactionControls.oneOutput :=
  CanonicalReactionControls.second

theorem duplicate_receipts_retained :
    first ≠ second ∧ first.target = second.target ∧
      first.target ∈ successors CanonicalReactionControls.rule.redex
        CanonicalReactionControls.oneOutput ∧
      second.target ∈ successors CanonicalReactionControls.rule.redex
        CanonicalReactionControls.oneOutput :=
  ⟨CanonicalReactionControls.different_occurrences, CanonicalReactionControls.same_endpoint,
    receipt_member _ _ first, receipt_member _ _ second⟩

theorem duplicate_complete_inventory : first.target.1 =
    ([CanonicalReactionControls.payload,
      output CanonicalReactionControls.channel CanonicalReactionControls.payload] : List Pattern) :=
  CanonicalReactionControls.complete_endpoint_inventory

theorem duplicate_whole_final_target : observe first.target = observe second.target :=
  congrArg observe CanonicalReactionControls.same_endpoint

theorem duplicate_whole_coloured_target :
    certificateObservation Bag id first.target = certificateObservation Bag id second.target :=
  congrArg (certificateObservation Bag id) CanonicalReactionControls.same_endpoint

/-- Even the entire coloured future of a target omits its selected COMM origin. -/
theorem no_coloured_firing_decoder :
    ¬ ∃ decode : FiniteActionTree.Tree Bag Bag →
      Receipt CanonicalReactionControls.rule.redex CanonicalReactionControls.oneOutput,
      ∀ receipt, decode (certificateObservation Bag id receipt.target) = receipt := by
  rintro ⟨decode, readout⟩
  apply CanonicalReactionControls.different_occurrences
  exact (readout first).symm.trans
    ((congrArg decode duplicate_whole_coloured_target).trans (readout second))

/-- Every supplied addressed receipt appears in the complete coloured future. -/
theorem coloured_receipt_successor (source partner : Bag) (receipt : Receipt source partner) :
    certificateObservation Bag id receipt.target ∈
      FiniteActionTree.Tree.step (certificateObservation Bag id source) partner := by
  rw [certificate_successors, FinitePowerset.mem_map]
  exact ⟨receipt.target, receipt_member source partner receipt, rfl⟩

theorem ground_comm_member (rule : GroundComm) :
    rule.reactum ∈ successors rule.redex empty := by
  apply (mem_successors_iff_reaction _ _ _).2
  exact ⟨rule, empty, rfl, (append_empty rule.reactum).symm⟩

theorem bound_position_successors :
    certificateObservation Bag id CanonicalReactionControls.older.reactum ∈
        FiniteActionTree.Tree.step
          (certificateObservation Bag id CanonicalReactionControls.older.redex) empty ∧
      certificateObservation Bag id CanonicalReactionControls.newer.reactum ∈
        FiniteActionTree.Tree.step
          (certificateObservation Bag id CanonicalReactionControls.newer.redex) empty := by
  constructor
  · rw [certificate_successors, FinitePowerset.mem_map]
    exact ⟨_, ground_comm_member CanonicalReactionControls.older, rfl⟩
  · rw [certificate_successors, FinitePowerset.mem_map]
    exact ⟨_, ground_comm_member CanonicalReactionControls.newer, rfl⟩

/-- Decode the actual complete cofree-root inventory, after the authored name equations. -/
theorem older_bound_name_readout :
    (toProcess (FiniteActionTree.Tree.root
      (certificateObservation Bag id CanonicalReactionControls.older.reactum))).1 =
      Canonical.canonicalize (input CanonicalReactionControls.channel
        (output (.apply "NQuote" [CanonicalReactionControls.payload])
          CanonicalReactionControls.zero)) := by
  rw [certificate_root]
  change (toProcess (fromProcess CanonicalReactionControls.older.result)).1 = _
  rw [toProcess_fromProcess]
  exact congrArg Canonical.canonicalize CanonicalReactionControls.outer_argument_readout

theorem newer_bound_name_readout :
    (toProcess (FiniteActionTree.Tree.root
      (certificateObservation Bag id CanonicalReactionControls.newer.reactum))).1 =
      Canonical.canonicalize (input CanonicalReactionControls.channel
        (output (.bvar 0) CanonicalReactionControls.zero)) := by
  rw [certificate_root]
  change (toProcess (fromProcess CanonicalReactionControls.newer.result)).1 = _
  rw [toProcess_fromProcess]
  exact congrArg Canonical.canonicalize CanonicalReactionControls.newer_bound_readout

theorem authored_name_equation_member :
    fromProcess (CanonicalReactionControls.rule.target empty) ∈
      successors (fromProcess CanonicalReactionControls.alternateSource) empty := by
  apply (mem_successors_iff_reaction _ _ _).2
  rw [append_empty]
  exact (publicStep_iff _ _).1
    CanonicalReactionControls.public_communication_accepts_name_equation

theorem free_drop_empty_partner : successors (fromProcess closedFreeDrop) empty = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro target member
  have reaction := (mem_successors_iff_reaction _ _ _).1 member
  rw [append_empty] at reaction
  exact CanonicalReactionControls.free_drop_has_no_reaction ⟨target, reaction⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalPartnerControls
