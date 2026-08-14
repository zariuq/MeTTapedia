import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Runtime
import Mathlib.Tactic

/-!
# Executable located cost-rho examples

These kernel-reduced examples cover every binary funding shape and the main
location failures.  Equal total spends with different purse decompositions
retain different contribution records.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimeExamples

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

set_option maxRecDepth 100000

def channel (name : String) : RawCostName := .signature [name]
def sig (authority : String) : RawCostSig := [authority]

def pay : RawCostName := channel "pay"
def wrong : RawCostName := channel "wrong"
def alice : RawCostSig := sig "alice"
def bob : RawCostSig := sig "bob"
def aliceBob : RawCostSig := ["alice", "bob"]

def done : RawCostTerm := .signed .nil (sig "done")
def payload : RawCostTerm := .signed .nil (sig "payload")

def whole (cost : RawCostSig) : RawCostTerm :=
  .signed (.par (.recv pay done) (.send pay payload)) cost

def recvEndpoint : RawCostTerm := .signed (.recv pay done) alice
def sendEndpoint : RawCostTerm := .signed (.send pay payload) bob

def purse (location : RawCostName) (stack : RawCostStack) : RawCostTerm :=
  .purse location stack

def parList (terms : List RawCostTerm) : RawCostTerm :=
  RawCostTerm.fromComponents terms

/-! ## The five binary funded-COMM cases -/

def wholeSingle : RawCostTerm :=
  parList [whole alice, purse pay [alice]]

def wholeCompoundSplit : RawCostTerm :=
  parList [whole aliceBob, purse pay [alice], purse pay [bob]]

def wholeCompoundCombined : RawCostTerm :=
  parList [whole aliceBob, purse pay [aliceBob]]

def splitEndpointsSplit : RawCostTerm :=
  parList [recvEndpoint, sendEndpoint, purse pay [alice], purse pay [bob]]

def splitEndpointsCombined : RawCostTerm :=
  parList [recvEndpoint, sendEndpoint, purse pay [aliceBob]]

theorem whole_single_fires :
    (runtimeCostFrontier wholeSingle).map List.length = some 1 := by
  decide

theorem whole_compound_split_fires :
    (runtimeCostFrontier wholeCompoundSplit).map List.length = some 1 := by
  decide

theorem whole_compound_combined_fires :
    (runtimeCostFrontier wholeCompoundCombined).map List.length = some 1 := by
  decide

theorem split_endpoints_split_fires :
    (runtimeCostFrontier splitEndpointsSplit).map List.length = some 1 := by
  decide

theorem split_endpoints_combined_fires :
    (runtimeCostFrontier splitEndpointsCombined).map List.length = some 1 := by
  decide

/-! ## Located funding -/

def wrongLocation : RawCostTerm :=
  parList [whole alice, purse wrong [alice]]

def wrongSignature : RawCostTerm :=
  parList [whole alice, purse pay [bob]]

def crossLocationPartialCover : RawCostTerm :=
  parList [whole aliceBob, purse pay [alice], purse wrong [bob]]

theorem correct_signature_wrong_location_blocks :
    runtimeCostFrontier wrongLocation = some [] := by
  decide

theorem wrong_signature_correct_location_blocks :
    runtimeCostFrontier wrongSignature = some [] := by
  decide

theorem cross_location_token_gathering_blocks :
    runtimeCostFrontier crossLocationPartialCover = some [] := by
  decide

/-! ## Contribution and residual fidelity -/

def splitPrefix : Option RawCausalPrefix :=
  boundedCausalPrefix 1 wholeCompoundSplit

def combinedPrefix : Option RawCausalPrefix :=
  boundedCausalPrefix 1 wholeCompoundCombined

theorem split_heads_emit_two_contributions :
    splitPrefix.map (fun result => result.receipt.head?.map (·.funding.length)) =
      some (some 2) := by
  decide

theorem combined_head_emits_one_contribution :
    combinedPrefix.map (fun result => result.receipt.head?.map (·.funding.length)) =
      some (some 1) := by
  decide

theorem split_and_combined_raw_spend_agree :
    splitPrefix.map (fun result => result.receipt.head?.map (·.rawSpend)) =
      combinedPrefix.map (fun result => result.receipt.head?.map (·.rawSpend)) := by
  decide

theorem selected_tail_retains_location :
    splitPrefix.map (fun result => result.residual.normalizeConfig.any fun term =>
      decide (term = RawCostTerm.purse pay [])) = some true := by
  decide

def unselectedPurse : RawCostTerm :=
  parList [whole alice, purse pay [alice], purse pay [bob]]

theorem unselected_purse_remains_unchanged :
    (boundedCausalPrefix 1 unselectedPurse).map (fun result =>
      result.residual.normalizeConfig.any fun term =>
        decide (term = RawCostTerm.purse pay [bob])) = some true := by
  decide

/-! ## Occurrence identity and cross-location independence -/

def wholeAt (location : RawCostName) (cost : RawCostSig) : RawCostTerm :=
  .signed (.par (.recv location done) (.send location payload)) cost

def twoIndependentLocations : RawCostTerm :=
  parList [wholeAt pay alice, purse pay [alice],
    wholeAt wrong bob, purse wrong [bob]]

theorem distinct_locations_form_two_independent_events :
    (boundedCausalPrefix 2 twoIndependentLocations).map (fun result =>
      (result.receipt.length, result.receipt.all (·.causes.isEmpty))) =
      some (2, true) := by
  decide

def repeatedEqualFirings : RawCostTerm :=
  parList [whole alice, whole alice, purse pay [alice], purse pay [alice]]

theorem repeated_equal_spends_remain_distinct_events :
    (boundedCausalPrefix 2 repeatedEqualFirings).map (fun result =>
      (result.receipt.map RawEmittedEvent.id,
       result.receipt.map RawEmittedEvent.rawSpend)) =
      some ([0, 1], [alice, alice]) := by
  decide

/-! ## Reflection and sort-correct dequotation -/

def normalizedReflectedPay : RawCostName :=
  .quote (.par .nil (.drop pay))

theorem quote_of_structural_drop_normalizes_in_one_pass :
    normalizedReflectedPay.normalize = pay := by
  decide

def dequotingWhole : RawCostTerm :=
  .signed (.par (.recv pay (.drop (.bvar 0))) (.send pay payload)) alice

def dequotationRun : RawCostTerm :=
  parList [dequotingWhole, purse pay [alice]]

theorem bound_drop_opens_only_through_comm :
    (boundedCausalPrefix 1 dequotationRun).map (fun result =>
      result.residual.normalizeConfig.any fun term => decide (term = payload)) =
      some true := by
  decide

theorem literal_quoted_drop_has_no_free_reduction :
    runtimeCostFrontier (.drop (.quote payload)) = some [] := by
  decide

/-! ## Honest bounded partiality -/

theorem zero_fuel_live_frontier_exhausts :
    (boundedCausalPrefix 0 wholeSingle).map RawCausalPrefix.status =
      some .fuelExhausted := by
  decide

theorem exact_bound_normal_form_is_quiescent :
    (boundedCausalPrefix 1 wholeSingle).map RawCausalPrefix.status =
      some .quiescent := by
  decide

theorem malformed_empty_seal_is_rejected :
    runtimeCostFrontier (whole []) = none := by
  decide

theorem malformed_empty_purse_head_is_rejected :
    runtimeCostFrontier (parList [whole alice, purse pay [[]]]) = none := by
  decide

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimeExamples
