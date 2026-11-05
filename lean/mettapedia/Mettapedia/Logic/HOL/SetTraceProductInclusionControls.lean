import Mettapedia.Logic.HOL.SetTraceProductInclusionProofs
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProductProofInterpretation

/-!
# Strict trace-product enlargement and a missing-bound countermodel

Both products contain the empty trace. The enlarged fibre also admits a
nonempty trace excluded by the original fibre. A separate trace containing
an entry outside the domain satisfies the original application guard but
fails membership in the bounded product.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.SetTraceProductInclusionControls
open SetComprehensionProofs SetInclusionProofs SetFamilyInclusionProofs SetTraceProductProofs SetTraceProductInclusionProofs
open Mettapedia.Logic.HOL.Embedding
open ZFSetHenkinInterpretation (ChoiceSymbol set mapping)
open ZFSetPairingProofInterpretation (core epsilon model value unordered_value ordered_value)
open ZFSetDependentProducts ZFSetTraceProducts

abbrev basis := ZFSetTraceProofInterpretation.basis []
def emptyTerm : ClosedTerm ChoiceSymbol set := .const (core .empty)
def domain : ClosedTerm ChoiceSymbol set := power core emptyTerm
def beforeFamily : ClosedTerm ChoiceSymbol mapping := .lam (truthCode core .top)
def afterFamily : ClosedTerm ChoiceSymbol mapping := .lam (power core (HOL.weaken domain))
def fibres := familyIncluded core domain beforeFamily afterFamily
noncomputable def valuation : model.{0}.Valuation [] := fun index => nomatch index

def receipt : ProofSyntax ChoiceSymbol (fibres :: basis)
    (included core (product core epsilon domain beforeFamily) (product core epsilon domain afterFamily)) :=
  productInclusion core epsilon domain beforeFamily afterFamily ((ZFSetTraceProofInterpretation.laws []).prepend _) (.hyp 0)

theorem receipt_free : receipt.FunctionExtensionalityFree :=
  productInclusion_free core epsilon domain beforeFamily afterFamily _ _
    ((ZFSetTraceProofInterpretation.laws []).prepend_free _ (ZFSetTraceProofInterpretation.laws_free [])) trivial

theorem empty_in_power : (∅ : ZFSet.{0}) ∈ ZFSet.powerset ∅ := ZFSet.mem_powerset.mpr (by simp)
theorem power_ne_empty : ZFSet.powerset (∅ : ZFSet.{0}) ≠ ∅ := by
  intro equal
  have present := empty_in_power
  rw [equal] at present
  exact ZFSet.notMem_empty _ present

theorem fibres_valid : (model.denote fibres valuation).down := by
  change ∀ point : ZFSet.{0}, True → point ∈ ZFSet.powerset ∅ → ∀ result : ZFSet.{0}, True →
    result ∈ ZFSet.sep (fun _ => True) (ZFSet.powerset ∅) → result ∈ ZFSet.powerset (ZFSet.powerset ∅)
  intro _ _ _ result _ present
  apply ZFSet.mem_powerset.mpr
  intro element inResult
  exact False.elim (ZFSet.notMem_empty _ ((ZFSet.mem_powerset.mp (ZFSet.mem_sep.mp present).1) inResult))

theorem background_valid : Soundness.SatisfiesHyps model valuation (fibres :: basis) := by
  intro formula present
  rcases List.mem_cons.mp present with rfl | old
  · exact fibres_valid
  · exact ZFSetTraceProofInterpretation.basis_valid valuation formula old

theorem actual_inclusion : (model.denote (included core (product core epsilon domain beforeFamily)
    (product core epsilon domain afterFamily)) valuation).down :=
  Soundness.extDerivation_sound receipt.erase
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (by intro _ index; nomatch index) background_valid

theorem empty_in_before : (∅ : ZFSet.{0}) ∈ value (product core epsilon domain beforeFamily) valuation := by
  rw [ZFSetTraceProductProofInterpretation.product_value]
  apply mem_tracePiSet.mpr
  refine ⟨graph (ZFSet.powerset ∅) (fun _ => ∅),?_,traceLam_graph_empty _⟩
  apply graph_mem_piSet
  intro _ _
  change (∅ : ZFSet.{0}) ∈ ZFSet.sep (fun _ => True) (ZFSet.powerset ∅)
  exact ZFSet.mem_sep.mpr ⟨empty_in_power,trivial⟩

theorem empty_in_after : (∅ : ZFSet.{0}) ∈ value (product core epsilon domain afterFamily) valuation :=
  actual_inclusion (∅ : ZFSet.{0}) trivial empty_in_before

noncomputable def largerTrace : ZFSet.{0} := traceLam (graph (ZFSet.powerset ∅) (fun _ => ZFSet.powerset ∅))

theorem larger_after : largerTrace ∈ value (product core epsilon domain afterFamily) valuation := by
  rw [ZFSetTraceProductProofInterpretation.product_value]
  apply mem_tracePiSet.mpr
  refine ⟨graph (ZFSet.powerset ∅) (fun _ => ZFSet.powerset ∅),?_,rfl⟩
  apply graph_mem_piSet
  intro _ _
  change ZFSet.powerset (∅ : ZFSet.{0}) ∈ ZFSet.powerset (ZFSet.powerset ∅)
  exact ZFSet.mem_powerset.mpr (fun _ present => present)

theorem larger_not_before : largerTrace ∉ value (product core epsilon domain beforeFamily) valuation := by
  intro present
  rw [ZFSetTraceProductProofInterpretation.product_value] at present
  have typed := traceApp_mem ⟨largerTrace,present⟩ ⟨∅,empty_in_power⟩
  change traceApp (traceLam (graph (ZFSet.powerset ∅) (fun _ => ZFSet.powerset ∅))) ∅ ∈
    ZFSet.sep (fun _ => True) (ZFSet.powerset ∅) at typed
  rw [traceApp_graph_beta _ empty_in_power] at typed
  exact ZFSet.mem_irrefl _ (ZFSet.mem_sep.mp typed).1

theorem larger_nonempty : largerTrace ≠ ∅ := by
  have present : ZFSet.pair (∅ : ZFSet.{0}) ∅ ∈ largerTrace :=
    mem_traceLam.mpr ⟨∅,ZFSet.powerset ∅,∅,pair_mem_graph.mpr ⟨empty_in_power,rfl⟩,empty_in_power,rfl⟩
  intro equal
  rw [equal] at present
  exact ZFSet.notMem_empty _ present

def junkEntry : ClosedTerm ChoiceSymbol set := SetPairingProofs.ordered core epsilon domain emptyTerm
def junkTrace : ClosedTerm ChoiceSymbol set := SetPairingProofs.unordered core epsilon junkEntry junkEntry
def junkGuard := guard core epsilon domain beforeFamily junkTrace
def junkMembership := member core junkTrace (product core epsilon domain beforeFamily)

theorem junk_value : value junkTrace valuation = {ZFSet.pair (ZFSet.powerset (∅ : ZFSet.{0})) ∅} := by
  have entry : value junkEntry valuation = ZFSet.pair (ZFSet.powerset (∅ : ZFSet.{0})) ∅ := by
    unfold junkEntry
    rw [ordered_value]
    rfl
  unfold junkTrace
  rw [unordered_value]
  simp only [entry]
  ext point
  simp

theorem junk_apply_empty : traceApp ({ZFSet.pair (ZFSet.powerset (∅ : ZFSet.{0})) ∅} : ZFSet.{0}) ∅ = ∅ := by
  apply ZFSet.ext
  intro point
  rw [mem_traceApp,ZFSet.mem_singleton]
  constructor
  · intro equal
    exact False.elim (power_ne_empty (ZFSet.pair_inj.mp equal).1.symm)
  · intro absent
    exact False.elim (ZFSet.notMem_empty _ absent)

theorem junk_guard_valid : (model.denote junkGuard valuation).down := by
  apply (ZFSetTraceProductProofInterpretation.guard_meaning domain beforeFamily junkTrace valuation).mpr
  intro point present
  change point ∈ ZFSet.powerset (∅ : ZFSet.{0}) at present
  have same : point = ∅ := by
    apply ZFSet.ext
    intro element
    exact ⟨fun admitted => (ZFSet.mem_powerset.mp present) admitted,
      fun absent => False.elim (ZFSet.notMem_empty _ absent)⟩
  subst point
  change traceApp (value junkTrace valuation) ∅ ∈ ZFSet.sep (fun _ => True) (ZFSet.powerset ∅)
  rw [junk_value,junk_apply_empty]
  exact ZFSet.mem_sep.mpr ⟨empty_in_power,trivial⟩

theorem junk_membership_false : ¬ (model.denote junkMembership valuation).down := by
  change ¬ (value junkTrace valuation ∈ value (product core epsilon domain beforeFamily) valuation)
  rw [junk_value,ZFSetTraceProductProofInterpretation.product_value]
  change ¬ (({ZFSet.pair (ZFSet.powerset (∅ : ZFSet.{0})) ∅} : ZFSet.{0}) ∈
    tracePiSet (ZFSet.powerset ∅) (fun _ => ZFSet.sep (fun _ => True) (ZFSet.powerset ∅)))
  intro present
  rw [ZFSetTraceProductProofInterpretation.tracePiSet_eq_bounded] at present
  have bounded := ZFSet.mem_powerset.mp (ZFSet.mem_sep.mp present).1
  have entry := bounded (show ZFSet.pair (ZFSet.powerset (∅ : ZFSet.{0})) ∅ ∈
    ({ZFSet.pair (ZFSet.powerset (∅ : ZFSet.{0})) ∅} : ZFSet.{0}) by simp)
  obtain ⟨index,inDomain,result,_,equal⟩ := mem_sigmaSet.mp entry
  have same := (ZFSet.pair_inj.mp equal).1
  rw [← same] at inDomain
  exact ZFSet.mem_irrefl _ inDomain

theorem guard_background_valid : Soundness.SatisfiesHyps model valuation (junkGuard :: basis) := by
  intro formula present
  rcases List.mem_cons.mp present with rfl | old
  · exact junk_guard_valid
  · exact ZFSetTraceProofInterpretation.basis_valid valuation formula old

theorem no_guard_without_bound : ¬ Nonempty (ProofSyntax ChoiceSymbol (junkGuard :: basis) junkMembership) := by
  rintro ⟨proof⟩
  exact junk_membership_false (Soundness.extDerivation_sound proof.erase
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (by intro _ index; nomatch index) guard_background_valid)

end Mettapedia.Logic.HOL.SetTraceProductInclusionControls
