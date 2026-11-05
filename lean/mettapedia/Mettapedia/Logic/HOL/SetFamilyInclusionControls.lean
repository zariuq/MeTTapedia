import Mettapedia.Logic.HOL.SetFamilyInclusionProofs
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofInterpretation

/-!
# A nonempty guarded-family control and failed guard erasure

Both fibres contain the empty set at the admitted index. Outside the domain,
the constant fibre still contains it and the index-sensitive fibre does not.
The guarded relation therefore supports sum inclusion but cannot justify an
unguarded inclusion of the two families.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.SetFamilyInclusionControls
open SetComprehensionProofs SetInclusionProofs SetFamilyInclusionProofs
open Mettapedia.Logic.HOL.Embedding
open ZFSetHenkinInterpretation (ChoiceSymbol set mapping)

abbrev core : Core ChoiceSymbol := ZFSetPairingProofInterpretation.core
abbrev epsilon : ClosedTerm ChoiceSymbol (SelectionProofs.Selection set) := ZFSetPairingProofInterpretation.epsilon
abbrev basis := ZFSetTraceProofInterpretation.basis []
def domain : ClosedTerm ChoiceSymbol set := power core (.const (core .empty))
def beforeFamily : ClosedTerm ChoiceSymbol mapping := .lam (truthCode core .top)
def afterFamily : ClosedTerm ChoiceSymbol mapping := .lam (truthCode core (.eq (.var .vz) (.const (core .empty))))
def guardedFamily := familyIncluded core domain beforeFamily afterFamily
def globalFamily : ClosedFormula ChoiceSymbol := .all (included core
  (.app (HOL.weaken beforeFamily) (.var .vz)) (.app (HOL.weaken afterFamily) (.var .vz)))

def sumReceipt : ProofSyntax ChoiceSymbol (guardedFamily :: basis) (included core
    (SetDependentSumProofs.sum core epsilon domain beforeFamily) (SetDependentSumProofs.sum core epsilon domain afterFamily)) :=
  sumInclusion core epsilon domain domain beforeFamily afterFamily ((ZFSetTraceProofInterpretation.laws []).prepend _)
    (reflexive core domain) (.hyp 0)

theorem sumReceipt_free : sumReceipt.FunctionExtensionalityFree :=
  sumInclusion_free core epsilon domain domain beforeFamily afterFamily _ _ _
    ((ZFSetTraceProofInterpretation.laws []).prepend_free _ (ZFSetTraceProofInterpretation.laws_free []))
    (reflexive_free core domain) trivial

noncomputable abbrev model := ZFSetPairingProofInterpretation.model.{0}
noncomputable def valuation : model.Valuation [] := fun index => nomatch index

theorem guarded_valid : (model.denote guardedFamily valuation).down := by
  change ∀ point : ZFSet.{0}, True → point ∈ ZFSet.powerset ∅ → ∀ value : ZFSet.{0}, True →
    value ∈ ZFSet.sep (fun _ => True) (ZFSet.powerset ∅) →
    value ∈ ZFSet.sep (fun _ => point = ∅) (ZFSet.powerset ∅)
  intro point _ inDomain value _ inBefore
  have same : point = ∅ := by
    apply ZFSet.ext
    intro element
    constructor
    · intro present
      exact (ZFSet.mem_powerset.mp inDomain) present
    · intro present
      exact False.elim (ZFSet.notMem_empty _ present)
  exact ZFSet.mem_sep.mpr ⟨(ZFSet.mem_sep.mp inBefore).1,same⟩

theorem global_false : ¬ (model.denote globalFamily valuation).down := by
  change ¬ (∀ point : ZFSet.{0}, True → ∀ value : ZFSet.{0}, True →
    value ∈ ZFSet.sep (fun _ => True) (ZFSet.powerset ∅) →
    value ∈ ZFSet.sep (fun _ => point = ∅) (ZFSet.powerset ∅))
  intro alleged
  have emptyInPower : (∅ : ZFSet.{0}) ∈ ZFSet.powerset ∅ := ZFSet.mem_powerset.mpr (by simp)
  have wrong := alleged (ZFSet.powerset ∅) trivial ∅ trivial (ZFSet.mem_sep.mpr ⟨emptyInPower,trivial⟩)
  have impossible := (ZFSet.mem_sep.mp wrong).2
  rw [impossible] at emptyInPower
  exact ZFSet.notMem_empty _ emptyInPower

theorem before_sum_nonempty : ZFSet.pair (∅ : ZFSet.{0}) ∅ ∈
    (show ZFSet.{0} from model.denote (SetDependentSumProofs.sum core epsilon domain beforeFamily) valuation) := by
  have meaning := ZFSetTraceProofInterpretation.sum_value domain beforeFamily valuation
  apply (congrArg (fun value : ZFSet.{0} => ZFSet.pair (∅ : ZFSet.{0}) ∅ ∈ value) meaning).mpr
  apply ZFSetDependentProducts.mem_sigmaSet.mpr
  refine ⟨(∅ : ZFSet.{0}),?_,(∅ : ZFSet.{0}),?_,rfl⟩
  · change (∅ : ZFSet.{0}) ∈ ZFSet.powerset ∅
    exact ZFSet.mem_powerset.mpr (by simp)
  · change (∅ : ZFSet.{0}) ∈ ZFSet.sep (fun _ => True) (ZFSet.powerset ∅)
    exact ZFSet.mem_sep.mpr ⟨ZFSet.mem_powerset.mpr (by simp),trivial⟩

theorem after_sum_nonempty : ZFSet.pair (∅ : ZFSet.{0}) ∅ ∈
    (show ZFSet.{0} from model.denote (SetDependentSumProofs.sum core epsilon domain afterFamily) valuation) := by
  have meaning := ZFSetTraceProofInterpretation.sum_value domain afterFamily valuation
  apply (congrArg (fun value : ZFSet.{0} => ZFSet.pair (∅ : ZFSet.{0}) ∅ ∈ value) meaning).mpr
  apply ZFSetDependentProducts.mem_sigmaSet.mpr
  refine ⟨(∅ : ZFSet.{0}),?_,(∅ : ZFSet.{0}),?_,rfl⟩
  · change (∅ : ZFSet.{0}) ∈ ZFSet.powerset ∅
    exact ZFSet.mem_powerset.mpr (by simp)
  · change (∅ : ZFSet.{0}) ∈ ZFSet.sep (fun _ => (∅ : ZFSet.{0}) = ∅) (ZFSet.powerset ∅)
    exact ZFSet.mem_sep.mpr ⟨ZFSet.mem_powerset.mpr (by simp),rfl⟩

theorem background_valid : Soundness.SatisfiesHyps model valuation (guardedFamily :: basis) := by
  intro formula present
  rcases List.mem_cons.mp present with rfl | old
  · exact guarded_valid
  · exact ZFSetTraceProofInterpretation.basis_valid valuation formula old

theorem actual_sum_inclusion : (model.denote (included core (SetDependentSumProofs.sum core epsilon domain beforeFamily)
    (SetDependentSumProofs.sum core epsilon domain afterFamily)) valuation).down :=
  Soundness.extDerivation_sound sumReceipt.erase
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (by intro _ index; nomatch index) background_valid

theorem no_guard_erasure : ¬ Nonempty (ProofSyntax ChoiceSymbol (guardedFamily :: basis) globalFamily) := by
  rintro ⟨proof⟩
  exact global_false (Soundness.extDerivation_sound proof.erase
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (by intro _ index; nomatch index) background_valid)

end Mettapedia.Logic.HOL.SetFamilyInclusionControls
