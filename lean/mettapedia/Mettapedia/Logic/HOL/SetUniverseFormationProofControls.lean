import Mettapedia.Logic.HOL.Embedding.ZFSetUniverseProofInterpretation
import Mettapedia.Logic.HOL.SetTraceProductProofControls

/-!
# Universe-formation controls and a missing-powerset countermodel

The open control forms sums and products for an arbitrary domain and family.
An actual two-point powerset family realizes it under the existing explicit
universe-model assumption. The smaller set `{empty}` satisfies transitivity,
union and replacement closure, but fails powerset closure and product formation.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.SetUniverseFormationProofControls
open SetComprehensionProofs SetMembershipProofs SetPairingProofs SetUniverseProofs
open Mettapedia.Logic.HOL.Embedding
open ZFSetHenkinInterpretation (ChoiceSymbol mapping)
open ZFSetPairingProofInterpretation (core epsilon model value)
open ZFSetUniverseProofInterpretation (basis laws setLaws laws_free setLaws_free basis_valid)
universe u

abbrev sourceContext : Ctx Unit := [mapping,object,object]
def universeTerm : Term ChoiceSymbol sourceContext object := .var (.vs (.vs .vz))
def domainTerm : Term ChoiceSymbol sourceContext object := .var (.vs .vz)
def familyTerm : Term ChoiceSymbol sourceContext mapping := .var .vz
abbrev domainPremise := member core domainTerm universeTerm
abbrev familyPremise := mapsInto core universeTerm domainTerm familyTerm
abbrev assumptions := familyPremise :: domainPremise :: basis universeTerm
def closure := ((laws universeTerm).prepend domainPremise).prepend familyPremise
def sets := ((setLaws universeTerm).prepend domainPremise).prepend familyPremise

def sumFormation := SetUniverseFormationProofs.sumClosed core epsilon universeTerm domainTerm familyTerm closure sets
  (.hyp 1 : ProofSyntax ChoiceSymbol assumptions domainPremise) (.hyp 0)
def productFormation := SetUniverseFormationProofs.productClosed core epsilon universeTerm domainTerm familyTerm closure sets
  (.hyp 1 : ProofSyntax ChoiceSymbol assumptions domainPremise) (.hyp 0)

theorem closure_free : closure.Free :=
  ((laws universeTerm).prepend domainPremise).prepend_free familyPremise
    ((laws universeTerm).prepend_free domainPremise (laws_free universeTerm))

theorem sets_free : sets.Free :=
  ((setLaws universeTerm).prepend domainPremise).prepend_free familyPremise
    ((setLaws universeTerm).prepend_free domainPremise (setLaws_free universeTerm))

theorem sumFormation_free : sumFormation.FunctionExtensionalityFree :=
  SetUniverseFormationProofs.sumClosed_free core epsilon universeTerm domainTerm familyTerm closure sets _ _
    closure_free sets_free trivial trivial

theorem productFormation_free : productFormation.FunctionExtensionalityFree :=
  SetUniverseFormationProofs.productClosed_free core epsilon universeTerm domainTerm familyTerm closure sets _ _
    closure_free sets_free trivial trivial

noncomputable def sourceValuation (universeSet domain : ZFSet.{u}) (family : ZFSet.{u} → ZFSet.{u}) :
    model.{u}.Valuation sourceContext
  | _, .vz => family
  | _, .vs .vz => domain
  | _, .vs (.vs .vz) => universeSet
  | _, .vs (.vs (.vs impossible)) => nomatch impossible

theorem positive_realized (universeSet domain : ZFSet.{u}) (family : ZFSet.{u} → ZFSet.{u})
    (closed : ZFSetUniverseClosure.Closed universeSet) (domainMember : domain ∈ universeSet)
    (familyMembers : ∀ point ∈ domain, family point ∈ universeSet) :
    let valuation : model.{u}.Valuation sourceContext := sourceValuation universeSet domain family
    Soundness.SatisfiesHyps model valuation assumptions ∧
    value (SetDependentSumProofs.sum core epsilon domainTerm familyTerm) valuation ∈ universeSet ∧
    value (SetTraceProductProofs.product core epsilon domainTerm familyTerm) valuation ∈ universeSet := by
  let valuation : model.{u}.Valuation sourceContext := sourceValuation universeSet domain family
  have satisfied : Soundness.SatisfiesHyps model valuation assumptions := by
    intro formula present
    rcases List.mem_cons.mp present with rfl | present
    · exact (ZFSetUniverseProofInterpretation.mapsInto_meaning universeTerm domainTerm familyTerm valuation).mpr familyMembers
    · rcases List.mem_cons.mp present with rfl | present
      · exact domainMember
      · exact basis_valid universeTerm valuation closed formula present
  refine ⟨satisfied,?_,?_⟩
  · exact Soundness.extDerivation_sound sumFormation.erase
      (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
      (by intro _ _; trivial) satisfied
  · exact Soundness.extDerivation_sound productFormation.erase
      (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
      (by intro _ _; trivial) satisfied

theorem actual_two_point_model (hierarchy : ZFSetUniverseClosure.CofinalInaccessibles.{u}) :
    ∃ valuation : model.{u}.Valuation sourceContext, Soundness.SatisfiesHyps model valuation assumptions ∧
      value (SetDependentSumProofs.sum core epsilon domainTerm familyTerm) valuation ∈ value universeTerm valuation ∧
      value (SetTraceProductProofs.product core epsilon domainTerm familyTerm) valuation ∈ value universeTerm valuation := by
  let domain : ZFSet.{u} := value.{u} SetTraceProductProofControls.domain (fun index => nomatch index)
  let universeSet := ZFSetUniverseClosure.univOf hierarchy domain
  have closed := ZFSetUniverseClosure.univOf_closed hierarchy domain
  have domainMember := ZFSetUniverseClosure.mem_univOf hierarchy domain
  have familyMembers : ∀ point ∈ domain, ZFSet.powerset point ∈ universeSet :=
    fun point present => closed.power_mem (closed.transitive domain domainMember present)
  exact ⟨sourceValuation universeSet domain ZFSet.powerset,
    positive_realized universeSet domain ZFSet.powerset closed domainMember familyMembers⟩

def zero : ClosedTerm ChoiceSymbol object := .const (.core .empty)
def one : ClosedTerm ChoiceSymbol object := power core zero
def emptyFamily : ClosedTerm ChoiceSymbol mapping := .lam (HOL.weaken zero)
abbrev negativeBasis : List (ClosedFormula ChoiceSymbol) := ZFSetTraceProofInterpretation.basis [] ++
  [transitive core one,unaryClosed core one (.const (core .union)),replacementClosed core one]

theorem one_transitive : ZFSet.IsTransitive (ZFSet.powerset (∅ : ZFSet.{u})) := by
  intro bound inPower point inBound
  exact False.elim (ZFSet.notMem_empty point ((ZFSet.mem_powerset.mp inPower) inBound))

theorem one_union_closed : ∀ bound ∈ ZFSet.powerset (∅ : ZFSet.{u}),
    ZFSet.sUnion bound ∈ ZFSet.powerset ∅ := by
  intro bound inPower
  apply ZFSet.mem_powerset.mpr
  intro point inUnion
  obtain ⟨index,inBound,_⟩ := ZFSet.mem_sUnion.mp inUnion
  exact False.elim (ZFSet.notMem_empty index ((ZFSet.mem_powerset.mp inPower) inBound))

theorem one_replacement_closed : ∀ bound ∈ ZFSet.powerset (∅ : ZFSet.{u}),
    ∀ function : ZFSet.{u} → ZFSet.{u},
      (∀ point ∈ bound, function point ∈ ZFSet.powerset ∅) →
        ZFSetHenkinInterpretation.replacement bound function ∈ ZFSet.powerset ∅ := by
  intro bound inPower function _
  apply ZFSet.mem_powerset.mpr
  intro point inImage
  obtain ⟨index,inBound,_⟩ := ZFSetHenkinInterpretation.mem_replacement.mp inImage
  exact False.elim (ZFSet.notMem_empty index ((ZFSet.mem_powerset.mp inPower) inBound))

theorem negativeBasis_valid : Soundness.SatisfiesHyps (Γ := []) model.{0} (fun index => nomatch index) negativeBasis := by
  intro formula present
  rcases List.mem_append.mp present with basic | extra
  · exact ZFSetTraceProofInterpretation.basis_valid.{0} (Γ := []) (fun index => nomatch index) formula basic
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at extra
    rcases extra with rfl | rfl | rfl
    · exact ZFSetUniverseProofInterpretation.transitive_valid.{0} one _ one_transitive.{0}
    · exact ZFSetUniverseProofInterpretation.unary_valid.{0} one (.const (core .union)) _ one_union_closed.{0}
    · exact ZFSetUniverseProofInterpretation.replacement_valid.{0} one _ one_replacement_closed.{0}

def smallDomain : ProofSyntax ChoiceSymbol negativeBasis (member core zero one) :=
  emptyInPowerEmpty core (.hyp ⟨1,by simp [negativeBasis,ZFSetTraceProofInterpretation.basis,ZFSetPairingProofInterpretation.basis]⟩)

def smallFamily : ProofSyntax ChoiceSymbol negativeBasis (mapsInto core one zero emptyFamily) := by
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  apply ProofSyntax.botE
  have emptyProof : ProofSyntax ChoiceSymbol negativeBasis (lawAt core ZFSetHenkinInterpretation.emptyLaw) :=
    .hyp ⟨0,by simp [negativeBasis,ZFSetTraceProofInterpretation.basis,ZFSetPairingProofInterpretation.basis]⟩
  exact .notE ((emptyElim core (.var .vz) (weakenLaw core _ emptyProof)).prepend _) (.hyp 0)

theorem powerClosure_refuted :
    ¬ (model.{0}.denote (unaryClosed core one (.const (core .power))) (fun index => nomatch index)).down := by
  intro closed
  have present : (∅ : ZFSet.{0}) ∈ ZFSet.powerset ∅ := ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)
  have impossible := closed (∅ : ZFSet.{0}) trivial present
  exact ZFSet.mem_irrefl _ impossible

theorem missingPowerFormation_false :
    ¬ value.{0} (SetTraceProductProofs.product core epsilon zero emptyFamily) (fun index => nomatch index) ∈
      value.{0} one (fun index => nomatch index) := by
  rw [ZFSetTraceProductProofInterpretation.product_value]
  change ¬ ZFSetTraceProducts.tracePiSet (∅ : ZFSet.{0}) (fun _ => ∅) ∈ ZFSet.powerset ∅
  intro small
  have containsEmpty : (∅ : ZFSet.{0}) ∈ ZFSetTraceProducts.tracePiSet ∅ (fun _ => ∅) := by
    rw [ZFSetTraceProductProofInterpretation.tracePiSet_eq_bounded,ZFSet.mem_sep,ZFSet.mem_powerset]
    exact ⟨ZFSet.empty_subset _,fun point absent => False.elim (ZFSet.notMem_empty point absent)⟩
  exact ZFSet.notMem_empty _ ((ZFSet.mem_powerset.mp small) containsEmpty)

theorem noFormationWithoutPower : ¬ Nonempty (ProofSyntax ChoiceSymbol negativeBasis
    (member core (SetTraceProductProofs.product core epsilon zero emptyFamily) one)) := by
  rintro ⟨proof⟩
  exact missingPowerFormation_false (Soundness.extDerivation_sound proof.erase
    (model.{0}.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (by intro _ index; nomatch index) negativeBasis_valid)

end Mettapedia.Logic.HOL.SetUniverseFormationProofControls
