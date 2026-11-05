import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProductProofInterpretation

/-!
# Dependent trace typing and separating controls

The positive function is the identity over a two-point domain with the
genuinely varying powerset family. The negative controls distinguish a
missing domain guard, a missing body-typing premise, and missing support.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.SetTraceProductProofControls
open SetComprehensionProofs SetMembershipProofs SetPairingProofs
open Mettapedia.Logic.HOL.Embedding
open ZFSetHenkinInterpretation (ChoiceSymbol)
open ZFSetPairingProofInterpretation (core epsilon model value)
open ZFSetTraceProofInterpretation (basis laws laws_free basis_valid application_value abstraction_value)
open ZFSetTraceProductProofInterpretation (product_value)

def zero : ClosedTerm ChoiceSymbol object := .const (.core .empty)
def one : ClosedTerm ChoiceSymbol object := power core zero
def domain : ClosedTerm ChoiceSymbol object := unordered core epsilon zero one
def identity : ClosedTerm ChoiceSymbol (object ⇒ object) := .lam (.var .vz)
def family : ClosedTerm ChoiceSymbol (object ⇒ object) := .lam (power core (.var .vz))
def emptyFamily : ClosedTerm ChoiceSymbol (object ⇒ object) := .lam (HOL.weaken zero)

def body : ProofSyntax ChoiceSymbol (basis []) (SetTraceProductProofs.pointwise core domain family identity) := by
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let premise := member core (.var .vz) (HOL.weaken domain)
  let localAssumptions := premise :: weakenHyps (σ := object) (basis [])
  let localLaws := ((laws []).weaken object).prepend premise
  have functionBeta : ProofSyntax ChoiceSymbol localAssumptions
      (.eq (.app (HOL.weaken identity) (.var .vz)) (.var .vz)) := .beta (.var .vz) (.var .vz)
  have familyBeta : ProofSyntax ChoiceSymbol localAssumptions
      (.eq (.app (HOL.weaken family) (.var .vz)) (power core (.var .vz))) := .beta (.var .vz) (power core (.var .vz))
  exact transportValue core _ (.eqSymm functionBeta)
    (transportBound core (.var .vz) (.eqSymm familyBeta) (selfInPower core (.var .vz) localLaws.pairing.power))

theorem body_free : body.FunctionExtensionalityFree := by
  unfold body
  apply transportValue_free
  · trivial
  · apply transportBound_free
    · trivial
    · apply selfInPower_free
      trivial

def typedFunction := SetTraceProductProofs.abstractionTyped core epsilon domain family identity (laws []) body

theorem typedFunction_free : typedFunction.FunctionExtensionalityFree :=
  SetTraceProductProofs.abstractionTyped_free core epsilon domain family identity (laws []) body (laws_free []) body_free

def zeroInDomain := leftMem core epsilon zero one (laws []).pairing
def oneInDomain := rightMem core epsilon zero one (laws []).pairing

def applicationZero := SetTraceProductProofs.applicationTyped core epsilon domain family
  (SetTraceProofs.abstraction core epsilon domain identity) zero (laws []) typedFunction zeroInDomain
def applicationOne := SetTraceProductProofs.applicationTyped core epsilon domain family
  (SetTraceProofs.abstraction core epsilon domain identity) one (laws []) typedFunction oneInDomain

theorem applicationZero_free : applicationZero.FunctionExtensionalityFree :=
  SetTraceProductProofs.applicationTyped_free core epsilon domain family _ zero (laws []) typedFunction zeroInDomain
    (laws_free []) typedFunction_free (leftMem_free core epsilon zero one _ (laws_free []).pairing)

theorem applicationOne_free : applicationOne.FunctionExtensionalityFree :=
  SetTraceProductProofs.applicationTyped_free core epsilon domain family _ one (laws []) typedFunction oneInDomain
    (laws_free []) typedFunction_free (rightMem_free core epsilon zero one _ (laws_free []).pairing)

theorem fibres_really_vary :
    value.{0} (.app family zero) (fun index => nomatch index) ≠
      value.{0} (.app family one) (fun index => nomatch index) := by
  change ZFSet.powerset (∅ : ZFSet.{0}) ≠ ZFSet.powerset (ZFSet.powerset ∅)
  intro equal
  have present : ZFSet.powerset (∅ : ZFSet.{0}) ∈ ZFSet.powerset (ZFSet.powerset ∅) :=
    ZFSet.mem_powerset.mpr (fun _ h => h)
  rw [← equal] at present
  have impossible := (ZFSet.mem_powerset.mp present)
    (ZFSet.mem_powerset.mpr (ZFSet.empty_subset _))
  exact ZFSet.notMem_empty _ impossible

def emptyBody : ProofSyntax ChoiceSymbol (basis [])
    (SetTraceProductProofs.pointwise core zero emptyFamily identity) := by
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  apply ProofSyntax.botE
  exact .notE ((emptyElim core (.var .vz) (weakenLaw core _ (laws []).pairing.empty)).prepend _) (.hyp 0)

theorem emptyBody_free : emptyBody.FunctionExtensionalityFree := by
  unfold emptyBody
  apply And.intro
  · simpa [ProofSyntax.prepend] using
      (emptyElim_free core _ _).mpr (weakenLaw_free core _ (laws []).pairing.empty trivial)
  · trivial

def emptyFunction := SetTraceProductProofs.abstractionTyped core epsilon zero emptyFamily identity (laws []) emptyBody

theorem emptyFunction_free : emptyFunction.FunctionExtensionalityFree :=
  SetTraceProductProofs.abstractionTyped_free core epsilon zero emptyFamily identity (laws []) emptyBody (laws_free []) emptyBody_free

theorem missingArgumentGuard_false :
    ¬ value.{0} (SetTraceProofs.application core epsilon (SetTraceProofs.abstraction core epsilon zero identity) zero)
      (fun index => nomatch index) ∈ value.{0} (.app emptyFamily zero) (fun index => nomatch index) := by
  exact ZFSet.notMem_empty _

theorem no_unguarded_application : ¬ Nonempty (ProofSyntax ChoiceSymbol (basis [])
    (member core (SetTraceProofs.application core epsilon (SetTraceProofs.abstraction core epsilon zero identity) zero)
      (.app emptyFamily zero))) := by
  rintro ⟨proof⟩
  exact missingArgumentGuard_false (Soundness.extDerivation_sound proof.erase
    (model.{0}.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (by intro _ index; nomatch index) (basis_valid (Γ := []) (fun index => nomatch index)))

theorem missingBodyGuard_false :
    ¬ value.{0} (SetTraceProofs.abstraction core epsilon domain identity) (fun index => nomatch index) ∈
      value.{0} (SetTraceProductProofs.product core epsilon domain emptyFamily) (fun index => nomatch index) := by
  rw [product_value]
  intro admitted
  have inDomain : value.{0} zero (fun index => nomatch index) ∈ value.{0} domain (fun index => nomatch index) := by
    unfold domain
    rw [ZFSetPairingProofInterpretation.unordered_value]
    exact ZFSet.mem_pair.mpr (Or.inl rfl)
  have output := ZFSetTraceProducts.traceApp_mem ⟨_,admitted⟩ ⟨_,inDomain⟩
  exact ZFSet.notMem_empty _ output

theorem no_untyped_abstraction : ¬ Nonempty (ProofSyntax ChoiceSymbol (basis [])
    (member core (SetTraceProofs.abstraction core epsilon domain identity)
      (SetTraceProductProofs.product core epsilon domain emptyFamily))) := by
  rintro ⟨proof⟩
  exact missingBodyGuard_false (Soundness.extDerivation_sound proof.erase
    (model.{0}.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (by intro _ index; nomatch index) (basis_valid (Γ := []) (fun index => nomatch index)))

theorem missingSupportGuard_separates :
    (∀ x ∈ value.{0} zero (fun index => nomatch index),
      ZFSetTraceProducts.traceApp (value.{0} one (fun index => nomatch index)) x ∈ (∅ : ZFSet.{0})) ∧
    ¬ value.{0} one (fun index => nomatch index) ∈
      value.{0} (SetTraceProductProofs.product core epsilon zero emptyFamily) (fun index => nomatch index) := by
  constructor
  · intro x present
    exact False.elim (ZFSet.notMem_empty x present)
  · rw [product_value,ZFSetTraceProductProofInterpretation.tracePiSet_eq_bounded,ZFSet.mem_sep,ZFSet.mem_powerset]
    rintro ⟨bounded,_⟩
    have emptyInOne : (∅ : ZFSet.{0}) ∈ value.{0} one (fun index => nomatch index) := by
      change (∅ : ZFSet.{0}) ∈ ZFSet.powerset ∅
      exact ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)
    obtain ⟨x,present,_,_,_⟩ := ZFSetDependentProducts.mem_sigmaSet.mp (bounded emptyInOne)
    exact ZFSet.notMem_empty x present

end Mettapedia.Logic.HOL.SetTraceProductProofControls
