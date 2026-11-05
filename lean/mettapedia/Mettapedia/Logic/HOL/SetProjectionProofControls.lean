import Mettapedia.Logic.HOL.Embedding.ZFSetProjectionProofInterpretation

/-!
# Guarded projection controls and failure of untyped reconstruction

The admitted value is an actual constructed pair in a nonempty dependent sum.
An empty set is not an ordered pair; the unguarded reconstruction equation is
false there and has no proof from the realized theory profile.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.SetProjectionProofControls
open SetComprehensionProofs SetMembershipProofs SetPairingProofs
open Mettapedia.Logic.HOL.Embedding
open ZFSetHenkinInterpretation (ChoiceSymbol)
open ZFSetPairingProofInterpretation (core epsilon model value ordered_value)
open ZFSetTraceProofInterpretation (basis laws laws_free basis_valid)

def zero : ClosedTerm ChoiceSymbol object := .const (.core .empty)
def one : ClosedTerm ChoiceSymbol object := power core zero
def fibre : ClosedTerm ChoiceSymbol object := power core one
def family : ClosedTerm ChoiceSymbol (object ⇒ object) := .lam (HOL.weaken fibre)
def pair : ClosedTerm ChoiceSymbol object := ordered core epsilon zero one

def inDomain : ProofSyntax ChoiceSymbol (basis []) (member core zero one) :=
  emptyInPowerEmpty core (laws []).pairing.power

def inFibre : ProofSyntax ChoiceSymbol (basis []) (member core one (.app family zero)) :=
  transportBound core one (.eqSymm (.beta zero (HOL.weaken fibre)))
    (selfInPower core one (laws []).pairing.power)

def admitted : ProofSyntax ChoiceSymbol (basis [])
    (member core pair (SetDependentSumProofs.sum core epsilon one family)) :=
  SetDependentSumProofs.introduce core epsilon one family zero one (laws []).pairing (laws []).union inDomain inFibre

theorem admitted_free : admitted.FunctionExtensionalityFree :=
  SetDependentSumProofs.introduce_free core epsilon one family zero one (laws []).pairing (laws []).union
    inDomain inFibre (laws_free []).pairing (laws_free []).union
    (emptyInPowerEmpty_free core _ trivial) ⟨trivial,selfInPower_free core one _ trivial⟩

def recovery := SetPairProjectionProofs.beta core epsilon zero one (laws []).pairing

theorem recovery_free : recovery.FunctionExtensionalityFree :=
  SetPairProjectionProofs.beta_free core epsilon zero one (laws []).pairing (laws_free []).pairing

def typed := SetSumProjectionProofs.typedFields core epsilon one family pair
  (laws []).pairing (laws []).union admitted

theorem typed_free : typed.FunctionExtensionalityFree :=
  SetSumProjectionProofs.typedFields_free core epsilon one family pair _ _ _ (laws_free []).pairing
    (laws_free []).union admitted_free

theorem wrongSecond_rejected :
    value.{0} (SetPairProjectionProofs.second core epsilon pair) (fun index => nomatch index) ≠
      value.{0} zero (fun index => nomatch index) := by
  unfold pair
  rw [(ZFSetProjectionProofInterpretation.constructor_values zero one (fun index => nomatch index)).2]
  change ZFSet.powerset (∅ : ZFSet.{0}) ≠ ∅
  intro equal
  have present : (∅ : ZFSet.{0}) ∈ ZFSet.powerset ∅ := ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)
  rw [equal] at present
  exact ZFSet.notMem_empty _ present

theorem unguardedReconstruction_false :
    value.{0} (ordered core epsilon (SetPairProjectionProofs.first core epsilon zero)
      (SetPairProjectionProofs.second core epsilon zero)) (fun index => nomatch index) ≠
    value.{0} zero (fun index => nomatch index) := by
  rw [ordered_value]
  change ZFSet.pair _ _ ≠ (∅ : ZFSet.{0})
  intro equal
  have present : ({value.{0} (SetPairProjectionProofs.first core epsilon zero) (fun index => nomatch index)} : ZFSet.{0}) ∈
      ZFSet.pair (value.{0} (SetPairProjectionProofs.first core epsilon zero) (fun index => nomatch index))
        (value.{0} (SetPairProjectionProofs.second core epsilon zero) (fun index => nomatch index)) := by
    simp [ZFSet.pair]
  rw [equal] at present
  exact ZFSet.notMem_empty _ present

theorem no_unguarded_reconstruction : ¬ Nonempty (ProofSyntax ChoiceSymbol (basis []) (.eq
    (ordered core epsilon (SetPairProjectionProofs.first core epsilon zero) (SetPairProjectionProofs.second core epsilon zero))
    zero)) := by
  rintro ⟨proof⟩
  apply unguardedReconstruction_false
  have result := Soundness.extDerivation_sound (ρ := fun index => nomatch index) proof.erase
    (model.{0}.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (by intro _ index; nomatch index) (basis_valid (Γ := []) (fun index => nomatch index))
  exact result

end Mettapedia.Logic.HOL.SetProjectionProofControls

