import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofInterpretation

/-!
# Guarded trace computation and separating controls

The value function is a genuine constant-one lambda. The guarded computation
has retained proof data. The empty-domain interpretation refutes the same
computation without its domain premise.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.SetTraceProofControls
open SetComprehensionProofs SetMembershipProofs SetPairingProofs
open Mettapedia.Logic.HOL.Embedding
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (ChoiceSymbol)
open Mettapedia.Logic.HOL.Embedding.ZFSetPairingProofInterpretation (core epsilon model value)
open Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofInterpretation
  (basis laws laws_free basis_valid application_value abstraction_value)

def zero : ClosedTerm ChoiceSymbol object := .const (.core .empty)
def one : ClosedTerm ChoiceSymbol object := power core zero
def constantOne : ClosedTerm ChoiceSymbol (object ⇒ object) := .lam (HOL.weaken one)
def constantZero : ClosedTerm ChoiceSymbol (object ⇒ object) := .lam (HOL.weaken zero)

def inDomain : ProofSyntax ChoiceSymbol (basis []) (member core zero one) :=
  emptyInPowerEmpty core (laws []).pairing.power

theorem inDomain_free : inDomain.FunctionExtensionalityFree :=
  emptyInPowerEmpty_free core _ trivial

def computation : ProofSyntax ChoiceSymbol (basis []) (.eq
    (SetTraceProofs.application core epsilon (SetTraceProofs.abstraction core epsilon one constantOne) zero)
    (.app constantOne zero)) :=
  SetTraceProofs.beta core epsilon one constantOne zero (laws []) inDomain

theorem computation_free : computation.FunctionExtensionalityFree :=
  SetTraceProofs.beta_free core epsilon one constantOne zero (laws []) inDomain (laws_free []) inDomain_free

def absentFibre : ProofSyntax ChoiceSymbol (basis []) (.not (member core one (.app constantZero zero))) :=
  .notI (.notE ((emptyElim core one (laws []).pairing.empty).prepend _)
    (transportBound core one (.beta zero (HOL.weaken zero)) (.hyp 0)))

theorem absentFibre_free : absentFibre.FunctionExtensionalityFree := by
  change ((emptyElim core one (laws []).pairing.empty).prepend _).FunctionExtensionalityFree ∧ (True ∧ True)
  refine ⟨?_,trivial,trivial⟩
  simpa [ProofSyntax.prepend] using (emptyElim_free core one (laws []).pairing.empty).mpr trivial

def emptyFibreRefutation : ProofSyntax ChoiceSymbol (basis []) (.not
    (member core (ordered core epsilon zero one) (SetDependentSumProofs.sum core epsilon one constantZero))) :=
  SetDependentSumProofs.outsideFibre core epsilon one constantZero zero one
    (laws []).pairing (laws []).union absentFibre

theorem emptyFibreRefutation_free : emptyFibreRefutation.FunctionExtensionalityFree :=
  SetDependentSumProofs.outsideFibre_free core epsilon one constantZero zero one
    (laws []).pairing (laws []).union absentFibre (laws_free []).pairing (laws_free []).union absentFibre_free

theorem unguardedComputation_false :
    value.{0} (SetTraceProofs.application core epsilon (SetTraceProofs.abstraction core epsilon zero constantOne) zero)
      (fun index => nomatch index) ≠
    value.{0} (.app constantOne zero) (fun index => nomatch index) := by
  rw [application_value,abstraction_value]
  have outside := ZFSetTraceProducts.traceApp_graph_outside
    (ZFSetGraphProofInterpretation.functionValue constantOne (fun index => nomatch index))
    (show value zero (fun index => nomatch index) ∉ value zero (fun index => nomatch index) from
      ZFSet.notMem_empty _)
  rw [outside]
  change (∅ : ZFSet.{0}) ≠ ZFSet.powerset ∅
  intro equal
  have present : (∅ : ZFSet.{0}) ∈ ZFSet.powerset ∅ := ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)
  rw [← equal] at present
  exact ZFSet.notMem_empty _ present

theorem no_unguarded_proof : ¬ Nonempty (ProofSyntax ChoiceSymbol (basis []) (.eq
    (SetTraceProofs.application core epsilon (SetTraceProofs.abstraction core epsilon zero constantOne) zero)
    (.app constantOne zero))) := by
  rintro ⟨proof⟩
  apply unguardedComputation_false
  have result := Soundness.extDerivation_sound (ρ := fun index => nomatch index) proof.erase
    (model.{0}.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (by intro _ index; nomatch index) (basis_valid (Γ := []) (fun index => nomatch index))
  exact result

end Mettapedia.Logic.HOL.SetTraceProofControls

