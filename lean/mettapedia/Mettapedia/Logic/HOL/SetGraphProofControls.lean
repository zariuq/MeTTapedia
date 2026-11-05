import Mettapedia.Logic.HOL.SetGraphProofs
import Mettapedia.Logic.HOL.Embedding.ZFSetPairingProofInterpretation

/-!
# Positive graph lookup and domain/result refusal controls

The domain is the singleton powerset of the empty set, and the function is
the actual identity lambda. The controls produce retained membership and
refutation proofs under the original five set-profile hypotheses.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.SetGraphProofControls
open SetComprehensionProofs SetMembershipProofs SetPairingProofs SetGraphProofs
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (ChoiceSymbol)
open Mettapedia.Logic.HOL.Embedding.ZFSetPairingProofInterpretation (core epsilon laws laws_free basis)

def zero : ClosedTerm ChoiceSymbol object := .const (.core .empty)
def one : ClosedTerm ChoiceSymbol object := power core zero
def identity : ClosedTerm ChoiceSymbol (object ⇒ object) := .lam (.var .vz)
def sample : ClosedTerm ChoiceSymbol object := graph core epsilon one identity

def identityBeta : ProofSyntax ChoiceSymbol (basis []) (.eq (.app identity zero) zero) :=
  .beta zero (.var .vz)

def admitted : ProofSyntax ChoiceSymbol (basis []) (member core (ordered core epsilon zero zero) sample) :=
  transportValue core _ (orderedCongrSecond core epsilon zero identityBeta)
    (graphIntro core epsilon one identity zero (laws []).replacement
      (emptyInPowerEmpty core (laws []).power))

theorem admitted_free : admitted.FunctionExtensionalityFree :=
  ⟨orderedCongrSecond_free core epsilon _ _ trivial,
    graphIntro_free core epsilon _ _ _ _ _ trivial
      (SetComprehensionProofs.emptyInPowerEmpty_free core _ trivial)⟩

def emptyRefutation : ProofSyntax ChoiceSymbol (basis [])
    (.not (member core (ordered core epsilon zero zero) (graph core epsilon zero identity))) :=
  outside core epsilon zero identity zero zero (laws []) (emptyElim core zero (laws []).empty)

theorem emptyRefutation_free : emptyRefutation.FunctionExtensionalityFree :=
  outside_free core epsilon _ _ _ _ _ _ (laws_free []) ((emptyElim_free core _ _).mpr trivial)

def resultRefutation : ProofSyntax ChoiceSymbol (basis [])
    (.not (member core (ordered core epsilon zero one) sample)) :=
  .notI (.notE ((emptyNePower core (laws []).empty (laws []).power).prepend _)
    (.eqTrans (.eqSymm (.beta zero (.var .vz)))
      (.andER (graphElim core epsilon one identity zero one ((laws []).prepend _) (.hyp 0)))))

theorem resultRefutation_free : resultRefutation.FunctionExtensionalityFree := by
  change ((emptyNePower core (laws []).empty (laws []).power).prepend
      (member core (ordered core epsilon zero one) sample)).FunctionExtensionalityFree ∧
    (ProofSyntax.beta (Δ := member core (ordered core epsilon zero one) sample :: basis [])
      zero (.var .vz)).FunctionExtensionalityFree ∧
    (graphElim core epsilon one identity zero one
      ((laws []).prepend (member core (ordered core epsilon zero one) sample)) (.hyp 0)).FunctionExtensionalityFree
  refine ⟨?_,?_,?_⟩
  · simpa [ProofSyntax.prepend] using
      emptyNePower_free core (laws []).empty (laws []).power trivial trivial
  · trivial
  · exact graphElim_free core epsilon one identity zero one
      ((laws []).prepend (member core (ordered core epsilon zero one) sample)) (.hyp 0)
      ((laws []).prepend_free _ (laws_free [])) trivial

end Mettapedia.Logic.HOL.SetGraphProofControls

