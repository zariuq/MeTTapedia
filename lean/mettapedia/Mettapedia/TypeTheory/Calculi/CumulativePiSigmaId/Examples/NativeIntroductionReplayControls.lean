import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveIntroductionReplay
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAll

/-!
# Introduction replay controls in the native natural-number profile

The pair has the dependent type `Σ n : Nat, Id Nat n n`. Changing its equality
witness to the successor case is refused. Lambda controls likewise distinguish
a natural-number identity function from an extra abstraction at its result.
All observations use the original producer and independent checker.
-/

set_option autoImplicit false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveElaboration

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeIntroductionReplayControls
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeNaturalVectorFamilies

local instance : DecidableRel NativeVectorAll.rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred NativeVectorAll.rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (NativeVectorAll.rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel NativeVectorAll.rules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel NativeVectorAll.rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def identityType : Tower.Tm 0 := .pi natTm natTm
def dependentPairType : Tower.Tm 0 := .sigma natTm (.id natTm (.var 0) (.var 0))

private theorem identity_view :
    NativeVectorAll.choices.normalize 15 identityType = .pi natTm natTm := by decide +kernel
private theorem dependentPair_view :
    NativeVectorAll.choices.normalize 15 dependentPairType =
      .sigma natTm (.id natTm (.var 0) (.var 0)) := by decide +kernel

theorem identity_accepted : termReplayAccepted NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 16 .nil (.lam (.var 0)) identityType = true := by
  apply (lambda_replay_factor NativeVectorAll.rules NativeVectorAll.decoder NativeVectorAll.choices
    15 .nil (.var 0) identityType natTm natTm identity_view).trans
  decide +kernel

theorem extra_abstraction_refused : termReplayAccepted NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 16 .nil (.lam (.lam (.var 0))) identityType = false := by
  apply (lambda_replay_factor NativeVectorAll.rules NativeVectorAll.decoder NativeVectorAll.choices
    15 .nil (.lam (.var 0)) identityType natTm natTm identity_view).trans
  decide +kernel

theorem dependent_pair_accepted : termReplayAccepted NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 16 .nil (.pair zeroTm (.refl zeroTm)) dependentPairType = true := by
  apply (pair_replay_factor NativeVectorAll.rules NativeVectorAll.decoder NativeVectorAll.choices
    15 .nil zeroTm (.refl zeroTm) dependentPairType natTm (.id natTm (.var 0) (.var 0))
    dependentPair_view).trans
  decide +kernel

theorem changed_dependent_witness_refused : termReplayAccepted NativeVectorAll.rules NativeVectorAll.decoder
    NativeVectorAll.choices 16 .nil (.pair zeroTm (.refl (succApp zeroTm))) dependentPairType = false := by
  apply (pair_replay_factor NativeVectorAll.rules NativeVectorAll.decoder NativeVectorAll.choices
    15 .nil zeroTm (.refl (succApp zeroTm)) dependentPairType natTm (.id natTm (.var 0) (.var 0))
    dependentPair_view).trans
  decide +kernel

#print axioms identity_accepted
#print axioms extra_abstraction_refused
#print axioms dependent_pair_accepted
#print axioms changed_dependent_witness_refused
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeIntroductionReplayControls
