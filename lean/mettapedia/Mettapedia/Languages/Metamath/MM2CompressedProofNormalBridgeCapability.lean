import Mettapedia.Languages.ProcessCalculi.MORK.SupportedExecErasure

/-!
# Capability vocabulary for the compressed-to-normal dispatch bridge

The decorated assertion launcher may capture executable code only through
this inert two-field carrier.  Authorization relative to a concrete verifier
presentation is proved in separate source-frame modules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofNormalBridgeCapability

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

def decodeNormalDispatchBridgeCapture : Atom → Option Atom
  | .expression
      [.symbol "mm-internal-compressed-normal-dispatch-bridge", payload] =>
      some payload
  | _ => none

def NormalDispatchBridgeCapabilities
    (expected : Atom) (space : List Atom) : Prop :=
  ∀ carrier ∈ space, ∀ payload,
    decodeNormalDispatchBridgeCapture carrier = some payload →
      payload = expected

theorem decodeNormalDispatchBridgeCapture_eq_none_of_supported
    {atom : Atom} {directive : SourceExecFact}
    (decoded : extractSupportedSourceExecFact atom = some directive) :
    decodeNormalDispatchBridgeCapture directive.atom = none := by
  rw [extractSupportedSourceExecFact_atom decoded]
  have rawSome : (extractRawExecFact atom).isSome := by
    unfold extractSupportedSourceExecFact at decoded
    cases rawEq : extractRawExecFact atom <;> simp_all
  unfold extractRawExecFact at rawSome
  split at rawSome
  · rfl
  · contradiction

theorem NormalDispatchBridgeCapabilities.nil (expected : Atom) :
    NormalDispatchBridgeCapabilities expected [] := by
  intro carrier member
  contradiction

theorem NormalDispatchBridgeCapabilities.cons_of_decode_none
    {expected carrier : Atom} {space : List Atom}
    (decoded : decodeNormalDispatchBridgeCapture carrier = none)
    (tail : NormalDispatchBridgeCapabilities expected space) :
    NormalDispatchBridgeCapabilities expected (carrier :: space) := by
  intro candidate member payload candidateDecoded
  rcases List.mem_cons.mp member with equal | member
  · subst candidate
    rw [decoded] at candidateDecoded
    contradiction
  · exact tail candidate member payload candidateDecoded

theorem NormalDispatchBridgeCapabilities.cons_expected
    {expected carrier : Atom} {space : List Atom}
    (decoded : decodeNormalDispatchBridgeCapture carrier = some expected)
    (tail : NormalDispatchBridgeCapabilities expected space) :
    NormalDispatchBridgeCapabilities expected (carrier :: space) := by
  intro candidate member payload candidateDecoded
  rcases List.mem_cons.mp member with equal | member
  · subst candidate
    exact Option.some.inj (candidateDecoded.symm.trans decoded)
  · exact tail candidate member payload candidateDecoded

theorem NormalDispatchBridgeCapabilities.append
    {expected : Atom} {left right : List Atom}
    (leftCapabilities : NormalDispatchBridgeCapabilities expected left)
    (rightCapabilities : NormalDispatchBridgeCapabilities expected right) :
    NormalDispatchBridgeCapabilities expected (left ++ right) := by
  intro carrier member payload decoded
  rcases List.mem_append.mp member with member | member
  · exact leftCapabilities carrier member payload decoded
  · exact rightCapabilities carrier member payload decoded

#print axioms NormalDispatchBridgeCapabilities
#print axioms decodeNormalDispatchBridgeCapture_eq_none_of_supported
#print axioms NormalDispatchBridgeCapabilities.cons_of_decode_none
#print axioms NormalDispatchBridgeCapabilities.cons_expected
#print axioms NormalDispatchBridgeCapabilities.append

end Mettapedia.Languages.Metamath.MM2CompressedProofNormalBridgeCapability
