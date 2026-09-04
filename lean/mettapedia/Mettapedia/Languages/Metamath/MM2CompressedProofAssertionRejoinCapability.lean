import Mettapedia.Languages.Metamath.MM2CompressedProofCapabilityOrigin

/-!
# Assertion-rejoin capability vocabulary

This role-specific boundary states exactly which opaque assertion-rejoin
payload may be captured from a space.  It avoids assigning authority to names
or to unrelated executable families.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinCapability

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofCapabilityOrigin

def AssertionRejoinCapabilities (expected : Atom) (space : List Atom) : Prop :=
  ∀ carrier ∈ space, ∀ payload,
    decodeCompressedExecutableCapture carrier =
        some ⟨.runtime, "assertion-rejoin", payload⟩ →
      payload = expected

theorem AssertionRejoinCapabilities.nil (expected : Atom) :
    AssertionRejoinCapabilities expected [] := by
  intro carrier member
  contradiction

theorem AssertionRejoinCapabilities.cons_of_decode_none
    {expected carrier : Atom} {space : List Atom}
    (decoded : decodeCompressedExecutableCapture carrier = none)
    (tail : AssertionRejoinCapabilities expected space) :
    AssertionRejoinCapabilities expected (carrier :: space) := by
  intro candidate member payload candidateDecoded
  rcases List.mem_cons.mp member with equal | member
  · subst candidate
    rw [decoded] at candidateDecoded
    contradiction
  · exact tail candidate member payload candidateDecoded

theorem AssertionRejoinCapabilities.cons_expected
    {expected carrier : Atom} {space : List Atom}
    (decoded : decodeCompressedExecutableCapture carrier =
      some ⟨.runtime, "assertion-rejoin", expected⟩)
    (tail : AssertionRejoinCapabilities expected space) :
    AssertionRejoinCapabilities expected (carrier :: space) := by
  intro candidate member payload candidateDecoded
  rcases List.mem_cons.mp member with equal | member
  · subst candidate
    have captureEqual := Option.some.inj (candidateDecoded.symm.trans decoded)
    exact congrArg CompressedExecutableCapture.payload captureEqual
  · exact tail candidate member payload candidateDecoded

theorem AssertionRejoinCapabilities.append
    {expected : Atom} {left right : List Atom}
    (leftCapabilities : AssertionRejoinCapabilities expected left)
    (rightCapabilities : AssertionRejoinCapabilities expected right) :
    AssertionRejoinCapabilities expected (left ++ right) := by
  intro carrier member payload decoded
  rcases List.mem_append.mp member with member | member
  · exact leftCapabilities carrier member payload decoded
  · exact rightCapabilities carrier member payload decoded

#print axioms AssertionRejoinCapabilities
#print axioms AssertionRejoinCapabilities.cons_of_decode_none
#print axioms AssertionRejoinCapabilities.cons_expected
#print axioms AssertionRejoinCapabilities.append

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinCapability
