import Mettapedia.Languages.Metamath.MM2CompressedProofCapabilityOrigin

/-!
# Assertion-resume capability vocabulary

An assertion rejoin may republish exactly one opaque resume rule.  This
role-indexed predicate records that the value came from the admitted runtime
inventory rather than from an unrelated carrier or ordinary proof data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionResumeCapability

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofCapabilityOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution

def AssertionResumeCapture (carrier payload : Atom) : Prop :=
  decodeCompressedExecutableCapture carrier =
    some ⟨.runtime, "assertion-resume", payload⟩

def AssertionResumeCapabilities (expected : Atom) (space : List Atom) : Prop :=
  ∀ carrier ∈ space, ∀ payload,
    AssertionResumeCapture carrier payload → payload = expected

theorem AssertionResumeCapabilities.nil (expected : Atom) :
    AssertionResumeCapabilities expected [] := by
  intro carrier member
  contradiction

theorem AssertionResumeCapabilities.cons_of_not_capture
    {expected carrier : Atom} {space : List Atom}
    (notCapture : ∀ payload, ¬ AssertionResumeCapture carrier payload)
    (tail : AssertionResumeCapabilities expected space) :
    AssertionResumeCapabilities expected (carrier :: space) := by
  intro candidate member payload captured
  rcases List.mem_cons.mp member with rfl | member
  · exact False.elim (notCapture payload captured)
  · exact tail candidate member payload captured

theorem AssertionResumeCapabilities.cons_expected
    {expected carrier : Atom} {space : List Atom}
    (decoded : AssertionResumeCapture carrier expected)
    (tail : AssertionResumeCapabilities expected space) :
    AssertionResumeCapabilities expected (carrier :: space) := by
  intro candidate member payload candidateDecoded
  rcases List.mem_cons.mp member with rfl | member
  · unfold AssertionResumeCapture at decoded candidateDecoded
    have captureEqual := Option.some.inj (candidateDecoded.symm.trans decoded)
    exact congrArg CompressedExecutableCapture.payload captureEqual
  · exact tail candidate member payload candidateDecoded

theorem AssertionResumeCapabilities.append
    {expected : Atom} {left right : List Atom}
    (leftCapabilities : AssertionResumeCapabilities expected left)
    (rightCapabilities : AssertionResumeCapabilities expected right) :
    AssertionResumeCapabilities expected (left ++ right) := by
  intro carrier member payload captured
  rcases List.mem_append.mp member with member | member
  · exact leftCapabilities carrier member payload captured
  · exact rightCapabilities carrier member payload captured

/-- Positive control: the admitted assertion-resume carrier decodes with its
exact role and payload. -/
theorem exact_resume_carrier_captures :
    AssertionResumeCapture
      (compressedOwnedRuntimeRuleRow "assertion-resume"
        compressedAssertionResumeRule)
      compressedAssertionResumeRule := by
  rfl

/-- Negative control: the neighboring assertion-rejoin carrier cannot be
reclassified as an assertion-resume capability. -/
theorem rejoin_carrier_not_resume_capture (payload : Atom) :
    ¬ AssertionResumeCapture
      (compressedOwnedRuntimeRuleRow "assertion-rejoin"
        compressedAssertionRejoinRule) payload := by
  simp [AssertionResumeCapture, compressedOwnedRuntimeRuleRow,
    decodeCompressedExecutableCapture]

#print axioms AssertionResumeCapture
#print axioms AssertionResumeCapabilities
#print axioms AssertionResumeCapabilities.cons_of_not_capture
#print axioms AssertionResumeCapabilities.cons_expected
#print axioms AssertionResumeCapabilities.append
#print axioms exact_resume_carrier_captures
#print axioms rejoin_carrier_not_resume_capture

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionResumeCapability
