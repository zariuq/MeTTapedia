import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeKeySeparation

/-!
# Bridge-key reflection for assertion publications

The authored assertion sinks publish four non-executable row families and two
exact compiler-captured continuations.  Consequently a published row at the
normal-dispatch bridge key is the bridge itself.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgePublishedKeyReflection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeKeySeparation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalDecoratedAssertionLaunch
open Mettapedia.Languages.ProcessCalculi.MORK

def NormalDispatchBridgeKeyReflects (row : Atom) : Prop :=
  morkSupportKey row = morkSupportKey compressedNormalDispatchBridgeRule →
    row = compressedNormalDispatchBridgeRule

private theorem exactPublished_bridge_classification {row : Atom}
    (published : DecoratedAssertionExactPublishedAtom row) :
    (∃ head,
      compressedDynamicRowHead? row = some head ∧
        0 < (morkUtf8Bytes head).length ∧
        (morkUtf8Bytes head).length < 64 ∧
        head ≠ "exec") ∨
      row = compressedAssertionRejoinRule ∨
      row = compressedNormalDispatchBridgeRule := by
  rcases published with assertionContext | normalControl | normalLabel |
      reload | rejoin | bridge
  · exact Or.inl ⟨"mm-compressed-assertion-context", assertionContext,
      by decide, by decide, by decide⟩
  · exact Or.inl ⟨"mm-normal-control", normalControl,
      by decide, by decide, by decide⟩
  · exact Or.inl ⟨"mm-linked-row", normalLabel,
      by decide, by decide, by decide⟩
  · exact Or.inl ⟨"mm-reload-compressed-normal-dispatch", reload,
      by decide, by decide, by decide⟩
  · exact Or.inr (Or.inl rejoin)
  · exact Or.inr (Or.inr bridge)

theorem exactPublished_bridge_key_reflects {row : Atom}
    (published : DecoratedAssertionExactPublishedAtom row) :
    NormalDispatchBridgeKeyReflects row := by
  rcases exactPublished_bridge_classification published with
    dynamic | rejoin | bridge
  · obtain ⟨head, headExact, headPositive, headBound, nonExec⟩ := dynamic
    intro equal
    exact (dynamicRow_key_ne_normalDispatchBridge head headExact headPositive
      headBound nonExec equal).elim
  · intro equal
    have rejoinKeyEqual :
        morkSupportKey compressedAssertionRejoinRule =
          morkSupportKey compressedNormalDispatchBridgeRule :=
      (congrArg morkSupportKey rejoin).symm.trans equal
    exact (compressedAssertionRejoin_key_ne_normalDispatchBridge
      rejoinKeyEqual).elim
  · intro _
    exact bridge

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgePublishedKeyReflection
