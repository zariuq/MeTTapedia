import Mettapedia.Languages.Metamath.MM2CompressedProofSourceNormalBridgeCapability
import Mettapedia.Languages.ProcessCalculi.MORK.ComputablePatternCaptureOrigin

/-!
# Matcher origin for the decorated assertion bridge

A decorated assertion match may republish a normal-dispatch bridge only when
the matched pre-state contains a carrier for that exact bridge.  Combined with
the source-space capability invariant, the emitted payload is fixed to the
compiler-authored bridge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionBridgeOrigin

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofNormalBridgeCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

def NormalDispatchBridgeCapture (carrier payload : Atom) : Prop :=
  decodeNormalDispatchBridgeCapture carrier = some payload

private theorem matchAtom_decoratedBridge_captures
    {beforeCapture afterCapture : Subst} {carrier : Atom}
    (matched : cmatchAtom beforeCapture
      decoratedDirectAssertionBridgeCaptureTemplate carrier =
        some afterCapture) :
    ∃ payload,
      Subst.lookup afterCapture "normal-bridge-rule" = some payload ∧
        NormalDispatchBridgeCapture carrier payload := by
  rw [Conformance.cmatchAtom_eq_matchAtom] at matched
  have relational := matchAtom_sound matched
  cases relational with
  | expr_cons headMatched tail1 =>
      cases headMatched
      cases tail1 with
      | expr_cons payloadMatched finalTail =>
          cases finalTail
          cases payloadMatched with
          | var_fresh lookup =>
              rename_i payload
              exact ⟨payload, by simp [Subst.lookup], rfl⟩
          | var_bound lookup =>
              rename_i payload
              exact ⟨payload, lookup, rfl⟩

private theorem decoratedDirectAssertion_not_bridge_capture
    (payload : Atom) :
    ¬ NormalDispatchBridgeCapture decoratedDirectAssertionDirective.atom
      payload := by
  intro captured
  unfold NormalDispatchBridgeCapture at captured
  rw [decodeNormalDispatchBridgeCapture_eq_none_of_supported
    extract_decoratedDirectAssertionRule_exact] at captured
  contradiction

/-- Every bridge value published by an arbitrary decorated assertion matcher
row originates in a concrete bridge carrier in the pre-state. -/
theorem decoratedAssertionMatcherRow_bridge_origin
    {space : List Atom} {substitution : Subst} {payload : Atom}
    (rowMember : substitution ∈
      (cmatchInputSpec []
        (decoratedDirectAssertionDirective.atom ::
          space.erase decoratedDirectAssertionDirective.atom)
        decoratedDirectAssertionDirective.rule.input).map Prod.fst)
    (instantiates : instantiateTemplateAtom? substitution
      (.var "normal-bridge-rule") = some payload) :
    ∃ carrier ∈ space, NormalDispatchBridgeCapture carrier payload := by
  have rowMember' : substitution ∈
      (cmatchInputSpec []
        (decoratedDirectAssertionDirective.atom ::
          space.erase decoratedDirectAssertionDirective.atom)
        (.compat (mkPattern
          (directAssertionPatterns ++
            decoratedDirectAssertionBridgeCaptureTemplate :: [])))).map
              Prod.fst := by
    rw [decoratedDirectAssertionDirective_input_exact] at rowMember
    simpa [decoratedDirectAssertionPatterns] using rowMember
  obtain ⟨carrier, capturedPayload, carrierMember, capturedLookup, captured⟩ :=
    cmatchInputSpec_capture_origin NormalDispatchBridgeCapture
      "normal-bridge-rule"
      (decoratedDirectAssertionDirective.atom ::
        space.erase decoratedDirectAssertionDirective.atom)
      directAssertionPatterns decoratedDirectAssertionBridgeCaptureTemplate []
      rowMember' matchAtom_decoratedBridge_captures
  have payloadLookup :
      Subst.lookup substitution "normal-bridge-rule" = some payload :=
    (instantiateTemplateAtom?_var_eq_some_iff substitution
      "normal-bridge-rule" payload).1 instantiates
  have payloadEqual : capturedPayload = payload :=
    Option.some.inj (capturedLookup.symm.trans payloadLookup)
  subst capturedPayload
  rcases List.mem_cons.mp carrierMember with selected | prior
  · exact False.elim
      (decoratedDirectAssertion_not_bridge_capture payload
        (selected ▸ captured))
  · exact ⟨carrier, List.mem_of_mem_erase prior, captured⟩

/-- A successful matcher row over a capability-closed space can instantiate
only the compiler-authored normal-dispatch bridge. -/
theorem decoratedAssertionMatcherRow_bridge_exact
    {space : List Atom}
    (capabilities : NormalDispatchBridgeCapabilities
      compressedNormalDispatchBridgeRule space)
    {substitution : Subst} {payload : Atom}
    (rowMember : substitution ∈
      (cmatchInputSpec []
        (decoratedDirectAssertionDirective.atom ::
          space.erase decoratedDirectAssertionDirective.atom)
        decoratedDirectAssertionDirective.rule.input).map Prod.fst)
    (instantiates : instantiateTemplateAtom? substitution
      (.var "normal-bridge-rule") = some payload) :
    payload = compressedNormalDispatchBridgeRule := by
  obtain ⟨carrier, member, captured⟩ :=
    decoratedAssertionMatcherRow_bridge_origin rowMember instantiates
  exact capabilities carrier member payload captured

#print axioms decoratedAssertionMatcherRow_bridge_origin
#print axioms decoratedAssertionMatcherRow_bridge_exact

end Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionBridgeOrigin
