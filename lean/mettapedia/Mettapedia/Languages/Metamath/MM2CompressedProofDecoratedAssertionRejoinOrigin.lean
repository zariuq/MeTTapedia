import Mettapedia.Languages.Metamath.MM2CompressedProofSourceAssertionRejoinCapability
import Mettapedia.Languages.ProcessCalculi.MORK.ComputablePatternCaptureOrigin

/-!
# Matcher origin for the decorated assertion rejoin

The normal-machine rejoin emitted by a decorated assertion match originates
in an actual role-indexed carrier.  The following bridge premise does not
alter that captured value.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionRejoinOrigin

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofCapabilityOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionExecutableFrameCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

def AssertionRejoinCapture (carrier payload : Atom) : Prop :=
  decodeCompressedExecutableCapture carrier =
    some ⟨.runtime, "assertion-rejoin", payload⟩

private theorem matchAtom_directAssertionRejoin_captures
    {beforeCapture afterCapture : Subst} {carrier : Atom}
    (matched : cmatchAtom beforeCapture directAssertionRejoinCaptureTemplate
      carrier = some afterCapture) :
    ∃ payload,
      Subst.lookup afterCapture "compressed-assertion-rejoin-rule" =
          some payload ∧
        AssertionRejoinCapture carrier payload := by
  rw [Conformance.cmatchAtom_eq_matchAtom] at matched
  have relational := matchAtom_sound matched
  cases relational with
  | expr_cons headMatched tail1 =>
      cases headMatched
      cases tail1 with
      | expr_cons kindMatched tail2 =>
          cases kindMatched
          cases tail2 with
          | expr_cons payloadMatched finalTail =>
              cases finalTail
              cases payloadMatched with
              | var_fresh lookup =>
                  rename_i payload
                  exact ⟨payload, by simp [Subst.lookup], rfl⟩
              | var_bound lookup =>
                  rename_i payload
                  exact ⟨payload, lookup, rfl⟩

private theorem decoratedDirectAssertion_not_rejoin_capture
    (payload : Atom) :
    ¬ AssertionRejoinCapture decoratedDirectAssertionDirective.atom
      payload := by
  intro captured
  unfold AssertionRejoinCapture at captured
  rw [decodeCompressedExecutableCapture_eq_none_of_supported
    extract_decoratedDirectAssertionRule_exact] at captured
  contradiction

theorem decoratedAssertionMatcherRow_rejoin_origin
    {space : List Atom} {substitution : Subst} {payload : Atom}
    (rowMember : substitution ∈
      (cmatchInputSpec []
        (decoratedDirectAssertionDirective.atom ::
          space.erase decoratedDirectAssertionDirective.atom)
        decoratedDirectAssertionDirective.rule.input).map Prod.fst)
    (instantiates : instantiateTemplateAtom? substitution
      (.var "compressed-assertion-rejoin-rule") = some payload) :
    ∃ carrier ∈ space, AssertionRejoinCapture carrier payload := by
  have rowMember' : substitution ∈
      (cmatchInputSpec []
        (decoratedDirectAssertionDirective.atom ::
          space.erase decoratedDirectAssertionDirective.atom)
        (.compat (mkPattern
          ([directAssertionSelfTemplate, directAssertionPendingTemplate,
            directAssertionLookupTemplate, directAssertionHeapTemplate,
            directAssertionMachineTemplate, directAssertionHeaderTemplate] ++
            directAssertionRejoinCaptureTemplate ::
              decoratedDirectAssertionBridgeCaptureTemplate :: [])))).map
                Prod.fst := by
    rw [decoratedDirectAssertionDirective_input_exact] at rowMember
    simpa [decoratedDirectAssertionPatterns, directAssertionPatterns] using
      rowMember
  obtain ⟨carrier, capturedPayload, carrierMember, capturedLookup, captured⟩ :=
    cmatchInputSpec_capture_origin AssertionRejoinCapture
      "compressed-assertion-rejoin-rule"
      (decoratedDirectAssertionDirective.atom ::
        space.erase decoratedDirectAssertionDirective.atom)
      [directAssertionSelfTemplate, directAssertionPendingTemplate,
       directAssertionLookupTemplate, directAssertionHeapTemplate,
       directAssertionMachineTemplate, directAssertionHeaderTemplate]
      directAssertionRejoinCaptureTemplate
      [decoratedDirectAssertionBridgeCaptureTemplate]
      rowMember' matchAtom_directAssertionRejoin_captures
  have payloadLookup :
      Subst.lookup substitution "compressed-assertion-rejoin-rule" =
        some payload :=
    (instantiateTemplateAtom?_var_eq_some_iff substitution
      "compressed-assertion-rejoin-rule" payload).1 instantiates
  have payloadEqual : capturedPayload = payload :=
    Option.some.inj (capturedLookup.symm.trans payloadLookup)
  subst capturedPayload
  rcases List.mem_cons.mp carrierMember with selected | prior
  · exact False.elim
      (decoratedDirectAssertion_not_rejoin_capture payload
        (selected ▸ captured))
  · exact ⟨carrier, List.mem_of_mem_erase prior, captured⟩

theorem decoratedAssertionMatcherRow_rejoin_exact
    {space : List Atom}
    (capabilities : AssertionRejoinCapabilities compressedAssertionRejoinRule
      space)
    {substitution : Subst} {payload : Atom}
    (rowMember : substitution ∈
      (cmatchInputSpec []
        (decoratedDirectAssertionDirective.atom ::
          space.erase decoratedDirectAssertionDirective.atom)
        decoratedDirectAssertionDirective.rule.input).map Prod.fst)
    (instantiates : instantiateTemplateAtom? substitution
      (.var "compressed-assertion-rejoin-rule") = some payload) :
    payload = compressedAssertionRejoinRule := by
  obtain ⟨carrier, member, captured⟩ :=
    decoratedAssertionMatcherRow_rejoin_origin rowMember instantiates
  exact capabilities carrier member payload captured

#print axioms decoratedAssertionMatcherRow_rejoin_origin
#print axioms decoratedAssertionMatcherRow_rejoin_exact

end Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionRejoinOrigin
