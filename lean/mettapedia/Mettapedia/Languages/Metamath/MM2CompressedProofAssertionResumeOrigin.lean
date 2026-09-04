import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinContinuous
import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionResumeCapability
import Mettapedia.Languages.ProcessCalculi.MORK.ComputablePatternCaptureOrigin

/-!
# Matcher origin for the compressed assertion resume

The assertion-rejoin matcher republishes the resume rule captured by its last
premise.  These theorems reconstruct that value from a concrete carrier in the
pre-state and then fix it using the role-indexed capability invariant.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionResumeOrigin

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionResumeCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofCapabilityOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

private theorem matchAtom_assertionResume_captures
    {beforeCapture afterCapture : Subst} {carrier : Atom}
    (matched : cmatchAtom beforeCapture rejoinResumeCaptureTemplate carrier =
      some afterCapture) :
    ∃ payload,
      Subst.lookup afterCapture "compressed-assertion-resume-rule" =
          some payload ∧
        AssertionResumeCapture carrier payload := by
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

private theorem rejoinDirective_not_resume_capture (payload : Atom) :
    ¬ AssertionResumeCapture compressedAssertionRejoinDirective.atom
      payload := by
  intro captured
  unfold AssertionResumeCapture at captured
  simp [decodeCompressedExecutableCapture,
    compressedAssertionRejoinDirective, compressedAssertionRejoinRule] at captured

theorem assertionRejoinMatcherRow_resume_origin
    {space : List Atom} {substitution : Subst} {payload : Atom}
    (rowMember : substitution ∈
      (cmatchInputSpec []
        (compressedAssertionRejoinDirective.atom ::
          space.erase compressedAssertionRejoinDirective.atom)
        compressedAssertionRejoinDirective.rule.input).map Prod.fst)
    (instantiates : instantiateTemplateAtom? substitution
      (.var "compressed-assertion-resume-rule") = some payload) :
    ∃ carrier ∈ space, AssertionResumeCapture carrier payload := by
  have rowMember' : substitution ∈
      (cmatchInputSpec []
        (compressedAssertionRejoinDirective.atom ::
          space.erase compressedAssertionRejoinDirective.atom)
        (.compat (mkPattern rejoinPatterns))).map Prod.fst := by
    rw [compressedAssertionRejoin_input_exact] at rowMember
    simpa [rejoinPatterns] using rowMember
  obtain ⟨carrier, capturedPayload, carrierMember, capturedLookup, captured⟩ :=
    cmatchInputSpec_capture_origin AssertionResumeCapture
      "compressed-assertion-resume-rule"
      (compressedAssertionRejoinDirective.atom ::
        space.erase compressedAssertionRejoinDirective.atom)
      [rejoinSelfTemplate, rejoinContextTemplate,
       rejoinReturnedControlTemplate, rejoinReturnedStackTemplate,
       rejoinNormalStackSuccessorTemplate, rejoinNodeSuccessorTemplate,
       rejoinNormalLabelTemplate]
      rejoinResumeCaptureTemplate [] rowMember'
      matchAtom_assertionResume_captures
  have payloadLookup :
      Subst.lookup substitution "compressed-assertion-resume-rule" =
        some payload :=
    (instantiateTemplateAtom?_var_eq_some_iff substitution
      "compressed-assertion-resume-rule" payload).1 instantiates
  have payloadEqual : capturedPayload = payload :=
    Option.some.inj (capturedLookup.symm.trans payloadLookup)
  subst capturedPayload
  rcases List.mem_cons.mp carrierMember with selected | prior
  · exact False.elim
      (rejoinDirective_not_resume_capture payload (selected ▸ captured))
  · exact ⟨carrier, List.mem_of_mem_erase prior, captured⟩

theorem assertionRejoinMatcherRow_resume_exact
    {space : List Atom}
    (capabilities : AssertionResumeCapabilities compressedAssertionResumeRule
      space)
    {substitution : Subst} {payload : Atom}
    (rowMember : substitution ∈
      (cmatchInputSpec []
        (compressedAssertionRejoinDirective.atom ::
          space.erase compressedAssertionRejoinDirective.atom)
        compressedAssertionRejoinDirective.rule.input).map Prod.fst)
    (instantiates : instantiateTemplateAtom? substitution
      (.var "compressed-assertion-resume-rule") = some payload) :
    payload = compressedAssertionResumeRule := by
  obtain ⟨carrier, member, captured⟩ :=
    assertionRejoinMatcherRow_resume_origin rowMember instantiates
  exact capabilities carrier member payload captured

#print axioms assertionRejoinMatcherRow_resume_origin
#print axioms assertionRejoinMatcherRow_resume_exact

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionResumeOrigin
