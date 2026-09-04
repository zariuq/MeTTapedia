import Mettapedia.Languages.Metamath.MM2NormalDVAddressed
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveGSLTNativeTypes
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveInertScheduling

/-!
# Continuous addressed disjoint-variable execution

The focused addressed phase theorems identify the semantic transition selected
by each cursor.  The executable verifier loads all eight phase rules together,
so lower-priority rules whose inputs do not match are genuine administrative
steps.  This module threads those inert probes through the actual list-valued
work queue instead of rebuilding a fresh focused space for each phase.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2NormalDVContinuous

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2NormalBodyBuildAddressed
open Mettapedia.Languages.Metamath.MM2NormalDVAddressed
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-! ## Terminal cursor in the loaded work queue -/

/-- The terminal cursor together with the suffix of DV phase rules that has
not yet been consumed by the scheduler. -/
def normalDVLoadedCompleteStageAt
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd phase : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) : List Atom :=
  normalDVLoadedPhaseRules.drop phase ++
    [normalDVNextPairRowAt scopeOwner proofOwner proofAddress assertionLabel
      pairEnd pairEnd sourceBody context]

theorem normalDVLoadedCompleteStageAt_zero
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
        assertionLabel pairEnd 0 sourceBody context =
      normalDVLoadedCompleteSpaceAt scopeOwner proofOwner proofAddress
        assertionLabel pairEnd sourceBody context := by
  rfl

/-- Every remaining rule has an `exec` head, while the terminal data row has
an `mm-dv-next-pair` head.  Any other fixed head therefore has no carrier in
any terminal suffix state. -/
private theorem normalDVLoadedCompleteStageAt_head_never_matches
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd phase : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom)
    (beforeFactor : Subst) (carrier : Atom)
    (carrierMember : carrier ∈
      normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
        assertionLabel pairEnd phase sourceBody context)
    {patternHead : String} {patternTail : List Atom}
    (notExec : patternHead ≠ "exec")
    (notCursor : patternHead ≠ "mm-dv-next-pair") :
    cmatchAtom beforeFactor
        (.expression (.symbol patternHead :: patternTail)) carrier = none := by
  simp only [normalDVLoadedCompleteStageAt, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at carrierMember
  rcases carrierMember with ruleMember | cursorEqual
  · have fullRuleMember : carrier ∈ normalDVLoadedPhaseRules :=
      List.mem_of_mem_drop ruleMember
    simp only [normalDVLoadedPhaseRules, List.mem_cons,
      List.not_mem_nil, or_false] at fullRuleMember
    rcases fullRuleMember with h | h | h | h | h | h | h | h
    all_goals subst carrier
    all_goals
      change cmatchAtom beforeFactor
        (.expression (.symbol patternHead :: patternTail))
        (.expression (.symbol "exec" :: _)) = none
      exact cmatchAtom_expression_symbol_head_ne beforeFactor patternHead
        "exec" patternTail _ notExec
  · subst carrier
    change cmatchAtom beforeFactor
      (.expression (.symbol patternHead :: patternTail))
      (.expression (.symbol "mm-dv-next-pair" :: _)) = none
    exact cmatchAtom_expression_symbol_head_ne beforeFactor patternHead
      "mm-dv-next-pair" patternTail _ notCursor

theorem normalDVLoadedComplete_leftConst_no_matches
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    cmatchInputSpec []
        (normalDVLeftConstDirective.atom ::
          (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
            assertionLabel pairEnd 1 sourceBody context).erase
              normalDVLeftConstDirective.atom)
        normalDVLeftConstDirective.rule.input = [] := by
  have readSpaceExact :
      normalDVLeftConstDirective.atom ::
          (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
            assertionLabel pairEnd 1 sourceBody context).erase
              normalDVLeftConstDirective.atom =
        normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd 1 sourceBody context := by
    rfl
  rw [readSpaceExact]
  change cmatchInputSpec [] _
    (.compat (mkPattern normalDVLeftConstPatternAtoms)) = []
  apply cmatchInputSpec_compat_eq_nil_of_factor_never_matches
    (before := []) (factor := normalDVLeftConstPatternAtoms[0])
    (after := normalDVLeftConstPatternAtoms.drop 1)
  intro beforeFactor carrier carrierMember
  change cmatchAtom beforeFactor
    (.expression (.symbol "mm-dv-scan-left" :: _)) carrier = none
  exact normalDVLoadedCompleteStageAt_head_never_matches scopeOwner
    proofOwner proofAddress assertionLabel pairEnd 1 sourceBody context
    beforeFactor carrier carrierMember (by decide) (by decide)

theorem normalDVLoadedComplete_leftVariable_no_matches
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    cmatchInputSpec []
        (normalDVLeftVariableDirective.atom ::
          (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
            assertionLabel pairEnd 2 sourceBody context).erase
              normalDVLeftVariableDirective.atom)
        normalDVLeftVariableDirective.rule.input = [] := by
  have readSpaceExact :
      normalDVLeftVariableDirective.atom ::
          (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
            assertionLabel pairEnd 2 sourceBody context).erase
              normalDVLeftVariableDirective.atom =
        normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd 2 sourceBody context := by
    rfl
  rw [readSpaceExact]
  change cmatchInputSpec [] _
    (.compat (mkPattern normalDVLeftVariablePatternAtoms)) = []
  apply cmatchInputSpec_compat_eq_nil_of_factor_never_matches
    (before := []) (factor := normalDVLeftVariablePatternAtoms[0])
    (after := normalDVLeftVariablePatternAtoms.drop 1)
  intro beforeFactor carrier carrierMember
  change cmatchAtom beforeFactor
    (.expression (.symbol "mm-dv-scan-left" :: _)) carrier = none
  exact normalDVLoadedCompleteStageAt_head_never_matches scopeOwner
    proofOwner proofAddress assertionLabel pairEnd 2 sourceBody context
    beforeFactor carrier carrierMember (by decide) (by decide)

theorem normalDVLoadedComplete_rightConst_no_matches
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    cmatchInputSpec []
        (normalDVRightConstDirective.atom ::
          (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
            assertionLabel pairEnd 3 sourceBody context).erase
              normalDVRightConstDirective.atom)
        normalDVRightConstDirective.rule.input = [] := by
  have readSpaceExact :
      normalDVRightConstDirective.atom ::
          (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
            assertionLabel pairEnd 3 sourceBody context).erase
              normalDVRightConstDirective.atom =
        normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd 3 sourceBody context := by
    rfl
  rw [readSpaceExact]
  change cmatchInputSpec [] _
    (.compat (mkPattern normalDVRightConstPatternAtoms)) = []
  apply cmatchInputSpec_compat_eq_nil_of_factor_never_matches
    (before := []) (factor := normalDVRightConstPatternAtoms[0])
    (after := normalDVRightConstPatternAtoms.drop 1)
  intro beforeFactor carrier carrierMember
  change cmatchAtom beforeFactor
    (.expression (.symbol "mm-dv-scan-right" :: _)) carrier = none
  exact normalDVLoadedCompleteStageAt_head_never_matches scopeOwner
    proofOwner proofAddress assertionLabel pairEnd 3 sourceBody context
    beforeFactor carrier carrierMember (by decide) (by decide)

theorem normalDVLoadedComplete_rightVariable_no_matches
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    cmatchInputSpec []
        (normalDVRightVariableDirective.atom ::
          (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
            assertionLabel pairEnd 4 sourceBody context).erase
              normalDVRightVariableDirective.atom)
        normalDVRightVariableDirective.rule.input = [] := by
  have readSpaceExact :
      normalDVRightVariableDirective.atom ::
          (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
            assertionLabel pairEnd 4 sourceBody context).erase
              normalDVRightVariableDirective.atom =
        normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd 4 sourceBody context := by
    rfl
  rw [readSpaceExact]
  change cmatchInputSpec [] _
    (.compat (mkPattern normalDVRightVariablePatternAtoms)) = []
  apply cmatchInputSpec_compat_eq_nil_of_factor_never_matches
    (before := []) (factor := normalDVRightVariablePatternAtoms[0])
    (after := normalDVRightVariablePatternAtoms.drop 1)
  intro beforeFactor carrier carrierMember
  change cmatchAtom beforeFactor
    (.expression (.symbol "mm-dv-scan-right" :: _)) carrier = none
  exact normalDVLoadedCompleteStageAt_head_never_matches scopeOwner
    proofOwner proofAddress assertionLabel pairEnd 4 sourceBody context
    beforeFactor carrier carrierMember (by decide) (by decide)

theorem normalDVLoadedComplete_rightNil_no_matches
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    cmatchInputSpec []
        (normalDVRightNilDirective.atom ::
          (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
            assertionLabel pairEnd 5 sourceBody context).erase
              normalDVRightNilDirective.atom)
        normalDVRightNilDirective.rule.input = [] := by
  have readSpaceExact :
      normalDVRightNilDirective.atom ::
          (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
            assertionLabel pairEnd 5 sourceBody context).erase
              normalDVRightNilDirective.atom =
        normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd 5 sourceBody context := by
    rfl
  rw [readSpaceExact]
  change cmatchInputSpec [] _
    (.compat (mkPattern normalDVRightNilPatternAtoms)) = []
  apply cmatchInputSpec_compat_eq_nil_of_factor_never_matches
    (before := []) (factor := normalDVRightNilPatternAtoms[0])
    (after := normalDVRightNilPatternAtoms.drop 1)
  intro beforeFactor carrier carrierMember
  change cmatchAtom beforeFactor
    (.expression (.symbol "mm-dv-scan-right" :: _)) carrier = none
  exact normalDVLoadedCompleteStageAt_head_never_matches scopeOwner
    proofOwner proofAddress assertionLabel pairEnd 5 sourceBody context
    beforeFactor carrier carrierMember (by decide) (by decide)

theorem normalDVLoadedComplete_leftNil_no_matches
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    cmatchInputSpec []
        (normalDVLeftNilDirective.atom ::
          (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
            assertionLabel pairEnd 6 sourceBody context).erase
              normalDVLeftNilDirective.atom)
        normalDVLeftNilDirective.rule.input = [] := by
  have readSpaceExact :
      normalDVLeftNilDirective.atom ::
          (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
            assertionLabel pairEnd 6 sourceBody context).erase
              normalDVLeftNilDirective.atom =
        normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd 6 sourceBody context := by
    rfl
  rw [readSpaceExact]
  change cmatchInputSpec [] _
    (.compat (mkPattern normalDVLeftNilPatternAtoms)) = []
  apply cmatchInputSpec_compat_eq_nil_of_factor_never_matches
    (before := []) (factor := normalDVLeftNilPatternAtoms[0])
    (after := normalDVLeftNilPatternAtoms.drop 1)
  intro beforeFactor carrier carrierMember
  change cmatchAtom beforeFactor
    (.expression (.symbol "mm-dv-scan-left" :: _)) carrier = none
  exact normalDVLoadedCompleteStageAt_head_never_matches scopeOwner
    proofOwner proofAddress assertionLabel pairEnd 6 sourceBody context
    beforeFactor carrier carrierMember (by decide) (by decide)

/-! ## Exact administrative stuttering -/

theorem normalDVLoadedComplete_pairBegin_fires_stage_one
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    cFireReflectiveSourceExecFact
        (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd 0 sourceBody context)
        normalDVPairBeginDirective =
      normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
        assertionLabel pairEnd 1 sourceBody context := by
  rw [cFireReflectiveSourceExecFact_eq_erase_of_no_matches]
  · rfl
  · simpa [normalDVLoadedCompleteStageAt_zero] using
      normalDVLoadedComplete_pairBegin_no_matches scopeOwner proofOwner
        proofAddress assertionLabel pairEnd sourceBody context

theorem normalDVLoadedComplete_leftConst_fires_stage_two
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    cFireReflectiveSourceExecFact
        (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd 1 sourceBody context)
        normalDVLeftConstDirective =
      normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
        assertionLabel pairEnd 2 sourceBody context := by
  rw [cFireReflectiveSourceExecFact_eq_erase_of_no_matches]
  · rfl
  · exact normalDVLoadedComplete_leftConst_no_matches scopeOwner proofOwner
      proofAddress assertionLabel pairEnd sourceBody context

theorem normalDVLoadedComplete_leftVariable_fires_stage_three
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    cFireReflectiveSourceExecFact
        (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd 2 sourceBody context)
        normalDVLeftVariableDirective =
      normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
        assertionLabel pairEnd 3 sourceBody context := by
  rw [cFireReflectiveSourceExecFact_eq_erase_of_no_matches]
  · rfl
  · exact normalDVLoadedComplete_leftVariable_no_matches scopeOwner proofOwner
      proofAddress assertionLabel pairEnd sourceBody context

theorem normalDVLoadedComplete_rightConst_fires_stage_four
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    cFireReflectiveSourceExecFact
        (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd 3 sourceBody context)
        normalDVRightConstDirective =
      normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
        assertionLabel pairEnd 4 sourceBody context := by
  rw [cFireReflectiveSourceExecFact_eq_erase_of_no_matches]
  · rfl
  · exact normalDVLoadedComplete_rightConst_no_matches scopeOwner proofOwner
      proofAddress assertionLabel pairEnd sourceBody context

theorem normalDVLoadedComplete_rightVariable_fires_stage_five
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    cFireReflectiveSourceExecFact
        (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd 4 sourceBody context)
        normalDVRightVariableDirective =
      normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
        assertionLabel pairEnd 5 sourceBody context := by
  rw [cFireReflectiveSourceExecFact_eq_erase_of_no_matches]
  · rfl
  · exact normalDVLoadedComplete_rightVariable_no_matches scopeOwner proofOwner
      proofAddress assertionLabel pairEnd sourceBody context

theorem normalDVLoadedComplete_rightNil_fires_stage_six
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    cFireReflectiveSourceExecFact
        (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd 5 sourceBody context)
        normalDVRightNilDirective =
      normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
        assertionLabel pairEnd 6 sourceBody context := by
  rw [cFireReflectiveSourceExecFact_eq_erase_of_no_matches]
  · rfl
  · exact normalDVLoadedComplete_rightNil_no_matches scopeOwner proofOwner
      proofAddress assertionLabel pairEnd sourceBody context

theorem normalDVLoadedComplete_leftNil_fires_stage_seven
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    cFireReflectiveSourceExecFact
        (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd 6 sourceBody context)
        normalDVLeftNilDirective =
      normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
        assertionLabel pairEnd 7 sourceBody context := by
  rw [cFireReflectiveSourceExecFact_eq_erase_of_no_matches]
  · rfl
  · exact normalDVLoadedComplete_leftNil_no_matches scopeOwner proofOwner
      proofAddress assertionLabel pairEnd sourceBody context

/-! ## Shared work-queue execution -/

theorem normalDVLoadedComplete_step_zero
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    cReflectiveSourceWorkQueueStep .leaveInert
        (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd 0 sourceBody context) =
      some (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
        assertionLabel pairEnd 1 sourceBody context) := by
  change some (cFireReflectiveSourceExecFact _ normalDVPairBeginDirective) = _
  rw [normalDVLoadedComplete_pairBegin_fires_stage_one]

theorem normalDVLoadedComplete_step_one
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    cReflectiveSourceWorkQueueStep .leaveInert
        (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd 1 sourceBody context) =
      some (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
        assertionLabel pairEnd 2 sourceBody context) := by
  change some (cFireReflectiveSourceExecFact _ normalDVLeftConstDirective) = _
  rw [normalDVLoadedComplete_leftConst_fires_stage_two]

theorem normalDVLoadedComplete_step_two
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    cReflectiveSourceWorkQueueStep .leaveInert
        (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd 2 sourceBody context) =
      some (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
        assertionLabel pairEnd 3 sourceBody context) := by
  change some (cFireReflectiveSourceExecFact _ normalDVLeftVariableDirective) = _
  rw [normalDVLoadedComplete_leftVariable_fires_stage_three]

theorem normalDVLoadedComplete_step_three
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    cReflectiveSourceWorkQueueStep .leaveInert
        (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd 3 sourceBody context) =
      some (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
        assertionLabel pairEnd 4 sourceBody context) := by
  change some (cFireReflectiveSourceExecFact _ normalDVRightConstDirective) = _
  rw [normalDVLoadedComplete_rightConst_fires_stage_four]

theorem normalDVLoadedComplete_step_four
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    cReflectiveSourceWorkQueueStep .leaveInert
        (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd 4 sourceBody context) =
      some (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
        assertionLabel pairEnd 5 sourceBody context) := by
  change some (cFireReflectiveSourceExecFact _ normalDVRightVariableDirective) = _
  rw [normalDVLoadedComplete_rightVariable_fires_stage_five]

theorem normalDVLoadedComplete_step_five
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    cReflectiveSourceWorkQueueStep .leaveInert
        (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd 5 sourceBody context) =
      some (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
        assertionLabel pairEnd 6 sourceBody context) := by
  change some (cFireReflectiveSourceExecFact _ normalDVRightNilDirective) = _
  rw [normalDVLoadedComplete_rightNil_fires_stage_six]

theorem normalDVLoadedComplete_step_six
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    cReflectiveSourceWorkQueueStep .leaveInert
        (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd 6 sourceBody context) =
      some (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
        assertionLabel pairEnd 7 sourceBody context) := by
  change some (cFireReflectiveSourceExecFact _ normalDVLeftNilDirective) = _
  rw [normalDVLoadedComplete_leftNil_fires_stage_seven]

theorem normalDVLoadedComplete_step_seven
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    cReflectiveSourceWorkQueueStep .leaveInert
        (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd 7 sourceBody context) =
      some
        (cFireReflectiveSourceExecFact
          (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
            assertionLabel pairEnd 7 sourceBody context)
          normalDVCompleteDirective) := by
  rfl

/-- A terminal DV cursor in the fully loaded machine takes seven observable
inert scheduler steps followed by the completing transition. -/
theorem normalDVLoadedComplete_reachable
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    CReflectiveReachable .leaveInert 8
        (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd 0 sourceBody context)
        (cFireReflectiveSourceExecFact
          (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
            assertionLabel pairEnd 7 sourceBody context)
          normalDVCompleteDirective) := by
  exact .step
    (normalDVLoadedComplete_step_zero scopeOwner proofOwner proofAddress
      assertionLabel pairEnd sourceBody context)
    (.step
      (normalDVLoadedComplete_step_one scopeOwner proofOwner proofAddress
        assertionLabel pairEnd sourceBody context)
      (.step
        (normalDVLoadedComplete_step_two scopeOwner proofOwner proofAddress
          assertionLabel pairEnd sourceBody context)
        (.step
          (normalDVLoadedComplete_step_three scopeOwner proofOwner proofAddress
            assertionLabel pairEnd sourceBody context)
          (.step
            (normalDVLoadedComplete_step_four scopeOwner proofOwner proofAddress
              assertionLabel pairEnd sourceBody context)
            (.step
              (normalDVLoadedComplete_step_five scopeOwner proofOwner
                proofAddress assertionLabel pairEnd sourceBody context)
              (.step
                (normalDVLoadedComplete_step_six scopeOwner proofOwner
                  proofAddress assertionLabel pairEnd sourceBody context)
                (.step
                  (normalDVLoadedComplete_step_seven scopeOwner proofOwner
                    proofAddress assertionLabel pairEnd sourceBody context)
                  .refl)))))))

/-- Proof-relevant form of the same eight-step terminal DV execution.  Unlike
proposition-valued reachability, this trace retains every intermediate list
state so OSLF can classify every primitive transition by its generated native
target type. -/
def normalDVLoadedComplete_trace
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    CReflectiveTrace .leaveInert 8
        (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd 0 sourceBody context)
        (cFireReflectiveSourceExecFact
          (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
            assertionLabel pairEnd 7 sourceBody context)
          normalDVCompleteDirective) :=
  .step
    (normalDVLoadedComplete_step_zero scopeOwner proofOwner proofAddress
      assertionLabel pairEnd sourceBody context)
    (.step
      (normalDVLoadedComplete_step_one scopeOwner proofOwner proofAddress
        assertionLabel pairEnd sourceBody context)
      (.step
        (normalDVLoadedComplete_step_two scopeOwner proofOwner proofAddress
          assertionLabel pairEnd sourceBody context)
        (.step
          (normalDVLoadedComplete_step_three scopeOwner proofOwner proofAddress
            assertionLabel pairEnd sourceBody context)
          (.step
            (normalDVLoadedComplete_step_four scopeOwner proofOwner proofAddress
              assertionLabel pairEnd sourceBody context)
            (.step
              (normalDVLoadedComplete_step_five scopeOwner proofOwner
                proofAddress assertionLabel pairEnd sourceBody context)
              (.step
                (normalDVLoadedComplete_step_six scopeOwner proofOwner
                  proofAddress assertionLabel pairEnd sourceBody context)
                (.step
                  (normalDVLoadedComplete_step_seven scopeOwner proofOwner
                    proofAddress assertionLabel pairEnd sourceBody context)
                  .refl)))))))

/-- The executable terminal DV path is passed through OSLF step by step and
therefore inhabits the native target type generated for every successor. -/
def normalDVLoadedComplete_nativeTypeTrace
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    ReflectiveNativeTypeTrace .leaveInert 8
        (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd 0 sourceBody context)
        (cFireReflectiveSourceExecFact
          (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
            assertionLabel pairEnd 7 sourceBody context)
          normalDVCompleteDirective) :=
  (normalDVLoadedComplete_trace scopeOwner proofOwner proofAddress
    assertionLabel pairEnd sourceBody context).toNativeTypeTrace

theorem normalDVLoadedComplete_multistep
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    (reflectiveNativeListExecGSLT .leaveInert).MultiStep
        (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd 0 sourceBody context)
        (cFireReflectiveSourceExecFact
          (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
            assertionLabel pairEnd 7 sourceBody context)
          normalDVCompleteDirective) :=
  (normalDVLoadedComplete_reachable scopeOwner proofOwner proofAddress
    assertionLabel pairEnd sourceBody context).toMultiStep

/-- The final list-valued firing agrees with the support-valued authored
semantics and therefore contains the addressed body-construction row. -/
theorem normalDVLoadedComplete_final_contains_body_build
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    normalBodyBuildRowAt proofOwner proofAddress sourceBody [] context ∈
      cFireReflectiveSourceExecFact
        (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd 7 sourceBody context)
        normalDVCompleteDirective := by
  let stage := normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
    assertionLabel pairEnd 7 sourceBody context
  have stageNodup : stage.Nodup := by
    simp [stage, normalDVLoadedCompleteStageAt, normalDVLoadedPhaseRules,
      normalDVCompleteRule, normalDVNextPairRowAt]
  have supportedTemplate :
      ReflectiveSupportSetTemplate normalDVCompleteDirective.rule.tmpl := by
    apply (all_reflectiveSupportSetSinkB_eq_true_iff _).mp
    rfl
  have firingAgreement :
      ReflectiveSourceFiringAgreement stage normalDVCompleteDirective :=
    reflectiveSourceFiringAgreement_of_supportAlignment stage
      normalDVCompleteDirective stageNodup supportedTemplate
      (reflectiveSourceRowSupportAlignment_of_nodup stage
        normalDVCompleteDirective stageNodup)
  have phaseExact :
      stage.toFinset =
        normalDVCompletePhaseSpaceAt scopeOwner proofOwner proofAddress
          assertionLabel pairEnd sourceBody context := by
    rfl
  have supportMember :
      normalBodyBuildRowAt proofOwner proofAddress sourceBody [] context ∈
        (cFireReflectiveSourceExecFact stage
          normalDVCompleteDirective).toFinset := by
    rw [firingAgreement, phaseExact]
    exact normalDVCompleteDirectiveAt_fires_body_build scopeOwner proofOwner
      proofAddress assertionLabel pairEnd sourceBody context
  exact List.mem_toFinset.mp supportMember

/-- Complete terminal boundary: the actual shared work queue performs eight
steps in its executable GSLT and exposes the exact addressed successor row. -/
theorem normalDVLoadedComplete_boundary
    (scopeOwner proofOwner proofAddress : Atom)
    (assertionLabel : String) (pairEnd : Nat)
    (sourceBody : List Metamath.Verify.Sym) (context : Atom) :
    let source := normalDVLoadedCompleteStageAt scopeOwner proofOwner
      proofAddress assertionLabel pairEnd 0 sourceBody context
    let target := cFireReflectiveSourceExecFact
      (normalDVLoadedCompleteStageAt scopeOwner proofOwner proofAddress
        assertionLabel pairEnd 7 sourceBody context)
      normalDVCompleteDirective
    (reflectiveNativeListExecGSLT .leaveInert).MultiStep source target ∧
      Nonempty (ReflectiveNativeTypeTrace .leaveInert 8 source target) ∧
      normalBodyBuildRowAt proofOwner proofAddress sourceBody [] context ∈
        target := by
  dsimp only
  exact ⟨normalDVLoadedComplete_multistep scopeOwner proofOwner proofAddress
      assertionLabel pairEnd sourceBody context,
    ⟨normalDVLoadedComplete_nativeTypeTrace scopeOwner proofOwner proofAddress
      assertionLabel pairEnd sourceBody context⟩,
    normalDVLoadedComplete_final_contains_body_build scopeOwner proofOwner
      proofAddress assertionLabel pairEnd sourceBody context⟩

section AxiomAudit

#print axioms normalDVLoadedComplete_supported_exact
#print axioms normalDVLoadedComplete_pairBegin_no_matches
#print axioms normalDVLoadedCompleteStageAt_zero
#print axioms normalDVLoadedComplete_leftConst_no_matches
#print axioms normalDVLoadedComplete_leftVariable_no_matches
#print axioms normalDVLoadedComplete_rightConst_no_matches
#print axioms normalDVLoadedComplete_rightVariable_no_matches
#print axioms normalDVLoadedComplete_rightNil_no_matches
#print axioms normalDVLoadedComplete_leftNil_no_matches
#print axioms normalDVLoadedComplete_reachable
#print axioms normalDVLoadedComplete_nativeTypeTrace
#print axioms normalDVLoadedComplete_multistep
#print axioms normalDVLoadedComplete_final_contains_body_build
#print axioms normalDVLoadedComplete_boundary

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2NormalDVContinuous
