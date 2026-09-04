import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCOneStepSimulation
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSkipHeadSimulation
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSkipAritySimulation
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCBeginDeclarationSimulation
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCArgumentsFinishedSimulation
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCRawInputSimulation
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCUndefinedInputSimulation
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCHoleInputSimulation
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedInputSimulation
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCOpenInputSimulation
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCLiteralResultSimulation
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCCheckedResultSimulation
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCOpenResultSimulation

/-!
# Total cold-call-guard realization by generated StructuredC

The family modules prove the fifteen semantic cases separately.  This module
closes their sum: every source compiler step is executed by the one generated
StructuredC function, its retained target path is nonempty and bounded, and
the terminal state observation is exactly the source successor.

The target path ends at one function-return configuration.  Re-entry for the
next cold step is intentionally a driver operation, so the packaged object is
an invocation realization rather than a direct `OperationalRealization` whose
term map would incorrectly identify a returned configuration with a fresh
function invocation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCTotalRealization

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.TotalGSLT
open Mettapedia.GSLT.LanguageDef.StructuredC
open Mettapedia.GSLT.LanguageDef.NormalizationPath
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCFinishSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCOneStepSimulation
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCInputPrefixSimulation
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCResultPrefixSimulation

/-- Execute exactly one invocation of the generated cold StructuredC
function, retaining the actual target rewrite path. -/
abbrev generatedRun (source : CompileLanguageControl) :
    NormalizationPath.Run coldRelations StructuredC.language coldLaws 1 64
      (runControl source) :=
  normalizeFirstRunUsing coldRelations StructuredC.language coldLaws 1 64
    (runControl source)

/-- Every source edge is observed exactly after executing the generated
StructuredC invocation.  The proof dispatches on source semantics, not on a
target-family tag. -/
theorem generatedRun_observes_source_step
    {source target : CompileLanguageControl}
    (step : compileLanguageGSLT.Step source target) :
    terminalControl? (generatedRun source).endpoint = some target := by
  change compileLanguageStep? source = some target at step
  cases source with
  | halted result =>
      simp [compileLanguageStep?] at step
  | running owner revision head arity remaining accepted =>
      cases remaining with
      | nil =>
          simp [compileLanguageStep?] at step
          subst target
          simpa [generatedRun,
            MainlineCallGuardCompileStructuredCOneStepSimulation.finishRun,
            MainlineCallGuardCompileStructuredCOneStepSimulation.finishSource,
            MainlineCallGuardCompileStructuredCOneStepSimulation.finishTarget] using
            MainlineCallGuardCompileStructuredCOneStepSimulation.finish_run_observation_exact owner revision head arity
              accepted
      | cons declaration remaining =>
          by_cases relevant : Relevant declaration head arity
          · simp [compileLanguageStep?, relevant] at step
            subst target
            rcases relevant with ⟨sameHead, sameArity⟩
            subst head
            subst arity
            simpa [generatedRun,
              MainlineCallGuardCompileStructuredCBeginDeclarationSimulation.run,
              MainlineCallGuardCompileStructuredCBeginDeclarationSimulation.beginSource,
              MainlineCallGuardCompileStructuredCBeginDeclarationSimulation.beginTarget,
              MainlineCallGuardCompileStructuredCSkipAritySimulation.skipAritySource, MainlineCallGuardCompileStructuredCSkipHeadSimulation.skipHeadSource] using
              MainlineCallGuardCompileStructuredCBeginDeclarationSimulation.run_observation_exact owner revision declaration remaining
                accepted
          · simp [compileLanguageStep?, relevant] at step
            subst target
            by_cases sameHead : declaration.function = head
            · have differentArity : declaration.inputTypes.length ≠ arity := by
                intro sameArity
                exact relevant ⟨sameHead, sameArity⟩
              subst head
              simpa [generatedRun,
                MainlineCallGuardCompileStructuredCSkipAritySimulation.run,
                MainlineCallGuardCompileStructuredCSkipAritySimulation.skipAritySource,
                MainlineCallGuardCompileStructuredCSkipAritySimulation.skipArityTarget, MainlineCallGuardCompileStructuredCSkipHeadSimulation.skipHeadSource,
                MainlineCallGuardCompileStructuredCSkipHeadSimulation.skipHeadTarget] using
                MainlineCallGuardCompileStructuredCSkipAritySimulation.run_observation_exact owner revision arity declaration
                  remaining accepted differentArity
            · simpa [generatedRun,
                MainlineCallGuardCompileStructuredCSkipHeadSimulation.run,
                MainlineCallGuardCompileStructuredCSkipHeadSimulation.skipHeadSource,
                MainlineCallGuardCompileStructuredCSkipHeadSimulation.skipHeadTarget] using
                MainlineCallGuardCompileStructuredCSkipHeadSimulation.run_observation_exact owner revision head arity
                  declaration remaining accepted sameHead
  | arguments owner revision head arity declaration remaining inputCursor
      modes accepted =>
      cases inputCursor with
      | nil =>
          simp [compileLanguageStep?] at step
          subst target
          simpa [generatedRun,
            MainlineCallGuardCompileStructuredCArgumentsFinishedSimulation.run,
            MainlineCallGuardCompileStructuredCArgumentsFinishedSimulation.source,
            MainlineCallGuardCompileStructuredCArgumentsFinishedSimulation.target] using
            MainlineCallGuardCompileStructuredCArgumentsFinishedSimulation.run_observation_exact owner revision head arity
              declaration remaining modes accepted
      | cons expected inputCursor =>
          cases compiled : compileArgMode expected with
          | none =>
              simp [compileLanguageStep?, compiled] at step
              subst target
              simpa [generatedRun,
                MainlineCallGuardCompileStructuredCOpenInputSimulation.execution,
                MainlineCallGuardCompileStructuredCOpenInputSimulation.source,
                MainlineCallGuardCompileStructuredCOpenInputSimulation.Checked.source,
                MainlineCallGuardCompileStructuredCCheckedInputSimulation.source,
                MainlineCallGuardCompileStructuredCCheckedInputSimulation.inputData,
                MainlineCallGuardCompileStructuredCOpenInputSimulation.inputData,
                MainlineCallGuardCompileStructuredCOpenInputSimulation.target, InputStateData.source] using
                MainlineCallGuardCompileStructuredCOpenInputSimulation.execution_observation_exact expected owner revision
                  head arity declaration remaining inputCursor modes accepted
                  compiled
          | some mode =>
              simp [compileLanguageStep?, compiled] at step
              subst target
              by_cases atom : expected = atomType
              · subst expected
                have modeExact : mode = .rawAtom := by
                  simpa [compileArgMode, atomType] using
                    compiled.symm
                subst mode
                simpa [generatedRun,
                  MainlineCallGuardCompileStructuredCRawInputSimulation.run,
                  MainlineCallGuardCompileStructuredCRawInputSimulation.source,
                  MainlineCallGuardCompileStructuredCRawInputSimulation.inputData,
                  MainlineCallGuardCompileStructuredCRawInputSimulation.target, InputStateData.source] using
                  MainlineCallGuardCompileStructuredCRawInputSimulation.run_observation_exact owner revision head arity
                    declaration remaining inputCursor modes accepted
              · by_cases undefined : expected = undefinedType
                · subst expected
                  have modeExact : mode = .evalUnchecked := by
                    simpa [compileArgMode, undefinedType, atomType] using
                      compiled.symm
                  subst mode
                  simpa [generatedRun,
                    MainlineCallGuardCompileStructuredCUndefinedInputSimulation.run,
                    MainlineCallGuardCompileStructuredCLiteralInputSuffixSimulation.source,
                    MainlineCallGuardCompileStructuredCLiteralInputSuffixSimulation.inputData, MainlineCallGuardCompileStructuredCLiteralInputSuffixSimulation.target,
                    MainlineCallGuardCompileStructuredCLiteralInputSuffixSimulation.literalMode, LiteralPredicate.term,
                    InputStateData.source] using
                    MainlineCallGuardCompileStructuredCUndefinedInputSimulation.run_observation_exact owner revision head
                      arity declaration remaining inputCursor modes accepted
                · by_cases hole : expected = holeType
                  · subst expected
                    have modeExact : mode = .evalUnchecked := by
                      simpa [compileArgMode, holeType, undefinedType, atomType]
                        using compiled.symm
                    subst mode
                    simpa [generatedRun,
                      MainlineCallGuardCompileStructuredCHoleInputSimulation.run,
                      MainlineCallGuardCompileStructuredCLiteralInputSuffixSimulation.source,
                      MainlineCallGuardCompileStructuredCLiteralInputSuffixSimulation.inputData, MainlineCallGuardCompileStructuredCLiteralInputSuffixSimulation.target,
                      MainlineCallGuardCompileStructuredCLiteralInputSuffixSimulation.literalMode, LiteralPredicate.term,
                      InputStateData.source] using
                      MainlineCallGuardCompileStructuredCHoleInputSimulation.run_observation_exact owner revision head arity
                        declaration remaining inputCursor modes accepted
                  · cases closed : termIsClosed expected
                    · simp [compileArgMode, atom, undefined, hole, closed] at compiled
                    · have modeExact : mode = .evalSoftcutType expected := by
                        simpa [compileArgMode, atom, undefined, hole, closed]
                          using compiled.symm
                      subst mode
                      simpa [generatedRun,
                        MainlineCallGuardCompileStructuredCCheckedInputSimulation.run,
                        MainlineCallGuardCompileStructuredCCheckedInputSimulation.source,
                        MainlineCallGuardCompileStructuredCCheckedInputSimulation.inputData, MainlineCallGuardCompileStructuredCCheckedInputSimulation.target,
                        InputStateData.source] using
                        MainlineCallGuardCompileStructuredCCheckedInputSimulation.run_observation_exact expected owner
                          revision head arity declaration remaining inputCursor
                          modes accepted compiled
  | result owner revision head arity declaration remaining modes accepted =>
      cases declaration with
      | mk occurrence declarationHead inputs output =>
          cases compiled : compileResultMode output with
          | none =>
              simp [compileLanguageStep?, compiled] at step
              subst target
              let data : ResultStateData := {
                owner, revision, head, arity
                declaration := ⟨occurrence, declarationHead, inputs, output⟩
                remaining, modes, accepted }
              simpa [generatedRun,
                MainlineCallGuardCompileStructuredCOpenResultSimulation.execution,
                MainlineCallGuardCompileStructuredCOpenResultSimulation.source,
                MainlineCallGuardCompileStructuredCOpenResultSimulation.target, data,
                ResultStateData.source] using
                MainlineCallGuardCompileStructuredCOpenResultSimulation.execution_observation_exact data compiled
          | some mode =>
              simp [compileLanguageStep?, compiled] at step
              subst target
              by_cases undefined : output = undefinedType
              · subst output
                have modeExact : mode = .resultUnchecked := by
                  simpa [compileResultMode, undefinedType] using
                    compiled.symm
                subst mode
                simpa [generatedRun,
                  MainlineCallGuardCompileStructuredCLiteralResultSimulation.execution,
                  MainlineCallGuardCompileStructuredCLiteralResultSimulation.source,
                  MainlineCallGuardCompileStructuredCLiteralResultSimulation.data, MainlineCallGuardCompileStructuredCLiteralResultSimulation.declaration,
                  MainlineCallGuardCompileStructuredCLiteralResultSimulation.target, MainlineCallGuardCompileStructuredCLiteralResultSimulation.plan,
                  LiteralPredicate.term, ResultStateData.source] using
                  MainlineCallGuardCompileStructuredCLiteralResultSimulation.execution_observation_exact .undefined owner
                    revision head arity occurrence declarationHead inputs
                    remaining modes accepted
              · by_cases hole : output = holeType
                · subst output
                  have modeExact : mode = .resultUnchecked := by
                    simpa [compileResultMode, holeType, undefinedType] using
                      compiled.symm
                  subst mode
                  simpa [generatedRun,
                    MainlineCallGuardCompileStructuredCLiteralResultSimulation.execution,
                    MainlineCallGuardCompileStructuredCLiteralResultSimulation.source,
                    MainlineCallGuardCompileStructuredCLiteralResultSimulation.data, MainlineCallGuardCompileStructuredCLiteralResultSimulation.declaration,
                    MainlineCallGuardCompileStructuredCLiteralResultSimulation.target, MainlineCallGuardCompileStructuredCLiteralResultSimulation.plan,
                    LiteralPredicate.term, ResultStateData.source] using
                    MainlineCallGuardCompileStructuredCLiteralResultSimulation.execution_observation_exact .hole owner
                      revision head arity occurrence declarationHead inputs
                      remaining modes accepted
                · by_cases atom : output = atomType
                  · subst output
                    have modeExact : mode = .resultUnchecked := by
                      simpa [compileResultMode, atomType, holeType,
                        undefinedType] using compiled.symm
                    subst mode
                    simpa [generatedRun,
                      MainlineCallGuardCompileStructuredCLiteralResultSimulation.execution,
                      MainlineCallGuardCompileStructuredCLiteralResultSimulation.source,
                      MainlineCallGuardCompileStructuredCLiteralResultSimulation.data, MainlineCallGuardCompileStructuredCLiteralResultSimulation.declaration,
                      MainlineCallGuardCompileStructuredCLiteralResultSimulation.target, MainlineCallGuardCompileStructuredCLiteralResultSimulation.plan,
                      LiteralPredicate.term, ResultStateData.source] using
                      MainlineCallGuardCompileStructuredCLiteralResultSimulation.execution_observation_exact .atom owner
                        revision head arity occurrence declarationHead inputs
                        remaining modes accepted
                  · cases closed : termIsClosed output
                    · simp [compileResultMode, undefined, hole, atom, closed]
                        at compiled
                    · have modeExact :
                          mode = .resultSoftcutType output := by
                        simpa [compileResultMode, undefined, hole, atom, closed]
                          using compiled.symm
                      subst mode
                      let data : ResultStateData := {
                        owner, revision, head, arity
                        declaration :=
                          ⟨occurrence, declarationHead, inputs, output⟩
                        remaining, modes, accepted }
                      simpa [generatedRun,
                        MainlineCallGuardCompileStructuredCCheckedResultSimulation.execution,
                        MainlineCallGuardCompileStructuredCCheckedResultSimulation.source,
                        MainlineCallGuardCompileStructuredCCheckedResultSimulation.target, MainlineCallGuardCompileStructuredCCheckedResultSimulation.plan, data,
                        ResultStateData.source] using
                        MainlineCallGuardCompileStructuredCCheckedResultSimulation.execution_observation_exact data compiled

/-- A complete proof-relevant witness for one generated invocation. -/
structure InvocationRealization
    (source target : CompileLanguageControl) where
  endpoint : Pattern
  path : ExecutionPath coldGSLT (runControl source) endpoint
  observes : terminalControl? endpoint = some target
  nonempty : 0 < path.length
  bounded : path.length ≤ 64

/-- A path from a fresh invocation to an observed return cannot be reflexive:
the invocation configuration itself is not terminal. -/
private theorem path_nonempty_of_terminal_observation
    {source target : CompileLanguageControl} {endpoint : Pattern}
    (path : ExecutionPath coldGSLT (runControl source) endpoint)
    (observed : terminalControl? endpoint = some target) :
    0 < path.length := by
  cases path with
  | refl =>
      simp [runControl, StructuredC.run, StructuredC.a, terminalControl?]
        at observed
  | cons _ _ =>
      simp [Mettapedia.GSLT.Ultrainfinite.Route.length]

/-- Every source compiler step has one bounded, nonempty invocation
realization in the actual generated StructuredC GSLT. -/
def realizeStep {source target : CompileLanguageControl}
    (step : compileLanguageGSLT.Step source target) :
    InvocationRealization source target := by
  let executed := generatedRun source
  have observed : terminalControl? executed.endpoint = some target :=
    generatedRun_observes_source_step step
  refine {
    endpoint := executed.endpoint
    path := executed.path
    observes := observed
    nonempty := path_nonempty_of_terminal_observation executed.path observed
    bounded := executed.length_le }

/-- The deterministic generated invocation can observe no successor other
than the source step's target. -/
theorem normalized_observation_iff_of_step
    {source target : CompileLanguageControl}
    (step : compileLanguageGSLT.Step source target)
    (observed : CompileLanguageControl) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (runControl source)) = some observed ↔ observed = target := by
  let executed := generatedRun source
  have endpointExact : executed.endpoint =
      normalizeFirstUsing coldRelations StructuredC.language 1 64
        (runControl source) := executed.endpoint_eq
  have targetExact : terminalControl? executed.endpoint = some target :=
    generatedRun_observes_source_step step
  rw [← endpointExact, targetExact]
  simp [eq_comm]

theorem wrong_target_rejected
    {source target : CompileLanguageControl}
    (step : compileLanguageGSLT.Step source target)
    (observed : CompileLanguageControl) (wrong : observed ≠ target) :
    terminalControl?
        (normalizeFirstUsing coldRelations StructuredC.language 1 64
          (runControl source)) ≠ some observed := by
  intro invented
  exact wrong ((normalized_observation_iff_of_step step observed).mp invented)

#print axioms generatedRun_observes_source_step
#print axioms realizeStep
#print axioms normalized_observation_iff_of_step
#print axioms wrong_target_rejected

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileStructuredCTotalRealization
