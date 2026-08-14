import Mettapedia.GSLT.LanguageDef.InferenceCompiledPlanLowering
import Mettapedia.Languages.Metamath.NativeSourceCalculus

/-!
# Compiled-plan admission for the native Metamath source slice

The admitted native source presentation is recognized by the generic
finite-Horn lowering without adding a Metamath case to the compiler.  The
result contains one compiled rule for every admitted source rule.  Packet
soundness is inherited from the generic translation-validation theorem.
-/

namespace Mettapedia.Languages.Metamath.NativeSourceCompiledPlan

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CompiledPlanWireFormat
open Mettapedia.GSLT.LanguageDef.CompiledPlanAdmission
open Mettapedia.GSLT.LanguageDef.CompiledPlanLowering
open Mettapedia.GSLT.LanguageDef.InferenceCompiledPlanLowering
open NativeSourceCalculus

private theorem mapM_some_length {alpha beta : Type}
    (f : alpha -> Option beta) {xs : List alpha} {ys : List beta}
    (success : xs.mapM f = some ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil =>
      simp at success
      subst ys
      rfl
  | cons x xs ih =>
      simp only [List.mapM_cons] at success
      cases value : f x with
      | none => simp [value] at success
      | some y =>
          cases tailResult : xs.mapM f with
          | none => simp [value, tailResult] at success
          | some tail =>
              simp [value, tailResult] at success
              subst ys
              simp [ih tailResult]

/-- The real admitted source slice lies in the locally recognized finite-Horn
fragment.  This proof reduces the authored presentation itself; it does not
replace it with a separately written compiler fixture. -/
theorem validatedPresentation_lowers :
    (lowerValidatedPresentation? validatedPresentation).isSome = true := by
  rw [lowerValidatedPresentation?_isSome]
  change generatedDefinition.rules.all admittedRuleSupported = true
  set_option maxRecDepth 100000 in
    simp [targetHypotheses, rFloat, sFloat, tFloat,
      theoremRSEssential, theoremSTEssential, hypothesisRule, assertionRules,
      axiomSyllogism, rsEssential, stEssential, rule, admittedRuleSupported,
      applicationPatternSupported, applicationPatternsSupported,
      patternsSupported, patternSupported, physicalName?, stringBytes,
      textEncodable?, bytesNulFree, bytesNonempty, provesPattern,
      identityPattern, formulaPattern, atomPattern, atomListPattern, app,
      substitutionJudgment, contextJudgment, substitutionPattern,
      identityBindingsPattern, bindingPattern, contextPattern,
      substitutionRuleId, contextRuleId, sourceRevision, sourceDigest,
      SourceHypothesis.formula, SourceHypothesis.label,
      String.utf8EncodeChar_eq_utf8EncodeCharFast,
      String.utf8EncodeCharFast,
      show UInt32.size = 4294967296 from rfl]

theorem generatedPresentation_lowers :
    (lowerPresentation? generatedPresentation).isSome = true := by
  unfold lowerPresentation?
  rw [dif_pos generatedPresentation_valid]
  simpa only [validatedPresentation] using validatedPresentation_lowers

/-- Recognition preserves the eight-rule inventory supplied by the admitted
source presentation. -/
theorem generatedPresentation_fragment_witness :
    exists source,
      lowerValidatedPresentation? validatedPresentation = some source /\
        source.length = 8 := by
  rcases Option.isSome_iff_exists.mp validatedPresentation_lowers with
    ⟨source, success⟩
  refine ⟨source, success, ?_⟩
  have preserved := mapM_some_length lowerAdmittedRule?
    (show validatedPresentation.1.rules.mapM lowerAdmittedRule? = some source by
      simpa [lowerValidatedPresentation?] using success)
  have count : validatedPresentation.1.rules.length = 8 := by rfl
  exact preserved.trans count

/-- Any packet emitted for this recognized presentation reconstructs exactly
the meaning assigned by the admitted source lowering. -/
theorem generated_packet_sound {bytes : List UInt8}
    (success : compileBytes? generatedPresentation = some bytes) :
    admitBytes? bytes = admittedMeaning? generatedPresentation :=
  Mettapedia.GSLT.LanguageDef.InferenceCompiledPlanLowering.compileBytes?_sound
    success

end Mettapedia.Languages.Metamath.NativeSourceCompiledPlan
