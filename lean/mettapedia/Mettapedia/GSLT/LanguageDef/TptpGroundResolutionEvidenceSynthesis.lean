import Mettapedia.GSLT.LanguageDef.TptpGroundResolutionProblemAuthority

/-!
# Evidence synthesis for ground TSTP resolution edges

Ordinary TSTP resolution records name their parents and result but need not
record a pivot.  This module reconstructs only the missing *local* evidence:
it enumerates complementary literals in the two supplied ground clauses and
compiles the first exact ordered resolvent into a typed derivation of the
authored calculus.  `articleOfDerivation` then produces the versioned article
consumed by the generic whole-problem checker.

The synthesizer does not search for new clauses, does not traverse the global
proof graph, and does not contain a second acceptance test.  Its return type
contains the theorem that the generated article is accepted by the supplied
calculus authority; the whole-problem checker still performs the one public
admission pass.
-/

namespace Mettapedia.GSLT.LanguageDef.TptpGroundResolutionEvidenceSynthesis

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionCalculus
open Mettapedia.GSLT.LanguageDef.TptpGroundResolutionProblemAuthority

abbrev Clause := TptpGroundResolutionProblemAuthority.SemanticClause
abbrev Literal := TptpGroundResolutionProblemAuthority.SemanticLiteral

abbrev RemovePositiveDerivation (pivot : Pattern) (source : Clause) :=
  Sigma fun result : Clause =>
    Derivation validated
      (removePositiveJ pivot (encodeClause source) (encodeClause result))

abbrev RemoveNegativeDerivation (pivot : Pattern) (source : Clause) :=
  Sigma fun result : Clause =>
    Derivation validated
      (removeNegativeJ pivot (encodeClause source) (encodeClause result))

def liftRemovePositiveTail? (pivot : Pattern) (literal : Literal)
    (source : Clause) (derived : RemovePositiveDerivation pivot source) :
    Option (RemovePositiveDerivation pivot (literal :: source)) := do
  let ⟨result, child⟩ := derived
  if pivotValid : argumentValidAt 0 pivot = true then
    if headValid : argumentValidAt 0 (encodeLiteral literal) = true then
      if sourceValid : argumentValidAt 0 (encodeClause source) = true then
        if resultValid : argumentValidAt 0 (encodeClause result) = true then
          some ⟨literal :: result, by
            simpa [encodeClause, encodeLiteral] using
              deriveRemovePositiveTail pivot (encodeLiteral literal)
                (encodeClause source) (encodeClause result) pivotValid
                headValid sourceValid resultValid child⟩
        else none
      else none
    else none
  else none

def deriveRemovePositive? (pivot : Pattern) :
    (source : Clause) -> Option (RemovePositiveDerivation pivot source)
  | [] => none
  | literal :: source =>
      match literal with
      | .positive atom =>
          if atomEq : atom = pivot then
            if pivotValid : argumentValidAt 0 pivot = true then
              if restValid : argumentValidAt 0 (encodeClause source) = true then
                some ⟨source, by
                  subst atom
                  simpa [encodeClause, encodeLiteral] using
                    deriveRemovePositiveHead pivot (encodeClause source)
                      pivotValid restValid⟩
              else none
            else none
          else do
            let derived <- deriveRemovePositive? pivot source
            liftRemovePositiveTail? pivot (.positive atom) source derived
      | .negative atom =>
          do
            let derived <- deriveRemovePositive? pivot source
            liftRemovePositiveTail? pivot (.negative atom) source derived
termination_by source => source.length

def liftRemoveNegativeTail? (pivot : Pattern) (literal : Literal)
    (source : Clause) (derived : RemoveNegativeDerivation pivot source) :
    Option (RemoveNegativeDerivation pivot (literal :: source)) := do
  let ⟨result, child⟩ := derived
  if pivotValid : argumentValidAt 0 pivot = true then
    if headValid : argumentValidAt 0 (encodeLiteral literal) = true then
      if sourceValid : argumentValidAt 0 (encodeClause source) = true then
        if resultValid : argumentValidAt 0 (encodeClause result) = true then
          some ⟨literal :: result, by
            simpa [encodeClause, encodeLiteral] using
              deriveRemoveNegativeTail pivot (encodeLiteral literal)
                (encodeClause source) (encodeClause result) pivotValid
                headValid sourceValid resultValid child⟩
        else none
      else none
    else none
  else none

def deriveRemoveNegative? (pivot : Pattern) :
    (source : Clause) -> Option (RemoveNegativeDerivation pivot source)
  | [] => none
  | literal :: source =>
      match literal with
      | .negative atom =>
          if atomEq : atom = pivot then
            if pivotValid : argumentValidAt 0 pivot = true then
              if restValid : argumentValidAt 0 (encodeClause source) = true then
                some ⟨source, by
                  subst atom
                  simpa [encodeClause, encodeLiteral] using
                    deriveRemoveNegativeHead pivot (encodeClause source)
                      pivotValid restValid⟩
              else none
            else none
          else do
            let derived <- deriveRemoveNegative? pivot source
            liftRemoveNegativeTail? pivot (.negative atom) source derived
      | .positive atom =>
          do
            let derived <- deriveRemoveNegative? pivot source
            liftRemoveNegativeTail? pivot (.positive atom) source derived
termination_by source => source.length

abbrev AppendDerivation (left right : Clause) :=
  Derivation validated
    (appendJ (encodeClause left) (encodeClause right)
      (encodeClause (left ++ right)))

def deriveAppend? : (left right : Clause) ->
    Option (AppendDerivation left right)
  | [], right =>
      if rightValid : argumentValidAt 0 (encodeClause right) = true then
        some (by
          simpa [AppendDerivation, encodeClause] using
            deriveAppendNil (encodeClause right) rightValid)
      else none
  | literal :: left, right => do
      let child <- deriveAppend? left right
      if headValid : argumentValidAt 0 (encodeLiteral literal) = true then
        if leftValid : argumentValidAt 0 (encodeClause left) = true then
          if rightValid : argumentValidAt 0 (encodeClause right) = true then
            if resultValid :
                argumentValidAt 0 (encodeClause (left ++ right)) = true then
              some (by
                simpa [AppendDerivation, encodeClause, encodeLiteral,
                  List.cons_append] using
                  deriveAppendCons (encodeLiteral literal) (encodeClause left)
                    (encodeClause right) (encodeClause (left ++ right))
                    headValid leftValid rightValid resultValid child)
            else none
          else none
        else none
      else none
termination_by left _ => left.length

abbrev LiteralsDerivation (clause : Clause) :=
  Derivation validated (literalsJ (encodeClause clause))

def deriveLiterals? : (clause : Clause) ->
    Option (LiteralsDerivation clause)
  | [] => some (by
      simpa [LiteralsDerivation, encodeClause] using
        deriveLiteralsNil)
  | literal :: clause => do
      let child <- deriveLiterals? clause
      match literal with
      | .positive atom =>
          if atomValid : argumentValidAt 0 atom = true then
            if restValid : argumentValidAt 0 (encodeClause clause) = true then
              some (by
                simpa [LiteralsDerivation, encodeClause, encodeLiteral] using
                  deriveLiteralsPositive atom (encodeClause clause)
                    atomValid restValid child)
            else none
          else none
      | .negative atom =>
          if atomValid : argumentValidAt 0 atom = true then
            if restValid : argumentValidAt 0 (encodeClause clause) = true then
              some (by
                simpa [LiteralsDerivation, encodeClause, encodeLiteral] using
                  deriveLiteralsNegative atom (encodeClause clause)
                    atomValid restValid child)
            else none
          else none
termination_by clause => clause.length

abbrev ResolutionDerivation (positiveOnLeft : Bool) (pivot : Pattern)
    (left right : Clause) :=
  Sigma fun result : Clause =>
    Derivation validated
      (resolveJ (orientationPattern positiveOnLeft) pivot
        (encodeClause left) (encodeClause right) (encodeClause result))

def deriveResolutionPositiveLeft? (pivot : Pattern) (left right : Clause) :
    Option (ResolutionDerivation true pivot left right) := do
  let ⟨leftRest, removeLeft⟩ <-
    deriveRemovePositive? pivot left
  let ⟨rightRest, removeRight⟩ <-
    deriveRemoveNegative? pivot right
  let append <- deriveAppend? leftRest rightRest
  let leftLiterals <- deriveLiterals? left
  let rightLiterals <- deriveLiterals? right
  let resultLiterals <- deriveLiterals? (leftRest ++ rightRest)
  if pivotValid : argumentValidAt 0 pivot = true then
    if leftValid : argumentValidAt 0 (encodeClause left) = true then
      if rightValid : argumentValidAt 0 (encodeClause right) = true then
        if leftRestValid : argumentValidAt 0 (encodeClause leftRest) = true then
          if rightRestValid : argumentValidAt 0 (encodeClause rightRest) = true then
            if resultValid :
                argumentValidAt 0 (encodeClause (leftRest ++ rightRest)) = true then
              some ⟨leftRest ++ rightRest, by
                simpa [orientationPattern] using
                  deriveResolvePositiveLeft pivot (encodeClause left)
                    (encodeClause right) (encodeClause leftRest)
                    (encodeClause rightRest)
                    (encodeClause (leftRest ++ rightRest)) pivotValid
                    leftValid rightValid leftRestValid rightRestValid
                    resultValid removeLeft removeRight append leftLiterals
                    rightLiterals resultLiterals⟩
            else none
          else none
        else none
      else none
    else none
  else none

def deriveResolutionPositiveRight? (pivot : Pattern) (left right : Clause) :
    Option (ResolutionDerivation false pivot left right) := do
  let ⟨leftRest, removeLeft⟩ <- deriveRemoveNegative? pivot left
  let ⟨rightRest, removeRight⟩ <- deriveRemovePositive? pivot right
  let append <- deriveAppend? leftRest rightRest
  let leftLiterals <- deriveLiterals? left
  let rightLiterals <- deriveLiterals? right
  let resultLiterals <- deriveLiterals? (leftRest ++ rightRest)
  if pivotValid : argumentValidAt 0 pivot = true then
    if leftValid : argumentValidAt 0 (encodeClause left) = true then
      if rightValid : argumentValidAt 0 (encodeClause right) = true then
        if leftRestValid : argumentValidAt 0 (encodeClause leftRest) = true then
          if rightRestValid : argumentValidAt 0 (encodeClause rightRest) = true then
            if resultValid :
                argumentValidAt 0 (encodeClause (leftRest ++ rightRest)) = true then
              some ⟨leftRest ++ rightRest, by
                simpa [orientationPattern] using
                  deriveResolvePositiveRight pivot (encodeClause left)
                    (encodeClause right) (encodeClause leftRest)
                    (encodeClause rightRest)
                    (encodeClause (leftRest ++ rightRest)) pivotValid
                    leftValid rightValid leftRestValid rightRestValid
                    resultValid removeLeft removeRight append leftLiterals
                    rightLiterals resultLiterals⟩
            else none
          else none
        else none
      else none
    else none
  else none

def deriveResolutionAt? : (positiveOnLeft : Bool) -> (pivot : Pattern) ->
    (left right : Clause) ->
    Option (ResolutionDerivation positiveOnLeft pivot left right)
  | true, pivot, left, right =>
      deriveResolutionPositiveLeft? pivot left right
  | false, pivot, left, right =>
      deriveResolutionPositiveRight? pivot left right

abbrev CertifiedResolutionEvidence (left right result : Clause) :=
  { evidence : ResolutionEvidence //
    evidenceCheck resolutionKey
      { parents := [.clause left, .clause right]
        inferred := .clause result }
      evidence = true }

def evidenceAt? (positiveOnLeft : Bool) (pivot : Pattern)
    (left right expected : Clause) :
    Option (CertifiedResolutionEvidence left right expected) := do
  let ⟨result, derivation⟩ <-
    deriveResolutionAt? positiveOnLeft pivot left right
  if resultEq : result = expected then
    let expectedDerivation : Derivation validated
        (resolveJ (orientationPattern positiveOnLeft) pivot
          (encodeClause left) (encodeClause right) (encodeClause expected)) :=
      resultEq ▸ derivation
    let article := articleOfDerivation expectedDerivation
    let evidence : ResolutionEvidence := {
      pivot := pivot
      positiveLeft := positiveOnLeft
      article := article
    }
    some ⟨evidence, by
      simp only [evidenceCheck, resolutionKey]
      change semanticAuthority.check
        (resolutionClaim pivot positiveOnLeft left right expected) article = true
      simpa [semanticAuthority, judgmentWireAuthority,
        decodedResolutionAdequacy, resolutionClaim, article,
        DecodedResolutionClaim.encode] using
        wireArticleAuthority_complete authorityId expectedDerivation⟩
  else none

def synthesizeEvidenceFrom? (left right expected : Clause) :
    Clause -> Option (CertifiedResolutionEvidence left right expected)
  | [] => none
  | literal :: literals =>
      let attempt := match literal with
        | .positive pivot => evidenceAt? true pivot left right expected
        | .negative pivot => evidenceAt? false pivot left right expected
      match attempt with
      | some evidence => some evidence
      | none => synthesizeEvidenceFrom? left right expected literals
termination_by literals => literals.length

/-- Reconstruct a calculus article for a claimed binary ground resolvent.  The
search space is only the literal occurrences of the left parent. -/
def synthesizeEvidence? (left right expected : Clause) :
    Option (CertifiedResolutionEvidence left right expected) :=
  synthesizeEvidenceFrom? left right expected left

@[simp] theorem argumentValidAt_encodePositive (atom : Pattern) :
    argumentValidAt 0 (encodeLiteral (.positive atom)) =
      argumentValidAt 0 atom := by
  simp [argumentValidAt, encodeLiteral, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

@[simp] theorem argumentValidAt_encodeNegative (atom : Pattern) :
    argumentValidAt 0 (encodeLiteral (.negative atom)) =
      argumentValidAt 0 atom := by
  simp [argumentValidAt, encodeLiteral, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

@[simp] theorem argumentValidAt_encodeClause_nil :
    argumentValidAt 0 (encodeClause []) = true := by
  rfl

@[simp] theorem argumentValidAt_encodeClause_cons
    (literal : Literal) (clause : Clause) :
    argumentValidAt 0 (encodeClause (literal :: clause)) =
      (argumentValidAt 0 (encodeLiteral literal) &&
        argumentValidAt 0 (encodeClause clause)) := by
  simp [argumentValidAt, encodeClause, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]
  ac_rfl

/-- A binary clause containing a positive pivot resolves with the singleton
negative pivot clause to its untouched tail literal.  This theorem is
parametric in the atom representation; official TPTP AST atoms therefore do
not require a syntax-specific evidence synthesizer. -/
theorem synthesize_binary_positive_left
    (pivot untouched : Pattern)
    (pivotValid : argumentValidAt 0 pivot = true)
    (untouchedValid : argumentValidAt 0 untouched = true) :
    (synthesizeEvidence?
      [.positive pivot, .positive untouched]
      [.negative pivot]
      [.positive untouched]).isSome = true := by
  simp [synthesizeEvidence?, synthesizeEvidenceFrom?, evidenceAt?,
    deriveResolutionAt?, deriveResolutionPositiveLeft?,
    deriveRemovePositive?, deriveRemoveNegative?, deriveAppend?, deriveLiterals?,
    pivotValid, untouchedValid]

/-- Resolving complementary singleton clauses produces the empty clause. -/
theorem synthesize_binary_singletons
    (pivot : Pattern) (pivotValid : argumentValidAt 0 pivot = true) :
    (synthesizeEvidence? [.positive pivot] [.negative pivot] []).isSome = true := by
  simp [synthesizeEvidence?, synthesizeEvidenceFrom?, evidenceAt?,
    deriveResolutionAt?, deriveResolutionPositiveLeft?,
    deriveRemovePositive?, deriveRemoveNegative?, deriveAppend?,
    deriveLiterals?, pivotValid]

/-! ## Controls -/

namespace Canary

open TptpGroundResolutionProblemAuthority.Canary

theorem first_resolution_synthesized :
    (synthesizeEvidence? disjunction negativeP positiveQ).isSome = true := by
  decide +kernel

theorem second_resolution_synthesized :
    (synthesizeEvidence? positiveQ negativeQ []).isSome = true := by
  decide +kernel

theorem invented_result_not_synthesized :
    synthesizeEvidence? disjunction negativeP positiveP = none := by
  decide +kernel

theorem no_complement_not_synthesized :
    synthesizeEvidence? positiveP positiveQ [] = none := by
  decide +kernel

end Canary

#print axioms Canary.first_resolution_synthesized
#print axioms Canary.second_resolution_synthesized
#print axioms Canary.invented_result_not_synthesized
#print axioms Canary.no_complement_not_synthesized

end Mettapedia.GSLT.LanguageDef.TptpGroundResolutionEvidenceSynthesis
