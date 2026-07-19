import Mettapedia.Languages.MeTTa.HE.HumanEvalSteps

/-!
# Executable-independent human evaluator specification

Six mutually recursive, fuel-free judgments transcribe the published HE MeTTa
evaluator.  The type, unify, switch, matcher, merger, alpha-renaming, and
equation-query premises are the independent relations from the preceding
modules.  Grounded operations remain an explicitly parameterized host
relation.

The mutual block presents individual raw results.  `HumanEval` below adds the
published top-level success-priority rule: an error is observable only when no
non-error raw result exists for the same configuration.
-/

namespace Mettapedia.Languages.MeTTa.HE.HumanEvalSpec

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open HumanMatchMergeSpec
open HumanTypeSpec
open HumanEvalSteps

/-! ## Syntax and host boundaries -/

/-- Intrinsic meta-type, stated relationally. -/
inductive MetaTypeRel : Atom → Atom → Prop where
  | symbol (name : String) :
      MetaTypeRel (.symbol name) Atom.symbolType
  | variable (name : String) :
      MetaTypeRel (.var name) Atom.variableType
  | grounded (value : GroundedValue) :
      MetaTypeRel (.grounded value) Atom.groundedType
  | expression (atoms : List Atom) :
      MetaTypeRel (.expression atoms) Atom.expressionType

/-- Syntactic error atom.  The published `(Error ...)` pattern recognizes
every expression headed by `Error`, independently of its tail shape. -/
def IsErrorRel (atom : Atom) : Prop :=
  ∃ tail, atom = .expression (.symbol "Error" :: tail)

/-- Empty or syntactic error atom. -/
def IsEmptyOrErrorRel (atom : Atom) : Prop :=
  atom = Atom.empty ∨ IsErrorRel atom

/-- Host-grounded operations are genuinely external to the MeTTa semantics.
The evaluator sees only an executable predicate and a relation of possible
host outcomes. -/
structure HumanGroundedDispatch where
  executable : Atom → Prop
  outcome : Atom → List Atom → GroundedResult → Prop

/-- The equation-query lane is used only when the head is not a host operation
or one of the two structural control instructions. -/
def NonGroundedCallRel (dispatch : HumanGroundedDispatch) (atom : Atom) : Prop :=
  match atom with
  | .expression (operator :: _) =>
      ¬dispatch.executable operator ∧
        operator ≠ .symbol "unify" ∧
        operator ≠ .symbol "switch-minimal"
  | _ => True

/-! ## Type-service boundary and ordered candidate selection -/

/-- Result of the published left-to-right function-candidate scan.  Success
stops the scan immediately.  Exhaustion retains one error from every failed
function candidate and records whether a non-function candidate made tuple
fallback eligible. -/
inductive FunctionCandidateScanOutcome where
  | success (functionType returnType : Atom) (bindings : Bindings)
  | exhausted (errors : List Atom) (tupleEligible : Bool)

/-- Literal transcription of the candidate loop in `interpret_expression`
(`Specs/he_metta_official_specs.md:172-210`): non-functions enable tuple
fallback, failed functions accumulate errors, and the first applicable
function stops the scan. -/
inductive FunctionCandidateScanRel
    (applicability :
      Space → Atom → Atom → Atom → Bindings → ApplicabilityOutcome → Prop)
    (space : Space)
    (expression expectedType : Atom) (bindings : Bindings) :
    List Atom → FunctionCandidateScanOutcome → Prop where
  | nil :
      FunctionCandidateScanRel applicability space expression expectedType bindings
        [] (.exhausted [] false)
  | nonFunctionSuccess {candidate : Atom} {candidates : List Atom}
      {functionType returnType : Atom} {output : Bindings} :
      (¬∃ argumentTypes candidateReturn,
        FunctionTypeRel candidate argumentTypes candidateReturn) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        candidates (.success functionType returnType output) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        (candidate :: candidates) (.success functionType returnType output)
  | nonFunctionExhausted {candidate : Atom} {candidates errors : List Atom}
      {tupleEligible : Bool} :
      (¬∃ argumentTypes candidateReturn,
        FunctionTypeRel candidate argumentTypes candidateReturn) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        candidates (.exhausted errors tupleEligible) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        (candidate :: candidates) (.exhausted errors true)
  | functionSuccess {candidate : Atom} {candidates argumentTypes : List Atom}
      {returnType : Atom} {output : Bindings} :
      FunctionTypeRel candidate argumentTypes returnType →
      applicability space expression candidate expectedType bindings
        (.success output) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        (candidate :: candidates) (.success candidate returnType output)
  | functionFailureThenSuccess
      {candidate : Atom} {candidates argumentTypes : List Atom}
      {candidateReturn error functionType returnType : Atom}
      {output : Bindings} :
      FunctionTypeRel candidate argumentTypes candidateReturn →
      (∀ candidateOutput,
        ¬applicability space expression candidate expectedType bindings
          (.success candidateOutput)) →
      applicability space expression candidate expectedType bindings
        (.error error) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        candidates (.success functionType returnType output) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        (candidate :: candidates) (.success functionType returnType output)
  | functionFailureExhausted
      {candidate : Atom} {candidates argumentTypes errors : List Atom}
      {candidateReturn error : Atom} {tupleEligible : Bool} :
      FunctionTypeRel candidate argumentTypes candidateReturn →
      (∀ candidateOutput,
        ¬applicability space expression candidate expectedType bindings
          (.success candidateOutput)) →
      applicability space expression candidate expectedType bindings
        (.error error) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        candidates (.exhausted errors tupleEligible) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        (candidate :: candidates)
        (.exhausted (error :: errors) tupleEligible)

/-- The exact type surface consumed by the six evaluator judgments.  One
service supplies both positive and negative premises; mixing a permissive
positive layer with a different negative candidate set is unrepresentable.

`candidateScan` is deliberately a single ordered relation rather than a bare
applicability predicate: first-success and all-failed outcomes must quantify
over the same exact candidate sequence.

The published instance below is the specification-textual core.  The repaired
runtime instance is defined in the conformance layer from the exact ordered
package relation. -/
structure HumanEvalTypeService where
  typesOf : Space → Atom → List Atom → Prop
  typeCast : Space → Atom → Atom → Bindings → ResultPair → Prop
  candidateScan :
    Space → Atom → Atom → Bindings →
      List Atom → FunctionCandidateScanOutcome → Prop

/-- The published human type layer, definitionally, as one coherent evaluator
service. -/
def publishedTypeService : HumanEvalTypeService where
  typesOf := TypesOfRel
  typeCast := TypeCastRel
  candidateScan := FunctionCandidateScanRel ApplicabilityRel

private def scanFailureType : Atom :=
  .expression [.symbol "->", .symbol "A"]

private def scanSuccessType : Atom :=
  .expression [.symbol "->", .symbol "B"]

private def scanExpression : Atom :=
  .expression [.symbol "scan-target"]

private def scanFailure : Atom :=
  mkError scanExpression (.badType Atom.undefinedType (.symbol "A"))

private def orderedScanCanaryApplicability
    (_space : Space) (_expression functionType _expectedType : Atom)
    (_bindings : Bindings) (outcome : ApplicabilityOutcome) : Prop :=
  (functionType = scanFailureType ∧ outcome = .error scanFailure) ∨
  (functionType = scanSuccessType ∧ outcome = .success Bindings.empty)

/-- Positive order canary: a failed first function candidate is recorded and
the second successful candidate is selected. -/
theorem ordered_scan_skips_failed_candidate :
    FunctionCandidateScanRel orderedScanCanaryApplicability Space.empty
      scanExpression Atom.undefinedType Bindings.empty
      [scanFailureType, scanSuccessType]
      (.success scanSuccessType (.symbol "B") Bindings.empty) := by
  apply FunctionCandidateScanRel.functionFailureThenSuccess
      (argumentTypes := []) (candidateReturn := .symbol "A")
      (error := scanFailure)
  · rfl
  · intro candidateOutput hsuccess
    simp [orderedScanCanaryApplicability, scanFailureType, scanSuccessType]
      at hsuccess
  · simp [orderedScanCanaryApplicability]
  · apply FunctionCandidateScanRel.functionSuccess
        (argumentTypes := []) (returnType := .symbol "B")
    · rfl
    · simp [orderedScanCanaryApplicability]

/-- Negative order canary: once the head function candidate succeeds, the
same candidate list cannot be presented as exhausted, so tuple fallback and
all-failed errors are unavailable. -/
theorem ordered_scan_first_success_excludes_exhaustion
    (candidates errors : List Atom) (tupleEligible : Bool) :
    ¬FunctionCandidateScanRel orderedScanCanaryApplicability Space.empty
      scanExpression Atom.undefinedType Bindings.empty
      (scanSuccessType :: candidates) (.exhausted errors tupleEligible) := by
  intro hscan
  cases hscan with
  | nonFunctionExhausted hnot _ =>
      exact hnot ⟨[], .symbol "B", rfl⟩
  | functionFailureExhausted _ hnoSuccess _ _ =>
      exact hnoSuccess Bindings.empty (by
        simp [orderedScanCanaryApplicability])

/-! ## Six mutual evaluator judgments -/

mutual

/-- Evaluate one atom to one raw result. -/
inductive HumanEvalAtomRaw
    (space : Space) (dispatch : HumanGroundedDispatch) (live : List Atom) :
    Atom → Atom → Bindings → ResultPair →
      (typing : HumanEvalTypeService := publishedTypeService) → Prop where
  | emptyOrError (atom expectedType : Atom) (bindings : Bindings) :
      IsEmptyOrErrorRel atom →
      HumanEvalAtomRaw space dispatch live (typing := typing) atom expectedType bindings
        (atom, bindings)
  | typePass (atom expectedType metaType : Atom) (bindings : Bindings) :
      ¬IsEmptyOrErrorRel atom →
      MetaTypeRel atom metaType →
      (expectedType = Atom.atomType ∨
        expectedType = metaType ∨ metaType = Atom.variableType) →
      HumanEvalAtomRaw space dispatch live (typing := typing) atom expectedType bindings
        (atom, bindings)
  | cast (atom expectedType metaType : Atom) (bindings : Bindings)
      (result : ResultPair) :
      ¬IsEmptyOrErrorRel atom →
      MetaTypeRel atom metaType →
      ¬(expectedType = Atom.atomType ∨
        expectedType = metaType ∨ metaType = Atom.variableType) →
      ((∃ name, atom = .symbol name) ∨
        (∃ value, atom = .grounded value) ∨ atom = Atom.unit) →
      typing.typeCast space atom expectedType bindings result →
      HumanEvalAtomRaw space dispatch live (typing := typing)
        atom expectedType bindings result
  | interpretSuccess (atom expectedType metaType : Atom) (bindings : Bindings)
      (result : ResultPair) :
      ¬IsEmptyOrErrorRel atom →
      MetaTypeRel atom metaType →
      ¬(expectedType = Atom.atomType ∨
        expectedType = metaType ∨ metaType = Atom.variableType) →
      (∃ head tail, atom = .expression (head :: tail)) →
      HumanInterpretExpression space dispatch live (typing := typing)
        atom expectedType bindings result →
      ¬IsErrorRel result.1 →
      HumanEvalAtomRaw space dispatch live (typing := typing)
        atom expectedType bindings result
  | interpretError (atom expectedType metaType : Atom) (bindings : Bindings)
      (result : ResultPair) :
      ¬IsEmptyOrErrorRel atom →
      MetaTypeRel atom metaType →
      ¬(expectedType = Atom.atomType ∨
        expectedType = metaType ∨ metaType = Atom.variableType) →
      (∃ head tail, atom = .expression (head :: tail)) →
      HumanInterpretExpression space dispatch live (typing := typing)
        atom expectedType bindings result →
      IsErrorRel result.1 →
      HumanEvalAtomRaw space dispatch live (typing := typing)
        atom expectedType bindings result

/-- Interpret an expression through a function type, tuple fallback, or
operator-type error. -/
inductive HumanInterpretExpression
    (space : Space) (dispatch : HumanGroundedDispatch) (live : List Atom) :
    Atom → Atom → Bindings → ResultPair →
      (typing : HumanEvalTypeService := publishedTypeService) → Prop where
  | functionPath (expression expectedType operator : Atom)
      (arguments types : List Atom)
      (functionType declaredReturnType callType : Atom)
      (bindings applicableBindings : Bindings)
      (interpreted callResult : ResultPair) :
      expression = .expression (operator :: arguments) →
      typing.typesOf space operator types →
      typing.candidateScan space expression expectedType bindings
        types (.success functionType declaredReturnType applicableBindings) →
      callType = (if declaredReturnType = Atom.expressionType
        then Atom.undefinedType else declaredReturnType) →
      HumanInterpretFunction space dispatch live (typing := typing)
        expression functionType expectedType applicableBindings interpreted →
      HumanCall space dispatch live (typing := typing)
        interpreted.1 callType interpreted.2 callResult →
      HumanInterpretExpression space dispatch live (typing := typing)
        expression expectedType bindings callResult
  | tuplePath (expression expectedType operator : Atom)
      (arguments types errors : List Atom) (bindings : Bindings)
      (tupleResult callResult : ResultPair) :
      expression = .expression (operator :: arguments) →
      typing.typesOf space operator types →
      typing.candidateScan space expression expectedType bindings
        types (.exhausted errors true) →
      HumanInterpretTuple space dispatch live (typing := typing)
        expression bindings tupleResult →
      HumanCall space dispatch live (typing := typing)
        tupleResult.1 expectedType tupleResult.2 callResult →
      HumanInterpretExpression space dispatch live (typing := typing)
        expression expectedType bindings callResult
  | functionError (expression expectedType operator errorAtom : Atom)
      (arguments types errors : List Atom) (tupleEligible : Bool)
      (bindings : Bindings) :
      expression = .expression (operator :: arguments) →
      typing.typesOf space operator types →
      typing.candidateScan space expression expectedType bindings
        types (.exhausted errors tupleEligible) →
      errorAtom ∈ errors →
      HumanInterpretExpression space dispatch live (typing := typing)
        expression expectedType bindings (errorAtom, bindings)

/-- Evaluate a function head, then its arguments. -/
inductive HumanInterpretFunction
    (space : Space) (dispatch : HumanGroundedDispatch) (live : List Atom) :
    Atom → Atom → Atom → Bindings → ResultPair →
      (typing : HumanEvalTypeService := publishedTypeService) → Prop where
  | headError (expression functionType returnType operator : Atom)
      (arguments argumentTypes : List Atom) (bindings : Bindings)
      (headResult : ResultPair) :
      expression = .expression (operator :: arguments) →
      FunctionTypeRel functionType argumentTypes returnType →
      HumanEvalAtomRaw space dispatch live (typing := typing)
        operator functionType bindings
        headResult →
      IsEmptyOrErrorRel headResult.1 →
      HumanInterpretFunction space dispatch live (typing := typing)
        expression functionType
        returnType bindings headResult
  | tailError (expression functionType returnType operator : Atom)
      (arguments argumentTypes : List Atom) (bindings : Bindings)
      (headResult tailResult : ResultPair) :
      expression = .expression (operator :: arguments) →
      FunctionTypeRel functionType argumentTypes returnType →
      HumanEvalAtomRaw space dispatch live (typing := typing)
        operator functionType bindings
        headResult →
      ¬IsEmptyOrErrorRel headResult.1 →
      HumanInterpretArgs space dispatch live (typing := typing)
        arguments argumentTypes
        headResult.2 tailResult →
      IsEmptyOrErrorRel tailResult.1 →
      HumanInterpretFunction space dispatch live (typing := typing)
        expression functionType
        returnType bindings tailResult
  | success (expression functionType returnType operator : Atom)
      (arguments argumentTypes : List Atom) (bindings : Bindings)
      (headResult tailResult : ResultPair) :
      expression = .expression (operator :: arguments) →
      FunctionTypeRel functionType argumentTypes returnType →
      HumanEvalAtomRaw space dispatch live (typing := typing)
        operator functionType bindings
        headResult →
      ¬IsEmptyOrErrorRel headResult.1 →
      HumanInterpretArgs space dispatch live (typing := typing)
        arguments argumentTypes
        headResult.2 tailResult →
      ¬IsEmptyOrErrorRel tailResult.1 →
      HumanInterpretFunction space dispatch live (typing := typing)
        expression functionType
        returnType bindings
        (.expression (headResult.1 :: match tailResult.1 with
          | .expression atoms => atoms | atom => [atom]), tailResult.2)

/-- Evaluate argument lists left to right. -/
inductive HumanInterpretArgs
    (space : Space) (dispatch : HumanGroundedDispatch) (live : List Atom) :
    List Atom → List Atom → Bindings → ResultPair →
      (typing : HumanEvalTypeService := publishedTypeService) → Prop where
  | nil (bindings : Bindings) :
      HumanInterpretArgs space dispatch live (typing := typing) [] [] bindings
        (Atom.unit, bindings)
  | headChangedError (argument : Atom) (arguments : List Atom)
      (expectedType : Atom) (expectedTypes : List Atom)
      (bindings : Bindings) (headResult : ResultPair) :
      HumanEvalAtomRaw space dispatch live (typing := typing)
        argument expectedType bindings
        headResult →
      IsEmptyOrErrorRel headResult.1 →
      headResult.1 ≠ argument →
      HumanInterpretArgs space dispatch live (typing := typing)
        (argument :: arguments) (expectedType :: expectedTypes)
        bindings headResult
  | tailError (argument : Atom) (arguments : List Atom)
      (expectedType : Atom) (expectedTypes : List Atom)
      (bindings : Bindings) (headResult tailResult : ResultPair) :
      HumanEvalAtomRaw space dispatch live (typing := typing)
        argument expectedType bindings
        headResult →
      (¬IsEmptyOrErrorRel headResult.1 ∨ headResult.1 = argument) →
      HumanInterpretArgs space dispatch live (typing := typing)
        arguments expectedTypes
        headResult.2 tailResult →
      IsEmptyOrErrorRel tailResult.1 →
      HumanInterpretArgs space dispatch live (typing := typing)
        (argument :: arguments) (expectedType :: expectedTypes)
        bindings tailResult
  | success (argument : Atom) (arguments : List Atom)
      (expectedType : Atom) (expectedTypes : List Atom)
      (bindings : Bindings) (headResult tailResult : ResultPair) :
      HumanEvalAtomRaw space dispatch live (typing := typing)
        argument expectedType bindings
        headResult →
      (¬IsEmptyOrErrorRel headResult.1 ∨ headResult.1 = argument) →
      HumanInterpretArgs space dispatch live (typing := typing)
        arguments expectedTypes
        headResult.2 tailResult →
      ¬IsEmptyOrErrorRel tailResult.1 →
      HumanInterpretArgs space dispatch live (typing := typing)
        (argument :: arguments) (expectedType :: expectedTypes) bindings
        (.expression (headResult.1 :: match tailResult.1 with
          | .expression atoms => atoms | atom => [atom]), tailResult.2)

/-- Evaluate tuple elements left to right. -/
inductive HumanInterpretTuple
    (space : Space) (dispatch : HumanGroundedDispatch) (live : List Atom) :
    Atom → Bindings → ResultPair →
      (typing : HumanEvalTypeService := publishedTypeService) → Prop where
  | singleton (atom : Atom) (bindings : Bindings) (result : ResultPair) :
      HumanEvalAtomRaw space dispatch live (typing := typing)
        atom Atom.undefinedType bindings
        result →
      HumanInterpretTuple space dispatch live (typing := typing)
        (.expression [atom])
        bindings result
  | headError (head : Atom) (tail : List Atom) (bindings : Bindings)
      (headResult : ResultPair) :
      tail ≠ [] →
      HumanEvalAtomRaw space dispatch live (typing := typing)
        head Atom.undefinedType bindings
        headResult →
      IsEmptyOrErrorRel headResult.1 →
      HumanInterpretTuple space dispatch live (typing := typing)
        (.expression (head :: tail))
        bindings headResult
  | tailError (head : Atom) (tail : List Atom) (bindings : Bindings)
      (headResult tailResult : ResultPair) :
      tail ≠ [] →
      HumanEvalAtomRaw space dispatch live (typing := typing)
        head Atom.undefinedType bindings
        headResult →
      ¬IsEmptyOrErrorRel headResult.1 →
      HumanInterpretTuple space dispatch live (typing := typing)
        (.expression tail)
        headResult.2 tailResult →
      IsEmptyOrErrorRel tailResult.1 →
      HumanInterpretTuple space dispatch live (typing := typing)
        (.expression (head :: tail))
        bindings tailResult
  | success (head : Atom) (tail : List Atom) (bindings : Bindings)
      (headResult tailResult : ResultPair) :
      tail ≠ [] →
      HumanEvalAtomRaw space dispatch live (typing := typing)
        head Atom.undefinedType bindings
        headResult →
      ¬IsEmptyOrErrorRel headResult.1 →
      HumanInterpretTuple space dispatch live (typing := typing)
        (.expression tail)
        headResult.2 tailResult →
      ¬IsEmptyOrErrorRel tailResult.1 →
      HumanInterpretTuple space dispatch live (typing := typing)
        (.expression (head :: tail))
        bindings
        (.expression (headResult.1 :: match tailResult.1 with
          | .expression atoms => atoms | atom => [atom]), tailResult.2)

/-- Perform one MeTTa call step, recursively evaluating host or equation
results when the published evaluator requires it. -/
inductive HumanCall
    (space : Space) (dispatch : HumanGroundedDispatch) (live : List Atom) :
    Atom → Atom → Bindings → ResultPair →
      (typing : HumanEvalTypeService := publishedTypeService) → Prop where
  | errorPassthrough (atom expectedType : Atom) (bindings : Bindings) :
      IsErrorRel atom →
      HumanCall space dispatch live (typing := typing) atom expectedType bindings
        (atom, bindings)
  | unify (atom expectedType target pattern thenBranch elseBranch result : Atom)
      (bindings output : Bindings) :
      atom = .expression
        [.symbol "unify", target, pattern, thenBranch, elseBranch] →
      ¬IsErrorRel atom →
      HumanUnifyStep target pattern thenBranch elseBranch bindings
        result output →
      HumanCall space dispatch live (typing := typing)
        atom expectedType bindings (result, output)
  | unifyBadArity (atom expectedType : Atom) (tail : List Atom)
      (bindings : Bindings) :
      atom = .expression (.symbol "unify" :: tail) →
      tail.length ≠ 4 →
      ¬IsErrorRel atom →
      HumanCall space dispatch live (typing := typing) atom expectedType bindings
        (mkUnifyBadArityError atom, bindings)
  | switchMinimal (atom expectedType scrutinee : Atom)
      (branches : List Atom) (bindings : Bindings) (result : ResultPair) :
      atom = .expression
        [.symbol "switch-minimal", scrutinee, .expression branches] →
      ¬IsErrorRel atom →
      HumanSwitchStep scrutinee branches bindings result.1 result.2 →
      HumanCall space dispatch live (typing := typing)
        atom expectedType bindings result
  | switchMinimalBadShape (atom expectedType : Atom) (tail : List Atom)
      (bindings : Bindings) :
      atom = .expression (.symbol "switch-minimal" :: tail) →
      (¬∃ scrutinee branches,
        tail = [scrutinee, .expression branches]) →
      ¬IsErrorRel atom →
      HumanCall space dispatch live (typing := typing) atom expectedType bindings
        (mkError atom .incorrectNumberOfArguments, bindings)
  | groundedSuccess (atom expectedType operator : Atom)
      (arguments : List Atom) (bindings : Bindings)
      (nativeResults : ResultSet) (nativeResult finalResult : ResultPair)
      (merged : Bindings) :
      atom = .expression (operator :: arguments) →
      dispatch.executable operator →
      operator ≠ .symbol "unify" →
      operator ≠ .symbol "switch-minimal" →
      ¬IsErrorRel atom →
      dispatch.outcome operator arguments (.ok nativeResults) →
      nativeResult ∈ nativeResults →
      MergeRel equalityGroundedSemantic nativeResult.2 bindings merged →
      HumanEvalAtomRaw space dispatch live (typing := typing)
        nativeResult.1 expectedType merged
        finalResult →
      HumanCall space dispatch live (typing := typing)
        atom expectedType bindings finalResult
  | groundedRuntimeError (atom expectedType operator : Atom)
      (arguments : List Atom) (bindings : Bindings) (message : String) :
      atom = .expression (operator :: arguments) →
      dispatch.executable operator →
      operator ≠ .symbol "unify" →
      operator ≠ .symbol "switch-minimal" →
      ¬IsErrorRel atom →
      dispatch.outcome operator arguments (.runtimeError message) →
      HumanCall space dispatch live (typing := typing) atom expectedType bindings
        (Atom.error atom (.symbol message), bindings)
  | groundedNoReduce (atom expectedType operator : Atom)
      (arguments : List Atom) (bindings : Bindings) :
      atom = .expression (operator :: arguments) →
      dispatch.executable operator →
      operator ≠ .symbol "unify" →
      operator ≠ .symbol "switch-minimal" →
      ¬IsErrorRel atom →
      dispatch.outcome operator arguments .noReduce →
      HumanCall space dispatch live (typing := typing)
        atom expectedType bindings (atom, bindings)
  | groundedIncorrectArgument (atom expectedType operator : Atom)
      (arguments : List Atom) (bindings : Bindings) :
      atom = .expression (operator :: arguments) →
      dispatch.executable operator →
      operator ≠ .symbol "unify" →
      operator ≠ .symbol "switch-minimal" →
      ¬IsErrorRel atom →
      dispatch.outcome operator arguments .incorrectArgument →
      HumanCall space dispatch live (typing := typing)
        atom expectedType bindings (atom, bindings)
  | groundedEmpty (atom expectedType operator : Atom)
      (arguments : List Atom) (bindings : Bindings) :
      atom = .expression (operator :: arguments) →
      dispatch.executable operator →
      operator ≠ .symbol "unify" →
      operator ≠ .symbol "switch-minimal" →
      ¬IsErrorRel atom →
      dispatch.outcome operator arguments (.ok []) →
      HumanCall space dispatch live (typing := typing) atom expectedType bindings
        (Atom.empty, bindings)
  | equation (atom expectedType emitted : Atom) (bindings merged : Bindings)
      (finalResult : ResultPair) :
      ¬IsErrorRel atom →
      NonGroundedCallRel dispatch atom →
      HumanEquationQueryCandidateRel space live atom bindings emitted merged →
      HumanEvalAtomRaw space dispatch live (typing := typing)
        emitted expectedType merged
        finalResult →
      HumanCall space dispatch live (typing := typing)
        atom expectedType bindings finalResult
  | noEquation (atom expectedType : Atom) (bindings : Bindings) :
      ¬IsErrorRel atom →
      NonGroundedCallRel dispatch atom →
      HumanEquationQueryNoMatchRel space live atom bindings →
      HumanCall space dispatch live (typing := typing)
        atom expectedType bindings (atom, bindings)
  | allEquationsFiltered (atom expectedType : Atom) (bindings : Bindings) :
      ¬IsErrorRel atom →
      NonGroundedCallRel dispatch atom →
      HumanEquationQueryAllFilteredRel space live atom bindings →
      HumanCall space dispatch live (typing := typing) atom expectedType bindings
        (Atom.empty, bindings)

end

/-! ## Public success-priority boundary -/

/-- A published evaluator result: raw successes are admitted directly; a raw
error is admitted only if no raw non-error result exists for the same input. -/
def HumanEval
    (space : Space) (dispatch : HumanGroundedDispatch) (live : List Atom)
    (atom expectedType : Atom) (bindings : Bindings) (result : ResultPair)
    (typing : HumanEvalTypeService := publishedTypeService) : Prop :=
  HumanEvalAtomRaw space dispatch live (typing := typing)
      atom expectedType bindings result ∧
    (IsErrorRel result.1 →
      ∀ candidate,
        HumanEvalAtomRaw space dispatch live (typing := typing)
          atom expectedType bindings candidate →
          IsErrorRel candidate.1)

/-! ## Boundary examples -/

private def noHostDispatch : HumanGroundedDispatch where
  executable := fun _ => False
  outcome := fun _ _ _ => False

/-- Positive error-shape canary: the published ellipsis permits an empty
tail after the `Error` head. -/
example : IsErrorRel (.expression [.symbol "Error"]) :=
  ⟨[], rfl⟩

/-- Negative error-shape canary: the bare `Error` symbol is data, not an
error expression. -/
example : ¬IsErrorRel (.symbol "Error") := by
  rintro ⟨tail, h⟩
  cases h

/-- Positive: `Empty` passes through unchanged. -/
example : HumanEval Space.empty noHostDispatch []
    Atom.empty Atom.undefinedType Bindings.empty
    (Atom.empty, Bindings.empty) := by
  constructor
  · exact HumanEvalAtomRaw.emptyOrError _ _ _ (Or.inl rfl)
  · intro herror
    exact (by rcases herror with ⟨tail, h⟩; cases h)

private theorem variablePassRaw (name : String) (expectedType : Atom) :
    HumanEvalAtomRaw Space.empty noHostDispatch []
    (.var name) expectedType Bindings.empty
    (.var name, Bindings.empty) := by
  apply HumanEvalAtomRaw.typePass (.var name) expectedType
      Atom.variableType Bindings.empty
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · exact MetaTypeRel.variable name
  · exact Or.inr (Or.inr rfl)

/-- Positive tuple recursion: a singleton tuple delegates to atom evaluation. -/
example : HumanInterpretTuple Space.empty noHostDispatch []
    (.expression [.var "x"]) Bindings.empty
    (.var "x", Bindings.empty) :=
  HumanInterpretTuple.singleton (.var "x") Bindings.empty
    (.var "x", Bindings.empty) (variablePassRaw "x" Atom.undefinedType)

private def unaryWantedType : Atom :=
  .expression [.symbol "->", .symbol "Wanted", .symbol "Wanted"]

private theorem variableArgumentRaw :
    HumanInterpretArgs Space.empty noHostDispatch []
      [.var "x"] [.symbol "Wanted"] Bindings.empty
      (.expression [.var "x"], Bindings.empty) := by
  apply HumanInterpretArgs.success
      (.var "x") [] (.symbol "Wanted") [] Bindings.empty
      (.var "x", Bindings.empty) (Atom.unit, Bindings.empty)
  · exact variablePassRaw "x" (.symbol "Wanted")
  · exact Or.inr rfl
  · exact HumanInterpretArgs.nil Bindings.empty
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty, Atom.unit]

/-- Positive function recursion: variables pass the declared unary function
and argument types, producing the interpreted call expression. -/
example : HumanInterpretFunction Space.empty noHostDispatch []
    (.expression [.var "f", .var "x"])
    unaryWantedType (.symbol "Wanted") Bindings.empty
    (.expression [.var "f", .var "x"], Bindings.empty) := by
  apply HumanInterpretFunction.success
      (.expression [.var "f", .var "x"])
      unaryWantedType (.symbol "Wanted") (.var "f")
      [.var "x"] [.symbol "Wanted"] Bindings.empty
      (.var "f", Bindings.empty)
      (.expression [.var "x"], Bindings.empty)
  · rfl
  · rfl
  · exact variablePassRaw "f" unaryWantedType
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · exact variableArgumentRaw
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]

/-- Positive type-cast path: an unannotated symbol has `%Undefined%`, which
matches any expected type. -/
example : HumanEvalAtomRaw Space.empty noHostDispatch []
    (.symbol "x") (.symbol "Wanted") Bindings.empty
    (.symbol "x", Bindings.empty) := by
  apply HumanEvalAtomRaw.cast
      (.symbol "x") (.symbol "Wanted") Atom.symbolType Bindings.empty
      (.symbol "x", Bindings.empty)
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · exact MetaTypeRel.symbol "x"
  · simp [Atom.atomType, Atom.symbolType, Atom.variableType]
  · exact Or.inl ⟨"x", rfl⟩
  · apply TypeCastRel.success
        (types := [Atom.undefinedType]) (earlierTypes := [])
        (laterTypes := []) (actualType := Atom.undefinedType)
    · exact TypesOfRel.symbolUndefined AnnotationTypesRel.nil
    · rfl
    · simp
    · exact TypeMatchRel.undefinedLeft (.symbol "Wanted") Bindings.empty

/-- Negative unify branch: a symbol mismatch returns the else atom. -/
example : HumanCall Space.empty noHostDispatch []
    (.expression [.symbol "unify", .symbol "a", .symbol "b",
      .symbol "then", .symbol "else"])
    Atom.undefinedType Bindings.empty (.symbol "else", Bindings.empty) := by
  apply HumanCall.unify
      (.expression [.symbol "unify", .symbol "a", .symbol "b",
        .symbol "then", .symbol "else"])
      Atom.undefinedType (.symbol "a") (.symbol "b")
      (.symbol "then") (.symbol "else") (.symbol "else")
      Bindings.empty Bindings.empty rfl
  · simp [IsErrorRel]
  · apply HumanUnifyStep.noMatch
    intro output hcandidate
    obtain ⟨matched, hmatch, _⟩ := hcandidate
    exact symbol_mismatch_not_match (by decide) matched hmatch

/-- Negative switch branch: an empty branch list has no selected result and
therefore reduces to `Empty`. -/
example : HumanCall Space.empty noHostDispatch []
    (.expression [.symbol "switch-minimal", .symbol "a", .expression []])
    Atom.undefinedType Bindings.empty (Atom.empty, Bindings.empty) := by
  apply HumanCall.switchMinimal
      (.expression [.symbol "switch-minimal", .symbol "a", .expression []])
      Atom.undefinedType (.symbol "a") [] Bindings.empty
      (Atom.empty, Bindings.empty) rfl
  · simp [IsErrorRel]
  · exact HumanSwitchStep.noMatch HumanSwitchRawRel.nil

/-- Negative equation-query branch: an empty space returns the atom unchanged. -/
example : HumanCall Space.empty noHostDispatch []
    (.symbol "unreduced") Atom.undefinedType Bindings.empty
    (.symbol "unreduced", Bindings.empty) := by
  apply HumanCall.noEquation
  · rintro ⟨tail, hError⟩
    cases hError
  · trivial
  · intro freshPattern freshRhs matched hmatch
    obtain ⟨rawLhs, rawRhs, hmem, _⟩ := hmatch
    simp [Space.empty] at hmem

private def noReduceDispatch : HumanGroundedDispatch where
  executable := fun operator => operator = .symbol "native"
  outcome := fun operator _ result =>
    operator = .symbol "native" ∧ result = .noReduce

/-- Positive grounded boundary: a host `NoReduce` outcome preserves the call
unchanged without importing an executable dispatcher. -/
example : HumanCall Space.empty noReduceDispatch []
    (.expression [.symbol "native", .symbol "argument"])
    Atom.undefinedType Bindings.empty
    (.expression [.symbol "native", .symbol "argument"], Bindings.empty) := by
  apply HumanCall.groundedNoReduce
      (.expression [.symbol "native", .symbol "argument"])
      Atom.undefinedType (.symbol "native") [.symbol "argument"]
      Bindings.empty rfl
  · rfl
  · decide
  · decide
  · simp [IsErrorRel]
  · exact ⟨rfl, rfl⟩

end Mettapedia.Languages.MeTTa.HE.HumanEvalSpec
