import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat
import Mettapedia.GSLT.LanguageDef.InferenceSupportIndexedABTLowering

/-!
# Direct CeTTa schema-instantiation refinement

The exact CeTTa carrier can be decoded and replayed by the logical checker,
but the native checker does not first construct `Pattern`: it walks the
physical `Var`/`FVar`/`PApp` carrier directly.  This module gives that walk an
independent executable model and proves that it commutes with canonical
Pattern encoding.

The result isolates the remaining native trust boundary precisely.  Canonical
physical schema execution, logical inference instantiation, and the
support-indexed ABT lowering compute the same result; relating the C function
to this executable model remains a source-refinement obligation.
-/

namespace Mettapedia.GSLT.LanguageDef.InferenceCettaExecutionRefinement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceCettaWire
open Mettapedia.GSLT.LanguageDef.InferencePresentationWire
open Mettapedia.GSLT.LanguageDef.InferenceSupportIndexedABTLowering

/-- Physical ordered lookup used by native schema instantiation after a rule
and its arguments have been decoded into arrays. -/
def lookupArgumentAt? :
    List (String × Nat) → List CettaTerm → String → Nat → Option CettaTerm
  | formal :: formals, argument :: arguments, target, depth =>
      if formal = (target, depth) then some argument
      else lookupArgumentAt? formals arguments target depth
  | _, _, _, _ => none

mutual

/-- Direct execution over the physical CeTTa Pattern carrier. -/
def instantiatePatternAt? (formals : List (String × Nat))
    (arguments : List CettaTerm) (depth : Nat) : CettaTerm → Option CettaTerm
  | .application "Var" [.natural index] =>
      some (.application "Var" [.natural index])
  | .application "FVar" [.string name] =>
      lookupArgumentAt? formals arguments name depth
  | .application "PApp" [.string head, schemas] => do
      let results ← instantiatePatternsAt? formals arguments depth schemas
      some (.application "PApp" [.string head, results])
  | .application "PLam" [binder, body] => do
      let result ← instantiatePatternAt? formals arguments (depth + 1) body
      some (.application "PLam" [binder, result])
  | .application "PMultiLam" [.natural arity, binders, body] => do
      let result ← instantiatePatternAt?
        formals arguments (depth + arity) body
      some (.application "PMultiLam" [.natural arity, binders, result])
  | .application "PSubst" [body, replacement] => do
      let bodyResult ← instantiatePatternAt?
        formals arguments (depth + 1) body
      let replacementResult ← instantiatePatternAt?
        formals arguments depth replacement
      some (.application "PSubst" [bodyResult, replacementResult])
  | .application "PCollection"
      [collectionType, schemas, .symbol "RNone"] => do
      let results ← instantiatePatternsAt? formals arguments depth schemas
      some (.application "PCollection"
        [collectionType, results, .symbol "RNone"])
  | _ => none
termination_by schema => sizeOf schema

/-- Direct execution over the physical algebraic list used inside Pattern
constructors. -/
def instantiatePatternsAt? (formals : List (String × Nat))
    (arguments : List CettaTerm) (depth : Nat) : CettaTerm → Option CettaTerm
  | .symbol "LNil" => some (.symbol "LNil")
  | .application "LCons" [schema, schemas] => do
      let result ← instantiatePatternAt? formals arguments depth schema
      let results ← instantiatePatternsAt? formals arguments depth schemas
      some (.application "LCons" [result, results])
  | _ => none
termination_by schemas => sizeOf schemas

end


/-- Physical lookup of canonical encoded arguments is exactly logical
exact-depth lookup followed by Pattern encoding. -/
theorem lookupArgumentAt?_encode
    (formals : List (String × Nat)) (arguments : List Pattern)
    (target : String) (depth : Nat) :
    lookupArgumentAt? formals (arguments.map encodePattern) target depth =
      (InferenceChecker.lookupArgumentAt?
        formals arguments target depth).map encodePattern := by
  induction formals generalizing arguments with
  | nil => rfl
  | cons formal formals inductionHypothesis =>
      cases arguments with
      | nil => rfl
      | cons argument arguments =>
          by_cases hMatch : formal = (target, depth)
          · simp [lookupArgumentAt?, InferenceChecker.lookupArgumentAt?,
              hMatch]
          · simp [lookupArgumentAt?, InferenceChecker.lookupArgumentAt?,
              hMatch, inductionHypothesis]

mutual

/-- Canonical direct physical execution commutes with logical schema
instantiation. -/
@[simp] theorem instantiatePatternAt?_encode
    (formals : List (String × Nat)) (arguments : List Pattern)
    (depth : Nat) (schema : Pattern) :
    instantiatePatternAt? formals (arguments.map encodePattern) depth
        (encodePattern schema) =
      (InferenceChecker.instantiateSchemaAt?
        formals arguments depth schema).map encodePattern := by
  cases schema with
  | bvar index =>
      simp [encodePattern, instantiatePatternAt?,
        InferenceChecker.instantiateSchemaAt?]
  | fvar name =>
      simp [encodePattern, instantiatePatternAt?,
        InferenceChecker.instantiateSchemaAt?, lookupArgumentAt?_encode]
  | apply head schemas =>
      simp only [encodePattern, instantiatePatternAt?]
      rw [instantiatePatternsAt?_encode]
      cases result : InferenceChecker.instantiateSchemasAt?
          formals arguments depth schemas <;>
        simp [InferenceChecker.instantiateSchemaAt?, result, encodePattern]
  | lambda binder body =>
      simp only [encodePattern, instantiatePatternAt?]
      rw [instantiatePatternAt?_encode]
      cases result : InferenceChecker.instantiateSchemaAt?
          formals arguments (depth + 1) body <;>
        simp [InferenceChecker.instantiateSchemaAt?, result, encodePattern]
  | multiLambda arity binders body =>
      simp only [encodePattern, instantiatePatternAt?]
      rw [instantiatePatternAt?_encode]
      cases result : InferenceChecker.instantiateSchemaAt?
          formals arguments (depth + arity) body <;>
        simp [InferenceChecker.instantiateSchemaAt?, result, encodePattern]
  | subst body replacement =>
      simp only [encodePattern, instantiatePatternAt?]
      rw [instantiatePatternAt?_encode, instantiatePatternAt?_encode]
      cases bodyResult : InferenceChecker.instantiateSchemaAt?
          formals arguments (depth + 1) body <;>
        cases replacementResult : InferenceChecker.instantiateSchemaAt?
          formals arguments depth replacement <;>
        simp [InferenceChecker.instantiateSchemaAt?, bodyResult,
          replacementResult, encodePattern]
  | collection collectionType schemas rest =>
      cases rest with
      | none =>
          simp only [encodePattern, encodeRest, instantiatePatternAt?]
          rw [instantiatePatternsAt?_encode]
          cases result : InferenceChecker.instantiateSchemasAt?
              formals arguments depth schemas <;>
            simp [InferenceChecker.instantiateSchemaAt?, result, encodePattern,
              encodeRest]
      | some name =>
          simp [encodePattern, encodeRest, instantiatePatternAt?,
            InferenceChecker.instantiateSchemaAt?]

/-- Canonical direct physical list execution commutes with logical ordered
schema instantiation. -/
@[simp] theorem instantiatePatternsAt?_encode
    (formals : List (String × Nat)) (arguments : List Pattern)
    (depth : Nat) (schemas : List Pattern) :
    instantiatePatternsAt? formals (arguments.map encodePattern) depth
        (encodePatterns schemas) =
      (InferenceChecker.instantiateSchemasAt?
        formals arguments depth schemas).map encodePatterns := by
  cases schemas with
  | nil =>
      simp [encodePatterns, instantiatePatternsAt?,
        InferenceChecker.instantiateSchemasAt?]
  | cons schema schemas =>
      simp only [encodePatterns, instantiatePatternsAt?]
      rw [instantiatePatternAt?_encode, instantiatePatternsAt?_encode]
      cases headResult : InferenceChecker.instantiateSchemaAt?
          formals arguments depth schema <;>
        cases tailResult : InferenceChecker.instantiateSchemasAt?
          formals arguments depth schemas <;>
        simp [InferenceChecker.instantiateSchemasAt?, headResult, tailResult,
          encodePatterns]

end


/-- On canonical physical inputs, successful direct execution has exactly the
same result as logical schema instantiation. -/
theorem instantiatePatternAt?_eq_some_iff
    (formals : List (String × Nat)) (arguments : List Pattern)
    (depth : Nat) (schema result : Pattern) :
    instantiatePatternAt? formals (arguments.map encodePattern) depth
        (encodePattern schema) = some (encodePattern result) ↔
      InferenceChecker.instantiateSchemaAt?
        formals arguments depth schema = some result := by
  rw [instantiatePatternAt?_encode]
  cases logicalResult :
      InferenceChecker.instantiateSchemaAt?
        formals arguments depth schema with
  | none => simp
  | some actual =>
      simp only [Option.map, Option.some.injEq]
      constructor
      · intro equality
        exact encodePattern_injective equality
      · intro equality
        exact congrArg encodePattern equality

/-- A successful direct physical instantiation of an admitted rule schema
therefore has the same support-indexed ABT meaning. -/
theorem physical_rule_schema_refines_abt
    {rule : RuleSchema} {arguments : List Pattern}
    {schema result : Pattern}
    (ruleValid : RuleSchema.isValidV1 rule = true)
    (argumentsValid :
      InferenceChecker.argumentsValidAt
        rule.metavariables arguments = true)
    (physical :
      instantiatePatternAt? rule.metavariables
          (arguments.map encodePattern) 0 (encodePattern schema) =
        some (encodePattern result)) :
    ContextSupport.substituteAt
        (supportOfFormals rule.metavariables)
        (assignmentOfArguments rule.metavariables arguments) 0 schema =
      result := by
  apply ruleSchema_instantiate_eq_supportSubstitution
    ruleValid argumentsValid
  exact (instantiatePatternAt?_eq_some_iff
    rule.metavariables arguments 0 schema result).mp physical

/-! ## CeTTa-shaped bottom-up replay

The native checker does not recursively compare a child against an expected
premise.  It first evaluates every child, retains the resulting judgments in
order, then applies the parent rule and compares the complete child vector to
the instantiated premise vector.  The definitions below model that control
flow independently.  The physical version additionally uses the exact
CeTTa-term instantiator above rather than constructing logical `Pattern`
results.

This is still a model of the C algorithm, not a theorem about the C source.
The commutation and adequacy theorems isolate the remaining source-refinement
obligation to the implementation of this small bottom-up machine.
-/

/-- Instantiate an array of physical schemas, matching the native rule
record's premise array rather than its serialized `LCons` representation. -/
def instantiatePatternArrayAt? (formals : List (String × Nat))
    (arguments : List CettaTerm) (depth : Nat) :
    List CettaTerm → Option (List CettaTerm)
  | [] => some []
  | schema :: schemas => do
      let result ← instantiatePatternAt? formals arguments depth schema
      let results ← instantiatePatternArrayAt?
        formals arguments depth schemas
      some (result :: results)

/-- Physical premise-array execution commutes with logical ordered schema
instantiation on canonical inputs. -/
@[simp] theorem instantiatePatternArrayAt?_encode
    (formals : List (String × Nat)) (arguments : List Pattern)
    (depth : Nat) (schemas : List Pattern) :
    instantiatePatternArrayAt? formals (arguments.map encodePattern) depth
        (schemas.map encodePattern) =
      (InferenceChecker.instantiateSchemasAt?
        formals arguments depth schemas).map (List.map encodePattern) := by
  induction schemas with
  | nil =>
      simp [instantiatePatternArrayAt?,
        InferenceChecker.instantiateSchemasAt?]
  | cons schema schemas inductionHypothesis =>
      simp only [List.map_cons, instantiatePatternArrayAt?,
        InferenceChecker.instantiateSchemasAt?]
      rw [instantiatePatternAt?_encode, inductionHypothesis]
      cases headResult : InferenceChecker.instantiateSchemaAt?
          formals arguments depth schema <;>
        cases tailResult : InferenceChecker.instantiateSchemasAt?
          formals arguments depth schemas <;>
        simp

/-- Encode the physical result record returned by one native rule
application. -/
def encodeRuleResult (result : List Pattern × Pattern) :
    List CettaTerm × CettaTerm :=
  (result.1.map encodePattern, encodePattern result.2)

/-- One local rule application through the exact physical premise array and
physical conclusion walker.  Catalog lookup, argument admission, and generic
side conditions are deliberately repeated rather than delegated to the
logical local checker. -/
def physicalInstantiateRule? (presentation : RuntimePresentation)
    (ruleInstance : RuleInstance) :
    Option (List CettaTerm × CettaTerm) :=
  match presentation.lookupRule? ruleInstance.ruleId with
  | none => none
  | some rule =>
      if presentation.argumentsValidAt
          rule.metavariables ruleInstance.arguments then do
        if RuleSchema.sideConditionsHold
            rule ruleInstance.arguments then do
          let premises ← instantiatePatternArrayAt? rule.metavariables
            (ruleInstance.arguments.map encodePattern) 0
            (rule.premises.map encodePattern)
          let conclusion ← instantiatePatternAt? rule.metavariables
            (ruleInstance.arguments.map encodePattern) 0
            (encodePattern rule.conclusion)
          some (premises, conclusion)
        else
          none
      else
        none

/-- The independently stated physical local application computes exactly the
canonical encoding of the closed-payload runtime application. -/
theorem physicalInstantiateRule?_encode
    (presentation : RuntimePresentation) (ruleInstance : RuleInstance) :
    physicalInstantiateRule? presentation ruleInstance =
      (presentation.instantiateRule? ruleInstance).map encodeRuleResult := by
  simp only [physicalInstantiateRule?, RuntimePresentation.instantiateRule?]
  cases lookup : presentation.lookupRule? ruleInstance.ruleId with
  | none => simp
  | some rule =>
      cases arguments : presentation.argumentsValidAt
          rule.metavariables ruleInstance.arguments with
      | false => simp [arguments]
      | true =>
          cases sideConditions : RuleSchema.sideConditionsHold
              rule ruleInstance.arguments with
          | false => simp [arguments, sideConditions]
          | true =>
              simp only [arguments, sideConditions, ite_true]
              unfold InferenceChecker.instantiateSchemas?
                InferenceChecker.instantiateSchema?
              rw [instantiatePatternArrayAt?_encode,
                instantiatePatternAt?_encode]
              cases premisesResult :
                  InferenceChecker.instantiateSchemasAt?
                    rule.metavariables ruleInstance.arguments 0
                    rule.premises with
              | none => simp
              | some premises =>
                  cases conclusionResult :
                      InferenceChecker.instantiateSchemaAt?
                        rule.metavariables ruleInstance.arguments 0
                        rule.conclusion with
                  | none => simp
                  | some conclusion =>
                      simp [encodeRuleResult]

/-- Decode the native premise array back into canonical logical Patterns.
This is separate from the serialized `LCons` decoder because the C rule
record stores premises in a flat array after admission. -/
def decodePatternArray? : List CettaTerm → Option (List Pattern)
  | [] => some []
  | term :: terms => do
      let pattern ← decodePattern term
      let patterns ← decodePatternArray? terms
      some (pattern :: patterns)

@[simp] theorem decodePatternArray?_encode (patterns : List Pattern) :
    decodePatternArray? (patterns.map encodePattern) = some patterns := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns inductionHypothesis =>
      simp [decodePatternArray?, inductionHypothesis]

/-- Canonical physical-array equality.  Malformed physical terms fail closed;
on admitted arrays this is exactly structural Pattern equality. -/
def physicalPatternArraysEqual
    (left right : List CettaTerm) : Bool :=
  match decodePatternArray? left, decodePatternArray? right with
  | some leftPatterns, some rightPatterns => decide (leftPatterns = rightPatterns)
  | _, _ => false

@[simp] theorem physicalPatternArraysEqual_encode
    (left right : List Pattern) :
    physicalPatternArraysEqual
        (left.map encodePattern) (right.map encodePattern) =
      decide (left = right) := by
  simp [physicalPatternArraysEqual]

mutual

/-- Independent bottom-up logical replay.  Children are evaluated before the
parent rule, matching CeTTa's explicit-frame traversal. -/
def bottomUpReplay? (presentation : RuntimePresentation) :
    RawProof → Option Pattern
  | .node ruleInstance children => do
      let childConclusions ← bottomUpReplayList? presentation children
      let localResult ← presentation.instantiateRule? ruleInstance
      if childConclusions = localResult.1 then
        some localResult.2
      else
        none
termination_by proof => sizeOf proof

def bottomUpReplayList? (presentation : RuntimePresentation) :
    List RawProof → Option (List Pattern)
  | [] => some []
  | proof :: proofs => do
      let conclusion ← bottomUpReplay? presentation proof
      let conclusions ← bottomUpReplayList? presentation proofs
      some (conclusion :: conclusions)
termination_by proofs => sizeOf proofs

end

mutual

/-- Physical bottom-up replay over canonical CeTTa terms. -/
def physicalBottomUpReplay? (presentation : RuntimePresentation) :
    RawProof → Option CettaTerm
  | .node ruleInstance children => do
      let childConclusions ← physicalBottomUpReplayList? presentation children
      let localResult ← physicalInstantiateRule? presentation ruleInstance
      if physicalPatternArraysEqual childConclusions localResult.1 then
        some localResult.2
      else
        none
termination_by proof => sizeOf proof

def physicalBottomUpReplayList? (presentation : RuntimePresentation) :
    List RawProof → Option (List CettaTerm)
  | [] => some []
  | proof :: proofs => do
      let conclusion ← physicalBottomUpReplay? presentation proof
      let conclusions ← physicalBottomUpReplayList? presentation proofs
      some (conclusion :: conclusions)
termination_by proofs => sizeOf proofs

end


mutual

/-- Bottom-up replay directly over the physical `GProof` carrier.  Unlike
`InferenceCettaWire.decodeRawProof`, this function does not first allocate a
logical proof tree: it parses one node, evaluates its physical child list,
then applies the parent rule.  This is the control shape of CeTTa's explicit
raw-proof frame machine. -/
def physicalBottomUpReplayTerm? (presentation : RuntimePresentation) :
    CettaTerm → Option CettaTerm
  | .application "GProof" [ruleInstanceTerm, childrenTerm] => do
      let ruleInstance ← decodeRuleInstance ruleInstanceTerm
      let childConclusions ←
        physicalBottomUpReplayTerms? presentation childrenTerm
      let localResult ← physicalInstantiateRule? presentation ruleInstance
      if physicalPatternArraysEqual childConclusions localResult.1 then
        some localResult.2
      else
        none
  | _ => none
termination_by term => sizeOf term

/-- Direct traversal of CeTTa's canonical `PrNil`/`PrCons` proof list. -/
def physicalBottomUpReplayTerms? (presentation : RuntimePresentation) :
    CettaTerm → Option (List CettaTerm)
  | .symbol "PrNil" => some []
  | .application "PrCons" [proofTerm, proofTerms] => do
      let conclusion ← physicalBottomUpReplayTerm? presentation proofTerm
      let conclusions ← physicalBottomUpReplayTerms? presentation proofTerms
      some (conclusion :: conclusions)
  | _ => none
termination_by term => sizeOf term

end


mutual

/-- Canonical proof encoding followed by the direct physical traversal is
exactly the isolated physical bottom-up machine. -/
@[simp] theorem physicalBottomUpReplayTerm?_encode
    (presentation : RuntimePresentation) (proof : RawProof) :
    physicalBottomUpReplayTerm? presentation (encodeRawProof proof) =
      physicalBottomUpReplay? presentation proof := by
  cases proof with
  | node ruleInstance children =>
      simp only [encodeRawProof, physicalBottomUpReplayTerm?,
        physicalBottomUpReplay?]
      rw [decodeRuleInstance_encodeRuleInstance,
        physicalBottomUpReplayTerms?_encode]
      simp

/-- Canonical proof-list encoding commutes with direct physical traversal. -/
@[simp] theorem physicalBottomUpReplayTerms?_encode
    (presentation : RuntimePresentation) (proofs : List RawProof) :
    physicalBottomUpReplayTerms? presentation (encodeProofs proofs) =
      physicalBottomUpReplayList? presentation proofs := by
  cases proofs with
  | nil =>
      simp [encodeProofs, physicalBottomUpReplayTerms?,
        physicalBottomUpReplayList?]
  | cons proof proofs =>
      simp only [encodeProofs, physicalBottomUpReplayTerms?,
        physicalBottomUpReplayList?]
      rw [physicalBottomUpReplayTerm?_encode,
        physicalBottomUpReplayTerms?_encode]

end


/-- Canonical Pattern-list encoding is collision-free. -/
theorem encodePatternList_injective :
    Function.Injective (List.map encodePattern) :=
  List.map_injective_iff.mpr encodePattern_injective

mutual

/-- The physical bottom-up machine is pointwise the canonical encoding of the
independent logical bottom-up machine. -/
@[simp] theorem physicalBottomUpReplay?_commutes
    (presentation : RuntimePresentation) (proof : RawProof) :
    physicalBottomUpReplay? presentation proof =
      (bottomUpReplay? presentation proof).map encodePattern := by
  cases proof with
  | node ruleInstance children =>
      simp only [physicalBottomUpReplay?, bottomUpReplay?]
      rw [physicalBottomUpReplayList?_commutes,
        physicalInstantiateRule?_encode]
      cases childResult : bottomUpReplayList? presentation children with
      | none => simp
      | some childConclusions =>
          cases localResult : presentation.instantiateRule? ruleInstance with
          | none => simp
          | some result =>
              rcases result with ⟨premises, conclusion⟩
              by_cases hMatches : childConclusions = premises
              · simp [encodeRuleResult, hMatches]
              · simp [encodeRuleResult, hMatches]
termination_by sizeOf proof

@[simp] theorem physicalBottomUpReplayList?_commutes
    (presentation : RuntimePresentation) (proofs : List RawProof) :
    physicalBottomUpReplayList? presentation proofs =
      (bottomUpReplayList? presentation proofs).map
        (List.map encodePattern) := by
  cases proofs with
  | nil =>
      simp [physicalBottomUpReplayList?, bottomUpReplayList?]
  | cons proof proofs =>
      simp only [physicalBottomUpReplayList?, bottomUpReplayList?]
      rw [physicalBottomUpReplay?_commutes,
        physicalBottomUpReplayList?_commutes]
      cases headResult : bottomUpReplay? presentation proof <;>
        cases tailResult : bottomUpReplayList? presentation proofs <;>
        simp
termination_by sizeOf proofs

end


mutual

/-- Bottom-up replay accepts exactly the same goal as the structurally
recursive closed-payload checker. -/
theorem bottomUpReplay?_eq_some_iff_checkRaw
    (presentation : RuntimePresentation) (proof : RawProof) (goal : Pattern) :
    bottomUpReplay? presentation proof = some goal ↔
      presentation.checkRaw goal proof = true := by
  cases proof with
  | node ruleInstance children =>
      simp only [bottomUpReplay?, RuntimePresentation.checkRaw]
      cases localResult : presentation.instantiateRule? ruleInstance with
      | none =>
          cases childResult : bottomUpReplayList? presentation children <;>
            simp
      | some result =>
          rcases result with ⟨premises, conclusion⟩
          cases childResult : bottomUpReplayList? presentation children with
          | none =>
              have childrenReject :
                  presentation.checkRawChildren premises children ≠ true := by
                intro accepted
                have replayed :=
                  (bottomUpReplayList?_eq_some_iff_checkRaw
                    presentation children premises).2 accepted
                rw [childResult] at replayed
                contradiction
              have childrenFalse :
                  presentation.checkRawChildren premises children = false :=
                Bool.eq_false_of_not_eq_true childrenReject
              simp [childrenFalse]
          | some childConclusions =>
              have childrenIff :=
                bottomUpReplayList?_eq_some_iff_checkRaw
                  presentation children premises
              rw [childResult] at childrenIff
              simp only [Option.some.injEq] at childrenIff
              by_cases hMatches : childConclusions = premises
              · have childrenAccepted := childrenIff.mp hMatches
                simp [hMatches, childrenAccepted]
              · have childrenReject :
                    presentation.checkRawChildren premises children ≠ true := by
                  intro accepted
                  exact hMatches (childrenIff.mpr accepted)
                have childrenFalse :
                    presentation.checkRawChildren premises children = false :=
                  Bool.eq_false_of_not_eq_true childrenReject
                simp [hMatches, childrenFalse]
termination_by sizeOf proof

theorem bottomUpReplayList?_eq_some_iff_checkRaw
    (presentation : RuntimePresentation) (proofs : List RawProof)
    (goals : List Pattern) :
    bottomUpReplayList? presentation proofs = some goals ↔
      presentation.checkRawChildren goals proofs = true := by
  cases proofs with
  | nil =>
      cases goals <;>
        simp [bottomUpReplayList?, RuntimePresentation.checkRawChildren]
  | cons proof proofs =>
      cases goals with
      | nil =>
          cases headResult : bottomUpReplay? presentation proof <;>
            cases tailResult : bottomUpReplayList? presentation proofs <;>
            simp [bottomUpReplayList?, headResult, tailResult,
              RuntimePresentation.checkRawChildren]
      | cons goal goals =>
          simp only [bottomUpReplayList?,
            RuntimePresentation.checkRawChildren, Bool.and_eq_true]
          cases headResult : bottomUpReplay? presentation proof with
          | none =>
              have headReject : presentation.checkRaw goal proof ≠ true := by
                intro accepted
                have replayed :=
                  (bottomUpReplay?_eq_some_iff_checkRaw
                    presentation proof goal).2 accepted
                rw [headResult] at replayed
                contradiction
              simp [headReject]
          | some conclusion =>
              cases tailResult : bottomUpReplayList? presentation proofs with
              | none =>
                  have tailReject :
                      presentation.checkRawChildren goals proofs ≠ true := by
                    intro accepted
                    have replayed :=
                      (bottomUpReplayList?_eq_some_iff_checkRaw
                        presentation proofs goals).2 accepted
                    rw [tailResult] at replayed
                    contradiction
                  simp [tailReject]
              | some conclusions =>
                  have headIff := bottomUpReplay?_eq_some_iff_checkRaw
                    presentation proof goal
                  have tailIff := bottomUpReplayList?_eq_some_iff_checkRaw
                    presentation proofs goals
                  rw [headResult] at headIff
                  rw [tailResult] at tailIff
                  simp only [Option.some.injEq] at headIff tailIff
                  constructor
                  · intro equality
                    cases equality
                    exact ⟨headIff.mp rfl, tailIff.mp rfl⟩
                  · rintro ⟨headAccepted, tailAccepted⟩
                    rw [headIff.mpr headAccepted, tailIff.mpr tailAccepted]
                    rfl
termination_by sizeOf proofs

end


/-- End-to-end physical bottom-up acceptance is exactly closed-payload runtime
acceptance. -/
theorem physicalBottomUpReplay?_eq_some_iff_checkRaw
    (presentation : RuntimePresentation) (proof : RawProof) (goal : Pattern) :
    physicalBottomUpReplay? presentation proof =
        some (encodePattern goal) ↔
      presentation.checkRaw goal proof = true := by
  rw [physicalBottomUpReplay?_commutes]
  cases replay : bottomUpReplay? presentation proof with
  | none =>
      have reject : presentation.checkRaw goal proof ≠ true := by
        intro accepted
        have result := (bottomUpReplay?_eq_some_iff_checkRaw
          presentation proof goal).2 accepted
        rw [replay] at result
        contradiction
      simp [reject]
  | some conclusion =>
      have logicalIff := bottomUpReplay?_eq_some_iff_checkRaw
        presentation proof goal
      rw [replay] at logicalIff
      simp only [Option.some.injEq] at logicalIff
      simp only [Option.map, Option.some.injEq]
      exact encodePattern_injective.eq_iff.trans logicalIff

/-- Direct execution of the canonical physical proof carrier accepts exactly
when the closed-payload runtime checker accepts the corresponding article. -/
theorem physicalBottomUpReplayTerm?_eq_some_iff_checkRaw
    (presentation : RuntimePresentation) (proof : RawProof) (goal : Pattern) :
    physicalBottomUpReplayTerm? presentation (encodeRawProof proof) =
        some (encodePattern goal) ↔
      presentation.checkRaw goal proof = true := by
  rw [physicalBottomUpReplayTerm?_encode,
    physicalBottomUpReplay?_eq_some_iff_checkRaw]

/-- The direct physical traversal and the packet decoder agree on acceptance
of every canonical CeTTa presentation, goal, and article packet. -/
theorem physicalBottomUpReplayTerm?_iff_checkPacket
    (presentation : RuntimePresentation) (proof : RawProof) (goal : Pattern) :
    physicalBottomUpReplayTerm? presentation (encodeRawProof proof) =
        some (encodePattern goal) ↔
      checkPacket (encodeRuntimePresentation presentation)
          (encodePattern goal) (encodeRawProof proof) = some true := by
  rw [physicalBottomUpReplayTerm?_eq_some_iff_checkRaw, checkPacket_encode]
  simp

/-! ## Whole-rule and whole-article physical certificates -/

/-- One authenticated rule application whose premise vector and conclusion
have both been replayed by the direct physical carrier walk.  The companion
`ABTRuleApplication` retains the exact support-indexed meaning of those
physical computations. -/
inductive PhysicalABTRuleApplication (presentation : ValidatedPresentation)
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern) : Prop where
  | intro (rule : RuleSchema)
      (lookup : presentation.1.lookupRule? ruleInstance.ruleId = some rule)
      (premisesPhysical :
        instantiatePatternsAt? rule.metavariables
            (ruleInstance.arguments.map encodePattern) 0
            (encodePatterns rule.premises) =
          some (encodePatterns premises))
      (conclusionPhysical :
        instantiatePatternAt? rule.metavariables
            (ruleInstance.arguments.map encodePattern) 0
            (encodePattern rule.conclusion) =
          some (encodePattern conclusion))
      (abt : ABTRuleApplication
        presentation ruleInstance premises conclusion) :
      PhysicalABTRuleApplication
        presentation ruleInstance premises conclusion

/-- Every admitted logical application has a direct physical replay and a
support-indexed ABT certificate with the same endpoints. -/
theorem ruleApplication_toPhysicalABTRuleApplication
    {presentation : ValidatedPresentation} {ruleInstance : RuleInstance}
    {premises : List Pattern} {conclusion : Pattern}
    (application :
      RuleApplication presentation ruleInstance premises conclusion) :
    PhysicalABTRuleApplication
      presentation ruleInstance premises conclusion := by
  cases application with
  | intro rule lookup argumentsValid sideConditionsValid
      premisesInstantiate conclusionInstantiates =>
      have premisesLogical :
          InferenceChecker.instantiateSchemasAt? rule.metavariables
              ruleInstance.arguments 0 rule.premises = some premises :=
        InferenceChecker.instantiateSchemasAt?_complete premisesInstantiate
      have conclusionLogical :
          InferenceChecker.instantiateSchemaAt? rule.metavariables
              ruleInstance.arguments 0 rule.conclusion = some conclusion :=
        InferenceChecker.instantiateSchemaAt?_complete
          conclusionInstantiates
      refine .intro rule lookup ?_ ?_
        (ruleApplication_toABTRuleApplication (.intro rule lookup
          argumentsValid sideConditionsValid premisesInstantiate
          conclusionInstantiates))
      · rw [instantiatePatternsAt?_encode, premisesLogical]
        rfl
      · rw [instantiatePatternAt?_encode, conclusionLogical]
        rfl

mutual

/-- A proof-relevant article whose every node has been replayed by the direct
physical carrier walk and lowered to support-indexed ABT. -/
inductive PhysicalABTDerivation
    (presentation : ValidatedPresentation) : Pattern → Type where
  | byRule (ruleInstance : RuleInstance) {premises : List Pattern}
      {conclusion : Pattern}
      (application : PhysicalABTRuleApplication
        presentation ruleInstance premises conclusion)
      (children : PhysicalABTDerivationList presentation premises) :
      PhysicalABTDerivation presentation conclusion

inductive PhysicalABTDerivationList
    (presentation : ValidatedPresentation) : List Pattern → Type where
  | nil : PhysicalABTDerivationList presentation []
  | cons {premise : Pattern} {premises : List Pattern}
      (head : PhysicalABTDerivation presentation premise)
      (tail : PhysicalABTDerivationList presentation premises) :
      PhysicalABTDerivationList presentation (premise :: premises)

end

mutual

/-- Replay an authenticated logical derivation through the direct physical
carrier at every node. -/
def derivationToPhysicalABT
    {presentation : ValidatedPresentation} {goal : Pattern} :
    Derivation presentation goal → PhysicalABTDerivation presentation goal
  | .byRule ruleInstance application children =>
      .byRule ruleInstance
        (ruleApplication_toPhysicalABTRuleApplication application)
        (derivationListToPhysicalABT children)

def derivationListToPhysicalABT
    {presentation : ValidatedPresentation} {premises : List Pattern} :
    DerivationList presentation premises →
      PhysicalABTDerivationList presentation premises
  | .nil => .nil
  | .cons head tail =>
      .cons (derivationToPhysicalABT head)
        (derivationListToPhysicalABT tail)

end


mutual

/-- Erase a direct-physical derivation to its chronological proof article. -/
def PhysicalABTDerivation.erase
    {presentation : ValidatedPresentation} {goal : Pattern} :
    PhysicalABTDerivation presentation goal → RawProof
  | .byRule ruleInstance _ children =>
      .node ruleInstance (PhysicalABTDerivationList.erase children)

def PhysicalABTDerivationList.erase
    {presentation : ValidatedPresentation} {premises : List Pattern} :
    PhysicalABTDerivationList presentation premises → List RawProof
  | .nil => []
  | .cons head tail => head.erase :: tail.erase

end


mutual

/-- Direct physical replay preserves the exact chronological article. -/
@[simp] theorem derivationToPhysicalABT_erase
    {presentation : ValidatedPresentation} {goal : Pattern}
    (derivation : Derivation presentation goal) :
    PhysicalABTDerivation.erase (derivationToPhysicalABT derivation) =
      Derivation.erase derivation := by
  cases derivation with
  | byRule ruleInstance application children =>
      simp [derivationToPhysicalABT, PhysicalABTDerivation.erase,
        derivationListToPhysicalABT_erase children, Derivation.erase]

@[simp] theorem derivationListToPhysicalABT_erase
    {presentation : ValidatedPresentation} {premises : List Pattern}
    (derivations : DerivationList presentation premises) :
    PhysicalABTDerivationList.erase
        (derivationListToPhysicalABT derivations) =
      DerivationList.erase derivations := by
  cases derivations with
  | nil => rfl
  | cons head tail =>
      simp [derivationListToPhysicalABT,
        PhysicalABTDerivationList.erase,
        derivationToPhysicalABT_erase head,
        derivationListToPhysicalABT_erase tail,
        DerivationList.erase]

end

/-! ## End-to-end physical acceptance -/

/-- A physical bottom-up acceptance under the exact projection of a validated
presentation yields a proof-relevant derivation whose every rule node carries
the direct physical instantiation and support-indexed ABT witness. -/
theorem physicalBottomUpReplay_acceptance_refines_abt
    (presentation : ValidatedPresentation) (proof : RawProof) (goal : Pattern)
    (accepted :
      physicalBottomUpReplay?
          (RuntimePresentation.ofPresentation presentation.1) proof =
        some (encodePattern goal)) :
    ∃ derivation : PhysicalABTDerivation presentation goal,
      derivation.erase = proof := by
  have runtimeAccepted :
      (RuntimePresentation.ofPresentation presentation.1).checkRaw
          goal proof = true :=
    (physicalBottomUpReplay?_eq_some_iff_checkRaw
      (RuntimePresentation.ofPresentation presentation.1) proof goal).mp
        accepted
  have logicalAccepted := RuntimePresentation.checkRaw_sound
    presentation goal proof runtimeAccepted
  rcases G2_checkRaw_iff_exists_derivation_erases_to.mp logicalAccepted with
    ⟨derivation, erases⟩
  exact ⟨derivationToPhysicalABT derivation,
    (derivationToPhysicalABT_erase derivation).trans erases⟩

/-! ## Physical execution canaries -/

private def bottomUpCanaryGoal : Pattern :=
  .apply "J" [.apply "Unit" []]

private def bottomUpCanaryRule : RuleSchema :=
  { id := ⟨"unit-introduction"⟩
    metavariables := []
    premises := []
    conclusion := bottomUpCanaryGoal
    sideConditions := [] }

private def bottomUpCanaryPresentation : RuntimePresentation :=
  { constructors := [⟨"Unit", 0⟩]
    judgments := [⟨"J", 1⟩]
    rules := [bottomUpCanaryRule]
    conversion := none }

private def bottomUpCanaryProof : RawProof :=
  .node ⟨⟨"unit-introduction"⟩, []⟩ []

/-- Positive whole-machine canary: a premise-free physical rule application
returns its canonical conclusion. -/
theorem physical_bottom_up_canary_accepts :
    physicalBottomUpReplay? bottomUpCanaryPresentation bottomUpCanaryProof =
      some (encodePattern bottomUpCanaryGoal) := by
  rw [physicalBottomUpReplay?_commutes]
  simp [bottomUpReplay?, bottomUpReplayList?, bottomUpCanaryPresentation,
    bottomUpCanaryProof, bottomUpCanaryRule, bottomUpCanaryGoal,
    RuntimePresentation.lookupRule?, RuntimePresentation.instantiateRule?,
    RuntimePresentation.argumentsValidAt, RuleSchema.sideConditionsHold,
    InferenceChecker.instantiateSchemas?,
    InferenceChecker.instantiateSchemasAt?,
    InferenceChecker.instantiateSchema?,
    InferenceChecker.instantiateSchemaAt?]

/-- Negative whole-machine canary: an extra child cannot be hidden under a
premise-free rule.  This is the source-level role of CeTTa's per-frame stack
base accounting. -/
theorem physical_bottom_up_extra_child_rejects :
    physicalBottomUpReplay? bottomUpCanaryPresentation
        (.node ⟨⟨"unit-introduction"⟩, []⟩ [bottomUpCanaryProof]) =
      none := by
  rw [physicalBottomUpReplay?_commutes]
  simp [bottomUpReplay?, bottomUpReplayList?, bottomUpCanaryPresentation,
    bottomUpCanaryProof, bottomUpCanaryRule, bottomUpCanaryGoal,
    RuntimePresentation.lookupRule?, RuntimePresentation.instantiateRule?,
    RuntimePresentation.argumentsValidAt, RuleSchema.sideConditionsHold,
    InferenceChecker.instantiateSchemas?,
    InferenceChecker.instantiateSchemasAt?,
    InferenceChecker.instantiateSchema?,
    InferenceChecker.instantiateSchemaAt?]

/-- Positive wire-level canary: direct traversal of the physical proof packet
returns the physical goal without first constructing a logical proof tree. -/
theorem physical_wire_bottom_up_canary_accepts :
    physicalBottomUpReplayTerm? bottomUpCanaryPresentation
        (encodeRawProof bottomUpCanaryProof) =
      some (encodePattern bottomUpCanaryGoal) := by
  rw [physicalBottomUpReplayTerm?_encode]
  exact physical_bottom_up_canary_accepts

/-- Negative wire-level canary: proof children use `PrNil`, not the
presentation-list terminator `LNil`; a cross-sorted list forgery fails
closed. -/
theorem physical_wire_wrong_list_sort_rejects :
    physicalBottomUpReplayTerm? bottomUpCanaryPresentation
        (.application "GProof"
          [encodeRuleInstance ⟨⟨"unit-introduction"⟩, []⟩,
            .symbol "LNil"]) = none := by
  simp [physicalBottomUpReplayTerm?, physicalBottomUpReplayTerms?]

private def canaryFormals : List (String × Nat) :=
  [("body", 1), ("value", 0)]

private def canaryArguments : List Pattern :=
  [.bvar 0, .apply "Unit" []]

private def canarySchema : Pattern :=
  .apply "HasType" [.lambda none (.fvar "body"), .fvar "value"]

/-- The direct physical walk retains a depth-one argument under its binder. -/
theorem physical_supported_binder_instantiation_accepts :
    instantiatePatternAt? canaryFormals
        (canaryArguments.map encodePattern) 0 (encodePattern canarySchema) =
      some (encodePattern
        (.apply "HasType"
          [.lambda none (.bvar 0), .apply "Unit" []])) := by
  rw [instantiatePatternAt?_encode]
  simp [canaryFormals, canaryArguments, canarySchema,
    InferenceChecker.instantiateSchemaAt?,
    InferenceChecker.instantiateSchemasAt?,
    InferenceChecker.lookupArgumentAt?]

/-- A free variable at an undeclared occurrence depth fails closed. -/
theorem physical_wrong_depth_instantiation_rejects :
    instantiatePatternAt? [("body", 0)] [encodePattern (.bvar 0)] 1
        (encodePattern (.fvar "body")) = none := by
  change instantiatePatternAt? [("body", 0)]
      (([.bvar 0] : List Pattern).map encodePattern) 1
        (encodePattern (.fvar "body")) = none
  rw [instantiatePatternAt?_encode]
  simp [InferenceChecker.instantiateSchemaAt?,
    InferenceChecker.lookupArgumentAt?]

/-- A collection-rest metavariable is outside the executable physical
profile, matching logical schema instantiation. -/
theorem physical_collection_rest_rejects :
    instantiatePatternAt? [] [] 0
        (encodePattern (.collection .vec [] (some "rest"))) = none := by
  change instantiatePatternAt? []
      (([] : List Pattern).map encodePattern) 0
        (encodePattern (.collection .vec [] (some "rest"))) = none
  rw [instantiatePatternAt?_encode]
  simp [InferenceChecker.instantiateSchemaAt?]

end Mettapedia.GSLT.LanguageDef.InferenceCettaExecutionRefinement
