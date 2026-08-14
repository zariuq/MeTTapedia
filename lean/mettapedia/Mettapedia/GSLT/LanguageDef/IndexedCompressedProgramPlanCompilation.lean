import Mettapedia.GSLT.LanguageDef.IndexedEffectMachinePhysicalRefinement
import Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation

/-!
# Generated compressed-program plan compilation

A public indexed proof path needs one generated program, not a collection of
runtime guesses.  This module models the composite record emitted from an
authored call site, its numeric decoder, its split value carrier, and its
effect plan.  Admission checks the composite against the independently
generated component records and fails closed on every mismatch.

Nothing in the construction names a guest language.  Three independent byte
alphabets below witness that the plan is data interpreted by one fixed
compiler interface; the third has five source kinds and is the additive
inventory canary.
-/

namespace Mettapedia.GSLT.LanguageDef.IndexedCompressedProgramPlanCompilation

open IndexedInstructionStreamCompilation
open IndexedEffectMachinePhysicalRefinement

structure IndexedValueRecord where
  operation : String
  actionIndex : UInt32
  machine : String
  headerRole : String
  codeRole : String
  carrier : String
  region : String
  deriving DecidableEq, Repr

inductive PreparedAction where
  | pushDeclared
  | applyFrame
  deriving DecidableEq, Repr

def preparedActionName : PreparedAction → String
  | .pushDeclared => "stack-push-declared-v1"
  | .applyFrame => "stack-apply-frame-v1"

def decodePreparedAction? (name : String) : Option PreparedAction :=
  if name = preparedActionName .pushDeclared then some .pushDeclared
  else if name = preparedActionName .applyFrame then some .applyFrame
  else none

structure GeneratedActionCaseRecord where
  machine : String
  sourceKind : String
  action : String
  deriving DecidableEq, Repr

structure PreparedActionCase where
  sourceKind : String
  action : PreparedAction
  deriving DecidableEq, Repr

structure PreparedActionPlan where
  cases : List PreparedActionCase
  deriving DecidableEq, Repr

def PreparedActionPlan.valid (plan : PreparedActionPlan) : Bool :=
  !plan.cases.isEmpty && decide (plan.cases.map (·.sourceKind)).Nodup

/-- The 22-field composite record and its variable generated action relation. -/
structure GeneratedProgramRecord where
  operation : String
  actionIndex : UInt32
  machine : String
  headerRole : String
  codeRole : String
  terminalLow : UInt8
  terminalHigh : UInt8
  continuationLow : UInt8
  continuationHigh : UInt8
  saveByte : UInt8
  unknownByte : UInt8
  terminalRadix : UInt32
  terminalDigitBias : UInt32
  continuationRadix : UInt32
  continuationDigitBias : UInt32
  unknownPolicy : UnknownPolicy
  indexedCarrier : String
  effectCarrier : String
  preparedEffect : String
  savedEffect : String
  saveEffect : String
  region : String
  actionCases : List GeneratedActionCaseRecord
  deriving DecidableEq, Repr

structure ProgramRequest where
  operation : String
  actionIndex : UInt32
  machine : String
  headerRole : String
  codeRole : String
  unknownPolicy : UnknownPolicy
  region : String
  deriving DecidableEq, Repr

/-- Independently generated execution authority for one proof machine.  The
unknown token remains part of the public normal-proof semantics; the numeric
decoder and unknown policy must also agree with any optimized indexed program
that claims to implement this machine. -/
structure GeneratedExecutionDescriptor where
  machine : String
  unknownToken : String
  decoder : Plan
  unknownPolicy : UnknownPolicy
  deriving DecidableEq, Repr

def GeneratedExecutionDescriptor.valid
    (descriptor : GeneratedExecutionDescriptor) : Bool :=
  !descriptor.machine.isEmpty &&
    !descriptor.unknownToken.isEmpty &&
    descriptor.decoder.valid

structure AdmittedProgram where
  operation : String
  actionIndex : UInt32
  machine : String
  headerRole : String
  codeRole : String
  decoder : Plan
  actions : PreparedActionPlan
  effect : AdmittedPhysicalPlan
  region : String
  deriving DecidableEq, Repr

def genericIndexedCarrier : String := "prepared-classified-value-table-v1"

def decodeActionCase? (record : GeneratedProgramRecord)
    (candidate : GeneratedActionCaseRecord) : Option PreparedActionCase :=
  if candidate.machine ≠ record.machine then none
  else if candidate.sourceKind.isEmpty then none
  else
    match decodePreparedAction? candidate.action with
    | none => none
    | some action => some { sourceKind := candidate.sourceKind, action }

theorem decodeActionCase?_sound (record : GeneratedProgramRecord)
    (candidate : GeneratedActionCaseRecord) (prepared : PreparedActionCase)
    (decoded : decodeActionCase? record candidate = some prepared) :
    candidate.machine = record.machine ∧
      candidate.sourceKind.isEmpty = false ∧
      decodePreparedAction? candidate.action = some prepared.action ∧
      prepared.sourceKind = candidate.sourceKind := by
  simp only [decodeActionCase?] at decoded
  split at decoded
  next different => contradiction
  next sameMachine =>
    split at decoded
    next empty => contradiction
    next nonempty =>
      cases actionEq : decodePreparedAction? candidate.action with
      | none => simp [actionEq] at decoded
      | some action =>
          simp only [actionEq, Option.some.injEq] at decoded
          subst prepared
          exact ⟨by simpa using sameMachine, by simpa using nonempty,
            rfl, rfl⟩

def decodePreparedActionPlan?
    (record : GeneratedProgramRecord) : Option PreparedActionPlan :=
  match record.actionCases.mapM (decodeActionCase? record) with
  | none => none
  | some cases =>
      let plan : PreparedActionPlan := { cases }
      if plan.valid then some plan else none

def GeneratedProgramRecord.decoder (record : GeneratedProgramRecord) : Plan :=
  { terminalLow := record.terminalLow
    terminalHigh := record.terminalHigh
    continuationLow := record.continuationLow
    continuationHigh := record.continuationHigh
    saveByte := record.saveByte
    unknownByte := record.unknownByte
    terminalRadix := record.terminalRadix
    terminalDigitBias := record.terminalDigitBias
    continuationRadix := record.continuationRadix
    continuationDigitBias := record.continuationDigitBias }

def GeneratedProgramRecord.indexedValue
    (record : GeneratedProgramRecord) : IndexedValueRecord :=
  { operation := record.operation
    actionIndex := record.actionIndex
    machine := record.machine
    headerRole := record.headerRole
    codeRole := record.codeRole
    carrier := record.indexedCarrier
    region := record.region }

def GeneratedProgramRecord.effectRecord
    (record : GeneratedProgramRecord) : GeneratedPlanRecord :=
  { operation := record.operation
    actionIndex := record.actionIndex
    machine := record.machine
    carrier := record.effectCarrier
    preparedEffect := record.preparedEffect
    savedEffect := record.savedEffect
    saveEffect := record.saveEffect
    unknownPolicy := record.unknownPolicy
    region := record.region }

/-- An optimized indexed program may execute only when its independently
generated machine identity, decoder, and unknown policy agree with the public
execution descriptor. -/
def executionDescriptorMatches (record : GeneratedProgramRecord)
    (descriptor : GeneratedExecutionDescriptor) : Bool :=
  descriptor.valid &&
    record.machine == descriptor.machine &&
    decide (record.decoder = descriptor.decoder) &&
    record.unknownPolicy == descriptor.unknownPolicy

theorem executionDescriptorMatches_sound (record : GeneratedProgramRecord)
    (descriptor : GeneratedExecutionDescriptor)
    (accepted : executionDescriptorMatches record descriptor = true) :
    descriptor.valid = true ∧
      record.machine = descriptor.machine ∧
      record.decoder = descriptor.decoder ∧
      record.unknownPolicy = descriptor.unknownPolicy := by
  simp only [executionDescriptorMatches, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at accepted
  exact ⟨accepted.1.1.1, accepted.1.1.2, accepted.1.2, accepted.2⟩

/-- Decode only the closed generic ABI.  Guest-specific strings are retained
as opaque identities; only the fixed carrier/effect vocabulary is inspected. -/
def decodeProgram? (record : GeneratedProgramRecord) : Option AdmittedProgram :=
  if record.headerRole = record.codeRole then none
  else if record.indexedCarrier != genericIndexedCarrier then none
  else if record.decoder.valid != true then none
  else
    match decodePreparedActionPlan? record with
    | none => none
    | some actions =>
        match decodeGeneratedPlan? record.effectRecord with
        | none => none
        | some effect => some
            { operation := record.operation
              actionIndex := record.actionIndex
              machine := record.machine
              headerRole := record.headerRole
              codeRole := record.codeRole
              decoder := record.decoder
              actions
              effect
              region := record.region }

def requestMatches (program : AdmittedProgram) (request : ProgramRequest) : Bool :=
  program.operation == request.operation &&
    program.actionIndex == request.actionIndex &&
    program.machine == request.machine &&
    program.headerRole == request.headerRole &&
    program.codeRole == request.codeRole &&
    program.effect.unknownPolicy == request.unknownPolicy &&
    program.region == request.region

/-- Admission requires both independently generated component records to be
exact projections of the composite record.  Redundancy therefore detects
drift rather than creating a second authority. -/
def admitProgram? (record : GeneratedProgramRecord)
    (request : ProgramRequest) (indexed : IndexedValueRecord)
    (effect : GeneratedPlanRecord) : Option AdmittedProgram :=
  match decodeProgram? record with
  | none => none
  | some program =>
      if requestMatches program request &&
          decide (record.indexedValue = indexed) &&
          decide (record.effectRecord = effect) then
        some program
      else none

theorem decodeProgram?_sound (record : GeneratedProgramRecord)
    (program : AdmittedProgram) (decoded : decodeProgram? record = some program) :
    program.decoder.valid = true ∧
      program.actions.valid = true ∧
      record.indexedCarrier = genericIndexedCarrier ∧
      record.effectCarrier = genericCarrier ∧
      record.preparedEffect = genericPreparedEffect ∧
      record.savedEffect = genericSavedEffect ∧
      record.saveEffect = genericSaveEffect := by
  simp only [decodeProgram?] at decoded
  split at decoded <;> try contradiction
  split at decoded <;> try contradiction
  split at decoded <;> try contradiction
  next decoderValid =>
    cases actionEq : decodePreparedActionPlan? record with
    | none => simp [actionEq] at decoded
    | some actions =>
        cases effectEq : decodeGeneratedPlan? record.effectRecord with
        | none => simp [actionEq, effectEq] at decoded
        | some effect =>
            simp only [actionEq, effectEq, Option.some.injEq] at decoded
            subst program
            have actionSound : actions.valid = true := by
              simp only [decodePreparedActionPlan?] at actionEq
              cases mappedEq : record.actionCases.mapM
                  (decodeActionCase? record) with
              | none => simp [mappedEq] at actionEq
              | some cases =>
                  simp only [mappedEq] at actionEq
                  split at actionEq
                  next valid =>
                    have same : ({ cases } : PreparedActionPlan) = actions := by
                      simpa using actionEq
                    simpa [← same] using valid
                  next => contradiction
            have effectSound :=
              (decodeGeneratedPlan?_eq_some_iff record.effectRecord effect).mp effectEq
            exact ⟨by simpa using decoderValid, actionSound,
              by simp_all [GeneratedProgramRecord.effectRecord]⟩

/-- The admitted program inherits the execution semantics named by an
independently generated descriptor.  This is the formal counterpart of the C
loader's descriptor/program cross-check; no state-machine fallback supplies
these fields. -/
theorem decodeProgram?_execution_refines
    (record : GeneratedProgramRecord)
    (descriptor : GeneratedExecutionDescriptor)
    (program : AdmittedProgram)
    (decoded : decodeProgram? record = some program)
    (matched : executionDescriptorMatches record descriptor = true) :
    program.machine = descriptor.machine ∧
      program.decoder = descriptor.decoder ∧
      program.effect.unknownPolicy = descriptor.unknownPolicy := by
  have matchedFields := executionDescriptorMatches_sound record descriptor matched
  simp only [decodeProgram?] at decoded
  split at decoded <;> try contradiction
  split at decoded <;> try contradiction
  split at decoded <;> try contradiction
  next =>
    cases actionEq : decodePreparedActionPlan? record with
    | none => simp [actionEq] at decoded
    | some actions =>
        cases effectEq : decodeGeneratedPlan? record.effectRecord with
        | none => simp [actionEq, effectEq] at decoded
        | some effect =>
            simp only [actionEq, effectEq, Option.some.injEq] at decoded
            subst program
            have effectFields :=
              (decodeGeneratedPlan?_eq_some_iff record.effectRecord effect).mp
                effectEq
            have effectPolicy :
                effect.unknownPolicy = record.unknownPolicy := by
              rw [effectFields.2.2.2.2]
              rfl
            exact ⟨matchedFields.2.1, matchedFields.2.2.1,
              effectPolicy.trans matchedFields.2.2.2⟩

theorem admitProgram?_components (record : GeneratedProgramRecord)
    (request : ProgramRequest) (indexed : IndexedValueRecord)
    (effect : GeneratedPlanRecord) (program : AdmittedProgram)
    (admitted : admitProgram? record request indexed effect = some program) :
    record.indexedValue = indexed ∧ record.effectRecord = effect := by
  simp only [admitProgram?] at admitted
  cases decodeEq : decodeProgram? record with
  | none => simp [decodeEq] at admitted
  | some decoded =>
      simp only [decodeEq] at admitted
      split at admitted
      next condition =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at condition
        exact ⟨condition.1.2, condition.2⟩
      next => contradiction

theorem admitProgram?_request (record : GeneratedProgramRecord)
    (request : ProgramRequest) (indexed : IndexedValueRecord)
    (effect : GeneratedPlanRecord) (program : AdmittedProgram)
    (admitted : admitProgram? record request indexed effect = some program) :
    requestMatches program request = true := by
  simp only [admitProgram?] at admitted
  cases decodeEq : decodeProgram? record with
  | none => simp [decodeEq] at admitted
  | some decoded =>
      simp only [decodeEq] at admitted
      split at admitted
      next condition =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at condition
        have same : decoded = program := by simpa using admitted
        simpa [same] using condition.1.1
      next => contradiction

/-! ## Prepared immutable classifications

The admitted indexed carrier retains the result of a stable finite
classifier beside each prepared value.  Execution observes that cached result;
it does not ask the classifier again. -/

structure PreparedClassifiedValue (Value : Type u) (Class : Type v) where
  value : Value
  classification : Class
  deriving DecidableEq, Repr

def prepareClassifiedValues (classify : Value → Option Class) :
    List Value → Option (List (PreparedClassifiedValue Value Class))
  | [] => some []
  | value :: values =>
      match classify value, prepareClassifiedValues classify values with
      | some classification, some prepared =>
          some ({ value, classification } :: prepared)
      | _, _ => none

def observeFreshClassifications
    (classify : Value → Option Class)
    (observe : Value → Class → Observation) :
    List Value → Option (List Observation)
  | [] => some []
  | value :: values =>
      match classify value,
          observeFreshClassifications classify observe values with
      | some classification, some observations =>
          some (observe value classification :: observations)
      | _, _ => none

def observePreparedClassifications
    (observe : Value → Class → Observation)
    (prepared : List (PreparedClassifiedValue Value Class)) :
    List Observation :=
  prepared.map fun value => observe value.value value.classification

/-- Preparing a value with its stable classifier result and reusing that
result is observationally exact with classifying at execution time. -/
theorem prepareClassifiedValues_exact
    (classify : Value → Option Class)
    (observe : Value → Class → Observation)
    (values : List Value)
    (prepared : List (PreparedClassifiedValue Value Class))
    (preparedEq : prepareClassifiedValues classify values = some prepared) :
    observeFreshClassifications classify observe values =
      some (observePreparedClassifications observe prepared) := by
  induction values generalizing prepared with
  | nil =>
      simp [prepareClassifiedValues] at preparedEq
      subst prepared
      rfl
  | cons value values inductionHypothesis =>
      simp only [prepareClassifiedValues] at preparedEq
      cases classificationEq : classify value with
      | none => simp [classificationEq] at preparedEq
      | some classification =>
          cases tailEq : prepareClassifiedValues classify values with
          | none => simp [classificationEq, tailEq] at preparedEq
          | some tail =>
              simp only [classificationEq, tailEq, Option.some.injEq]
                at preparedEq
              subst prepared
              simp [observeFreshClassifications, classificationEq,
                observePreparedClassifications,
                inductionHypothesis tail tailEq]

/-- Once at least one execution is requested, preparing classifications once
never performs more classifier calls than reclassifying on every execution. -/
theorem preparedClassifierCalls_le_repeated
    (values : List Value) (additionalExecutions : Nat) :
    values.length ≤ values.length * (additionalExecutions + 1) := by
  exact Nat.le_mul_of_pos_right values.length
    (by omega : 0 < additionalExecutions + 1)

/-! ## Compact physical carrier admission

The native realization represents both the prepared value and its finite
classification by unsigned words.  Zero is reserved for an invalid or absent
classification; the generated adapter supplies the inclusive upper bound of
the admitted finite classification vocabulary. -/

def decodePhysicalClassifiedValue?
    (value classification maximumClassification : UInt32) :
    Option (PreparedClassifiedValue UInt32 UInt32) :=
  if classification != 0 ∧ classification ≤ maximumClassification then
    some { value, classification }
  else
    none

/-- Successful physical decoding is exactly bounded, nonzero classification;
there is no default classification for an unadmitted word. -/
theorem decodePhysicalClassifiedValue?_eq_some_iff
    (value classification maximumClassification : UInt32)
    (prepared : PreparedClassifiedValue UInt32 UInt32) :
    decodePhysicalClassifiedValue?
        value classification maximumClassification = some prepared ↔
      classification != 0 ∧
        classification ≤ maximumClassification ∧
        prepared = { value, classification } := by
  by_cases valid :
      classification != 0 ∧ classification ≤ maximumClassification
  · simp only [decodePhysicalClassifiedValue?, if_pos valid,
      Option.some.injEq]
    constructor
    · intro same
      exact ⟨valid.1, valid.2, same.symm⟩
    · intro accepted
      exact accepted.2.2.symm
  · rw [decodePhysicalClassifiedValue?, if_neg valid]
    constructor
    · intro impossible
      cases impossible
    · intro accepted
      exact (valid ⟨accepted.1, accepted.2.1⟩).elim

structure PhysicalClassificationCase where
  source : UInt32
  classification : UInt32
  deriving DecidableEq, Repr

/-- A generated finite classifier is deterministic only when exactly one case
matches.  Missing and duplicate source keys both fail closed. -/
def classifyPhysicalValue?
    (value source maximumClassification : UInt32)
    (cases : List PhysicalClassificationCase) :
    Option (PreparedClassifiedValue UInt32 UInt32) :=
  match cases.filter (fun candidate => candidate.source = source) with
  | [candidate] =>
      decodePhysicalClassifiedValue?
        value candidate.classification maximumClassification
  | _ => none

theorem classifyPhysicalValue?_single
    (value source classification maximumClassification : UInt32)
    (admitted : classification != 0 ∧
      classification ≤ maximumClassification) :
    classifyPhysicalValue? value source maximumClassification
        [{ source, classification }] =
      some { value, classification } := by
  simp [classifyPhysicalValue?, decodePhysicalClassifiedValue?, admitted]

/-! Independent witnesses: the generic decoder accepts distinct alphabets and
refuses cross-component drift. -/

def alphabetA : GeneratedProgramRecord :=
  { operation := "guest-a-operation"
    actionIndex := 2
    machine := "guest-a-machine"
    headerRole := "guest-a-header"
    codeRole := "guest-a-code"
    terminalLow := 65
    terminalHigh := 84
    continuationLow := 85
    continuationHigh := 89
    saveByte := 90
    unknownByte := 63
    terminalRadix := 20
    terminalDigitBias := 0
    continuationRadix := 5
    continuationDigitBias := 1
    unknownPolicy := .use
    indexedCarrier := genericIndexedCarrier
    effectCarrier := genericCarrier
    preparedEffect := genericPreparedEffect
    savedEffect := genericSavedEffect
    saveEffect := genericSaveEffect
    region := "guest-a-region"
    actionCases :=
      [{ machine := "guest-a-machine",
         sourceKind := "guest-a-binding-kind",
         action := preparedActionName .pushDeclared },
       { machine := "guest-a-machine",
         sourceKind := "guest-a-matching-kind",
         action := preparedActionName .pushDeclared },
       { machine := "guest-a-machine",
         sourceKind := "guest-a-first-rule-kind",
         action := preparedActionName .applyFrame },
       { machine := "guest-a-machine",
         sourceKind := "guest-a-second-rule-kind",
         action := preparedActionName .applyFrame }] }

def alphabetB : GeneratedProgramRecord :=
  { operation := "guest-b-operation"
    actionIndex := 7
    machine := "guest-b-machine"
    headerRole := "guest-b-prefix"
    codeRole := "guest-b-stream"
    terminalLow := 1
    terminalHigh := 8
    continuationLow := 16
    continuationHigh := 23
    saveByte := 31
    unknownByte := 32
    terminalRadix := 8
    terminalDigitBias := 1
    continuationRadix := 8
    continuationDigitBias := 0
    unknownPolicy := .reject
    indexedCarrier := genericIndexedCarrier
    effectCarrier := genericCarrier
    preparedEffect := genericPreparedEffect
    savedEffect := genericSavedEffect
    saveEffect := genericSaveEffect
    region := "guest-b-region"
    actionCases :=
      [{ machine := "guest-b-machine",
         sourceKind := "guest-b-declaration-kind",
         action := preparedActionName .pushDeclared },
       { machine := "guest-b-machine",
         sourceKind := "guest-b-rule-kind",
         action := preparedActionName .applyFrame }] }

/-- An additive canary: five opaque source kinds, including a guest relation
not present in either smaller inventory, require no new generic action code. -/
def alphabetC : GeneratedProgramRecord :=
  { alphabetB with
    machine := "guest-c-machine"
    actionCases :=
      [{ machine := "guest-c-machine",
         sourceKind := "guest-c-binder-kind",
         action := preparedActionName .pushDeclared },
       { machine := "guest-c-machine",
         sourceKind := "guest-c-matching-kind",
         action := preparedActionName .pushDeclared },
       { machine := "guest-c-machine",
         sourceKind := "guest-c-introduction-kind",
         action := preparedActionName .applyFrame },
       { machine := "guest-c-machine",
         sourceKind := "guest-c-elimination-kind",
         action := preparedActionName .applyFrame },
       { machine := "guest-c-machine",
         sourceKind := "guest-c-freshness-kind",
         action := preparedActionName .applyFrame }] }

def executionA : GeneratedExecutionDescriptor :=
  { machine := alphabetA.machine
    unknownToken := "?"
    decoder := alphabetA.decoder
    unknownPolicy := alphabetA.unknownPolicy }

example : (decodeProgram? alphabetA).isSome = true := by decide
example : (decodeProgram? alphabetB).isSome = true := by decide
example : (decodeProgram? alphabetC).isSome = true := by decide
example : (decodeProgram? alphabetA).map (·.actions.cases.length) = some 4 := by
  decide
example : (decodeProgram? alphabetB).map (·.actions.cases.length) = some 2 := by
  decide
example : (decodeProgram? alphabetC).map (·.actions.cases.length) = some 5 := by
  decide
example : executionDescriptorMatches alphabetA executionA = true := by decide
example : executionDescriptorMatches alphabetA
    { executionA with unknownToken := "" } = false := by decide
example : executionDescriptorMatches alphabetA
    { executionA with decoder :=
        { executionA.decoder with terminalRadix := 21 } } = false := by decide

example (program : AdmittedProgram)
    (decoded : decodeProgram? alphabetA = some program) :
    program.machine = executionA.machine ∧
      program.decoder = executionA.decoder ∧
      program.effect.unknownPolicy = executionA.unknownPolicy := by
  exact decodeProgram?_execution_refines alphabetA executionA program decoded
    (by decide)

example : decodePreparedAction? "stack-push-declared-v1" =
    some .pushDeclared := by
  decide

example : decodePreparedAction? "guest-specific-action" = none := by
  decide

example : decodeProgram?
    { alphabetA with actionCases :=
        [{ machine := alphabetA.machine,
           sourceKind := "guest-a-first-rule-kind",
           action := "guest-specific-action" }] } = none := by
  decide

example : decodeProgram?
    { alphabetA with actionCases :=
        [{ machine := alphabetA.machine,
           sourceKind := "",
           action := preparedActionName .applyFrame }] } = none := by
  decide

example : decodeProgram?
    { alphabetB with actionCases :=
        alphabetB.actionCases ++ alphabetB.actionCases } = none := by
  decide

example : admitProgram? alphabetA
    { operation := alphabetA.operation
      actionIndex := alphabetA.actionIndex
      machine := alphabetA.machine
      headerRole := alphabetA.headerRole
      codeRole := alphabetA.codeRole
      unknownPolicy := alphabetA.unknownPolicy
      region := alphabetA.region }
    alphabetA.indexedValue alphabetA.effectRecord = decodeProgram? alphabetA := by
  decide

example : admitProgram? alphabetA
    { operation := alphabetA.operation
      actionIndex := alphabetA.actionIndex
      machine := alphabetA.machine
      headerRole := alphabetA.headerRole
      codeRole := alphabetA.codeRole
      unknownPolicy := alphabetA.unknownPolicy
      region := alphabetA.region }
    { alphabetA.indexedValue with carrier := "unsupported-carrier" }
    alphabetA.effectRecord = none := by
  decide

private def parityClass (value : Nat) : Option Bool :=
  some (value % 2 = 0)

private def boundedClass (value : Nat) : Option Ordering :=
  if value < 10 then some .lt else if value = 10 then some .eq else some .gt

example : prepareClassifiedValues parityClass [2, 5, 8] =
    some [{ value := 2, classification := true },
      { value := 5, classification := false },
      { value := 8, classification := true }] := by
  decide

example : prepareClassifiedValues boundedClass [3, 10, 14] =
    some [{ value := 3, classification := .lt },
      { value := 10, classification := .eq },
      { value := 14, classification := .gt }] := by
  decide

example : decodePhysicalClassifiedValue? 81 2 3 =
    some { value := 81, classification := 2 } := by
  decide

example : decodePhysicalClassifiedValue? 81 0 3 = none := by
  decide

example : decodePhysicalClassifiedValue? 81 4 3 = none := by
  decide

example : prepareClassifiedValues
    (fun value : Nat => if value = 7 then none else some value) [3, 7, 9] =
    none := by
  decide

/-! ## Variable generated table inventories and dense machine coordinates

Generated guests provide an association list of semantic table capabilities.
The admitted first-order machine has a finite capability vocabulary, so the
loader may compile that variable list once to dense physical coordinates.
The assertion-apartness and active-apartness relations are independently
optional; the remaining capabilities are required by this machine class. -/

inductive FirstOrderTableCapability where
  | symbolKind
  | formula
  | floatingVariable
  | activeHypothesis
  | orderedHypothesis
  | mandatoryVariable
  | assertionApartness
  | activeApartness
  | labelKind
  deriving DecidableEq, Repr

def firstOrderTableCapabilities : List FirstOrderTableCapability :=
  [.symbolKind, .formula, .floatingVariable, .activeHypothesis,
    .orderedHypothesis, .mandatoryVariable, .assertionApartness,
    .activeApartness, .labelKind]

private theorem firstOrderTableCapabilities_nodup :
    firstOrderTableCapabilities.Nodup := by decide

def firstOrderTableInventory :
    FiniteEnvironmentCompilation.Inventory FirstOrderTableCapability :=
  { keys := firstOrderTableCapabilities
    nodup := firstOrderTableCapabilities_nodup }

abbrev GeneratedTableBinding := FirstOrderTableCapability × UInt32

inductive TablePresencePolicy where
  | required
  | optionalEmpty
  deriving DecidableEq, Repr

abbrev GeneratedTablePolicy :=
  FirstOrderTableCapability × TablePresencePolicy

def firstOrderTablePolicies : List GeneratedTablePolicy :=
  [(.symbolKind, .required), (.formula, .required),
    (.floatingVariable, .required), (.activeHypothesis, .required),
    (.orderedHypothesis, .required), (.mandatoryVariable, .required),
    (.assertionApartness, .optionalEmpty),
    (.activeApartness, .optionalEmpty), (.labelKind, .required)]

def generatedTableBindingsValid (policies : List GeneratedTablePolicy)
    (bindings : List GeneratedTableBinding) : Bool :=
  decide (policies.map Prod.fst).Nodup &&
    firstOrderTableCapabilities.all (fun role =>
      policies.any fun policy => policy.1 == role) &&
    decide (bindings.map Prod.fst).Nodup &&
    policies.all fun policy =>
      policy.2 == .optionalEmpty ||
        bindings.any fun binding => binding.1 == policy.1

def compileGeneratedTableBindings?
    (policies : List GeneratedTablePolicy)
    (bindings : List GeneratedTableBinding) :
    Option (List (FiniteEnvironmentCompilation.DenseWrite
      firstOrderTableInventory UInt32)) :=
  if generatedTableBindingsValid policies bindings then
    FiniteEnvironmentCompilation.compileWrites?
      firstOrderTableInventory bindings
  else
    none

/-- Dense physical coordinates preserve every source capability lookup.  The
proof is inherited from generic finite-environment compilation; this machine
instance adds only uniqueness and required-capability admission. -/
theorem compileGeneratedTableBindings?_refines
    (policies : List GeneratedTablePolicy)
    (bindings : List GeneratedTableBinding)
    (compiled : List (FiniteEnvironmentCompilation.DenseWrite
      firstOrderTableInventory UInt32))
    (accepted :
      compileGeneratedTableBindings? policies bindings = some compiled) :
    FiniteEnvironmentCompilation.decodeDense firstOrderTableInventory
        (FiniteEnvironmentCompilation.runDense
          firstOrderTableInventory compiled) =
      FiniteEnvironmentCompilation.runSource bindings := by
  unfold compileGeneratedTableBindings? at accepted
  split at accepted
  next valid =>
    exact FiniteEnvironmentCompilation.runDense_refines_runSource
      firstOrderTableInventory bindings compiled accepted
  next invalid => simp at accepted

private def completeTableBindings : List GeneratedTableBinding :=
  firstOrderTableCapabilities.zip [10, 11, 12, 13, 14, 15, 16, 17, 18]

private def noAssertionApartnessBindings : List GeneratedTableBinding :=
  completeTableBindings.filter fun binding =>
    binding.1 != .assertionApartness

private def noApartnessBindings : List GeneratedTableBinding :=
  completeTableBindings.filter fun binding =>
    binding.1 != .assertionApartness && binding.1 != .activeApartness

example : (compileGeneratedTableBindings?
    firstOrderTablePolicies completeTableBindings).isSome =
    true := by decide

example :
    (compileGeneratedTableBindings?
      firstOrderTablePolicies noAssertionApartnessBindings).isSome =
      true := by decide

example :
    (compileGeneratedTableBindings?
      firstOrderTablePolicies noApartnessBindings).isSome = true := by
  decide

example : compileGeneratedTableBindings? firstOrderTablePolicies
    (completeTableBindings.filter fun binding => binding.1 != .formula) =
      none := by decide

example : compileGeneratedTableBindings? firstOrderTablePolicies
    (completeTableBindings ++ [(.formula, 99)]) = none := by decide

example : compileGeneratedTableBindings?
    (firstOrderTablePolicies.filter fun policy => policy.1 != .formula)
    completeTableBindings = none := by decide

end Mettapedia.GSLT.LanguageDef.IndexedCompressedProgramPlanCompilation
