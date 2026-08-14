import Mettapedia.GSLT.LanguageDef.CompiledPlanGroundDenseCompilation

/-!
# Property-admitted activation views for compiled plans

A compiled rule body normally becomes a concrete substituted term before the
next rule is matched.  An activation view instead retains the immutable body
and its substitution environment, resolving descendants only as matching
demands them.

The optimization is admitted from three local facts: the producer is range
restricted, the body has a fixed application head, and every possible
consumer avoids capturing a variable-bearing source expression in one
pattern slot.  The executable view matcher below is independent of the source
instantiate-then-match implementation.  Its exactness theorem is the semantic
boundary implemented by the generic C matcher.
-/

namespace Mettapedia.GSLT.LanguageDef.CompiledPlanActivationViewCompilation

open CompiledPlanAdmission
open CompiledPlanLowering
open CompiledPlanTermSemantics
open CompiledPlanGroundDenseCompilation

mutual

/-- Match a source substitution view directly against a rule pattern. -/
def matchView (sourceEnvironment : Substitution) :
    Term -> Term -> SourceEnvironment -> Option SourceEnvironment
  | .variable slot, pattern, patternEnvironment =>
      match sourceEnvironment slot with
      | none => none
      | some target => matchSource pattern target patternEnvironment
  | .symbol value, pattern, patternEnvironment =>
      matchSource pattern (.symbol value) patternEnvironment
  | .string value, pattern, patternEnvironment =>
      matchSource pattern (.string value) patternEnvironment
  | .integer value, pattern, patternEnvironment =>
      matchSource pattern (.integer value) patternEnvironment
  | source@(.application sourceHead sourceArguments), pattern,
      patternEnvironment =>
      match pattern with
      | .application patternHead patternArguments =>
          if sourceHead = patternHead then
            matchViewTerms sourceEnvironment sourceArguments patternArguments
              patternEnvironment
          else
            none
      | .variable _ =>
          match instantiateTerm sourceEnvironment source with
          | none => none
          | some target => matchSource pattern target patternEnvironment
      | _ => none

def matchViewTerms (sourceEnvironment : Substitution) :
    Terms -> Terms -> SourceEnvironment -> Option SourceEnvironment
  | .nil, .nil, patternEnvironment => some patternEnvironment
  | .cons sourceHead sourceTail, .cons patternHead patternTail,
      patternEnvironment =>
      match matchView sourceEnvironment sourceHead patternHead
          patternEnvironment with
      | none => none
      | some extended =>
          matchViewTerms sourceEnvironment sourceTail patternTail extended
  | _, _, _ => none

end

private theorem instantiateTerm_application_eq
    (environment : Substitution) (head : List UInt8) (arguments : Terms) :
    instantiateTerm environment (.application head arguments) =
      (instantiateTerms environment arguments).bind fun grounded =>
        some (.application head grounded) := rfl

private theorem instantiateTerms_cons_eq
    (environment : Substitution) (head : Term) (tail : Terms) :
    instantiateTerms environment (.cons head tail) =
      (instantiateTerm environment head).bind fun groundedHead =>
        (instantiateTerms environment tail).bind fun groundedTail =>
          some (.cons groundedHead groundedTail) := rfl

private theorem matchSource_application_eq
    (patternHead : List UInt8) (patternArguments : Terms)
    (sourceHead : List UInt8) (sourceArguments : GroundTerms)
    (environment : SourceEnvironment) :
    matchSource (.application patternHead patternArguments)
        (.application sourceHead sourceArguments) environment =
      if patternHead = sourceHead then
        matchSourceTerms patternArguments sourceArguments environment
      else none := rfl

private theorem matchSourceTerms_nil_cons_eq
    (head : GroundTerm) (tail : GroundTerms)
    (environment : SourceEnvironment) :
    matchSourceTerms .nil (.cons head tail) environment = none := rfl

private theorem matchSourceTerms_cons_eq
    (patternHead : Term) (patternTail : Terms)
    (sourceHead : GroundTerm) (sourceTail : GroundTerms)
    (environment : SourceEnvironment) :
    matchSourceTerms (.cons patternHead patternTail)
        (.cons sourceHead sourceTail) environment =
      match matchSource patternHead sourceHead environment with
      | none => none
      | some extended =>
          matchSourceTerms patternTail sourceTail extended := rfl

mutual

/-- Direct view matching has exactly instantiate-then-match semantics. -/
theorem matchView_eq_materialized
    (sourceEnvironment : Substitution) (source pattern : Term)
    (patternEnvironment : SourceEnvironment) :
    matchView sourceEnvironment source pattern patternEnvironment =
      match instantiateTerm sourceEnvironment source with
      | none => none
      | some target => matchSource pattern target patternEnvironment := by
  cases source with
  | symbol value => rfl
  | «variable» slot =>
      cases sourceEnvironment slot <;> rfl
  | string value => rfl
  | integer value => rfl
  | application sourceHead sourceArguments =>
      cases pattern with
      | «variable» slot => rfl
      | application patternHead patternArguments =>
          by_cases same : sourceHead = patternHead
          · subst patternHead
            simp only [matchView, ↓reduceIte]
            rw [matchViewTerms_eq_materialized]
            rw [instantiateTerm_application_eq]
            cases instantiated :
                instantiateTerms sourceEnvironment sourceArguments with
            | none => rfl
            | some targets =>
                simp only [Option.bind_some, matchSource_application_eq,
                  ↓reduceIte]
          · have reverse : ¬patternHead = sourceHead := Ne.symm same
            simp only [matchView, same, ↓reduceIte]
            rw [instantiateTerm_application_eq]
            cases instantiated :
                instantiateTerms sourceEnvironment sourceArguments with
            | none => rfl
            | some targets =>
                simp only [Option.bind_some, matchSource_application_eq,
                  reverse, ↓reduceIte]
      | symbol value =>
          simp only [matchView]
          rw [instantiateTerm_application_eq]
          cases instantiateTerms sourceEnvironment sourceArguments <;> rfl
      | string value =>
          simp only [matchView]
          rw [instantiateTerm_application_eq]
          cases instantiateTerms sourceEnvironment sourceArguments <;> rfl
      | integer value =>
          simp only [matchView]
          rw [instantiateTerm_application_eq]
          cases instantiateTerms sourceEnvironment sourceArguments <;> rfl

/-- The list-shaped view traversal preserves ordered matching and all writes. -/
theorem matchViewTerms_eq_materialized
    (sourceEnvironment : Substitution) (sources patterns : Terms)
    (patternEnvironment : SourceEnvironment) :
    matchViewTerms sourceEnvironment sources patterns patternEnvironment =
      match instantiateTerms sourceEnvironment sources with
      | none => none
      | some targets => matchSourceTerms patterns targets patternEnvironment := by
  cases sources with
  | nil => cases patterns <;> rfl
  | cons sourceHead sourceTail =>
      cases patterns with
      | nil =>
          simp only [matchViewTerms]
          rw [instantiateTerms_cons_eq]
          cases instantiateTerm sourceEnvironment sourceHead with
          | none => rfl
          | some target =>
              cases instantiateTerms sourceEnvironment sourceTail with
              | none => rfl
              | some targets =>
                  exact matchSourceTerms_nil_cons_eq target targets
                    patternEnvironment |>.symm
      | cons patternHead patternTail =>
          simp only [matchViewTerms]
          rw [matchView_eq_materialized]
          rw [instantiateTerms_cons_eq]
          cases headInstantiation :
              instantiateTerm sourceEnvironment sourceHead with
          | none => rfl
          | some target =>
              simp only [Option.bind_some]
              cases headMatch : matchSource patternHead target patternEnvironment with
              | none =>
                  cases tailInstantiation :
                      instantiateTerms sourceEnvironment sourceTail with
                  | none => rfl
                  | some targets =>
                      simp only [Option.bind_some,
                        matchSourceTerms_cons_eq, headMatch]
              | some extended =>
                  change matchViewTerms sourceEnvironment sourceTail
                    patternTail extended = _
                  rw [matchViewTerms_eq_materialized]
                  cases tailInstantiation :
                      instantiateTerms sourceEnvironment sourceTail with
                  | none => rfl
                  | some targets =>
                      simp only [Option.bind_some,
                        matchSourceTerms_cons_eq, headMatch]

end

mutual

/-- Decidable absence of source variables. -/
def variableFree : Term -> Bool
  | .variable _ => false
  | .application _ arguments => variableFreeTerms arguments
  | _ => true

def variableFreeTerms : Terms -> Bool
  | .nil => true
  | .cons head tail => variableFree head && variableFreeTerms tail

end

mutual

/-- A consumer variable demands a constructed source value exactly when it
captures a variable-bearing source application. -/
def captureDemand : Term -> Term -> Bool
  | source@(.application _ _), .variable _ => !variableFree source
  | .application _ sourceArguments, .application _ patternArguments =>
      captureDemandTerms sourceArguments patternArguments
  | _, _ => false

def captureDemandTerms : Terms -> Terms -> Bool
  | .cons sourceHead sourceTail, .cons patternHead patternTail =>
      captureDemand sourceHead patternHead ||
        captureDemandTerms sourceTail patternTail
  | _, _ => false

end

def fixedApplicationHead? : Term -> Option (List UInt8)
  | .application head _ => some head
  | _ => none

/-- One consumer is safe for the lazy source body.  Unrelated fixed heads are
never scheduled together; a variable root could capture the complete body and
is therefore refused. -/
def consumerSafe (source consumer : Term) : Bool :=
  match consumer with
  | .variable _ => false
  | .application consumerHead _ =>
      match fixedApplicationHead? source with
      | some sourceHead =>
          sourceHead != consumerHead || !captureDemand source consumer
      | none => false
  | _ => true

mutual

def usedSlots : Term -> List UInt32
  | .variable slot => [slot]
  | .application _ arguments => usedSlotsTerms arguments
  | _ => []

def usedSlotsTerms : Terms -> List UInt32
  | .nil => []
  | .cons head tail => usedSlots head ++ usedSlotsTerms tail

end

/-- Every body variable is supplied by matching the producer head. -/
def rangeRestricted (producer : TypedRule) : Bool :=
  let headVariables := usedSlots producer.head
  (producer.body.flatMap usedSlots).all headVariables.contains

structure ActivationViewPlan where
  source : Term
  deriving DecidableEq, Repr

/-- Compile one body view only when all three local certificates hold. -/
def compile? (producer : TypedRule) (source : Term)
    (consumerHeads : List Term) : Option ActivationViewPlan :=
  if rangeRestricted producer &&
      (fixedApplicationHead? source).isSome &&
      consumerHeads.all (consumerSafe source) then
    some { source }
  else
    none

theorem compile?_success
    (producer : TypedRule) (source : Term) (consumerHeads : List Term)
    (plan : ActivationViewPlan)
    (accepted : compile? producer source consumerHeads = some plan) :
    rangeRestricted producer = true ∧
      (fixedApplicationHead? source).isSome = true ∧
      consumerHeads.all (consumerSafe source) = true ∧
      plan.source = source := by
  simp only [compile?] at accepted
  split at accepted
  · rename_i admitted
    simp only [Bool.and_eq_true] at admitted
    cases accepted
    exact ⟨admitted.1.1, admitted.1.2, admitted.2, rfl⟩
  · contradiction

/-- The source implementation constructs one complete substituted body. -/
def sourceWholeTermMaterializations (_plan : ActivationViewPlan) : Nat := 1

/-- An admitted consumer pair needs no captured substituted source
application.  Scalar and variable descendants are resolved directly. -/
def compiledCapturedMaterializations
    (plan : ActivationViewPlan) (consumer : Term) : Nat :=
  if captureDemand plan.source consumer then 1 else 0

theorem compiledCapturedMaterializations_eq_zero
    (producer : TypedRule) (source consumer : Term)
    (consumerHeads : List Term) (plan : ActivationViewPlan)
    (accepted : compile? producer source consumerHeads = some plan)
    (member : consumer ∈ consumerHeads)
    (sameHead : fixedApplicationHead? source =
      fixedApplicationHead? consumer) :
    compiledCapturedMaterializations plan consumer = 0 := by
  obtain ⟨_, sourceFixed, consumersSafe, planSource⟩ :=
    compile?_success producer source consumerHeads plan accepted
  have safe := (List.all_eq_true.mp consumersSafe) consumer member
  simp only [compiledCapturedMaterializations]
  rw [planSource]
  cases consumer with
  | «variable» slot => simp [consumerSafe] at safe
  | symbol value =>
      cases source <;>
        simp [fixedApplicationHead?] at sourceFixed sameHead
  | string value =>
      cases source <;>
        simp [fixedApplicationHead?] at sourceFixed sameHead
  | integer value =>
      cases source <;>
        simp [fixedApplicationHead?] at sourceFixed sameHead
  | application consumerHead arguments =>
      cases source with
      | symbol value => simp [fixedApplicationHead?] at sourceFixed
      | «variable» slot => simp [fixedApplicationHead?] at sourceFixed
      | string value => simp [fixedApplicationHead?] at sourceFixed
      | integer value => simp [fixedApplicationHead?] at sourceFixed
      | application sourceHead sourceArguments =>
          simp only [fixedApplicationHead?] at sameHead
          have heads : sourceHead = consumerHead := Option.some.inj sameHead
          simp [consumerSafe, fixedApplicationHead?, heads,
            captureDemand] at safe
          simp [captureDemand, safe]

theorem compiledCapturedMaterializations_lt_source
    (producer : TypedRule) (source consumer : Term)
    (consumerHeads : List Term) (plan : ActivationViewPlan)
    (accepted : compile? producer source consumerHeads = some plan)
    (member : consumer ∈ consumerHeads)
    (sameHead : fixedApplicationHead? source =
      fixedApplicationHead? consumer) :
    compiledCapturedMaterializations plan consumer <
      sourceWholeTermMaterializations plan := by
  rw [compiledCapturedMaterializations_eq_zero producer source consumer
    consumerHeads plan accepted member sameHead]
  simp [sourceWholeTermMaterializations]

/-! ## Cross-guest canaries -/

private def parserProducer : TypedRule :=
  { name := [1]
    head := .application [10] (.cons (.variable 0) .nil)
    body := [.application [11] (.cons (.variable 0) .nil)]
    variableCount := 1 }

private def parserConsumer : Term :=
  .application [11] (.cons (.variable 0) .nil)

private def parserBody : Term :=
  .application [11] (.cons (.variable 0) .nil)

private def ruleMachineProducer : TypedRule :=
  { name := [2]
    head := .application [20]
      (.cons (.variable 0) (.cons (.variable 1) .nil))
    body := [.application [21]
      (.cons (.variable 0) (.cons (.variable 1) .nil))]
    variableCount := 2 }

private def ruleMachineConsumer : Term :=
  .application [21]
    (.cons (.variable 0) (.cons (.variable 1) .nil))

private def ruleMachineBody : Term :=
  .application [21]
    (.cons (.variable 0) (.cons (.variable 1) .nil))

example : (compile? parserProducer parserBody
    [parserConsumer]).isSome = true := by decide

example : (compile? ruleMachineProducer ruleMachineBody
    [ruleMachineConsumer]).isSome = true := by decide

/-- A producer with an existential body slot is rejected. -/
example :
    (compile?
      { parserProducer with
        body := [.application [11] (.cons (.variable 1) .nil)] }
      (.application [11] (.cons (.variable 1) .nil))
      [parserConsumer]).isSome = false := by decide

/-- A consumer variable that would capture a substituted application is
rejected even though the outer constructor is fixed. -/
example :
    (compile? parserProducer
      (.application [11]
        (.cons (.application [12] (.cons (.variable 0) .nil)) .nil))
      [.application [11] (.cons (.variable 0) .nil)]).isSome = false := by
  decide

/-- A variable-headed consumer could capture the complete activation and is
therefore rejected. -/
example :
    (compile? parserProducer parserBody
      [.variable 0]).isSome = false := by decide

end Mettapedia.GSLT.LanguageDef.CompiledPlanActivationViewCompilation
