import Mettapedia.GSLT.LanguageDef.CompiledPlanActivationViewCompilation

/-!
# Dense matching directly over admitted activation views

Activation views avoid constructing a complete substituted producer body.
Ground-dense consumers avoid constructing a fresh consumer substitution map.
Using the two optimizations independently can nevertheless force the view
before dense matching begins.  This module gives their direct composition.

The local composition recognizer requires both existing admissions, membership
in the complete consumer inventory, and equal fixed heads.  The executable
matcher traverses the immutable source body and the bounded consumer program
together.  Its exactness theorem factors through the independent materialized
semantics of both component optimizations.
-/

namespace Mettapedia.GSLT.LanguageDef.CompiledPlanDenseActivationViewCompilation

open CompiledPlanAdmission
open CompiledPlanLowering
open CompiledPlanTermSemantics
open CompiledPlanGroundDenseCompilation

mutual

/-- Match a bounded consumer directly against a substituted source view. -/
def matchDenseView (sourceEnvironment : Substitution) :
    Term -> DenseTerm width -> DenseEnvironment width ->
      Option (DenseEnvironment width)
  | .variable slot, pattern, patternEnvironment =>
      match sourceEnvironment slot with
      | none => none
      | some target => matchDense pattern target patternEnvironment
  | .symbol value, pattern, patternEnvironment =>
      matchDense pattern (.symbol value) patternEnvironment
  | .string value, pattern, patternEnvironment =>
      matchDense pattern (.string value) patternEnvironment
  | .integer value, pattern, patternEnvironment =>
      matchDense pattern (.integer value) patternEnvironment
  | source@(.application sourceHead sourceArguments), pattern,
      patternEnvironment =>
      match pattern with
      | .application patternHead patternArguments =>
          if sourceHead = patternHead then
            matchDenseViewTerms sourceEnvironment sourceArguments
              patternArguments patternEnvironment
          else
            none
      | .variable _ =>
          match instantiateTerm sourceEnvironment source with
          | none => none
          | some target => matchDense pattern target patternEnvironment
      | _ => none

def matchDenseViewTerms (sourceEnvironment : Substitution) :
    Terms -> DenseTerms width -> DenseEnvironment width ->
      Option (DenseEnvironment width)
  | .nil, .nil, patternEnvironment => some patternEnvironment
  | .cons sourceHead sourceTail, .cons patternHead patternTail,
      patternEnvironment =>
      match matchDenseView sourceEnvironment sourceHead patternHead
          patternEnvironment with
      | none => none
      | some extended =>
          matchDenseViewTerms sourceEnvironment sourceTail patternTail extended
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

private theorem matchDense_application_eq
    (patternHead : List UInt8) (patternArguments : DenseTerms width)
    (sourceHead : List UInt8) (sourceArguments : GroundTerms)
    (environment : DenseEnvironment width) :
    matchDense (.application patternHead patternArguments)
        (.application sourceHead sourceArguments) environment =
      if patternHead = sourceHead then
        matchDenseTerms patternArguments sourceArguments environment
      else none := rfl

private theorem matchDenseTerms_nil_cons_eq
    (head : GroundTerm) (tail : GroundTerms)
    (environment : DenseEnvironment width) :
    matchDenseTerms .nil (.cons head tail) environment = none := rfl

private theorem matchDenseTerms_cons_eq
    (patternHead : DenseTerm width) (patternTail : DenseTerms width)
    (sourceHead : GroundTerm) (sourceTail : GroundTerms)
    (environment : DenseEnvironment width) :
    matchDenseTerms (.cons patternHead patternTail)
        (.cons sourceHead sourceTail) environment =
      match matchDense patternHead sourceHead environment with
      | none => none
      | some extended =>
          matchDenseTerms patternTail sourceTail extended := rfl

mutual

/-- Direct dense-view matching has exactly materialize-then-dense-match
semantics for every bounded consumer program. -/
theorem matchDenseView_eq_materialized
    (sourceEnvironment : Substitution) (source : Term)
    (pattern : DenseTerm width)
    (patternEnvironment : DenseEnvironment width) :
    matchDenseView sourceEnvironment source pattern patternEnvironment =
      match instantiateTerm sourceEnvironment source with
      | none => none
      | some target => matchDense pattern target patternEnvironment := by
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
            simp only [matchDenseView, ↓reduceIte]
            rw [matchDenseViewTerms_eq_materialized]
            rw [instantiateTerm_application_eq]
            cases instantiated :
                instantiateTerms sourceEnvironment sourceArguments with
            | none => rfl
            | some targets =>
                simp only [Option.bind_some, matchDense_application_eq,
                  ↓reduceIte]
          · have reverse : ¬patternHead = sourceHead := Ne.symm same
            simp only [matchDenseView, same, ↓reduceIte]
            rw [instantiateTerm_application_eq]
            cases instantiated :
                instantiateTerms sourceEnvironment sourceArguments with
            | none => rfl
            | some targets =>
                simp only [Option.bind_some, matchDense_application_eq,
                  reverse, ↓reduceIte]
      | symbol value =>
          simp only [matchDenseView]
          rw [instantiateTerm_application_eq]
          cases instantiateTerms sourceEnvironment sourceArguments <;> rfl
      | string value =>
          simp only [matchDenseView]
          rw [instantiateTerm_application_eq]
          cases instantiateTerms sourceEnvironment sourceArguments <;> rfl
      | integer value =>
          simp only [matchDenseView]
          rw [instantiateTerm_application_eq]
          cases instantiateTerms sourceEnvironment sourceArguments <;> rfl

/-- The list-shaped direct traversal preserves left-to-right slot writes and
repeated-slot comparisons. -/
theorem matchDenseViewTerms_eq_materialized
    (sourceEnvironment : Substitution) (sources : Terms)
    (patterns : DenseTerms width)
    (patternEnvironment : DenseEnvironment width) :
    matchDenseViewTerms sourceEnvironment sources patterns
        patternEnvironment =
      match instantiateTerms sourceEnvironment sources with
      | none => none
      | some targets => matchDenseTerms patterns targets patternEnvironment := by
  cases sources with
  | nil => cases patterns <;> rfl
  | cons sourceHead sourceTail =>
      cases patterns with
      | nil =>
          simp only [matchDenseViewTerms]
          rw [instantiateTerms_cons_eq]
          cases instantiateTerm sourceEnvironment sourceHead with
          | none => rfl
          | some target =>
              cases instantiateTerms sourceEnvironment sourceTail with
              | none => rfl
              | some targets =>
                  exact matchDenseTerms_nil_cons_eq target targets
                    patternEnvironment |>.symm
      | cons patternHead patternTail =>
          simp only [matchDenseViewTerms]
          rw [matchDenseView_eq_materialized]
          rw [instantiateTerms_cons_eq]
          cases headInstantiation :
              instantiateTerm sourceEnvironment sourceHead with
          | none => rfl
          | some target =>
              simp only [Option.bind_some]
              cases headMatch :
                  matchDense patternHead target patternEnvironment with
              | none =>
                  cases tailInstantiation :
                      instantiateTerms sourceEnvironment sourceTail with
                  | none => rfl
                  | some targets =>
                      simp only [Option.bind_some,
                        matchDenseTerms_cons_eq, headMatch]
              | some extended =>
                  change matchDenseViewTerms sourceEnvironment sourceTail
                    patternTail extended = _
                  rw [matchDenseViewTerms_eq_materialized]
                  cases tailInstantiation :
                      instantiateTerms sourceEnvironment sourceTail with
                  | none => rfl
                  | some targets =>
                      simp only [Option.bind_some,
                        matchDenseTerms_cons_eq, headMatch]

end

/-- The direct composition agrees with the independently specified activation
view matcher after decoding bounded consumer slots. -/
theorem matchDenseView_compileTerm?
    (width : UInt32) (source consumer : Term)
    (compiled : DenseTerm width)
    (compiledEq : compileTerm? width consumer = some compiled)
    (sourceEnvironment : Substitution)
    (sourceConsumerEnvironment : SourceEnvironment)
    (denseConsumerEnvironment : DenseEnvironment width)
    (related : decodeDense width denseConsumerEnvironment =
      sourceConsumerEnvironment) :
    Option.map (decodeDense width)
        (matchDenseView sourceEnvironment source compiled
          denseConsumerEnvironment) =
      CompiledPlanActivationViewCompilation.matchView
        sourceEnvironment source consumer
        sourceConsumerEnvironment := by
  rw [matchDenseView_eq_materialized]
  rw [CompiledPlanActivationViewCompilation.matchView_eq_materialized]
  cases instantiated : instantiateTerm sourceEnvironment source with
  | none => rfl
  | some target =>
      simpa [instantiated] using
        matchDense_compileTerm? width consumer compiled compiledEq
          sourceConsumerEnvironment denseConsumerEnvironment related target

/-! ## Decidable composition admission -/

structure Plan (width : UInt32) where
  activation :
    CompiledPlanActivationViewCompilation.ActivationViewPlan
  consumer : DenseTerm width
  deriving DecidableEq, Repr

/-- Compose the two partial compilers only for an inventoried same-head
consumer.  No extra guest vocabulary or rule shape is introduced. -/
def compile? (producer : TypedRule) (source : Term)
    (consumerHeads : List Term) (consumer : Term)
    (width : UInt32) : Option (Plan width) :=
  match CompiledPlanActivationViewCompilation.compile?
      producer source consumerHeads with
  | none => none
  | some activation =>
      match compileTerm? width consumer with
      | none => none
      | some compiled =>
          if _member : consumer ∈ consumerHeads then
            if _sameHead :
                CompiledPlanActivationViewCompilation.fixedApplicationHead?
                    source =
                  CompiledPlanActivationViewCompilation.fixedApplicationHead?
                    consumer then
              some { activation, consumer := compiled }
            else none
          else none

theorem compile?_success
    (producer : TypedRule) (source : Term)
    (consumerHeads : List Term) (consumer : Term)
    (width : UInt32) (plan : Plan width)
    (accepted : compile? producer source consumerHeads consumer width =
      some plan) :
    CompiledPlanActivationViewCompilation.compile?
        producer source consumerHeads =
        some plan.activation ∧
      compileTerm? width consumer = some plan.consumer ∧
      consumer ∈ consumerHeads ∧
      CompiledPlanActivationViewCompilation.fixedApplicationHead? source =
        CompiledPlanActivationViewCompilation.fixedApplicationHead?
          consumer := by
  unfold compile? at accepted
  cases activationEq :
      CompiledPlanActivationViewCompilation.compile?
        producer source consumerHeads with
  | none => simp [activationEq] at accepted
  | some activation =>
      cases compiledEq : compileTerm? width consumer with
      | none => simp [activationEq, compiledEq] at accepted
      | some compiled =>
          by_cases member : consumer ∈ consumerHeads
          · by_cases sameHead :
                CompiledPlanActivationViewCompilation.fixedApplicationHead?
                    source =
                  CompiledPlanActivationViewCompilation.fixedApplicationHead?
                    consumer
            · simp [activationEq, compiledEq, member, sameHead] at accepted
              subst plan
              exact ⟨rfl, rfl, member, sameHead⟩
            · simp [activationEq, compiledEq, member, sameHead] at accepted
          · simp [activationEq, compiledEq, member] at accepted

/-- A composed artifact inherits exactness from both independent compiler
certificates. -/
theorem match_compile?_some
    (producer : TypedRule) (source : Term)
    (consumerHeads : List Term) (consumer : Term)
    (width : UInt32) (plan : Plan width)
    (accepted : compile? producer source consumerHeads consumer width =
      some plan)
    (sourceEnvironment : Substitution)
    (sourceConsumerEnvironment : SourceEnvironment)
    (denseConsumerEnvironment : DenseEnvironment width)
    (related : decodeDense width denseConsumerEnvironment =
      sourceConsumerEnvironment) :
    Option.map (decodeDense width)
        (matchDenseView sourceEnvironment source plan.consumer
          denseConsumerEnvironment) =
      CompiledPlanActivationViewCompilation.matchView
        sourceEnvironment source consumer
        sourceConsumerEnvironment := by
  exact matchDenseView_compileTerm? width source consumer plan.consumer
    (compile?_success producer source consumerHeads consumer width plan
      accepted).2.1 sourceEnvironment sourceConsumerEnvironment
      denseConsumerEnvironment related

/-- The direct composition constructs no complete source body.  Any subtree
capture remains governed by the existing activation-view certificate. -/
def compiledCapturedMaterializations (plan : Plan width)
    (consumer : Term) : Nat :=
  CompiledPlanActivationViewCompilation.compiledCapturedMaterializations
    plan.activation consumer

theorem compiledCapturedMaterializations_eq_zero
    (producer : TypedRule) (source : Term)
    (consumerHeads : List Term) (consumer : Term)
    (width : UInt32) (plan : Plan width)
    (accepted : compile? producer source consumerHeads consumer width =
      some plan) :
    compiledCapturedMaterializations plan consumer = 0 := by
  obtain ⟨activationEq, _, member, sameHead⟩ :=
    compile?_success producer source consumerHeads consumer width plan accepted
  exact
    CompiledPlanActivationViewCompilation.compiledCapturedMaterializations_eq_zero
    producer source consumer consumerHeads plan.activation activationEq member
      sameHead

theorem compiledMaterializations_lt_source
    (producer : TypedRule) (source : Term)
    (consumerHeads : List Term) (consumer : Term)
    (width : UInt32) (plan : Plan width)
    (accepted : compile? producer source consumerHeads consumer width =
      some plan) :
    compiledCapturedMaterializations plan consumer <
      CompiledPlanActivationViewCompilation.sourceWholeTermMaterializations
        plan.activation := by
  rw [compiledCapturedMaterializations_eq_zero producer source consumerHeads
    consumer width plan accepted]
  simp [CompiledPlanActivationViewCompilation.sourceWholeTermMaterializations]

/-! ## Composition with candidate traversal and raw-tail frame reuse -/

/-- The compiled cursor establishes a representation-independent raw tail
exactly when neither generated candidates nor external rows remain. -/
def rawTail? (laterGenerated : List α) (laterExternal : List β) : Bool :=
  laterGenerated.isEmpty && laterExternal.isEmpty

theorem rawTail?_eq_true_iff
    (laterGenerated : List α) (laterExternal : List β) :
    rawTail? laterGenerated laterExternal = true ↔
      laterGenerated = [] ∧ laterExternal = [] := by
  simp [rawTail?]

/-- Candidate scheduling never needs to force an admitted activation view.
The exact matcher, rather than a representation-sensitive prefilter, decides
whether the current candidate matches.  Later candidates therefore remain a
control-flow concern rather than a reason to change representation. -/
def matchDenseViewScheduled (_laterGenerated : List α)
    (_laterExternal : List β) (sourceEnvironment : Substitution)
    (source : Term) (pattern : DenseTerm width)
    (patternEnvironment : DenseEnvironment width) :
    Option (DenseEnvironment width) :=
  matchDenseView sourceEnvironment source pattern patternEnvironment

/-- Direct traversal preserves the independent materialize-then-match
semantics regardless of later generated or extensional alternatives. -/
theorem matchDenseViewScheduled_eq_materialized
    (laterGenerated : List α) (laterExternal : List β)
    (sourceEnvironment : Substitution) (source : Term)
    (pattern : DenseTerm width)
    (patternEnvironment : DenseEnvironment width) :
    matchDenseViewScheduled laterGenerated laterExternal sourceEnvironment
        source pattern patternEnvironment =
      match instantiateTerm sourceEnvironment source with
      | none => none
      | some target => matchDense pattern target patternEnvironment := by
  exact matchDenseView_eq_materialized sourceEnvironment source pattern
    patternEnvironment

/-- The direct schedule constructs no complete source term. -/
def scheduledSourceMaterializations (_laterGenerated : List α)
    (_laterExternal : List β) : Nat :=
  0

theorem scheduledSourceMaterializations_eq_zero
    (laterGenerated : List α) (laterExternal : List β) :
    scheduledSourceMaterializations laterGenerated laterExternal = 0 := by
  rfl

theorem rawTail_strict_materialization_reduction :
    scheduledSourceMaterializations ([] : List α) ([] : List β) < 1 := by
  simp [scheduledSourceMaterializations]

theorem generated_alternatives_strict_materialization_reduction :
    scheduledSourceMaterializations [()] ([] : List Unit) < 1 := by
  simp [scheduledSourceMaterializations]

theorem external_alternatives_strict_materialization_reduction :
    scheduledSourceMaterializations ([] : List Unit) [()] < 1 := by
  simp [scheduledSourceMaterializations]

example : scheduledSourceMaterializations [()] ([] : List Unit) = 0 := by
  rfl

example : scheduledSourceMaterializations ([] : List Unit) [()] = 0 := by
  rfl

/-! ### Exact traversal over multiple candidates -/

/-- Return the index and environment of the first dense consumer that matches
an admitted source view. -/
def firstDenseViewMatch (sourceEnvironment : Substitution) (source : Term)
    (patternEnvironment : DenseEnvironment width) :
    List (DenseTerm width) → Option (Nat × DenseEnvironment width)
  | [] => none
  | pattern :: patterns =>
      match matchDenseView sourceEnvironment source pattern
          patternEnvironment with
      | some extended => some (0, extended)
      | none =>
          (firstDenseViewMatch sourceEnvironment source patternEnvironment
            patterns).map fun result => (result.1 + 1, result.2)

/-- Materialize once and return the index and environment of the first dense
consumer that matches. -/
def firstDenseMatch (target : GroundTerm)
    (patternEnvironment : DenseEnvironment width) :
    List (DenseTerm width) → Option (Nat × DenseEnvironment width)
  | [] => none
  | pattern :: patterns =>
      match matchDense pattern target patternEnvironment with
      | some extended => some (0, extended)
      | none =>
          (firstDenseMatch target patternEnvironment patterns).map fun result =>
            (result.1 + 1, result.2)

/-- Direct view traversal preserves both the selected alternative and its
dense environment for an arbitrary finite candidate inventory. -/
theorem firstDenseViewMatch_eq_materialized
    (sourceEnvironment : Substitution) (source : Term)
    (patterns : List (DenseTerm width))
    (patternEnvironment : DenseEnvironment width) :
    firstDenseViewMatch sourceEnvironment source patternEnvironment patterns =
      match instantiateTerm sourceEnvironment source with
      | none => none
      | some target => firstDenseMatch target patternEnvironment patterns := by
  induction patterns with
  | nil =>
      cases instantiateTerm sourceEnvironment source <;> rfl
  | cons pattern patterns inductionHypothesis =>
      simp only [firstDenseViewMatch, firstDenseMatch]
      rw [matchDenseView_eq_materialized]
      cases instantiated : instantiateTerm sourceEnvironment source with
      | none =>
          rw [instantiated] at inductionHypothesis
          simp only at inductionHypothesis
          simp only [Option.map]
          rw [inductionHypothesis]
      | some target =>
          rw [instantiated] at inductionHypothesis
          simp only at inductionHypothesis
          cases matched : matchDense pattern target patternEnvironment with
          | none =>
              simp only [matched]
              rw [inductionHypothesis]
          | some extended =>
              simp only [matched]

/-! ## Independent witnesses and rejecting controls -/

private def parserProducer : TypedRule :=
  { name := [1]
    head := .application [10] (.cons (.variable 0) .nil)
    body := [.application [11] (.cons (.variable 0) .nil)]
    variableCount := 1 }

private def parserBody : Term :=
  .application [11] (.cons (.variable 0) .nil)

private def parserConsumer : Term :=
  .application [11] (.cons (.variable 0) .nil)

private def ruleMachineProducer : TypedRule :=
  { name := [2]
    head := .application [20]
      (.cons (.variable 0) (.cons (.variable 1) .nil))
    body := [.application [21]
      (.cons (.variable 0) (.cons (.variable 1) .nil))]
    variableCount := 2 }

private def ruleMachineBody : Term :=
  .application [21]
    (.cons (.variable 0) (.cons (.variable 1) .nil))

private def ruleMachineConsumer : Term :=
  .application [21]
    (.cons (.variable 0) (.cons (.variable 1) .nil))

example : (compile? parserProducer parserBody [parserConsumer]
    parserConsumer 1).isSome = true := by decide

example : (compile? ruleMachineProducer ruleMachineBody
    [ruleMachineConsumer] ruleMachineConsumer 2).isSome = true := by decide

/-- A consumer absent from the complete inventory is rejected. -/
example : (compile? parserProducer parserBody [] parserConsumer 1).isSome =
    false := by decide

/-- A consumer whose slot exceeds its generated width is rejected. -/
example : (compile? parserProducer parserBody
    [.application [11] (.cons (.variable 1) .nil)]
    (.application [11] (.cons (.variable 1) .nil)) 1).isSome = false := by
  decide

/-- A same-head consumer that would capture a variable-bearing source
application is rejected by the activation certificate before composition. -/
example :
    (compile? parserProducer
      (.application [11]
        (.cons (.application [12] (.cons (.variable 0) .nil)) .nil))
      [.application [11] (.cons (.variable 0) .nil)]
      (.application [11] (.cons (.variable 0) .nil)) 1).isSome = false := by
  decide

end Mettapedia.GSLT.LanguageDef.CompiledPlanDenseActivationViewCompilation
