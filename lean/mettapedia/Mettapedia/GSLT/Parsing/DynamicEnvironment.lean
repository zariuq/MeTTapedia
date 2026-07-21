import Mettapedia.GSLT.Parsing.HornCertificate

/-!
# Presentation-declared dynamic syntax

Dynamic concrete syntax is an ordinary environment-indexed Horn relation.  A
relation shape declares how many ground terms constitute the pre-state and
post-state; the event occupies the single middle argument.  The generic fold
below knows no declaration, scope, priority, associativity, or guest-language
policy.  Every transition is accepted only by replaying a certificate against
the admitted Horn program.
-/

namespace Mettapedia.GSLT.Parsing.DynamicEnvironment

open HornCertificate

abbrev Configuration := List GroundTerm
abbrev Event := GroundTerm

structure RelationShape where
  relation : String
  stateArity : Nat
  deriving DecidableEq, Repr

def shapeValid (shape : RelationShape) : Bool :=
  decide (shape.stateArity > 0)

def makeStepGoal (shape : RelationShape)
    (before : Configuration) (event : Event)
    (after : Configuration) : Option GroundAtom :=
  if before.length != shape.stateArity then none
  else if after.length != shape.stateArity then none
  else some {
    relation := shape.relation
    arguments := GroundTerms.ofList (before ++ [event] ++ after) }

def SourceStep (program : Program) (shape : RelationShape)
    (before : Configuration) (event : Event)
    (after : Configuration) : Prop :=
  shapeValid shape = true ∧
  ∃ fuel goal,
    makeStepGoal shape before event after = some goal ∧
    DerivesWithin program fuel goal

structure StepCertificate where
  before : Configuration
  event : Event
  after : Configuration
  fuel : Nat
  certificate : HornCertificate.Certificate
  deriving DecidableEq, Repr

def replayStep (program : Program) (shape : RelationShape)
    (certificate : StepCertificate) : Bool :=
  shapeValid shape &&
  match makeStepGoal shape certificate.before certificate.event
      certificate.after with
  | none => false
  | some goal => replay program certificate.fuel goal certificate.certificate

theorem replayStep_sound (program : Program) (shape : RelationShape)
    (certificate : StepCertificate)
    (accepted : replayStep program shape certificate = true) :
    SourceStep program shape certificate.before certificate.event
      certificate.after := by
  cases goalEquation : makeStepGoal shape certificate.before certificate.event
      certificate.after with
  | none => simp [replayStep, goalEquation] at accepted
  | some goal =>
      simp only [replayStep, goalEquation, Bool.and_eq_true] at accepted
      exact ⟨accepted.1, certificate.fuel, goal, goalEquation,
        replay_sound program certificate.fuel goal certificate.certificate
          accepted.2⟩

inductive Runs (program : Program) (shape : RelationShape) :
    Configuration → List Event → Configuration → Prop where
  | nil (configuration) : Runs program shape configuration [] configuration
  | cons (before event middle events after)
      (step : SourceStep program shape before event middle)
      (rest : Runs program shape middle events after) :
      Runs program shape before (event :: events) after

def replayRun (program : Program) (shape : RelationShape) :
    Configuration → List Event → List StepCertificate → Option Configuration
  | current, [], [] => some current
  | _, [], _ :: _ => none
  | _, _ :: _, [] => none
  | current, event :: events, certificate :: certificates =>
      if certificate.before != current then none
      else if certificate.event != event then none
      else if replayStep program shape certificate != true then none
      else replayRun program shape certificate.after events certificates

theorem replayRun_sound (program : Program) (shape : RelationShape)
    (current : Configuration) (events : List Event)
    (certificates : List StepCertificate) (final : Configuration)
    (accepted : replayRun program shape current events certificates = some final) :
    Runs program shape current events final := by
  induction certificates generalizing current events final with
  | nil =>
      cases events with
      | nil =>
          simp [replayRun] at accepted
          subst final
          exact .nil current
      | cons event events => simp [replayRun] at accepted
  | cons certificate certificates inductionHypothesis =>
      cases events with
      | nil => simp [replayRun] at accepted
      | cons event events =>
          by_cases before : certificate.before = current
          · by_cases sameEvent : certificate.event = event
            · by_cases replayed : replayStep program shape certificate = true
              · have rest : replayRun program shape certificate.after events
                    certificates = some final := by
                  simpa [replayRun, before, sameEvent, replayed] using accepted
                exact .cons current event certificate.after events final
                  (by simpa [before, sameEvent] using
                    replayStep_sound program shape certificate replayed)
                  (inductionHypothesis certificate.after events final rest)
              · simp [replayRun, before, sameEvent, replayed] at accepted
            · simp [replayRun, before, sameEvent] at accepted
          · simp [replayRun, before] at accepted

theorem sourceStep_complete (program : Program) (shape : RelationShape)
    {before : Configuration} {event : Event} {after : Configuration}
    (step : SourceStep program shape before event after) :
    ∃ certificate : StepCertificate,
      certificate.before = before ∧ certificate.event = event ∧
      certificate.after = after ∧
      replayStep program shape certificate = true := by
  obtain ⟨valid, fuel, goal, goalEquation, derivation⟩ := step
  obtain ⟨proof, accepted⟩ :=
    derivesWithin_complete program fuel goal derivation
  let certificate : StepCertificate := {
    before := before
    event := event
    after := after
    fuel := fuel
    certificate := proof }
  refine ⟨certificate, rfl, rfl, rfl, ?_⟩
  simp [certificate, replayStep, valid, goalEquation, accepted]

theorem runs_complete (program : Program) (shape : RelationShape)
    {current : Configuration} {events : List Event} {final : Configuration}
    (run : Runs program shape current events final) :
    ∃ certificates,
      replayRun program shape current events certificates = some final := by
  induction run with
  | nil configuration => exact ⟨[], rfl⟩
  | cons before event middle events after step rest inductionHypothesis =>
      obtain ⟨certificate, beforeEq, eventEq, afterEq, accepted⟩ :=
        sourceStep_complete program shape step
      obtain ⟨certificates, restAccepted⟩ := inductionHypothesis
      refine ⟨certificate :: certificates, ?_⟩
      simp [replayRun, beforeEq, eventEq, afterEq, accepted, restAccepted]

theorem replayRun_iff_runs (program : Program) (shape : RelationShape)
    (current : Configuration) (events : List Event) (final : Configuration) :
    (∃ certificates,
      replayRun program shape current events certificates = some final) ↔
      Runs program shape current events final := by
  constructor
  · rintro ⟨certificates, accepted⟩
    exact replayRun_sound program shape current events certificates final accepted
  · exact runs_complete program shape

def sourceResults (program : Program) (shape : RelationShape)
    (initial : Configuration) (events : List Event) : Set Configuration :=
  { final | Runs program shape initial events final }

def certifiedResults (program : Program) (shape : RelationShape)
    (initial : Configuration) (events : List Event) : Set Configuration :=
  { final | ∃ certificates,
      replayRun program shape initial events certificates = some final }

theorem complete_result_set_agreement (program : Program)
    (shape : RelationShape) (initial : Configuration) (events : List Event) :
    certifiedResults program shape initial events =
      sourceResults program shape initial events := by
  ext final
  exact replayRun_iff_runs program shape initial events final

def Ambiguous (results : Set Configuration) : Prop :=
  ∃ first ∈ results, ∃ second ∈ results, first ≠ second

theorem complete_ambiguity_agreement (program : Program)
    (shape : RelationShape) (initial : Configuration) (events : List Event) :
    Ambiguous (certifiedResults program shape initial events) ↔
      Ambiguous (sourceResults program shape initial events) := by
  rw [complete_result_set_agreement]

/-! ## Executable scoped-shadowing controls -/

def terms (items : List Term) : Terms := Terms.ofList items
def groundTerms (items : List GroundTerm) : GroundTerms := GroundTerms.ofList items

def bindRule : Rule :=
  { name := "bind"
    head := {
      relation := "step"
      arguments := terms [
        .var 0,
        .app "bind" (terms [.var 1, .var 2]),
        .app "env-add" (terms [.var 0, .var 1, .var 2])] }
    body := [] }

def openRule : Rule :=
  { name := "open"
    head := {
      relation := "step"
      arguments := terms [
        .var 0,
        .app "open" (terms [.var 1]),
        .app "scoped" (terms [.var 0, .var 1, .var 0])] }
    body := [] }

def scopedBindRule : Rule :=
  { name := "scoped-bind"
    head := {
      relation := "step"
      arguments := terms [
        .app "scoped" (terms [.var 0, .var 1, .var 2]),
        .app "bind" (terms [.var 3, .var 4]),
        .app "scoped" (terms [
          .app "env-add" (terms [.var 0, .var 3, .var 4]),
          .var 1,
          .var 2])] }
    body := [] }

def closeRule : Rule :=
  { name := "close"
    head := {
      relation := "step"
      arguments := terms [
        .app "scoped" (terms [.var 0, .var 1, .var 2]),
        .app "close" (terms [.var 1]),
        .var 2] }
    body := [] }

def scopedProgram : Program := [bindRule, openRule, scopedBindRule, closeRule]
def stepShape : RelationShape := { relation := "step", stateArity := 1 }

def emptyEnvironment : GroundTerm := .atom "env-empty"
def operatorName : GroundTerm := .atom "operator"
def outerValue : GroundTerm := .atom "outer"
def innerValue : GroundTerm := .atom "inner"
def scopeName : GroundTerm := .atom "scope"

def bindEvent (value : GroundTerm) : Event :=
  .app "bind" (groundTerms [operatorName, value])

def openEvent : Event := .app "open" (groundTerms [scopeName])
def closeEvent : Event := .app "close" (groundTerms [scopeName])
def wrongCloseEvent : Event := .app "close" (groundTerms [.atom "other"])

def outerEnvironment : GroundTerm :=
  .app "env-add" (groundTerms [emptyEnvironment, operatorName, outerValue])

def openedEnvironment : GroundTerm :=
  .app "scoped" (groundTerms [outerEnvironment, scopeName, outerEnvironment])

def innerEnvironment : GroundTerm :=
  .app "env-add" (groundTerms [outerEnvironment, operatorName, innerValue])

def shadowedEnvironment : GroundTerm :=
  .app "scoped" (groundTerms [innerEnvironment, scopeName, outerEnvironment])

def bindOuterProof : HornCertificate.Certificate :=
  .node bindRule [(0, emptyEnvironment), (1, operatorName), (2, outerValue)] .nil

def openProof : HornCertificate.Certificate :=
  .node openRule [(0, outerEnvironment), (1, scopeName)] .nil

def bindInnerProof : HornCertificate.Certificate :=
  .node scopedBindRule [
    (0, outerEnvironment), (1, scopeName), (2, outerEnvironment),
    (3, operatorName), (4, innerValue)] .nil

def closeProof : HornCertificate.Certificate :=
  .node closeRule [
    (0, innerEnvironment), (1, scopeName), (2, outerEnvironment)] .nil

def bindOuterCertificate : StepCertificate :=
  { before := [emptyEnvironment]
    event := bindEvent outerValue
    after := [outerEnvironment]
    fuel := 1
    certificate := bindOuterProof }

def openCertificate : StepCertificate :=
  { before := [outerEnvironment]
    event := openEvent
    after := [openedEnvironment]
    fuel := 1
    certificate := openProof }

def bindInnerCertificate : StepCertificate :=
  { before := [openedEnvironment]
    event := bindEvent innerValue
    after := [shadowedEnvironment]
    fuel := 1
    certificate := bindInnerProof }

def closeCertificate : StepCertificate :=
  { before := [shadowedEnvironment]
    event := closeEvent
    after := [outerEnvironment]
    fuel := 1
    certificate := closeProof }

def scopedCertificates : List StepCertificate :=
  [bindOuterCertificate, openCertificate, bindInnerCertificate, closeCertificate]

def scopedEvents : List Event :=
  [bindEvent outerValue, openEvent, bindEvent innerValue, closeEvent]

theorem scopedShadowingAndRestoration_accepts :
    replayRun scopedProgram stepShape [emptyEnvironment] scopedEvents
      scopedCertificates = some [outerEnvironment] := by
  decide

theorem scopedShadowingAndRestoration_isSound :
    Runs scopedProgram stepShape [emptyEnvironment] scopedEvents
      [outerEnvironment] :=
  replayRun_sound scopedProgram stepShape [emptyEnvironment] scopedEvents
    scopedCertificates [outerEnvironment]
    scopedShadowingAndRestoration_accepts

theorem innerBinding_isDistinct : shadowedEnvironment ≠ openedEnvironment := by
  decide

theorem mismatchedClose_rejects :
    replayRun scopedProgram stepShape [emptyEnvironment]
      [bindEvent outerValue, openEvent, bindEvent innerValue, wrongCloseEvent]
      scopedCertificates = none := by
  decide

def programWithoutClose : Program := [bindRule, openRule, scopedBindRule]

theorem closeRuleDeletion_rejects :
    replayRun programWithoutClose stepShape [emptyEnvironment] scopedEvents
      scopedCertificates = none := by
  decide

end Mettapedia.GSLT.Parsing.DynamicEnvironment
