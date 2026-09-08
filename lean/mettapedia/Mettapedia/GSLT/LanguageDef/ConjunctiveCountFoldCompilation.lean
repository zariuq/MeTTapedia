import Mettapedia.GSLT.Dynamics.CollapseObservationContract
import Mettapedia.GSLT.LanguageDef.FlatTermDeadBindingCountCompilation

/-!
# Streaming compilation of pure conjunctive count folds

A materializing conjunction constructs every intermediate binding row and
counts the final list.  A count observer needs only the cardinality.  This
module proves that streaming accumulation of terminal units has exactly the
same meaning, including duplicate occurrences and cross-leg dependencies.

The producer is abstract in both pattern and environment.  Syntax trees,
compiled plans, BN closures, CBPV thunks, and relational rows therefore share
the theorem by supplying one pure `extend` operation.  A rigid leg may be
contracted to a multiplicative factor only with evidence that it preserves the
incoming environment; the negative canary shows why multiplying arbitrary leg
cardinalities is unsound.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ConjunctiveCountFoldCompilation

open Mettapedia.GSLT.Dynamics.Collapse
open Mettapedia.GSLT.Dynamics.CollapseObservationContract
open Mettapedia.GSLT.LanguageDef.FlatTermDeadBindingCountCompilation

universe uPattern uEnvironment uFrontPattern

/-- Pure relational extension of one environment by one conjunct.  The list
retains order and duplicate occurrences, although count observation later
forgets order. -/
structure PureConjunctionProducer
    (Pattern : Type uPattern) (Environment : Type uEnvironment) where
  extend : Environment → Pattern → List Environment

/-- Materializing reference evaluation from one seed environment. -/
def materializeFrom
    {Pattern : Type uPattern} {Environment : Type uEnvironment}
    (producer : PureConjunctionProducer Pattern Environment) :
    List Pattern → Environment → List Environment
  | [], environment => [environment]
  | pattern :: rest, environment =>
      (producer.extend environment pattern).flatMap
        (materializeFrom producer rest)

/-- Streaming count evaluation: retain only one path environment and add one
unit at each completed path. -/
def streamCountFrom
    {Pattern : Type uPattern} {Environment : Type uEnvironment}
    (producer : PureConjunctionProducer Pattern Environment) :
    List Pattern → Environment → Nat
  | [], _environment => 1
  | pattern :: rest, environment =>
      ((producer.extend environment pattern).map
        (streamCountFrom producer rest)).sum

/-- Keystone refinement: streaming terminal-unit accumulation is exactly the
length of the fully materialized binding relation. -/
theorem streamCountFrom_exact
    {Pattern : Type uPattern} {Environment : Type uEnvironment}
    (producer : PureConjunctionProducer Pattern Environment)
    (patterns : List Pattern) (environment : Environment) :
    streamCountFrom producer patterns environment =
      (materializeFrom producer patterns environment).length := by
  induction patterns generalizing environment with
  | nil => rfl
  | cons pattern rest inductionHypothesis =>
      simp only [streamCountFrom, materializeFrom, List.length_flatMap]
      apply congrArg List.sum
      exact List.map_congr_left fun next _ => inductionHypothesis next

/-- The same theorem stated through the shared collapse count algebra. -/
theorem streamCountFrom_countAlg_exact
    {Pattern : Type uPattern} {Environment : Type uEnvironment}
    (producer : PureConjunctionProducer Pattern Environment)
    (patterns : List Pattern) (environment : Environment) :
    streamCountFrom producer patterns environment =
      collapseWith (CountAlg Unit Unit)
        (unitCountObservations
          (materializeFrom producer patterns environment)) := by
  rw [collapseCount_unitCountObservations]
  exact streamCountFrom_exact producer patterns environment

/-- Reference meaning of a private let which binds the completed relation and
then observes only its tuple size. -/
def letCollapseSize
    {Pattern : Type uPattern} {Environment : Type uEnvironment}
    (producer : PureConjunctionProducer Pattern Environment)
    (patterns : List Pattern) (environment : Environment) : Nat :=
  (materializeFrom producer patterns environment).length

/-- Deforestation law for `let x = collapse(conjunction) in size x`: the
private tuple may be replaced by its streaming count fold. -/
theorem letCollapseSize_eq_streamCountFrom
    {Pattern : Type uPattern} {Environment : Type uEnvironment}
    (producer : PureConjunctionProducer Pattern Environment)
    (patterns : List Pattern) (environment : Environment) :
    letCollapseSize producer patterns environment =
      streamCountFrom producer patterns environment := by
  exact (streamCountFrom_exact producer patterns environment).symm

/-! ## Consumer certificates and representation-independent direct folds -/

/-- A frontend-owned proof that one unary collection consumer observes only
cardinality.  The consumer may be a primitive, a pair of recursive equations,
or a compiled closure; this interface retains only its semantic algebra. -/
structure CardinalityConsumerCertificate (Row : Type uEnvironment) where
  observe : List Row → Nat
  observe_nil : observe [] = 0
  observe_cons : ∀ row rows,
    observe (row :: rows) = Nat.succ (observe rows)

namespace CardinalityConsumerCertificate

/-- The two list-algebra equations determine the consumer uniquely. -/
theorem observe_eq_length
    {Row : Type uEnvironment}
    (certificate : CardinalityConsumerCertificate Row)
    (rows : List Row) :
    certificate.observe rows = rows.length := by
  induction rows with
  | nil => exact certificate.observe_nil
  | cons row rows inductionHypothesis =>
      rw [certificate.observe_cons, inductionHypothesis]
      rfl

/-- Ordinary list length is the canonical cardinality consumer. -/
def length (Row : Type uEnvironment) :
    CardinalityConsumerCertificate Row where
  observe := List.length
  observe_nil := rfl
  observe_cons := fun _ _ => rfl

/-- Pull a certified frontend consumer through the conjunction without ever
constructing its intermediate row list. -/
theorem observe_materialize_eq_streamCountFrom
    {Pattern : Type uPattern} {Environment : Type uEnvironment}
    (producer : PureConjunctionProducer Pattern Environment)
    (certificate : CardinalityConsumerCertificate Environment)
    (patterns : List Pattern) (environment : Environment) :
    certificate.observe
        (materializeFrom producer patterns environment) =
      streamCountFrom producer patterns environment := by
  calc
    certificate.observe
        (materializeFrom producer patterns environment) =
        (materializeFrom producer patterns environment).length :=
      certificate.observe_eq_length _
    _ = streamCountFrom producer patterns environment :=
      (streamCountFrom_exact producer patterns environment).symm

/-- The same frontend certificate factors through the shared collapse count
algebra.  This is the contract transported by an evaluator adapter. -/
theorem observe_materialize_eq_countAlg
    {Pattern : Type uPattern} {Environment : Type uEnvironment}
    (producer : PureConjunctionProducer Pattern Environment)
    (certificate : CardinalityConsumerCertificate Environment)
    (patterns : List Pattern) (environment : Environment) :
    certificate.observe
        (materializeFrom producer patterns environment) =
      collapseWith (CountAlg Unit Unit)
        (unitCountObservations
          (materializeFrom producer patterns environment)) := by
  rw [certificate.observe_eq_length,
    collapseCount_unitCountObservations]

end CardinalityConsumerCertificate

/-- A conjunction query packages the producer-independent source needed by a
direct count fold. -/
abbrev ConjunctionSource
    (Pattern : Type uPattern) (Environment : Type uEnvironment) :=
  List Pattern × Environment

/-- Materialized count observations for the abstract conjunction producer. -/
def conjunctionCountProducer
    {Pattern : Type uPattern} {Environment : Type uEnvironment}
    (producer : PureConjunctionProducer Pattern Environment) :
    Producer (ConjunctionSource Pattern Environment) (Obs Unit Unit) where
  materialize source :=
    unitCountObservations
      (materializeFrom producer source.1 source.2)

/-- The streaming conjunction evaluator is a direct implementation of the
shared count algebra.  Its source contains no evaluator or dialect choice. -/
def directCountFold
    {Pattern : Type uPattern} {Environment : Type uEnvironment}
    (producer : PureConjunctionProducer Pattern Environment) :
    DirectFold (conjunctionCountProducer producer) (CountAlg Unit Unit) where
  run source := streamCountFrom producer source.1 source.2
  refines source :=
    streamCountFrom_countAlg_exact producer source.1 source.2

@[simp] theorem directCountFold_run
    {Pattern : Type uPattern} {Environment : Type uEnvironment}
    (producer : PureConjunctionProducer Pattern Environment)
    (source : ConjunctionSource Pattern Environment) :
    (directCountFold producer).run source =
      streamCountFrom producer source.1 source.2 :=
  rfl

/-- A BN closure, CBPV thunk, syntax tree, or relational-row frontend reuses
the same native fold by presenting its query as an abstract conjunction
source. -/
def directCountFoldFromFrontend
    {Pattern : Type uPattern} {Environment : Type uEnvironment}
    {FrontendSource : Type uFrontPattern}
    (producer : PureConjunctionProducer Pattern Environment)
    (denote : FrontendSource → ConjunctionSource Pattern Environment) :
    DirectFold
      ((conjunctionCountProducer producer).pullback denote)
      (CountAlg Unit Unit) :=
  (directCountFold producer).pullback denote

@[simp] theorem directCountFoldFromFrontend_run
    {Pattern : Type uPattern} {Environment : Type uEnvironment}
    {FrontendSource : Type uFrontPattern}
    (producer : PureConjunctionProducer Pattern Environment)
    (denote : FrontendSource → ConjunctionSource Pattern Environment)
    (source : FrontendSource) :
    (directCountFoldFromFrontend producer denote).run source =
      streamCountFrom producer (denote source).1 (denote source).2 :=
  rfl

/-- Evidence that one conjunct is a multiplicity factor: every occurrence
returns the same incoming environment and therefore creates no binding needed
by the continuation. -/
structure RigidLegCertificate
    {Pattern : Type uPattern} {Environment : Type uEnvironment}
    (producer : PureConjunctionProducer Pattern Environment)
    (environment : Environment) (pattern : Pattern) where
  multiplicity : Nat
  exact : producer.extend environment pattern =
    List.replicate multiplicity environment

/-- A certified rigid leg multiplies the continuation count. -/
theorem streamCountFrom_rigid_factor
    {Pattern : Type uPattern} {Environment : Type uEnvironment}
    (producer : PureConjunctionProducer Pattern Environment)
    (environment : Environment) (pattern : Pattern)
    (rest : List Pattern)
    (certificate : RigidLegCertificate producer environment pattern) :
    streamCountFrom producer (pattern :: rest) environment =
      certificate.multiplicity *
        streamCountFrom producer rest environment := by
  simp [streamCountFrom, certificate.exact]

/-- At the terminal leg every produced environment is dead.  Any exact direct
row counter may therefore replace it without reconstructing those rows. -/
structure FinalDeadLegCertificate
    {Pattern : Type uPattern} {Environment : Type uEnvironment}
    (producer : PureConjunctionProducer Pattern Environment)
    (environment : Environment) (pattern : Pattern) where
  count : Nat
  exact : count = (producer.extend environment pattern).length

/-- A certified dead final leg is exactly its direct row count. -/
theorem streamCountFrom_final_dead
    {Pattern : Type uPattern} {Environment : Type uEnvironment}
    (producer : PureConjunctionProducer Pattern Environment)
    (environment : Environment) (pattern : Pattern)
    (certificate : FinalDeadLegCertificate producer environment pattern) :
    streamCountFrom producer [pattern] environment = certificate.count := by
  rw [streamCountFrom_exact, certificate.exact]
  simp [materializeFrom]

/-! ## Frontend transport -/

/-- Change only the frontend pattern representation.  The environment and
relational extension law remain unchanged. -/
def pullbackPattern
    {Pattern : Type uPattern} {Environment : Type uEnvironment}
    {FrontPattern : Type uFrontPattern}
    (producer : PureConjunctionProducer Pattern Environment)
    (lower : FrontPattern → Pattern) :
    PureConjunctionProducer FrontPattern Environment where
  extend environment pattern := producer.extend environment (lower pattern)

theorem materializeFrom_pullbackPattern
    {Pattern : Type uPattern} {Environment : Type uEnvironment}
    {FrontPattern : Type uFrontPattern}
    (producer : PureConjunctionProducer Pattern Environment)
    (lower : FrontPattern → Pattern)
    (patterns : List FrontPattern) (environment : Environment) :
    materializeFrom (pullbackPattern producer lower) patterns environment =
      materializeFrom producer (patterns.map lower) environment := by
  induction patterns generalizing environment with
  | nil => rfl
  | cons pattern rest inductionHypothesis =>
      simp only [materializeFrom, pullbackPattern, List.map_cons]
      apply List.flatMap_congr
      intro next _
      exact inductionHypothesis next

theorem streamCountFrom_pullbackPattern
    {Pattern : Type uPattern} {Environment : Type uEnvironment}
    {FrontPattern : Type uFrontPattern}
    (producer : PureConjunctionProducer Pattern Environment)
    (lower : FrontPattern → Pattern)
    (patterns : List FrontPattern) (environment : Environment) :
    streamCountFrom (pullbackPattern producer lower) patterns environment =
      streamCountFrom producer (patterns.map lower) environment := by
  induction patterns generalizing environment with
  | nil => rfl
  | cons pattern rest inductionHypothesis =>
      simp only [streamCountFrom, pullbackPattern, List.map_cons]
      apply congrArg List.sum
      exact List.map_congr_left fun next _ => inductionHypothesis next

/-! ## Discriminating canaries -/

namespace Canary

inductive Leg
  | choose
  | requireEven
deriving DecidableEq, Repr

/-- The first leg emits `1, 2, 2`; the second keeps even environments. -/
def dependentProducer : PureConjunctionProducer Leg Nat where
  extend environment
    | .choose => [1, 2, 2]
    | .requireEven => if environment % 2 = 0 then [environment] else []

/-- Positive: duplicates survive and the later leg reads the chosen value. -/
example :
    streamCountFrom dependentProducer [.choose, .requireEven] 0 = 2 := by
  decide

/-- The materializing oracle retains the same two duplicate terminal rows. -/
example :
    materializeFrom dependentProducer [.choose, .requireEven] 0 = [2, 2] := by
  decide

/-- Negative: multiplying per-leg counts at the initial environment gives
three, not the dependent conjunction's true count of two. -/
example :
    streamCountFrom dependentProducer [.choose, .requireEven] 0 ≠
      (dependentProducer.extend 0 .choose).length *
        (dependentProducer.extend 0 .requireEven).length := by
  decide

/-- Negative observer canary: equal counts do not license replacing a let
whose body observes the first row. -/
example :
    [1, 2].length = [2, 1].length ∧
      [1, 2].head? ≠ [2, 1].head? := by
  decide

/-- A concrete recursive frontend consumer earns the generic count contract
solely from its empty and constructor equations. -/
def recursiveCount : List Nat → Nat
  | [] => 0
  | _ :: rest => Nat.succ (recursiveCount rest)

def recursiveCountCertificate :
    CardinalityConsumerCertificate Nat where
  observe := recursiveCount
  observe_nil := rfl
  observe_cons := fun _ _ => rfl

example : recursiveCount [7, 8, 9] = 3 := by
  decide

/-- Negative: accepting only the empty equation would admit a head-sensitive
consumer, which cannot satisfy the constructor equation and is not a count. -/
def headSensitive : List Bool → Nat
  | [] => 0
  | head :: _ => if head then 1 else 0

example : headSensitive [] = 0 := rfl

example : ¬ ∀ head rest,
    headSensitive (head :: rest) = Nat.succ (headSensitive rest) := by
  intro claimed
  simpa [headSensitive] using claimed false [true]

/-- The certified recursive consumer and the streaming conjunction agree on
the duplicate-sensitive dependent example. -/
example :
    recursiveCount
        (materializeFrom dependentProducer
          [.choose, .requireEven] 0) =
      streamCountFrom dependentProducer
        [.choose, .requireEven] 0 := by
  exact recursiveCountCertificate.observe_materialize_eq_streamCountFrom
    dependentProducer [.choose, .requireEven] 0

/-- Positive rigid factor: three indistinguishable occurrences of a guard
multiply the continuation count without changing its environment. -/
def tripleGuardProducer : PureConjunctionProducer Unit Nat where
  extend environment _ := [environment, environment, environment]

def tripleGuardCertificate (environment : Nat) :
    RigidLegCertificate tripleGuardProducer environment () where
  multiplicity := 3
  exact := rfl

example :
    streamCountFrom tripleGuardProducer [(), ()] 7 = 9 := by
  decide

end Canary

#print axioms streamCountFrom_exact
#print axioms streamCountFrom_countAlg_exact
#print axioms letCollapseSize_eq_streamCountFrom
#print axioms streamCountFrom_rigid_factor
#print axioms streamCountFrom_final_dead
#print axioms materializeFrom_pullbackPattern
#print axioms streamCountFrom_pullbackPattern
#print axioms CardinalityConsumerCertificate.observe_eq_length
#print axioms CardinalityConsumerCertificate.observe_materialize_eq_streamCountFrom
#print axioms CardinalityConsumerCertificate.observe_materialize_eq_countAlg
#print axioms directCountFold
#print axioms directCountFoldFromFrontend

end Mettapedia.GSLT.LanguageDef.ConjunctiveCountFoldCompilation
