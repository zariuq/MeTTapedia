import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.Tactic

/-!
# Contextual candidate valuations

Candidate-local quantitative information has two independent interfaces.

* A **valuation** assigns values to candidates in context.  Context changes
  act on both candidates and values, and the assignment must commute with
  those actions.
* An **evaluator** may compute such values effectfully.  The effect is made
  explicit as a monad on context-indexed families; it is not inferred from
  the value carrier.

After valuation, a finite pushforward may combine values belonging to equal
outcomes.  A resolver then decides whether the resulting value family is
retained, filtered, normalized, sampled, scheduled, or measured.  Neither
the value carrier nor the pushforward chooses a resolver.

The final sections compare three representation choices without selecting
one as a language primitive:

* explicit valued occurrences;
* a sparse sidecar keyed by occurrence identity; and
* heterogeneous optional annotation channels.

The sidecar theorems isolate a load-bearing condition: distinct occurrences
whose values may differ require distinct keys.  Equal atoms are therefore
not sufficient keys when occurrence identity is observable.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ContextualCandidateValuation

open CategoryTheory
open scoped BigOperators

universe v uContext uFamily
universe uCandidate uOutcome uValue uKey uResult uChannel uPayload

/-! ## Context-indexed candidates and values -/

/-- A family varying contravariantly with context.  Substitution, weakening,
and restriction are all possible interpretations of the context arrows. -/
abbrev ContextFamily (Context : Type uContext) [Category.{v} Context] :=
  Contextᵒᵖ ⥤ Type uFamily

/-- Candidates and their observable outcomes, both indexed by context. -/
structure CandidateSystem (Context : Type uContext) [Category.{v} Context] where
  Candidate : ContextFamily.{v, uContext, uFamily} Context
  Outcome : ContextFamily.{v, uContext, uFamily} Context
  outcome : Candidate ⟶ Outcome

/-- A pure contextual valuation is a natural transformation.  Consequently,
valuation commutes with every declared context change. -/
abbrev ContextualValuation {Context : Type uContext} [Category.{v} Context]
    (Candidate Value : ContextFamily Context) :=
  Candidate ⟶ Value

/-- A context-independent carrier is the constant-family special case. -/
abbrev constantFamily (Context : Type uContext) [Category.{v} Context]
    (Value : Type uFamily) : ContextFamily Context :=
  (Functor.const Contextᵒᵖ).obj Value

/-- Naturality is the precise compatibility law between candidate reindexing
and value reindexing. -/
theorem valuation_naturality
    {Context : Type uContext} [Category.{v} Context]
    {Candidate Value : ContextFamily Context}
    (valuation : ContextualValuation Candidate Value)
    {source target : Contextᵒᵖ} (reindex : source ⟶ target) :
    Candidate.map reindex ≫ valuation.app target =
      valuation.app source ≫ Value.map reindex :=
  valuation.naturality reindex

/-- Translate candidates first, then value them. -/
def ContextualValuation.precompose
    {Context : Type uContext} [Category.{v} Context]
    {Source Candidate Value : ContextFamily Context}
    (valuation : ContextualValuation Candidate Value)
    (translate : Source ⟶ Candidate) :
    ContextualValuation Source Value :=
  translate ≫ valuation

@[simp] theorem ContextualValuation.precompose_app
    {Context : Type uContext} [Category.{v} Context]
    {Source Candidate Value : ContextFamily Context}
    (valuation : ContextualValuation Candidate Value)
    (translate : Source ⟶ Candidate) (context : Contextᵒᵖ) :
    (valuation.precompose translate).app context =
      translate.app context ≫ valuation.app context :=
  rfl

@[simp] theorem ContextualValuation.precompose_identity
    {Context : Type uContext} [Category.{v} Context]
    {Candidate Value : ContextFamily Context}
    (valuation : ContextualValuation Candidate Value) :
    valuation.precompose (𝟙 Candidate) = valuation := by
  ext context candidate
  rfl

theorem ContextualValuation.precompose_comp
    {Context : Type uContext} [Category.{v} Context]
    {First Second Candidate Value : ContextFamily Context}
    (valuation : ContextualValuation Candidate Value)
    (second : Second ⟶ Candidate) (first : First ⟶ Second) :
    valuation.precompose (first ≫ second) =
      (valuation.precompose second).precompose first := by
  rfl

/-! ## Effectful valuation -/

/-- An evaluator computes values in an explicit effect.  This is a Kleisli
arrow in the category of context-indexed families.  Randomness, clocks,
state, nondeterminism, and external evidence are different possible effects;
none is smuggled into `Value`. -/
structure Evaluator
    {Context : Type uContext} [Category.{v} Context]
    (Candidate Value : ContextFamily Context) where
  effect : CategoryTheory.Monad (ContextFamily Context)
  evaluate : Candidate ⟶ effect.obj Value

namespace Evaluator

/-- A pure valuation is an evaluator for the identity effect. -/
def pure
    {Context : Type uContext} [Category.{v} Context]
    {Candidate Value : ContextFamily Context}
    (valuation : ContextualValuation Candidate Value) :
    Evaluator Candidate Value where
  effect := CategoryTheory.Monad.id _
  evaluate := valuation

@[simp] theorem pure_evaluate
    {Context : Type uContext} [Category.{v} Context]
    {Candidate Value : ContextFamily Context}
    (valuation : ContextualValuation Candidate Value) :
    (pure valuation).evaluate = valuation :=
  rfl

end Evaluator

/-! ## One naturality square, isolated as an elementary law -/

/-- The componentwise form of naturality for one context change. -/
def ReindexingCompatible
    {RichCandidate : Type uCandidate} {CoarseCandidate : Type uOutcome}
    {RichValue : Type uValue} {CoarseValue : Type uResult}
    (candidateReindex : RichCandidate → CoarseCandidate)
    (valueReindex : RichValue → CoarseValue)
    (richValue : RichCandidate → RichValue)
    (coarseValue : CoarseCandidate → CoarseValue) : Prop :=
  ∀ candidate,
    valueReindex (richValue candidate) =
      coarseValue (candidateReindex candidate)

/-- If a context change identifies two candidates while value reindexing is
injective, naturality forces their rich values to agree. -/
theorem value_eq_of_candidate_collision
    {RichCandidate : Type uCandidate} {CoarseCandidate : Type uOutcome}
    {RichValue : Type uValue} {CoarseValue : Type uResult}
    {candidateReindex : RichCandidate → CoarseCandidate}
    {valueReindex : RichValue → CoarseValue}
    {richValue : RichCandidate → RichValue}
    {coarseValue : CoarseCandidate → CoarseValue}
    (compatible : ReindexingCompatible candidateReindex valueReindex
      richValue coarseValue)
    {first second : RichCandidate}
    (collision : candidateReindex first = candidateReindex second)
    (reflectsValues : Function.Injective valueReindex) :
    richValue first = richValue second := by
  apply reflectsValues
  rw [compatible first, compatible second, collision]

/-- A lossy value reindexing can retain context-local distinctions upstairs
while exposing one common value downstairs. -/
def exampleRichValue (candidate : Bool) : Bool × Nat :=
  (candidate, 7)

theorem example_projection_is_compatible :
    ReindexingCompatible
      (fun _ : Bool => ()) Prod.snd exampleRichValue (fun _ : Unit => 7) := by
  intro candidate
  cases candidate <;> rfl

theorem example_rich_values_are_distinct :
    exampleRichValue false ≠ exampleRichValue true := by
  decide

/-- With an injective value map, the same candidate collapse cannot support
the two distinct Boolean values. -/
theorem no_bool_valuation_through_candidate_collapse :
    ¬ ∃ coarseValue : Unit → Bool,
      ReindexingCompatible (fun _ : Bool => ()) id id coarseValue := by
  rintro ⟨coarseValue, compatible⟩
  have equalValues : (false : Bool) = true :=
    value_eq_of_candidate_collision compatible rfl Function.injective_id
  exact Bool.false_ne_true equalValues

/-! ## Finite fiberwise aggregation -/

/-- Add all candidate values whose observable outcome is `wanted`.

This is the finite pushforward used by bags, weighted relations, stochastic
rates, and coherent coefficients.  The operation combines equal outcomes;
it does not normalize, sample, schedule, or measure them. -/
def fiberSum
    {Candidate : Type uCandidate} {Outcome : Type uOutcome}
    {Value : Type uValue}
    [Fintype Candidate] [DecidableEq Outcome] [AddCommMonoid Value]
    (outcome : Candidate → Outcome) (value : Candidate → Value)
    (wanted : Outcome) : Value :=
  ∑ candidate,
    if outcome candidate = wanted then value candidate else 0

/-- Finite pushforward conserves total additive value. -/
theorem sum_fiberSum
    {Candidate : Type uCandidate} {Outcome : Type uOutcome}
    {Value : Type uValue}
    [Fintype Candidate] [Fintype Outcome] [DecidableEq Outcome]
    [AddCommMonoid Value]
    (outcome : Candidate → Outcome) (value : Candidate → Value) :
    (∑ result, fiberSum outcome value result) = ∑ candidate, value candidate := by
  classical
  simp [fiberSum, Finset.sum_comm]

/-- Fiberwise aggregation at one context of an indexed candidate system. -/
def CandidateSystem.fiberSumAt
    {Context : Type uContext} [Category.{v} Context]
    (system : CandidateSystem Context)
    {Value : ContextFamily Context}
    (valuation : ContextualValuation system.Candidate Value)
    (context : Contextᵒᵖ)
    [Fintype (system.Candidate.obj context)]
    [DecidableEq (system.Outcome.obj context)]
    [AddCommMonoid (Value.obj context)] :
    system.Outcome.obj context → Value.obj context :=
  fiberSum (system.outcome.app context) (valuation.app context)

/-! ## Resolution is separate from valuation and aggregation -/

/-- A resolver consumes an outcome-indexed value family.  Its result type is
chosen independently of the value carrier. -/
structure Resolver (Outcome : Type uOutcome) (Value : Type uValue) where
  Result : Type uResult
  resolve : (Outcome → Value) → Result

namespace Resolver

/-- Retain the complete enriched outcome family. -/
def retain (Outcome : Type uOutcome) (Value : Type uValue) :
    Resolver Outcome Value where
  Result := Outcome → Value
  resolve := id

/-- Forget outcome identity and add all values. -/
def total (Outcome : Type uOutcome) (Value : Type uValue)
    [Fintype Outcome] [AddCommMonoid Value] :
    Resolver Outcome Value where
  Result := Value
  resolve := fun values => ∑ outcome, values outcome

end Resolver

/-! ## Explicit valued occurrences -/

/-- One occurrence with an explicit value. -/
@[ext] structure ValuedOccurrence
    (Occurrence : Type uCandidate) (Value : Type uValue) where
  occurrence : Occurrence
  value : Value
deriving DecidableEq, Repr

/-- Materialize a valuation beside every occurrence. -/
def attachValues
    {Occurrence : Type uCandidate} {Value : Type uValue}
    (value : Occurrence → Value) (occurrences : List Occurrence) :
    List (ValuedOccurrence Occurrence Value) :=
  occurrences.map fun occurrence => ⟨occurrence, value occurrence⟩

/-- Erasing explicit values recovers the exact ordered occurrence list. -/
@[simp] theorem erase_attachValues
    {Occurrence : Type uCandidate} {Value : Type uValue}
    (value : Occurrence → Value) (occurrences : List Occurrence) :
    (attachValues value occurrences).map ValuedOccurrence.occurrence =
      occurrences := by
  simp [attachValues, Function.comp_def]

/-! ## Sparse sidecar representation -/

/-- A sidecar recovers a valuation through occurrence keys. -/
def SidecarRecovers
    {Occurrence : Type uCandidate} {Key : Type uKey} {Value : Type uValue}
    (key : Occurrence → Key) (value : Occurrence → Value)
    (sidecar : Key → Option Value) : Prop :=
  ∀ occurrence, sidecar (key occurrence) = some (value occurrence)

/-- An injective occurrence key yields a sparse sidecar, with `none` away
from the image. -/
noncomputable def sidecarOfInjective
    {Occurrence : Type uCandidate} {Key : Type uKey} {Value : Type uValue}
    (key : Occurrence → Key) (value : Occurrence → Value) :
    Key → Option Value :=
  Function.extend key (fun occurrence => some (value occurrence))
    (fun _ => none)

@[simp] theorem sidecarOfInjective_apply
    {Occurrence : Type uCandidate} {Key : Type uKey} {Value : Type uValue}
    {key : Occurrence → Key} (injective : Function.Injective key)
    (value : Occurrence → Value) (occurrence : Occurrence) :
    sidecarOfInjective key value (key occurrence) = some (value occurrence) :=
  injective.extend_apply _ _ _

theorem sidecarOfInjective_recovers
    {Occurrence : Type uCandidate} {Key : Type uKey} {Value : Type uValue}
    {key : Occurrence → Key} (injective : Function.Injective key)
    (value : Occurrence → Value) :
    SidecarRecovers key value (sidecarOfInjective key value) := by
  intro occurrence
  exact sidecarOfInjective_apply injective value occurrence

/-- A key collision forces equal values in every faithfully recovering
sidecar. -/
theorem value_eq_of_sidecar_key_collision
    {Occurrence : Type uCandidate} {Key : Type uKey} {Value : Type uValue}
    {key : Occurrence → Key} {value : Occurrence → Value}
    {sidecar : Key → Option Value}
    (recovers : SidecarRecovers key value sidecar)
    {first second : Occurrence} (collision : key first = key second) :
    value first = value second := by
  apply Option.some.inj
  calc
    some (value first) = sidecar (key first) := (recovers first).symm
    _ = sidecar (key second) := congrArg sidecar collision
    _ = some (value second) := recovers second

/-- Therefore no sidecar can recover distinct values through a colliding
key. -/
theorem no_sidecar_of_key_collision_and_value_difference
    {Occurrence : Type uCandidate} {Key : Type uKey} {Value : Type uValue}
    {key : Occurrence → Key} {value : Occurrence → Value}
    {first second : Occurrence} (collision : key first = key second)
    (different : value first ≠ value second) :
    ¬ ∃ sidecar : Key → Option Value, SidecarRecovers key value sidecar := by
  rintro ⟨sidecar, recovers⟩
  exact different (value_eq_of_sidecar_key_collision recovers collision)

/-- Read absent metadata as a declared neutral/default value. -/
def readOr
    {Key : Type uKey} {Value : Type uValue}
    (default : Value) (sidecar : Key → Option Value) (key : Key) : Value :=
  (sidecar key).getD default

@[simp] theorem readOr_empty
    {Key : Type uKey} {Value : Type uValue}
    (default : Value) (key : Key) :
    readOr default (fun _ : Key => none) key = default :=
  rfl

/-! ## Heterogeneous optional annotation channels -/

/-- A typed collection of optional annotation channels.  Channel payloads
may be scalars, evidence pairs, finite vectors, tensors, handles, or other
types without forcing one universal atom wrapper. -/
structure AnnotationSchema where
  Channel : Type uChannel
  Payload : Channel → Type uPayload

/-- One sparse heterogeneous row. -/
abbrev AnnotationRow (schema : AnnotationSchema) :=
  ∀ channel, Option (schema.Payload channel)

/-- No channel is populated. -/
def emptyRow (schema : AnnotationSchema) : AnnotationRow schema :=
  fun _ => none

/-- Independent schemas combine by a disjoint sum of channel names. -/
def AnnotationSchema.sum (left right : AnnotationSchema) :
    AnnotationSchema where
  Channel := Sum left.Channel right.Channel
  Payload
    | .inl channel => left.Payload channel
    | .inr channel => right.Payload channel

/-- Combine independent sparse rows without converting either payload
family. -/
def AnnotationRow.append
    {left right : AnnotationSchema}
    (leftRow : AnnotationRow left) (rightRow : AnnotationRow right) :
    AnnotationRow (left.sum right)
  | .inl channel => leftRow channel
  | .inr channel => rightRow channel

@[simp] theorem AnnotationRow.append_left
    {left right : AnnotationSchema}
    (leftRow : AnnotationRow left) (rightRow : AnnotationRow right)
    (channel : left.Channel) :
    AnnotationRow.append leftRow rightRow (.inl channel) = leftRow channel :=
  rfl

@[simp] theorem AnnotationRow.append_right
    {left right : AnnotationSchema}
    (leftRow : AnnotationRow left) (rightRow : AnnotationRow right)
    (channel : right.Channel) :
    AnnotationRow.append leftRow rightRow (.inr channel) = rightRow channel :=
  rfl

/-- The empty schema has no channel and hence one extensional row. -/
def emptySchema : AnnotationSchema where
  Channel := PEmpty
  Payload := PEmpty.elim

theorem emptySchema_row_unique (row : AnnotationRow emptySchema) :
    row = emptyRow emptySchema := by
  funext channel
  exact PEmpty.elim channel

/-- A heterogeneous example: semantic multiplicity, learned features, and
evidence retain their own payload types. -/
inductive ExampleChannel
  | semantic
  | features
  | evidence
deriving DecidableEq, Repr

def exampleSchema : AnnotationSchema where
  Channel := ExampleChannel
  Payload
    | .semantic => Nat
    | .features => Fin 4 → Int
    | .evidence => Nat × Nat

def exampleRow : AnnotationRow exampleSchema
  | .semantic => some (3 : Nat)
  | .features => none
  | .evidence => some ((2, 1) : Nat × Nat)

example : exampleRow .semantic = some (3 : Nat) := rfl
example : exampleRow .features = none := rfl
example : exampleRow .evidence = some ((2, 1) : Nat × Nat) := rfl

/-! ## Coherent aggregation is not collapse -/

/-- Two nonzero path coefficients with opposite signs.  Integers are used
here only to isolate the additive interference law. -/
def twoPathCoefficient : Bool → Int
  | false => 1
  | true => -1

/-- Forgetting path identity lets equal outcomes combine and cancel. -/
theorem two_paths_cancel_after_identity_erasure :
    fiberSum (fun _ : Bool => ()) twoPathCoefficient () = 0 := by
  norm_num [fiberSum, twoPathCoefficient]

/-- Both candidate paths remain present and individually nonzero. -/
theorem two_paths_are_individually_nonzero :
    ∀ path : Bool, twoPathCoefficient path ≠ 0 := by
  intro path
  cases path <;> norm_num [twoPathCoefficient]

/-- Retaining which-path identity prevents the cross-path cancellation. -/
theorem which_path_values_remain_distinct :
    fiberSum id twoPathCoefficient false = 1 ∧
      fiberSum id twoPathCoefficient true = -1 := by
  constructor <;> norm_num [fiberSum, twoPathCoefficient]

/-! ## Axiom audit targets -/

#print axioms valuation_naturality
#print axioms sum_fiberSum
#print axioms no_bool_valuation_through_candidate_collapse
#print axioms no_sidecar_of_key_collision_and_value_difference
#print axioms two_paths_cancel_after_identity_erasure

end Mettapedia.GSLT.Dynamics.ContextualCandidateValuation
