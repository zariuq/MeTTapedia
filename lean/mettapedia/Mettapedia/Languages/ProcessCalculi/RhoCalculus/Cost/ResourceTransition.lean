import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Path
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Valuation
import Mettapedia.CategoryTheory.ParameterizedMonad
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.SingleObj

/-!
# Resource-transition category for funded cost-rho execution

`CostPath` already has the indexing required by parameterised and
category-graded accounts of effects: a path starts at one event-counter and
resource/provenance state and ends at another.  This module proves that those
indices and paths form a category.

The identity is the existing empty path.  Composition concatenates actual
funded executions.  No injectivity of composition is required or claimed;
ordered emissions and proof-carrying causal receipts remain the operational
evidence, while signature totals are derived observations.

This is the grading category for the concrete funded semantics.  It does not
yet claim a category-graded monad for arbitrary result types.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

open CategoryTheory

universe u

namespace CostPath

/-- Well-formedness evidence carried at the source of a concrete path. -/
def sourceWellFormed
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    TraceComponentsWellFormed components :=
  match path with
  | .done supported _ => supported
  | .fire supported _ _ _ _ => supported

/-- Producer-bound evidence carried at the source of a concrete path. -/
def sourceBefore
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    TraceComponentsBefore nextId components :=
  match path with
  | .done _ bounded => bounded
  | .fire _ bounded _ _ _ => bounded

/-- Well-formedness evidence at the final state of a concrete path. -/
def finalWellFormed
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    TraceComponentsWellFormed finalComponents :=
  match path with
  | .done supported _ => supported
  | .fire _ _ _ _ rest => rest.finalWellFormed

/-- Producer-bound evidence at the final state of a concrete path. -/
def finalBefore
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    TraceComponentsBefore finalId finalComponents :=
  match path with
  | .done _ bounded => bounded
  | .fire _ _ _ _ rest => rest.finalBefore

/-- Sequential composition of occurrence-sensitive funded executions.  The
shared index ensures that the second path starts with exactly the event counter
and resource/provenance state produced by the first. -/
def append
    {startId middleId finalId : Nat}
    {source middle target : List RawTraceComponent}
    (first : CostPath startId source middleId middle)
    (second : CostPath middleId middle finalId target) :
    CostPath startId source finalId target :=
  match first with
  | .done _ _ => second
  | .fire supported bounded step enabled rest =>
      .fire supported bounded step enabled (rest.append second)

@[simp]
theorem done_append
    {startId finalId : Nat}
    {source target : List RawTraceComponent}
    (supported : TraceComponentsWellFormed source)
    (bounded : TraceComponentsBefore startId source)
    (path : CostPath startId source finalId target) :
    (CostPath.done supported bounded).append path = path :=
  rfl

@[simp]
theorem append_done
    {startId finalId : Nat}
    {source target : List RawTraceComponent}
    (path : CostPath startId source finalId target)
    (supported : TraceComponentsWellFormed target)
    (bounded : TraceComponentsBefore finalId target) :
    path.append (CostPath.done supported bounded) = path := by
  induction path with
  | done => rfl
  | fire supported bounded step enabled rest induction =>
      simp [append, induction]

@[simp]
theorem append_assoc
    {firstId secondId thirdId fourthId : Nat}
    {firstState secondState thirdState fourthState : List RawTraceComponent}
    (first : CostPath firstId firstState secondId secondState)
    (second : CostPath secondId secondState thirdId thirdState)
    (third : CostPath thirdId thirdState fourthId fourthState) :
    (first.append second).append third = first.append (second.append third) := by
  induction first with
  | done => rfl
  | fire supported bounded step enabled rest induction =>
      simp [append, induction]

@[simp]
theorem rawEmission_append
    {startId middleId finalId : Nat}
    {source middle target : List RawTraceComponent}
    (first : CostPath startId source middleId middle)
    (second : CostPath middleId middle finalId target) :
    (first.append second).rawEmission =
      first.rawEmission ++ second.rawEmission := by
  induction first with
  | done => rfl
  | fire supported bounded step enabled rest induction =>
      simp [append, rawEmission, induction]

@[simp]
theorem emission_append
    {startId middleId finalId : Nat}
    {source middle target : List RawTraceComponent}
    (first : CostPath startId source middleId middle)
    (second : CostPath middleId middle finalId target) :
    (first.append second).emission = first.emission ++ second.emission := by
  induction first with
  | done => rfl
  | fire supported bounded step enabled rest induction =>
      simp [append, emission, induction]

@[simp]
theorem steps_append
    {startId middleId finalId : Nat}
    {source middle target : List RawTraceComponent}
    (first : CostPath startId source middleId middle)
    (second : CostPath middleId middle finalId target) :
    (first.append second).steps = first.steps ++ second.steps := by
  induction first with
  | done => rfl
  | fire supported bounded step enabled rest induction =>
      simp [append, steps, induction]

@[simp]
theorem spends_append
    {startId middleId finalId : Nat}
    {source middle target : List RawTraceComponent}
    (first : CostPath startId source middleId middle)
    (second : CostPath middleId middle finalId target) :
    (first.append second).spends = first.spends ++ second.spends := by
  simp [spends, steps_append, List.map_append]

@[simp]
theorem depth_append
    {startId middleId finalId : Nat}
    {source middle target : List RawTraceComponent}
    (first : CostPath startId source middleId middle)
    (second : CostPath middleId middle finalId target) :
    (first.append second).depth = first.depth + second.depth := by
  induction first with
  | done => simp [append, depth]
  | fire supported bounded step enabled rest induction =>
      simp only [append, depth, induction]
      omega

/-- A firing path has a nonempty receipt.  This is the concrete contrast with
the empty identity path; every actual event remains positively funded. -/
theorem fire_rawEmission_ne_nil
    {nextId finalId : Nat}
    {components finalComponents : List RawTraceComponent}
    (supported : TraceComponentsWellFormed components)
    (bounded : TraceComponentsBefore nextId components)
    (step : RawRuntimeStep)
    (enabled : step ∈ runtimeCostCandidatesFromConfig
      (components.map RawTraceComponent.term))
    (rest : CostPath (nextId + 1)
      (applyTracedStep components step nextId) finalId finalComponents) :
    (CostPath.fire supported bounded step enabled rest).rawEmission ≠ [] := by
  simp [rawEmission]

/-- A path whose endpoints have the same event counter cannot contain a
firing.  This is the counter-level form of the no-free-unit boundary. -/
theorem eq_done_of_same_counter
    {nextId : Nat} {components finalComponents : List RawTraceComponent}
    (path : CostPath nextId components nextId finalComponents) :
    path.depth = 0 := by
  have counter := path.finalId_eq_start_add_depth
  omega

/-- The target counter records exactly the number of emitted events. -/
theorem finalId_eq_start_add_rawEmission_length
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    finalId = nextId + path.rawEmission.length := by
  rw [path.rawEmission_length_eq_depth]
  exact path.finalId_eq_start_add_depth

/-- Every nonempty funded execution strictly advances the event counter. -/
theorem start_lt_finalId_of_rawEmission_ne_nil
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents)
    (nonempty : path.rawEmission ≠ []) :
    nextId < finalId := by
  rw [path.finalId_eq_start_add_rawEmission_length]
  have positive : 0 < path.rawEmission.length := List.length_pos_iff.mpr nonempty
  omega

/-- The raw commutative spend measure is an observation of an exact path, not
its identity. -/
def rawAccount
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) : CostSig String :=
  path.spends.sum

@[simp]
theorem rawAccount_done
    {nextId : Nat} {components : List RawTraceComponent}
    (supported : TraceComponentsWellFormed components)
    (bounded : TraceComponentsBefore nextId components) :
    rawAccount (CostPath.done supported bounded) = 0 :=
  rfl

/-- Raw aggregation is a homomorphism out of exact sequential execution. -/
@[simp]
theorem rawAccount_append
    {startId middleId finalId : Nat}
    {source middle target : List RawTraceComponent}
    (first : CostPath startId source middleId middle)
    (second : CostPath middleId middle finalId target) :
    (first.append second).rawAccount =
      first.rawAccount + second.rawAccount := by
  simp [rawAccount, List.sum_append]

/-- An additive valuation is a second, explicitly selected observation out of
the raw signature account. -/
def additiveValue
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents)
    {Delta : Type*} [AddCommMonoid Delta] (weight : String → Delta) : Delta :=
  CostSig.additiveFold weight path.rawAccount

@[simp]
theorem additiveValue_done
    {nextId : Nat} {components : List RawTraceComponent}
    (supported : TraceComponentsWellFormed components)
    (bounded : TraceComponentsBefore nextId components)
    {Delta : Type*} [AddCommMonoid Delta] (weight : String → Delta) :
    additiveValue (CostPath.done supported bounded) weight = 0 := by
  simp [additiveValue]

@[simp]
theorem additiveValue_append
    {startId middleId finalId : Nat}
    {source middle target : List RawTraceComponent}
    (first : CostPath startId source middleId middle)
    (second : CostPath middleId middle finalId target)
    {Delta : Type*} [AddCommMonoid Delta] (weight : String → Delta) :
    (first.append second).additiveValue weight =
      first.additiveValue weight + second.additiveValue weight := by
  simp [additiveValue, CostSig.additiveFold_add]

/-- Multiplicative and quantale-valued pricing uses the same exact path and a
different downstream fold. -/
def multiplicativeValue
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents)
    {Delta : Type*} [CommMonoid Delta] (weight : String → Delta) : Delta :=
  CostSig.multiplicativeFold weight path.rawAccount

@[simp]
theorem multiplicativeValue_done
    {nextId : Nat} {components : List RawTraceComponent}
    (supported : TraceComponentsWellFormed components)
    (bounded : TraceComponentsBefore nextId components)
    {Delta : Type*} [CommMonoid Delta] (weight : String → Delta) :
    multiplicativeValue (CostPath.done supported bounded) weight = 1 := by
  simp [multiplicativeValue]

@[simp]
theorem multiplicativeValue_append
    {startId middleId finalId : Nat}
    {source middle target : List RawTraceComponent}
    (first : CostPath startId source middleId middle)
    (second : CostPath middleId middle finalId target)
    {Delta : Type*} [CommMonoid Delta] (weight : String → Delta) :
    (first.append second).multiplicativeValue weight =
      first.multiplicativeValue weight * second.multiplicativeValue weight := by
  simp [multiplicativeValue, CostSig.multiplicativeFold_add]

end CostPath

/-- A valid pre/post index for funded execution.  It contains the complete
runtime resource state together with the monotone event counter and the
proofs needed to continue execution safely. -/
structure FundedState where
  nextId : Nat
  components : List RawTraceComponent
  supported : TraceComponentsWellFormed components
  bounded : TraceComponentsBefore nextId components

namespace CostPath

/-- Package the source index already certified by a concrete path. -/
def sourceState
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) : FundedState where
  nextId := nextId
  components := components
  supported := path.sourceWellFormed
  bounded := path.sourceBefore

/-- Package the target index already certified by a concrete path. -/
def targetState
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) : FundedState where
  nextId := finalId
  components := finalComponents
  supported := path.finalWellFormed
  bounded := path.finalBefore

end CostPath

/-- Exact funded executions are the morphisms between valid runtime states. -/
abbrev ResourceTransition (source target : FundedState) : Type :=
  CostPath source.nextId source.components target.nextId target.components

instance fundedStateCategoryStruct : CategoryStruct FundedState where
  Hom := ResourceTransition
  id state := .done state.supported state.bounded
  comp first second := first.append second

instance fundedStateCategory : Category FundedState where
  id_comp := by
    intro source target path
    rfl
  comp_id := by
    intro source target path
    exact CostPath.append_done path target.supported target.bounded
  assoc := by
    intro first second third fourth left middle right
    exact CostPath.append_assoc left middle right

namespace ResourceTransition

/-- Every concrete `CostPath` is canonically an exact morphism between the
pre/post states whose validity evidence it already carries. -/
def ofPath
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    path.sourceState ⟶ path.targetState :=
  path

@[simp]
theorem identity_rawEmission (state : FundedState) :
    CostPath.rawEmission (𝟙 state) = [] :=
  rfl

@[simp]
theorem identity_emission (state : FundedState) :
    CostPath.emission (𝟙 state) = [] :=
  rfl

@[simp]
theorem identity_depth (state : FundedState) :
    CostPath.depth (𝟙 state) = 0 :=
  rfl

@[simp]
theorem identity_rawAccount (state : FundedState) :
    CostPath.rawAccount (𝟙 state) = 0 :=
  rfl

/-- An exact funded endomorphism is necessarily the empty identity path.
Every genuine firing advances the event counter, so there is no hidden
zero-event endomorphism. -/
theorem endomorphism_eq_identity (state : FundedState)
    (path : state ⟶ state) : path = 𝟙 state := by
  have zero := CostPath.eq_done_of_same_counter path
  cases path with
  | done => rfl
  | fire supported bounded step enabled rest =>
      simp [CostPath.depth] at zero

/-- Sequential categorical composition concatenates the exact external
receipt records; aggregation is not involved. -/
@[simp]
theorem comp_rawEmission {source middle target : FundedState}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    (first ≫ second).rawEmission =
      first.rawEmission ++ second.rawEmission :=
  CostPath.rawEmission_append first second

/-- Sequential categorical composition also concatenates the canonical
proof-carrying emissions from which causal receipts are constructed. -/
@[simp]
theorem comp_emission {source middle target : FundedState}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    (first ≫ second).emission = first.emission ++ second.emission :=
  CostPath.emission_append first second

@[simp]
theorem comp_depth {source middle target : FundedState}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    (first ≫ second).depth = first.depth + second.depth :=
  CostPath.depth_append first second

@[simp]
theorem comp_rawAccount {source middle target : FundedState}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    (first ≫ second).rawAccount =
      first.rawAccount + second.rawAccount :=
  CostPath.rawAccount_append first second

@[simp]
theorem comp_additiveValue {source middle target : FundedState}
    (first : source ⟶ middle) (second : middle ⟶ target)
    {Delta : Type*} [AddCommMonoid Delta] (weight : String → Delta) :
    (first ≫ second).additiveValue weight =
      first.additiveValue weight + second.additiveValue weight :=
  CostPath.additiveValue_append first second weight

@[simp]
theorem comp_multiplicativeValue {source middle target : FundedState}
    (first : source ⟶ middle) (second : middle ⟶ target)
    {Delta : Type*} [CommMonoid Delta] (weight : String → Delta) :
    (first ≫ second).multiplicativeValue weight =
      first.multiplicativeValue weight * second.multiplicativeValue weight :=
  CostPath.multiplicativeValue_append first second weight

/-- Forget an exact funded transition down to its commutative raw account.
This is a genuine functor of the transition category; it is intentionally not
claimed to be faithful. -/
def rawAccountFunctor :
    FundedState ⥤ SingleObj (Multiplicative (CostSig String)) where
  obj _ := SingleObj.star _
  map path := Multiplicative.ofAdd path.rawAccount
  map_id state := by
    change Multiplicative.ofAdd (CostPath.rawAccount (𝟙 state)) = 1
    simp
  map_comp first second := by
    change Multiplicative.ofAdd (CostPath.rawAccount (first ≫ second)) =
      Multiplicative.ofAdd (CostPath.rawAccount second) *
        Multiplicative.ofAdd (CostPath.rawAccount first)
    rw [comp_rawAccount]
    exact mul_comm _ _

end ResourceTransition

/-- A result paired with the exact funded transition that produced it.  The
pre/post resource states are type indices, while the transition field retains
the full occurrence-sensitive execution rather than an aggregate cost. -/
structure FundedExecution (source target : FundedState) (Result : Type u) where
  transition : source ⟶ target
  result : Result

namespace FundedExecution

/-- Pair any certified runtime path with its returned value. -/
def ofPath
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents)
    (result : Result) :
    FundedExecution path.sourceState path.targetState Result :=
  ⟨ResourceTransition.ofPath path, result⟩

@[simp]
theorem ofPath_transition
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents)
    (result : Result) :
    (ofPath path result).transition = ResourceTransition.ofPath path :=
  rfl

/-- Parameterised unit: return a result with the empty identity transition.
It emits no event and changes no resource state. -/
def pure (state : FundedState) (result : Result) :
    FundedExecution state state Result :=
  ⟨𝟙 state, result⟩

/-- Parameterised bind composes only executions whose intermediate resource
state agrees by type.  The continuation may depend on the first result. -/
def bind {source middle target : FundedState}
    (first : FundedExecution source middle Result)
    (next : Result → FundedExecution middle target NextResult) :
    FundedExecution source target NextResult :=
  ⟨first.transition ≫ (next first.result).transition,
    (next first.result).result⟩

/-- Result mapping does not change the exact funded transition. -/
def map (function : Result → NextResult)
    (execution : FundedExecution source target Result) :
    FundedExecution source target NextResult :=
  ⟨execution.transition, function execution.result⟩

@[simp]
theorem pure_transition (state : FundedState) (result : Result) :
    (pure state result).transition = 𝟙 state :=
  rfl

@[simp]
theorem pure_result (state : FundedState) (result : Result) :
    (pure state result).result = result :=
  rfl

@[simp]
theorem bind_transition {source middle target : FundedState}
    (first : FundedExecution source middle Result)
    (next : Result → FundedExecution middle target NextResult) :
    (first.bind next).transition =
      first.transition ≫ (next first.result).transition :=
  rfl

@[simp]
theorem bind_result {source middle target : FundedState}
    (first : FundedExecution source middle Result)
    (next : Result → FundedExecution middle target NextResult) :
    (first.bind next).result = (next first.result).result :=
  rfl

@[simp]
theorem pure_rawEmission (state : FundedState) (result : Result) :
    (pure state result).transition.rawEmission = [] :=
  ResourceTransition.identity_rawEmission state

/-- Exact receipts compose before any commutative aggregation is applied. -/
@[simp]
theorem bind_rawEmission {source middle target : FundedState}
    (first : FundedExecution source middle Result)
    (next : Result → FundedExecution middle target NextResult) :
    (first.bind next).transition.rawEmission =
      first.transition.rawEmission ++
        (next first.result).transition.rawEmission :=
  ResourceTransition.comp_rawEmission first.transition
    (next first.result).transition

@[simp]
theorem pure_rawAccount (state : FundedState) (result : Result) :
    (pure state result).transition.rawAccount = 0 :=
  ResourceTransition.identity_rawAccount state

/-- The raw commutative account is a homomorphic observation of bind, not the
identity of the computation. -/
@[simp]
theorem bind_rawAccount {source middle target : FundedState}
    (first : FundedExecution source middle Result)
    (next : Result → FundedExecution middle target NextResult) :
    (first.bind next).transition.rawAccount =
      first.transition.rawAccount +
        (next first.result).transition.rawAccount :=
  ResourceTransition.comp_rawAccount first.transition
    (next first.result).transition

@[simp]
theorem bind_additiveValue {source middle target : FundedState}
    (first : FundedExecution source middle Result)
    (next : Result → FundedExecution middle target NextResult)
    {Delta : Type*} [AddCommMonoid Delta] (weight : String → Delta) :
    (first.bind next).transition.additiveValue weight =
      first.transition.additiveValue weight +
        (next first.result).transition.additiveValue weight :=
  ResourceTransition.comp_additiveValue first.transition
    (next first.result).transition weight

@[simp]
theorem bind_multiplicativeValue {source middle target : FundedState}
    (first : FundedExecution source middle Result)
    (next : Result → FundedExecution middle target NextResult)
    {Delta : Type*} [CommMonoid Delta] (weight : String → Delta) :
    (first.bind next).transition.multiplicativeValue weight =
      first.transition.multiplicativeValue weight *
        (next first.result).transition.multiplicativeValue weight :=
  ResourceTransition.comp_multiplicativeValue first.transition
    (next first.result).transition weight

/-- Left unit of parameterised bind. -/
@[simp]
theorem pure_bind {source target : FundedState}
    (result : Result)
    (next : Result → FundedExecution source target NextResult) :
    (pure source result).bind next = next result := by
  rfl

/-- Right unit of parameterised bind. -/
@[simp]
theorem bind_pure {source target : FundedState}
    (execution : FundedExecution source target Result) :
    execution.bind (pure target) = execution := by
  cases execution
  simp [bind, pure]

/-- Associativity of parameterised bind.  The proof is exactly associativity
of certified resource-transition composition. -/
theorem bind_assoc
    {firstState secondState thirdState fourthState : FundedState}
    (first : FundedExecution firstState secondState Result)
    (second : Result → FundedExecution secondState thirdState NextResult)
    (third : NextResult → FundedExecution thirdState fourthState FinalResult) :
    (first.bind second).bind third =
      first.bind (fun result => (second result).bind third) := by
  cases first
  simp [bind, Category.assoc]

@[simp]
theorem map_id (execution : FundedExecution source target Result) :
    execution.map id = execution := by
  cases execution
  rfl

@[simp]
theorem map_comp (first : Result → NextResult)
    (second : NextResult → FinalResult)
    (execution : FundedExecution source target Result) :
    (execution.map first).map second = execution.map (second ∘ first) := by
  cases execution
  rfl

/-- A computation whose pre/post resource state is identical cannot hide a
funded event in its transition. -/
theorem endomorphism_transition_eq_identity (state : FundedState)
    (execution : FundedExecution state state Result) :
    execution.transition = 𝟙 state :=
  ResourceTransition.endomorphism_eq_identity state execution.transition

end FundedExecution

/-- The concrete funded execution family, packaged with its proved
Atkey-style parameterized-monad operations and laws. -/
def fundedExecutionParameterizedMonad :
    Mettapedia.Effects.ParameterizedMonad FundedState
      (fun source target Result => FundedExecution source target Result) where
  pure := FundedExecution.pure
  bind := FundedExecution.bind
  pure_bind := FundedExecution.pure_bind
  bind_pure := FundedExecution.bind_pure
  bind_assoc := FundedExecution.bind_assoc

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
