import Mettapedia.TypeTheory.Models.RevisionedFamilies.CheckedOpenScopeExecution
import Mettapedia.TypeTheory.DisplayedPresheafComprehension

/-!
# Guarded WM executions as a displayed family over equal observed requests

The base category is the kernel pair of the computed state-query request on
full model environments. Its arrows exist only when both observed components
agree; it is not discrete, as the counted repartitioning control shows.
The displayed family carries the actual checked engine occurrence along
these arrows without rerunning matching or guard evaluation.

This is the equal-request fragment of operational dependent transport. It
does not claim an action of arbitrary authored syntactic substitutions or
stability under edits to a language's rule/alternative indices.
-/

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective
set_option autoImplicit false

namespace Mettapedia.TypeTheory.Models.RevisionedFamilies.CheckedOpenExecutionDisplayed

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.GSLT.LanguageDef.NamedFreeContext
open Mettapedia.OSLF.Framework.WMCalculusCombinedSortedBoundary
open Mettapedia.OSLF.Framework.WMCalculusCombinedConcreteReading
open Mettapedia.OSLF.Framework.WMCalculusCombinedFirstOrderSemantics
open Mettapedia.OSLF.Framework.WMCalculusCheckedScopeRelationProvider
open Mettapedia.OSLF.Framework.WMCalculusCountScopeRelationProvider (singletonX)
open Mettapedia.TypeTheory.Models.RevisionedFamilies.CheckedOpenScopeExecution
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.Computability.ComputationalTrinity

/-- One full semantic environment, before forgetting how its captured world
and query were represented. -/
structure RequestEnvironment {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    (receipt : CheckedExtract entries bindings world query) where
  environment : Environment (State := State) (Query := Query)
    (Ev := Ev) (Ov := Ov) (Scope := Scope) (contextSorts entries)

/-- The request actually computed from the captured intrinsic substitution
and this full model environment. -/
def RequestEnvironment.observed
    {State Query Ev Ov Scope : Type}
    {reading : CombinedReading State Query Ev Ov Scope}
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    {receipt : CheckedExtract entries bindings world query}
    (point : RequestEnvironment reading receipt) : State × Query :=
  (receipt.worldValue reading point.environment,
    receipt.queryValue reading point.environment)

/-- The kernel-pair category of observed requests. A morphism does not
identify the full environments: it certifies equality only of the two
computed request components. -/
instance requestGroupoid
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    (receipt : CheckedExtract entries bindings world query) :
    Groupoid (RequestEnvironment reading receipt) where
  Hom first second := PLift (first.observed = second.observed)
  id _ := ⟨rfl⟩
  comp first second := ⟨first.down.trans second.down⟩
  inv arrow := ⟨arrow.down.symm⟩
  id_comp := by intros; apply Subsingleton.elim
  comp_id := by intros; apply Subsingleton.elim
  assoc := by intros; apply Subsingleton.elim
  inv_comp := by intros; apply Subsingleton.elim
  comp_inv := by intros; apply Subsingleton.elim

/-- The observed answer is a stable base index along equal-request arrows.
The dependent execution fibre below is not constant in the full environment. -/
def answerFace
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    (receipt : CheckedExtract entries bindings world query) :
    Face (RequestEnvironment reading receipt) :=
  (Functor.const ((RequestEnvironment reading receipt)ᵒᵖ)).obj Ev

private theorem cast_answer_occurrence
    {State Query Ev Ov Scope : Type}
    {reading : CombinedReading State Query Ev Ov Scope}
    {provider : CheckedProvider Scope Query reading.inScope}
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    {receipt : CheckedExtract entries bindings world query}
    {environment : Environment (State := State) (Query := Query)
      (Ev := Ev) (Ov := Ov) (Scope := Scope) (contextSorts entries)}
    {scopeHandle : Pattern} {scope : Scope} {firstAnswer secondAnswer : Ev}
    (same : firstAnswer = secondAnswer)
    (execution : ExecutedAnswer reading provider receipt environment
      scopeHandle scope firstAnswer) :
    (same ▸ execution).occurrence = execution.occurrence := by
  cases same
  rfl

private def transportExecution
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (provider : CheckedProvider Scope Query reading.inScope)
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    (receipt : CheckedExtract entries bindings world query)
    (scopeHandle : Pattern) (scope : Scope)
    {first second : (answerFace reading receipt).Elements}
    (arrow : first ⟶ second)
    (execution : ExecutedAnswer reading provider receipt
      first.1.unop.environment scopeHandle scope first.2) :
    ExecutedAnswer reading provider receipt
      second.1.unop.environment scopeHandle scope second.2 := by
  have sameAnswer : first.2 = second.2 := arrow.property
  have sameRequest := arrow.val.unop.down
  exact sameAnswer ▸ execution.transport_same_request
    (congrArg Prod.fst sameRequest).symm
    (congrArg Prod.snd sameRequest).symm

private theorem transportExecution_occurrence
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (provider : CheckedProvider Scope Query reading.inScope)
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    (receipt : CheckedExtract entries bindings world query)
    (scopeHandle : Pattern) (scope : Scope)
    {first second : (answerFace reading receipt).Elements}
    (arrow : first ⟶ second)
    (execution : ExecutedAnswer reading provider receipt
      first.1.unop.environment scopeHandle scope first.2) :
    (transportExecution reading provider receipt scopeHandle scope arrow execution).occurrence =
      execution.occurrence := by
  change ((show first.2 = second.2 from arrow.property) ▸
    execution.transport_same_request
      (congrArg Prod.fst arrow.val.unop.down).symm
      (congrArg Prod.snd arrow.val.unop.down).symm).occurrence =
        execution.occurrence
  exact (cast_answer_occurrence _ _).trans
    (execution.transport_same_request_occurrence _ _)

/-- Actual guarded executions form a proof-relevant displayed family over
an answer and a full environment. Reindexing is the proved transport of
the same numbered occurrence along equality of the computed request. -/
def executionFamily
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (provider : CheckedProvider Scope Query reading.inScope)
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    (receipt : CheckedExtract entries bindings world query)
    (scopeHandle : Pattern) (scope : Scope) :
    DisplayedFamily (answerFace reading receipt) where
  obj point := ExecutedAnswer reading provider receipt
    point.1.unop.environment scopeHandle scope point.2
  map arrow := TypeCat.ofHom
    (transportExecution reading provider receipt scopeHandle scope arrow)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro execution
    apply ExecutedAnswer.ext_occurrence
    change (transportExecution reading provider receipt scopeHandle scope
      (𝟙 point) execution).occurrence = execution.occurrence
    exact transportExecution_occurrence reading provider receipt
      scopeHandle scope (𝟙 point) execution
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro execution
    apply ExecutedAnswer.ext_occurrence
    change
      (transportExecution reading provider receipt scopeHandle scope
        (earlier ≫ later) execution).occurrence =
      (transportExecution reading provider receipt scopeHandle scope later
        (transportExecution reading provider receipt scopeHandle scope earlier
          execution)).occurrence
    rw [transportExecution_occurrence, transportExecution_occurrence,
      transportExecution_occurrence]

/-- At one displayed point, the numbered occurrence determines the full
guarded execution receipt. Thus the proof-relevant fibre has not silently
quotiented distinct successful firings with the same answer. -/
theorem executionFamily_occurrence_injective
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (provider : CheckedProvider Scope Query reading.inScope)
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    (receipt : CheckedExtract entries bindings world query)
    (scopeHandle : Pattern) (scope : Scope)
    (point : (answerFace reading receipt).Elements) :
    Function.Injective (fun execution :
      (executionFamily reading provider receipt scopeHandle scope).obj point =>
        execution.occurrence) := by
  intro first second same
  exact ExecutedAnswer.ext_occurrence first second same

/-- Equal-request context arrows induce actual equivalences of guarded
execution fibres. The inverse comes from reversing that same request
equality, not from searching for a second occurrence. -/
private def reverseAnswerArrow
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    (receipt : CheckedExtract entries bindings world query)
    {first second : (answerFace reading receipt).Elements}
    (arrow : first ⟶ second) : second ⟶ first :=
  CategoryOfElements.homMk second first
    (Quiver.Hom.op
      (⟨arrow.val.unop.down.symm⟩ : first.1.unop ⟶ second.1.unop))
    (by
      change second.2 = first.2
      exact (show first.2 = second.2 from arrow.property).symm)

noncomputable def executionArrowEquiv
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (provider : CheckedProvider Scope Query reading.inScope)
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    (receipt : CheckedExtract entries bindings world query)
    (scopeHandle : Pattern) (scope : Scope)
    {first second : (answerFace reading receipt).Elements}
    (arrow : first ⟶ second) :
    (executionFamily reading provider receipt scopeHandle scope).obj first ≃
      (executionFamily reading provider receipt scopeHandle scope).obj second := by
  let reverse := reverseAnswerArrow reading receipt arrow
  refine {
    toFun := fun execution =>
      (executionFamily reading provider receipt scopeHandle scope).map arrow execution
    invFun := fun execution =>
      (executionFamily reading provider receipt scopeHandle scope).map reverse execution
    left_inv := ?_
    right_inv := ?_
  }
  · intro execution
    apply ExecutedAnswer.ext_occurrence
    change (transportExecution reading provider receipt scopeHandle scope reverse
      (transportExecution reading provider receipt scopeHandle scope arrow
        execution)).occurrence = execution.occurrence
    exact (transportExecution_occurrence reading provider receipt
      scopeHandle scope reverse _).trans
      (transportExecution_occurrence reading provider receipt
        scopeHandle scope arrow execution)
  · intro execution
    apply ExecutedAnswer.ext_occurrence
    change (transportExecution reading provider receipt scopeHandle scope arrow
      (transportExecution reading provider receipt scopeHandle scope reverse
        execution)).occurrence = execution.occurrence
    exact (transportExecution_occurrence reading provider receipt
      scopeHandle scope arrow _).trans
      (transportExecution_occurrence reading provider receipt
        scopeHandle scope reverse execution)

@[simp] theorem executionArrowEquiv_occurrence
    {State Query Ev Ov Scope : Type}
    (reading : CombinedReading State Query Ev Ov Scope)
    (provider : CheckedProvider Scope Query reading.inScope)
    {entries : List (String × TypeExpr)} {bindings : Bindings} {world query : Pattern}
    (receipt : CheckedExtract entries bindings world query)
    (scopeHandle : Pattern) (scope : Scope)
    {first second : (answerFace reading receipt).Elements}
    (arrow : first ⟶ second)
    (execution : (executionFamily reading provider receipt scopeHandle scope).obj first) :
    (executionArrowEquiv reading provider receipt scopeHandle scope arrow
      execution).occurrence = execution.occurrence := by
  change (transportExecution reading provider receipt scopeHandle scope arrow
    execution).occurrence = execution.occurrence
  exact transportExecution_occurrence reading provider receipt
    scopeHandle scope arrow execution

namespace CountedControl

open Mettapedia.TypeTheory.Models.RevisionedFamilies.CheckedOpenScopeExecution.CountedExample

/-- Two unequal full environments with one computed request. -/
def distributed : RequestEnvironment countingCombined capture :=
  ⟨environment "y"⟩

def concentrated : RequestEnvironment countingCombined capture :=
  ⟨repartitionedEnvironment "y"⟩

theorem distributed_ne_concentrated : distributed ≠ concentrated := by
  intro equal
  exact repartitioned_environment_ne
    (congrArg RequestEnvironment.environment equal)

/-- A genuine nonidentity arrow of the observed-request kernel pair. -/
def repartitionArrow : distributed ⟶ concentrated :=
  ⟨Prod.ext (repartitioned_same_world "y")
    (repartitioned_same_query "y")⟩

def sourcePoint : (answerFace countingCombined capture).Elements :=
  ⟨Opposite.op distributed, by change Nat; exact 2⟩

def targetPoint : (answerFace countingCombined capture).Elements :=
  ⟨Opposite.op concentrated, by change Nat; exact 2⟩

def answerArrow : sourcePoint ⟶ targetPoint :=
  CategoryOfElements.homMk sourcePoint targetPoint
    (Quiver.Hom.op (⟨repartitionArrow.down.symm⟩ : concentrated ⟶ distributed)) rfl

theorem sourcePoint_ne_targetPoint : sourcePoint ≠ targetPoint := by
  intro equal
  apply distributed_ne_concentrated
  exact congrArg (fun point : (answerFace countingCombined capture).Elements =>
    point.1.unop) equal

/-- The generic displayed family accepts an actual checked guarded receipt
at the source and carries it along the nonidentity kernel-pair arrow. -/
theorem source_fibre_inhabited :
    Nonempty ((executionFamily countingCombined (provider "y") capture
      scopeHandle singletonX).obj sourcePoint) := by
  simpa [executionFamily, sourcePoint, distributed, answerFace]
    using counted_execution

theorem target_fibre_inhabited :
    Nonempty ((executionFamily countingCombined (provider "y") capture
      scopeHandle singletonX).obj targetPoint) := by
  obtain ⟨execution⟩ := source_fibre_inhabited
  exact ⟨(executionFamily countingCombined (provider "y") capture
    scopeHandle singletonX).map answerArrow execution⟩

theorem mapped_event_is_original
    (execution : (executionFamily countingCombined (provider "y") capture
      scopeHandle singletonX).obj sourcePoint) :
    ((executionFamily countingCombined (provider "y") capture
      scopeHandle singletonX).map answerArrow execution).proofRelevantEvent =
      execution.proofRelevantEvent := by
  rfl

/-- A changed decoded query is not an arrow of this kernel pair; hence no
guarded receipt can be transported along it by this displayed family. -/
def changedQuery : RequestEnvironment countingCombined capture :=
  ⟨environment "x"⟩

theorem changed_query_no_arrow : ¬ Nonempty (distributed ⟶ changedQuery) := by
  rintro ⟨arrow⟩
  have queryEqual := congrArg Prod.snd arrow.down
  change ("y" : String) = "x" at queryEqual
  simp at queryEqual

end CountedControl

#print axioms requestGroupoid
#print axioms answerFace
#print axioms executionFamily
#print axioms executionFamily_occurrence_injective
#print axioms executionArrowEquiv
#print axioms executionArrowEquiv_occurrence
#print axioms CountedControl.distributed_ne_concentrated
#print axioms CountedControl.sourcePoint_ne_targetPoint
#print axioms CountedControl.source_fibre_inhabited
#print axioms CountedControl.target_fibre_inhabited
#print axioms CountedControl.mapped_event_is_original
#print axioms CountedControl.changed_query_no_arrow

end Mettapedia.TypeTheory.Models.RevisionedFamilies.CheckedOpenExecutionDisplayed
