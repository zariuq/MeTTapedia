import Mettapedia.GSLT.Core.BindingStoreCapabilityAlgebra
import Mettapedia.GSLT.LanguageDef.AuthoritativeSlotTrailCompilation
import Mettapedia.GSLT.LanguageDef.CompiledPlanOpenActivationViewCompilation
import Mettapedia.GSLT.LanguageDef.TermObservationCoalgebra
import Mettapedia.GSLT.LanguageDef.UnificationEliminationTraceCompilation

/-!
# Delayed source bindings as coalgebraic term views

A binding produced by matching need not immediately contain a rebuilt term.
It may retain an immutable source term, its generation-qualified environment,
and the ownership identity that keeps that environment live.  This module
gives that representation an independent semantic meaning and proves that
one-layer structural observation commutes with complete materialization.

Repeated use of the one-layer operation is the algebraic basis of a matcher
that traverses a source view without allocating the intervening constructor
tree.  The result is observer-specific: consumers that need only constructors,
children, or matching may use the view, while serialization and unrestricted
capture must force the complete value.

The physical lowering remains conditional.  A runtime must separately prove
that its owner/revision token retains the environment, that rollback restores
the complete carrier, and that tracing, GC, and publication understand the
carrier.  No particular C binding representation is claimed here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DelayedSourceBindingCompilation

open Mettapedia.GSLT.Core.BindingStoreCapabilityAlgebra
open CompiledPlanAdmission
open CompiledPlanOpenActivationViewCompilation
open AuthoritativeSlotTrailCompilation
open TermObservationCoalgebra

universe uOwner uRevision uKey uChild uNext uResult

variable {Owner : Type uOwner} {Revision : Type uRevision}
  {Key : Type uKey} {Child : Type uChild} {Next : Type uNext}
  {Result : Type uResult}

/-! ## Immutable generation-qualified source views -/

/-- A source view is a revision-pinned closure.  `owner` and `revision` do not
affect term meaning; they are retained so a physical lowering can prove that
the referenced environment remains live and immutable. -/
structure SourceView (Owner : Type uOwner) (Revision : Type uRevision) where
  owner : Owner
  revision : Revision
  generation : UInt32
  environment : OpenEnvironment
  source : Term

/-- Complete semantic forcing of one source view. -/
def SourceView.force
    (view : SourceView Owner Revision) : OpenTerm :=
  instantiateOpen view.generation view.environment view.source

/-- A binding value is either already materialized or retains a source view.
This is a semantic representation sum, not a prescribed physical tag. -/
inductive BindingValue (Owner : Type uOwner) (Revision : Type uRevision) where
  | eager (value : OpenTerm)
  | delayed (view : SourceView Owner Revision)

def BindingValue.denote : BindingValue Owner Revision -> OpenTerm
  | .eager value => value
  | .delayed view => view.force

/-! ## Direct coalgebraic unfolding -/

def openTermsToList : OpenTerms -> List OpenTerm
  | .nil => []
  | .cons head tail => head :: openTermsToList tail

def sourceChildren
    (view : SourceView Owner Revision) : Terms -> List (BindingValue Owner Revision)
  | .nil => []
  | .cons head tail =>
      .delayed { view with source := head } :: sourceChildren view tail

/-- Ordinary one-layer observation of a materialized open term. -/
def outOpen : OpenTerm -> TermLayer OpenTerm
  | .symbol name => .symbol name
  | .variable name => .variable name
  | .string value => .string value
  | .integer value => .integer value
  | .application head children =>
      .application head (openTermsToList children)

/-- Inspect one binding layer without first forcing a delayed source tree.
Only a source variable requires an environment lookup.  A rigid application
returns delayed child views that retain the same owner, revision, generation,
and environment. -/
def outBinding : BindingValue Owner Revision ->
    TermLayer (BindingValue Owner Revision)
  | .eager value => (outOpen value).map .eager
  | .delayed view =>
      match view.source with
      | .symbol name => .symbol name
      | .variable slot =>
          match view.environment slot with
          | none => .variable { generation := view.generation, slot }
          | some value => (outOpen value).map .eager
      | .string value => .string value
      | .integer value => .integer value
      | .application head children =>
          .application head (sourceChildren view children)

private theorem denote_sourceChildren
    (view : SourceView Owner Revision) (children : Terms) :
    (sourceChildren view children).map BindingValue.denote =
      openTermsToList
        (instantiateOpenTerms view.generation view.environment children) :=
  match children with
  | .nil => rfl
  | .cons head tail =>
      congrArg (instantiateOpen view.generation view.environment head :: ·)
        (denote_sourceChildren view tail)
termination_by children

/-- The delayed carrier is a coalgebraic realization of ordinary open terms:
exposing one physical layer and denoting its children is exactly the same as
forcing the complete value and exposing its first layer. -/
theorem outBinding_exact (value : BindingValue Owner Revision) :
    (outBinding value).map BindingValue.denote =
      outOpen value.denote := by
  cases value with
  | eager value =>
      rw [outBinding, TermLayer.map_comp]
      change (outOpen value).map id = outOpen value
      exact TermLayer.map_id _
  | delayed view =>
      rcases view with ⟨owner, revision, generation, environment, source⟩
      cases source with
      | symbol name => rfl
      | «variable» slot =>
          cases bound : environment slot with
          | none =>
              simp [outBinding, bound, BindingValue.denote,
                SourceView.force, instantiateOpen, outOpen, TermLayer.map]
          | some value =>
              simp only [outBinding, bound, TermLayer.map_comp,
                BindingValue.denote, SourceView.force, instantiateOpen]
              change (outOpen value).map id = outOpen value
              exact TermLayer.map_id _
      | string value => rfl
      | integer value => rfl
      | application head children =>
          simp only [outBinding, TermLayer.map,
            BindingValue.denote, SourceView.force, instantiateOpen, outOpen]
          exact congrArg (TermLayer.application head)
            (denote_sourceChildren
              { owner, revision, generation, environment,
                source := .application head children }
              children)

/-- Any one-layer algebra obtains exactly the same answer through the delayed
and materialized routes. -/
theorem observeLayer_exact
    (algebra : TermLayer OpenTerm -> Result)
    (value : BindingValue Owner Revision) :
    algebra ((outBinding value).map BindingValue.denote) =
      algebra (outOpen value.denote) := by
  rw [outBinding_exact]

/-! ## Revision and lifetime admission -/

/-- A runtime registry states which owner/revision/environment triples remain
rooted.  This proposition is deliberately separate from term denotation: an
invalid view may still have a mathematical meaning while being unsafe to
retain physically. -/
structure SnapshotRegistry (Owner : Type uOwner) (Revision : Type uRevision) where
  retains : Owner -> Revision -> OpenEnvironment -> Prop

def SnapshotRegistry.Admitted
    (registry : SnapshotRegistry Owner Revision)
    (view : SourceView Owner Revision) : Prop :=
  registry.retains view.owner view.revision view.environment

/-- A physically admissible delayed source carries its lifetime proof. -/
structure AdmittedSourceView
    (registry : SnapshotRegistry Owner Revision) where
  view : SourceView Owner Revision
  retained : registry.Admitted view

/-- Forcing depends only on the slots named by the source.  A physical
implementation may therefore retain a support-restricted environment, but it
must prove this agreement rather than infer it from a revision number. -/
theorem SourceView.force_eq_of_agreesOn
    (left right : SourceView Owner Revision)
    (sameGeneration : left.generation = right.generation)
    (sameSource : left.source = right.source)
    (agrees : AgreesOn left.source left.environment right.environment) :
    left.force = right.force := by
  calc
    left.force =
        instantiateOpen left.generation right.environment left.source :=
      instantiateOpen_eq_of_agreesOn left.generation
        left.environment right.environment left.source agrees
    _ = right.force := by
      simp only [SourceView.force]
      rw [sameGeneration, sameSource]

/-! ## Binding-environment refinement -/

abbrev PhysicalEnvironment
    (Key : Type uKey) (Owner : Type uOwner) (Revision : Type uRevision) :=
  Key -> Option (BindingValue Owner Revision)

abbrev LogicalEnvironment (Key : Type uKey) := Key -> Option OpenTerm

def denoteEnvironment
    (physical : PhysicalEnvironment Key Owner Revision) :
    LogicalEnvironment Key :=
  fun key => (physical key).map BindingValue.denote

def writePhysical [DecidableEq Key]
    (environment : PhysicalEnvironment Key Owner Revision)
    (key : Key) (value : BindingValue Owner Revision) :
    PhysicalEnvironment Key Owner Revision :=
  fun candidate => if candidate = key then some value else environment candidate

def writeLogical [DecidableEq Key]
    (environment : LogicalEnvironment Key)
    (key : Key) (value : OpenTerm) : LogicalEnvironment Key :=
  fun candidate => if candidate = key then some value else environment candidate

/-- Writing a delayed carrier refines writing its forced value to the logical
binding environment. -/
theorem denoteEnvironment_writePhysical [DecidableEq Key]
    (environment : PhysicalEnvironment Key Owner Revision)
    (key : Key) (value : BindingValue Owner Revision) :
    denoteEnvironment (writePhysical environment key value) =
      writeLogical (denoteEnvironment environment) key value.denote := by
  funext candidate
  by_cases same : candidate = key <;>
    simp [denoteEnvironment, writePhysical, writeLogical, same]

/-- Eager and delayed writes of the same semantic value are observationally
identical at every binding key. -/
theorem delayed_write_eq_eager_write [DecidableEq Key]
    (environment : PhysicalEnvironment Key Owner Revision)
    (key : Key) (view : SourceView Owner Revision) :
    denoteEnvironment (writePhysical environment key (.delayed view)) =
      denoteEnvironment (writePhysical environment key (.eager view.force)) := by
  rw [denoteEnvironment_writePhysical, denoteEnvironment_writePhysical]
  rfl

/-! ## Constructor decomposition without parent materialization -/

/-- Decompose two exposed rigid applications.  This operation is stated over
the polynomial term layer rather than over any guest language.  Equal heads
and arities emit ordered child equations; every other layer declines. -/
def decomposeLayers?
    (left right : TermLayer Child) (rest : List (Equation Child)) :
    Option (List (Equation Child)) :=
  match left, right with
  | .application leftHead leftChildren,
      .application rightHead rightChildren =>
      if leftHead = rightHead && leftChildren.length = rightChildren.length then
        some (List.zipWith Prod.mk leftChildren rightChildren ++ rest)
      else
        none
  | _, _ => none

/-- Constructor decomposition is natural in the child representation.  It can
therefore run before or after forcing delayed children with the same result. -/
theorem decomposeLayers?_natural
    (function : Child -> Next)
    (left right : TermLayer Child) (rest : List (Equation Child)) :
    (decomposeLayers? left right rest).map (mapEquations function) =
      decomposeLayers? (left.map function) (right.map function)
        (mapEquations function rest) := by
  cases left <;> cases right <;> try rfl
  case application.application leftHead leftChildren rightHead rightChildren =>
    simp only [decomposeLayers?, TermLayer.map, List.length_map]
    by_cases sameHead : leftHead = rightHead
    · subst rightHead
      by_cases sameLength : leftChildren.length = rightChildren.length
      · simp [sameLength, mapEquations, List.map_append, mapEquation]
      · simp [sameLength]
    · simp [sameHead]

def decomposeBindings?
    (left right : BindingValue Owner Revision)
    (rest : List (Equation (BindingValue Owner Revision))) :
    Option (List (Equation (BindingValue Owner Revision))) :=
  decomposeLayers? (outBinding left) (outBinding right) rest

def decomposeOpen?
    (left right : OpenTerm) (rest : List (Equation OpenTerm)) :
    Option (List (Equation OpenTerm)) :=
  decomposeLayers? (outOpen left) (outOpen right) rest

/-- Direct decomposition of delayed children commutes with the reference
materialized decomposition, including ordered equations and decline.  Since
the result still contains delayed children, repeated application removes no
semantic boundary and allocates no reconstructed parent application. -/
theorem decomposeBindings?_exact
    (left right : BindingValue Owner Revision)
    (rest : List (Equation (BindingValue Owner Revision))) :
    (decomposeBindings? left right rest).map
        (mapEquations BindingValue.denote) =
      decomposeOpen? left.denote right.denote
        (mapEquations BindingValue.denote rest) := by
  unfold decomposeBindings? decomposeOpen?
  rw [decomposeLayers?_natural]
  rw [outBinding_exact, outBinding_exact]

/-! ## Repeated structural traversal without parent materialization -/

/-- Execute the representation-neutral rigid worklist directly over delayed
binding values.  Variables remain explicit suspension boundaries. -/
def traverseBindings (fuel : Nat)
    (work : List (Equation (BindingValue Owner Revision))) :
    TraversalResult (BindingValue Owner Revision) :=
  TermObservationCoalgebra.run outBinding fuel work

/-- Reference traversal after complete materialization. -/
def traverseOpen (fuel : Nat)
    (work : List (Equation OpenTerm)) : TraversalResult OpenTerm :=
  TermObservationCoalgebra.run outOpen fuel work

/-- Arbitrarily many direct constructor observations commute with complete
materialization.  The theorem preserves success, mismatch, the exact blocked
variable equation, and the complete fuel residual—not merely a Boolean answer. -/
theorem traverseBindings_exact
    (fuel : Nat)
    (work : List (Equation (BindingValue Owner Revision))) :
    (traverseBindings fuel work).map BindingValue.denote =
      traverseOpen fuel (mapEquations BindingValue.denote work) := by
  exact run_natural outBinding outOpen BindingValue.denote
    outBinding_exact fuel work

/-! ## Exact forcing fallback to the generic unifier -/

open Mettapedia.Logic.LP
open UnificationEliminationTraceCompilation

def forceTrace (fuel : Nat)
    (left right : BindingValue Owner Revision) :
    EliminationTrace openSignature :=
  runTrace fuel
    [(encodeOpenTerm left.denote, encodeOpenTerm right.denote)]

/-- If a consumer is not licensed for direct structural traversal, forcing the
carrier and executing the independently proved generic elimination trace has
exactly ordinary unification semantics. -/
theorem observe_forceTrace_exact
    (fuel : Nat) (left right : BindingValue Owner Revision) :
    observe (forceTrace fuel left right) =
      unifyFuel fuel
        [(encodeOpenTerm left.denote, encodeOpenTerm right.denote)] := by
  exact observe_runTrace_exact _ _

/-! ## Information-loss boundary -/

def rootShape (value : OpenTerm) : TermLayer Unit :=
  (outOpen value).map fun _ => ()

/-- Root shape cannot replace complete materialization: two applications with
the same root and arity but different children have the same root observation.
Thus serialization and unrestricted capture must not be admitted merely from
`outBinding_exact`. -/
theorem no_complete_reconstruction_from_rootShape :
    ¬ exists rebuild : TermLayer Unit -> OpenTerm,
      forall value, rebuild (rootShape value) = value := by
  rintro ⟨rebuild, exact⟩
  let left : OpenTerm :=
    .application [1] (.cons (.symbol [2]) .nil)
  let right : OpenTerm :=
    .application [1] (.cons (.symbol [3]) .nil)
  have sameShape : rootShape left = rootShape right := by
    rfl
  have sameValue : left = right := by
    calc
      left = rebuild (rootShape left) := (exact left).symm
      _ = rebuild (rootShape right) := congrArg rebuild sameShape
      _ = right := exact right
  have different : left ≠ right := by decide
  exact different sameValue

/-! ## Positive and negative controls -/

namespace Canaries

private def emptyEnvironment : OpenEnvironment := fun _ => none

private def boundEnvironment : OpenEnvironment
  | 0 => some (.symbol [9])
  | _ => none

private def applicationSource : Term :=
  .application [1]
    (.cons (.variable 0)
      (.cons (.string [2])
        (.cons (.integer 3) .nil)))

private def differentHeadSource : Term :=
  .application [4]
    (.cons (.variable 0)
      (.cons (.string [2])
        (.cons (.integer 3) .nil)))

private def nestedSource : Term :=
  .application [5]
    (.cons
      (.application [6]
        (.cons (.symbol [7]) .nil))
      (.cons (.symbol [8]) .nil))

private def nestedDifferentLeafSource : Term :=
  .application [5]
    (.cons
      (.application [6]
        (.cons (.symbol [9]) .nil))
      (.cons (.symbol [8]) .nil))

private def view (generation : UInt32) (environment : OpenEnvironment) :
    SourceView Unit Nat :=
  { owner := (), revision := 5, generation, environment,
    source := applicationSource }

/-- Application children remain delayed after one direct structural step. -/
example :
    outBinding (.delayed (view 7 boundEnvironment)) =
      .application [1]
        [.delayed { view 7 boundEnvironment with source := .variable 0 },
         .delayed { view 7 boundEnvironment with source := .string [2] },
         .delayed { view 7 boundEnvironment with source := .integer 3 }] := by
  rfl

/-- Direct delayed decomposition emits the three ordered child equations
without reconstructing either parent application. -/
example :
    (decomposeBindings?
        (.delayed (view 7 boundEnvironment))
        (.delayed (view 8 boundEnvironment)) []).map List.length =
      some 3 := by
  rfl

/-- A different rigid head is rejected directly and publishes no child
equations. -/
example :
    decomposeBindings?
        (.delayed (view 7 boundEnvironment))
        (.delayed
          { view 8 boundEnvironment with source := differentHeadSource }) [] =
      none := by
  rfl

/-- Repeated direct observation reaches a nested rigid normal form without
forcing either source view. -/
example :
    traverseBindings 5
      [(.delayed
          { view 7 boundEnvironment with source := nestedSource },
        .delayed
          { view 8 boundEnvironment with source := nestedSource })] =
      .complete := by
  rfl

/-- A disagreement below two constructors is still rejected directly. -/
example :
    traverseBindings 5
      [(.delayed
          { view 7 boundEnvironment with source := nestedSource },
        .delayed
          { view 8 boundEnvironment with
            source := nestedDifferentLeafSource })] =
      .mismatch := by
  rfl

/-- An unbound generation-qualified variable is preserved as the exact
suspension equation instead of being guessed or captured. -/
example :
    let left : BindingValue Unit Nat :=
      .delayed { view 7 emptyEnvironment with source := .variable 0 }
    let right : BindingValue Unit Nat :=
      .delayed { view 8 emptyEnvironment with source := .variable 0 }
    traverseBindings 1 [(left, right)] = .blocked [(left, right)] := by
  rfl

/-- Bounded execution retains the exact ordered child residual. -/
example :
    let left : BindingValue Unit Nat :=
      .delayed { view 7 boundEnvironment with source := nestedSource }
    let right : BindingValue Unit Nat :=
      .delayed { view 8 boundEnvironment with source := nestedSource }
    (traverseBindings 1 [(left, right)]).map BindingValue.denote =
      traverseOpen 1
        (mapEquations BindingValue.denote [(left, right)]) := by
  simpa only using
    (traverseBindings_exact (Owner := Unit) (Revision := Nat) 1
      [(.delayed
          { view 7 boundEnvironment with source := nestedSource },
        .delayed
          { view 8 boundEnvironment with source := nestedSource })])

/-- Zero fuel remains an explicit incomplete observation even for equal
materialized constants. -/
example :
    (observe
      (forceTrace 0
        ((.eager (.symbol [9])) : BindingValue Unit Nat)
        ((.eager (.symbol [9])) : BindingValue Unit Nat))).isSome = false := by
  rfl

/-- Sufficient fuel observes equality through the generic exact fallback. -/
example :
    (observe
      (forceTrace 2
        ((.eager (.symbol [9])) : BindingValue Unit Nat)
        ((.eager (.symbol [9])) : BindingValue Unit Nat))).isSome = true := by
  rfl

/-- A bound source variable exposes the bound value without rebuilding its
surrounding source application. -/
example :
    outBinding
        (.delayed { view 7 boundEnvironment with source := .variable 0 }) =
      .symbol [9] := by
  rfl

/-- An unbound source variable preserves generation-qualified identity. -/
example :
    outBinding
        (.delayed { view 7 emptyEnvironment with source := .variable 0 }) =
      .variable { generation := 7, slot := 0 } := by
  rfl

/-- Equal source slots from different generations remain distinct whenever
the slot is unbound. -/
example :
    (SourceView.force
      { view 7 emptyEnvironment with source := .variable 0 }) ≠
    SourceView.force
      { view 8 emptyEnvironment with source := .variable 0 } := by
  decide

/-- Generation does not invent a distinction after the complete support is
already bound to the same closed value. -/
example :
    SourceView.force
        { view 7 boundEnvironment with source := .variable 0 } =
      SourceView.force
        { view 8 boundEnvironment with source := .variable 0 } := by
  rfl

private def currentRegistry : SnapshotRegistry Unit Nat where
  retains _ revision _ := revision = 5

/-- The current revision is physically admissible. -/
example : currentRegistry.Admitted (view 7 boundEnvironment) := by
  rfl

/-- A stale revision is rejected even when its term would remain
mathematically denotable. -/
example :
    ¬ (currentRegistry.Admitted
      { view 7 boundEnvironment with revision := 4 }) := by
  simp [SnapshotRegistry.Admitted, currentRegistry]

private def oneKey : FiniteEnvironmentCompilation.Inventory Unit where
  keys := [()]
  nodup := by decide

private def emptyPhysicalState :
    State oneKey (BindingValue Unit Nat) :=
  { slots := FiniteEnvironmentCompilation.emptyDenseEnvironment oneKey,
    trail := [] }

/-- The existing authoritative value-restoring trail rolls a delayed carrier
back exactly, including its owner, revision, generation, environment, and
source closure. -/
example :
    let slot : oneKey.Slot := ⟨0, by decide⟩
    rollbackTo? oneKey (mark emptyPhysicalState)
        (run oneKey emptyPhysicalState
          [(slot, .delayed (view 7 boundEnvironment))]) =
      some emptyPhysicalState := by
  exact rollbackTo?_run oneKey emptyPhysicalState
    [(⟨0, by decide⟩, .delayed (view 7 boundEnvironment))]

end Canaries

#print axioms TermLayer.map_id
#print axioms TermLayer.map_comp
#print axioms outBinding_exact
#print axioms observeLayer_exact
#print axioms SourceView.force_eq_of_agreesOn
#print axioms denoteEnvironment_writePhysical
#print axioms delayed_write_eq_eager_write
#print axioms decomposeLayers?_natural
#print axioms decomposeBindings?_exact
#print axioms traverseBindings_exact
#print axioms observe_forceTrace_exact
#print axioms no_complete_reconstruction_from_rootShape

end Mettapedia.GSLT.LanguageDef.DelayedSourceBindingCompilation
