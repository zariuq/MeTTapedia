import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic
import Mettapedia.GSLT.Core.Composition
import Mettapedia.GSLT.Dynamics.MemoizationObserver
import Mettapedia.GSLT.Dynamics.RegionHoleRealizationTransformation
import Mettapedia.GSLT.Dynamics.StableOccurrenceIdentityIndex
import Mettapedia.GSLT.LanguageDef.DelayedSourceBindingCompilation
import Mettapedia.GSLT.LanguageDef.OwnershipClosedMaterialization
import Mettapedia.GSLT.LanguageDef.SupportRestrictedSourceViewCompilation
import Mettapedia.Languages.MeTTa.SearchStateStack

/-!
# Occurrence-qualified MeTTa term views

A term view is not a new term semantics.  It is a certified package of five
coordinates that a runtime already has when it activates a compiled equation:

* the stable source occurrence;
* the immutable binding image whose denotation supplies open variables;
* the source term and rule-instance generation;
* the source-space owner and revision which retain that source;
* the compiled plan together with evidence that it names this source revision.

The semantic map forgets the representation and forces an ordinary open term.
Support capture, root observation, child selection, and constructor-guided
traversal all commute with that map.  Consequently a runtime may preserve the
view across those observers and force only for a consumer which demands the
complete term.

Search order is deliberately absent from the carrier.  Strategy-independent
bag equivalence is inherited from the branching GSLT only for kernels carrying
an additive denotation and a world-preservation certificate.  Scoped commit
and noncommuting effects remain explicit boundaries.

The final section gives a structural node-observation grade.  It compares
semantic constructor observations, not bytes, allocations, or elapsed time;
those require a separately measured runtime refinement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TermViewCompilation

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.BindingStoreCapabilityAlgebra
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.Dynamics.StableOccurrenceIdentityIndex
open Mettapedia.GSLT.Dynamics.OrderedOccurrenceBodyAlgebra
open Mettapedia.GSLT.Dynamics.RegionHolePlan
open Mettapedia.GSLT.LanguageDef.CompiledPlanAdmission
open Mettapedia.GSLT.LanguageDef.CompiledPlanOpenActivationViewCompilation
open Mettapedia.GSLT.LanguageDef.DelayedSourceBindingCompilation
open Mettapedia.GSLT.LanguageDef.OwnershipClosedMaterialization
open Mettapedia.GSLT.LanguageDef.SupportRestrictedSourceViewCompilation
open Mettapedia.GSLT.LanguageDef.TermObservationCoalgebra
open Mettapedia.Languages.MeTTa.SearchStateStack

universe uOwner uRevision uOccurrence uPlan uPhysical uUpdate uBranch uWorld
  uVersion uRuntimeKey

/-! ## The certified carrier -/

/-- The semantic projection of a compiled plan.  A plan is qualified by both
the source term it was compiled from and the immutable program revision in
which that source occurrence was selected. -/
structure PlanProjection
    (Revision : Type uRevision) (Occurrence : Type uOccurrence)
    (Plan : Type uPlan) where
  source : Plan -> Term
  revision : Plan -> Revision
  occurrence : Plan -> Occurrence

/-- A source occurrence paired with one physical binding image and exact plan
evidence.  The binding-store denotation is the only binding authority. -/
structure TermView
    (Owner : Type uOwner) (Revision : Type uRevision)
    (Occurrence : Type uOccurrence) (Plan : Type uPlan)
    (Physical : Type uPhysical) (Update : Type uUpdate)
    (store : BindingStore OpenEnvironment Physical Update)
    (projection : PlanProjection Revision Occurrence Plan) where
  occurrence : Occurrence
  owner : Owner
  revision : Revision
  generation : UInt32
  bindings : Physical
  source : Term
  plan : Plan
  plan_source : projection.source plan = source
  plan_revision : projection.revision plan = revision
  plan_occurrence : projection.occurrence plan = occurrence

namespace TermView

variable {Owner : Type uOwner} {Revision : Type uRevision}
  {Occurrence : Type uOccurrence} {Plan : Type uPlan}
  {Physical : Type uPhysical} {Update : Type uUpdate}
  {store : BindingStore OpenEnvironment Physical Update}
  {projection : PlanProjection Revision Occurrence Plan}

/-- Forget plan and occurrence evidence only at the existing GSLT source-view
boundary. -/
def toSourceView
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) : SourceView Owner Revision where
  owner := view.owner
  revision := view.revision
  generation := view.generation
  environment := store.denote view.bindings
  source := view.source

/-- Complete observation of a term view. -/
def force
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) : OpenTerm :=
  view.toSourceView.force

/-- Stable occurrence identity and plan evidence are orthogonal to binding
denotation. -/
@[simp] theorem force_eq_instantiateOpen
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) :
    view.force = instantiateOpen view.generation
      (store.denote view.bindings) view.source := rfl

/-- Advance only the physical binding version through the store interface.
Source occurrence, plan evidence, and source lifetime coordinates are
unchanged. -/
def writeBinding
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) (update : Update) :
    TermView Owner Revision Occurrence Plan Physical Update store projection :=
  { view with bindings := store.write view.bindings update }

/-- A physical binding-version update changes forcing exactly as the
authoritative logical update specifies. -/
theorem writeBinding_force_exact
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) (update : Update) :
    (view.writeBinding update).force =
      instantiateOpen view.generation
        (store.logicalWrite (store.denote view.bindings) update) view.source := by
  simp only [writeBinding, force, toSourceView]
  rw [store.write_exact]
  rfl

/-- Advance through a finite authored update path without changing any source
or plan coordinate. -/
def writeBindings
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) (updates : List Update) :
    TermView Owner Revision Occurrence Plan Physical Update store projection :=
  { view with bindings := store.writeMany view.bindings updates }

theorem writeBindings_force_exact
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) (updates : List Update) :
    (view.writeBindings updates).force =
      instantiateOpen view.generation
        (store.logicalWriteMany (store.denote view.bindings) updates)
        view.source := by
  simp only [writeBindings, force, toSourceView]
  rw [store.writeMany_exact]
  rfl

/-- Expose a term view as an occurrence-index payload without identifying
equal terms from different source occurrences. -/
def toStableOccurrence
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) :
    Mettapedia.GSLT.Dynamics.StableOccurrenceIdentityIndex.Occurrence
      Occurrence OpenTerm :=
  { id := view.occurrence, payload := view.force }

end TermView

/-! ## Support-minimal owned capture as a certified realization -/

/-- The independently owned form of a term view.  Only the distinct source
support is retained in the binding snapshot. -/
structure CapturedTermView
    (Owner : Type uOwner) (Revision : Type uRevision)
    (Occurrence : Type uOccurrence) (Plan : Type uPlan)
    (projection : PlanProjection Revision Occurrence Plan) where
  occurrence : Occurrence
  snapshot : SupportSnapshot Owner Revision
  plan : Plan
  plan_source : projection.source plan = snapshot.source
  plan_revision : projection.revision plan = snapshot.revision
  plan_occurrence : projection.occurrence plan = occurrence

namespace CapturedTermView

variable {Owner : Type uOwner} {Revision : Type uRevision}
  {Occurrence : Type uOccurrence} {Plan : Type uPlan}
  {projection : PlanProjection Revision Occurrence Plan}

def force
    (view : CapturedTermView Owner Revision Occurrence Plan projection) :
    OpenTerm :=
  view.snapshot.toSourceView.force

end CapturedTermView

/-- Complete observations retain provenance even when two forced values are
equal. -/
@[ext] structure CompleteObservation
    (Occurrence : Type uOccurrence) (Plan : Type uPlan) where
  occurrence : Occurrence
  plan : Plan
  value : OpenTerm

section Capture

variable {Owner : Type uOwner} {Revision : Type uRevision}
  {Occurrence : Type uOccurrence} {Plan : Type uPlan}
  {Physical : Type uPhysical} {Update : Type uUpdate}
  {store : BindingStore OpenEnvironment Physical Update}
  {projection : PlanProjection Revision Occurrence Plan}

/-- Capture precisely the slots observable from the source term. -/
def capture
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) :
    CapturedTermView Owner Revision Occurrence Plan projection where
  occurrence := view.occurrence
  snapshot := SupportSnapshot.capture view.toSourceView
  plan := view.plan
  plan_source := by
    change projection.source view.plan = view.source
    exact view.plan_source
  plan_revision := by
    change projection.revision view.plan = view.revision
    exact view.plan_revision
  plan_occurrence := view.plan_occurrence

def observeSource
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) : CompleteObservation Occurrence Plan :=
  { occurrence := view.occurrence, plan := view.plan, value := view.force }

def observeCaptured
    (view : CapturedTermView Owner Revision Occurrence Plan projection) :
    CompleteObservation Occurrence Plan :=
  { occurrence := view.occurrence, plan := view.plan, value := view.force }

/-- Support-minimal capture is a non-identity GSLT realization.  Its physical
artifact differs from the source carrier, while occurrence, plan, and complete
term observation are preserved exactly. -/
def supportCaptureRealization :
    SimpleRealization
      (TermView Owner Revision Occurrence Plan Physical Update store projection)
      (CapturedTermView Owner Revision Occurrence Plan projection)
      (CompleteObservation Occurrence Plan) where
  compile := fun _ view => capture view
  observeSource := fun _ view => observeSource view
  observeArtifact := fun _ view => observeCaptured view
  adequate := by
    intro _ view
    apply CompleteObservation.ext
    · rfl
    · rfl
    · exact SupportSnapshot.capture_force_exact view.toSourceView

@[simp] theorem capture_occurrence
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) :
    (capture view).occurrence = view.occurrence := rfl

@[simp] theorem capture_plan
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) :
    (capture view).plan = view.plan := rfl

theorem capture_force_exact
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) :
    (capture view).force = view.force :=
  SupportSnapshot.capture_force_exact view.toSourceView

/-- Capture an authored source family pointwise.  List order and duplicate
occurrences are retained because capture never quotients the family. -/
def captureFamily
    (views : List (TermView Owner Revision Occurrence Plan Physical Update
      store projection)) :
    List (CapturedTermView Owner Revision Occurrence Plan projection) :=
  views.map capture

theorem captureFamily_observe_exact
    (views : List (TermView Owner Revision Occurrence Plan Physical Update
      store projection)) :
    (captureFamily views).map observeCaptured = views.map observeSource := by
  induction views with
  | nil => rfl
  | cons view views inductionHypothesis =>
      simp only [captureFamily, List.map_cons]
      have headExact : observeCaptured (capture view) = observeSource view := by
        apply CompleteObservation.ext
        · rfl
        · rfl
        · exact capture_force_exact view
      rw [headExact]
      simpa [captureFamily] using inductionHypothesis

end Capture

/-! ## Root and child observers with occurrence provenance -/

/-- A cursor retains the originating source occurrence and plan while moving
through a delayed or eager term.  `path` is the root-to-current child path. -/
@[ext] structure Cursor
    (Owner : Type uOwner) (Revision : Type uRevision)
    (Occurrence : Type uOccurrence) (Plan : Type uPlan) where
  occurrence : Occurrence
  plan : Plan
  path : List Nat
  value : BindingValue Owner Revision

namespace Cursor

variable {Owner : Type uOwner} {Revision : Type uRevision}
  {Occurrence : Type uOccurrence} {Plan : Type uPlan}

def denote (cursor : Cursor Owner Revision Occurrence Plan) : OpenTerm :=
  cursor.value.denote

/-- The root cursor over an owned support snapshot. -/
def root {projection : PlanProjection Revision Occurrence Plan}
    (view : CapturedTermView Owner Revision Occurrence Plan projection) :
    Cursor Owner Revision Occurrence Plan where
  occurrence := view.occurrence
  plan := view.plan
  path := []
  value := .delayed view.snapshot.toSourceView

@[simp] theorem root_denote
    {projection : PlanProjection Revision Occurrence Plan}
    (view : CapturedTermView Owner Revision Occurrence Plan projection) :
    (root view).denote = view.force := rfl

def decorateChildren (cursor : Cursor Owner Revision Occurrence Plan) :
    Nat -> List (BindingValue Owner Revision) ->
      List (Cursor Owner Revision Occurrence Plan)
  | _, [] => []
  | index, child :: children =>
      { cursor with path := cursor.path ++ [index], value := child } ::
        decorateChildren cursor (index + 1) children

theorem decorateChildren_denote
    (cursor : Cursor Owner Revision Occurrence Plan)
    (index : Nat) (children : List (BindingValue Owner Revision)) :
    (decorateChildren cursor index children).map Cursor.denote =
      children.map BindingValue.denote := by
  induction children generalizing index with
  | nil => rfl
  | cons child children inductionHypothesis =>
      simp [decorateChildren, denote, inductionHypothesis]

def decorateLayer (cursor : Cursor Owner Revision Occurrence Plan) :
    TermLayer (BindingValue Owner Revision) ->
      TermLayer (Cursor Owner Revision Occurrence Plan)
  | .symbol name => .symbol name
  | .variable name => .variable name
  | .string value => .string value
  | .integer value => .integer value
  | .application head children =>
      .application head (decorateChildren cursor 0 children)

theorem decorateLayer_denote
    (cursor : Cursor Owner Revision Occurrence Plan)
    (layer : TermLayer (BindingValue Owner Revision)) :
    (decorateLayer cursor layer).map Cursor.denote =
      layer.map BindingValue.denote := by
  cases layer <;> simp [decorateLayer, TermLayer.map,
    decorateChildren_denote]

/-- Observe one layer while retaining occurrence, plan, and child path on every
returned child cursor. -/
def out (cursor : Cursor Owner Revision Occurrence Plan) :
    TermLayer (Cursor Owner Revision Occurrence Plan) :=
  decorateLayer cursor (outBinding cursor.value)

/-- Root observation is a coalgebra morphism to ordinary open terms. -/
theorem out_exact (cursor : Cursor Owner Revision Occurrence Plan) :
    (out cursor).map Cursor.denote = outOpen cursor.denote := by
  calc
    (out cursor).map Cursor.denote =
        (outBinding cursor.value).map BindingValue.denote := by
      rw [out, decorateLayer_denote]
    _ = outOpen cursor.value.denote := outBinding_exact cursor.value
    _ = outOpen cursor.denote := rfl

/-- Select one immediate child without forcing its siblings or rebuilding the
parent application. -/
def child? (cursor : Cursor Owner Revision Occurrence Plan) (index : Nat) :
    Option (Cursor Owner Revision Occurrence Plan) :=
  match outBinding cursor.value with
  | .application _ children =>
      (children[index]?).map fun child =>
        { cursor with path := cursor.path ++ [index], value := child }
  | _ => none

def openChild? (value : OpenTerm) (index : Nat) : Option OpenTerm :=
  match outOpen value with
  | .application _ children => children[index]?
  | _ => none

/-- Child selection commutes with complete forcing. -/
theorem child_denote_exact
    (cursor : Cursor Owner Revision Occurrence Plan) (index : Nat) :
    (cursor.child? index).map Cursor.denote =
      openChild? cursor.denote index := by
  unfold child? openChild? denote
  have exact := outBinding_exact cursor.value
  cases observed : outBinding cursor.value <;>
    rw [observed] at exact <;>
    simp only [TermLayer.map] at exact
  all_goals rw [← exact]
  all_goals try rfl
  case application head children =>
    simp [Function.comp_def]

theorem child_occurrence_preserved
    (cursor child : Cursor Owner Revision Occurrence Plan) (index : Nat)
    (selected : cursor.child? index = some child) :
    child.occurrence = cursor.occurrence := by
  cases observed : outBinding cursor.value <;>
    simp [child?, observed] at selected
  case application head children =>
    cases chosen : children[index]? with
    | none => simp [chosen] at selected
    | some value =>
        simp [chosen] at selected
        subst child
        rfl

theorem child_plan_preserved
    (cursor child : Cursor Owner Revision Occurrence Plan) (index : Nat)
    (selected : cursor.child? index = some child) :
    child.plan = cursor.plan := by
  cases observed : outBinding cursor.value <;>
    simp [child?, observed] at selected
  case application head children =>
    cases chosen : children[index]? with
    | none => simp [chosen] at selected
    | some value =>
        simp [chosen] at selected
        subst child
        rfl

theorem child_path_exact
    (cursor child : Cursor Owner Revision Occurrence Plan) (index : Nat)
    (selected : cursor.child? index = some child) :
    child.path = cursor.path ++ [index] := by
  cases observed : outBinding cursor.value <;>
    simp [child?, observed] at selected
  case application head children =>
    cases chosen : children[index]? with
    | none => simp [chosen] at selected
    | some value =>
        simp [chosen] at selected
        subst child
        rfl

end Cursor

/-! ## Constructor-guided traversal and unification observation -/

def traverseCursors
    {Owner : Type uOwner} {Revision : Type uRevision}
    {Occurrence : Type uOccurrence} {Plan : Type uPlan}
    (fuel : Nat)
    (work : List (Equation (Cursor Owner Revision Occurrence Plan))) :
    TraversalResult (Cursor Owner Revision Occurrence Plan) :=
  Mettapedia.GSLT.LanguageDef.TermObservationCoalgebra.run
    Cursor.out fuel work

/-- Arbitrarily many rigid observations commute with forcing.  Every blocked
or exhausted residual equation retains its source occurrence, plan, and path
until the result is mapped to ordinary open terms. -/
theorem traverseCursors_exact
    {Owner : Type uOwner} {Revision : Type uRevision}
    {Occurrence : Type uOccurrence} {Plan : Type uPlan}
    (fuel : Nat)
    (work : List (Equation (Cursor Owner Revision Occurrence Plan))) :
    (traverseCursors fuel work).map Cursor.denote =
      Mettapedia.GSLT.LanguageDef.TermObservationCoalgebra.run outOpen fuel
        (mapEquations Cursor.denote work) := by
  exact run_natural Cursor.out outOpen Cursor.denote Cursor.out_exact fuel work

/-! ## Composition of open substitutions -/

/-- A simultaneous substitution over generation-qualified open variables. -/
abbrev OpenSubstitution := LogicVariable -> Option OpenTerm

def emptyOpenSubstitution : OpenSubstitution := fun _ => none

mutual

def substituteOpen (substitution : OpenSubstitution) : OpenTerm -> OpenTerm
  | .symbol name => .symbol name
  | .variable logicVariable =>
      (substitution logicVariable).getD (.variable logicVariable)
  | .string value => .string value
  | .integer value => .integer value
  | .application head arguments =>
      .application head (substituteOpenTerms substitution arguments)

def substituteOpenTerms
    (substitution : OpenSubstitution) : OpenTerms -> OpenTerms
  | .nil => .nil
  | .cons head tail =>
      .cons (substituteOpen substitution head)
        (substituteOpenTerms substitution tail)

end

/-- Apply `first`, then `second`, without constructing the intermediate term. -/
def composeOpen
    (first second : OpenSubstitution) : OpenSubstitution :=
  fun logicVariable =>
    match first logicVariable with
    | some value => some (substituteOpen second value)
    | none => second logicVariable

mutual

theorem substituteOpen_comp
    (first second : OpenSubstitution) (value : OpenTerm) :
    substituteOpen second (substituteOpen first value) =
      substituteOpen (composeOpen first second) value := by
  cases value with
  | symbol name => rfl
  | «variable» logicVariable =>
      simp only [substituteOpen, composeOpen]
      cases bound : first logicVariable <;> simp [substituteOpen]
  | string value => rfl
  | integer value => rfl
  | application head arguments =>
      simp only [substituteOpen]
      rw [substituteOpenTerms_comp]

theorem substituteOpenTerms_comp
    (first second : OpenSubstitution) (values : OpenTerms) :
    substituteOpenTerms second (substituteOpenTerms first values) =
      substituteOpenTerms (composeOpen first second) values := by
  cases values with
  | nil => rfl
  | cons head tail =>
      simp only [substituteOpenTerms]
      rw [substituteOpen_comp, substituteOpenTerms_comp]

end

mutual

theorem substituteOpen_empty (value : OpenTerm) :
    substituteOpen emptyOpenSubstitution value = value := by
  cases value with
  | symbol name => rfl
  | «variable» logicVariable => rfl
  | string value => rfl
  | integer value => rfl
  | application head arguments =>
      simp only [substituteOpen]
      rw [substituteOpenTerms_empty]

theorem substituteOpenTerms_empty (values : OpenTerms) :
    substituteOpenTerms emptyOpenSubstitution values = values := by
  cases values with
  | nil => rfl
  | cons head tail =>
      simp only [substituteOpenTerms]
      rw [substituteOpen_empty, substituteOpenTerms_empty]

end

@[simp] theorem empty_composeOpen (substitution : OpenSubstitution) :
    composeOpen emptyOpenSubstitution substitution = substitution := by
  funext logicVariable
  simp [composeOpen, emptyOpenSubstitution]

@[simp] theorem composeOpen_empty (substitution : OpenSubstitution) :
    composeOpen substitution emptyOpenSubstitution = substitution := by
  funext logicVariable
  cases bound : substitution logicVariable with
  | none => simp [composeOpen, emptyOpenSubstitution, bound]
  | some value =>
      simp [composeOpen, bound,
        substituteOpen_empty]

theorem composeOpen_assoc
    (first second third : OpenSubstitution) :
    composeOpen (composeOpen first second) third =
      composeOpen first (composeOpen second third) := by
  funext logicVariable
  cases bound : first logicVariable with
  | none => simp [composeOpen, bound]
  | some value => simp [composeOpen, bound, substituteOpen_comp]

/-- Fold an open substitution into the environment retained by a source view. -/
def composeEnvironment
    (generation : UInt32) (environment : OpenEnvironment)
    (substitution : OpenSubstitution) : OpenEnvironment :=
  fun slot =>
    match environment slot with
    | some value => some (substituteOpen substitution value)
    | none => substitution { generation, slot }

/-- Extending an environment twice is exactly one extension by the composed
substitution.  This is the representation-level associativity needed to retain
a source view across several deterministic Regions. -/
theorem composeEnvironment_assoc
    (generation : UInt32) (environment : OpenEnvironment)
    (first second : OpenSubstitution) :
    composeEnvironment generation
        (composeEnvironment generation environment first) second =
      composeEnvironment generation environment (composeOpen first second) := by
  funext slot
  simp only [composeEnvironment]
  cases bound : environment slot with
  | none =>
      simp only
      cases replacement : first { generation := generation, slot := slot } with
      | none => simp [composeOpen, replacement]
      | some value => simp [composeOpen, replacement]
  | some value =>
      simpa only [Option.some.injEq] using
        substituteOpen_comp first second value

@[simp] theorem composeEnvironment_empty
    (generation : UInt32) (environment : OpenEnvironment) :
    composeEnvironment generation environment emptyOpenSubstitution =
      environment := by
  funext slot
  cases bound : environment slot with
  | none => simp [composeEnvironment, emptyOpenSubstitution, bound]
  | some value =>
      simp [composeEnvironment, bound, substituteOpen_empty]

mutual

theorem substituteOpen_instantiateOpen
    (generation : UInt32) (environment : OpenEnvironment)
    (substitution : OpenSubstitution) (source : Term) :
    substituteOpen substitution
        (instantiateOpen generation environment source) =
      instantiateOpen generation
        (composeEnvironment generation environment substitution) source := by
  cases source with
  | symbol name => rfl
  | «variable» slot =>
      cases bound : environment slot with
      | none =>
          cases replacement : substitution { generation, slot } <;>
            simp [instantiateOpen, composeEnvironment, substituteOpen,
              bound, replacement]
      | some value =>
          simp [instantiateOpen, composeEnvironment, bound]
  | string value => rfl
  | integer value => rfl
  | application head arguments =>
      simp only [instantiateOpen, substituteOpen]
      rw [substituteOpenTerms_instantiateOpenTerms]

theorem substituteOpenTerms_instantiateOpenTerms
    (generation : UInt32) (environment : OpenEnvironment)
    (substitution : OpenSubstitution) (sources : Terms) :
    substituteOpenTerms substitution
        (instantiateOpenTerms generation environment sources) =
      instantiateOpenTerms generation
        (composeEnvironment generation environment substitution) sources := by
  cases sources with
  | nil => rfl
  | cons head tail =>
      simp only [instantiateOpenTerms, substituteOpenTerms]
      rw [substituteOpen_instantiateOpen,
        substituteOpenTerms_instantiateOpenTerms]

end

/-- Extend a source view by composing environments, without forcing its source
term. -/
def extendSourceView
    {Owner : Type uOwner} {Revision : Type uRevision}
    (view : SourceView Owner Revision) (substitution : OpenSubstitution) :
    SourceView Owner Revision :=
  { view with environment :=
      composeEnvironment view.generation view.environment substitution }

/-- Forcing an extended source view is exactly substitution after forcing the
original view. -/
theorem extendSourceView_force_exact
    {Owner : Type uOwner} {Revision : Type uRevision}
    (view : SourceView Owner Revision) (substitution : OpenSubstitution) :
    (extendSourceView view substitution).force =
      substituteOpen substitution view.force := by
  symm
  exact substituteOpen_instantiateOpen view.generation view.environment
    substitution view.source

/-! ## Ownership-closed publication -/

namespace DestinationMaterialization

variable {Owner : Type uOwner} {Revision : Type uRevision}
  {Occurrence : Type uOccurrence} {Plan : Type uPlan}
  {Physical : Type uPhysical} {Update : Type uUpdate}
  {store : BindingStore OpenEnvironment Physical Update}
  {projection : PlanProjection Revision Occurrence Plan}

/-- An unforced term view is a normalization boundary, not a resident public
subgraph.  Publication must observe its environment before the resulting
value can become destination-owned. -/
def boundarySource
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) :
    Source Owner (SourceView Owner Revision) :=
  .boundary view.toSourceView

@[simp] theorem boundarySource_denote
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) :
    (boundarySource view).denote SourceView.force = view.force :=
  rfl

/-- Publish a term view into a destination through the generic
ownership-closed GSLT materialization realization. -/
def publish [DecidableEq Owner]
    (destination : Owner)
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) : Artifact Owner :=
  materialize destination SourceView.force (boundarySource view)

/-- Publication preserves the complete term observation of the view. -/
theorem publish_exact [DecidableEq Owner]
    (destination : Owner)
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) :
    (publish destination view).denote = view.force := by
  simpa [publish, boundarySource_denote] using
    materialize_exact destination SourceView.force (boundarySource view)

/-- Publication of a view is rooted entirely at the requested destination. -/
theorem publish_rooted [DecidableEq Owner]
    (destination : Owner)
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) :
    (publish destination view).RootedAt destination :=
  materialize_rooted destination SourceView.force (boundarySource view)

/-- A term view remains a forcing boundary even when its source owner equals
the publication destination: source plus environment is not yet a normalized
public value. -/
theorem publish_boundary_is_copied [DecidableEq Owner]
    (destination : Owner)
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) :
    publish destination view = .copied destination view.force :=
  rfl

/-- The allocation-trace form of term-view publication records that the
published value is the only destination allocation retained by this semantic
construction.  A runtime implementation must refine its concrete allocation
trace to this model before claiming the same property. -/
def publicationTrace [DecidableEq Owner]
    (destination : Owner)
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) : PublicationTrace Owner :=
  outputOnlyTrace destination SourceView.force (boundarySource view)

@[simp] theorem publicationTrace_published [DecidableEq Owner]
    (destination : Owner)
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) :
    (publicationTrace destination view).published =
      publish destination view :=
  rfl

theorem publicationTrace_exact [DecidableEq Owner]
    (destination : Owner)
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) :
    (publicationTrace destination view).denote = view.force := by
  simp [publicationTrace, boundarySource_denote]

theorem publicationTrace_rooted [DecidableEq Owner]
    (destination : Owner)
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) :
    (publicationTrace destination view).RootedAt destination :=
  outputOnlyTrace_rooted destination SourceView.force (boundarySource view)

theorem publicationTrace_outputClosed [DecidableEq Owner]
    (destination : Owner)
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) :
    (publicationTrace destination view).OutputClosed :=
  outputOnlyTrace_outputClosed destination SourceView.force
    (boundarySource view)

/-- A semantically exact and lifetime-safe term-view publication may still
retain an unreachable eager intermediate.  This is the negative boundary
which a concrete output-only refinement has to exclude. -/
def retainedIntermediatePublication [DecidableEq Owner]
    (destination : Owner)
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) : PublicationTrace Owner :=
  retainedIntermediateTrace destination SourceView.force
    (boundarySource view)

theorem retainedIntermediatePublication_exact [DecidableEq Owner]
    (destination : Owner)
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) :
    (retainedIntermediatePublication destination view).denote =
      view.force := by
  simp [retainedIntermediatePublication, boundarySource_denote]

theorem retainedIntermediatePublication_rooted [DecidableEq Owner]
    (destination : Owner)
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) :
    (retainedIntermediatePublication destination view).RootedAt
      destination :=
  retainedIntermediateTrace_rooted destination SourceView.force
    (boundarySource view)

theorem retainedIntermediatePublication_not_outputClosed [DecidableEq Owner]
    (destination : Owner)
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) :
    ¬ (retainedIntermediatePublication destination view).OutputClosed :=
  retainedIntermediateTrace_not_outputClosed destination SourceView.force
    (boundarySource view)

end DestinationMaterialization

/-! ## Context-qualified memoization

Ownership and memoization answer different questions.  Destination rooting
certifies that a retained graph remains alive.  Reusing that graph for a later
request is exact only when the reuse key serves the requested observer.  In
particular, source occurrence and compiled-plan identity do not determine the
value of an open term after the binding image changes.

The generic `MemoizationObserver.SoundKey` law supplies the semantic boundary:
equal keys must imply equal observations.  The structures below specialize
that law to term views without choosing a hash table, pointer representation,
or eviction policy.
-/

namespace ContextQualifiedMemoization

open Mettapedia.GSLT.Dynamics.MemoizationObserver
open Mettapedia.GSLT.LanguageDef.CompiledPlanActivationViewCompilation

variable {Owner : Type uOwner} {Revision : Type uRevision}
  {Occurrence : Type uOccurrence} {Plan : Type uPlan}
  {Physical : Type uPhysical} {Update : Type uUpdate}
  {store : BindingStore OpenEnvironment Physical Update}
  {projection : PlanProjection Revision Occurrence Plan}

/-- A support-relative binding-version coordinate is exact when equal
coordinates imply agreement on every slot observed by the selected source.
It may be realized by an immutable image identity, a support fingerprint, or
another collision-free runtime representation.  Requiring only `AgreesOn`
allows writes outside the source support to retain the same key. -/
structure SupportVersionKey (Version : Type uVersion) where
  key : UInt32 -> Term -> Physical -> Version
  key_exact : forall {generation source left right},
    key generation source left = key generation source right ->
      AgreesOn source (store.denote left) (store.denote right)

/-- The semantic reference key retains exactly the environment restricted to
the selected source support.  It is an extensional specification; a concrete
runtime may refine it with finite dense slots, fingerprints, or stable IDs. -/
def supportEnvironmentVersionKey :
    SupportVersionKey (store := store) OpenEnvironment where
  key := fun _ source physical =>
    restrictEnvironment (sourceSupport source) (store.denote physical)
  key_exact := by
    intro generation source left right equal slot used
    have retained : slot ∈ sourceSupport source := by
      simpa [sourceSupport] using used
    have pointwise := congrFun equal slot
    simpa [restrictEnvironment, retained] using pointwise

/-- Equality of semantic support keys is exactly agreement on the selected
source support.  Thus the reference key neither distinguishes irrelevant
bindings nor conflates a binding that the source can observe. -/
theorem supportEnvironmentVersionKey_eq_iff_agreesOn
    (generation : UInt32) (source : Term) (left right : Physical) :
    (supportEnvironmentVersionKey (store := store)).key
        generation source left =
        (supportEnvironmentVersionKey (store := store)).key
          generation source right ↔
      AgreesOn source (store.denote left) (store.denote right) := by
  constructor
  · exact (supportEnvironmentVersionKey (store := store)).key_exact
  · intro agrees
    funext slot
    by_cases retained : slot ∈ sourceSupport source
    · have used : slot ∈ usedSlots source := by
        simpa [sourceSupport] using retained
      simpa [supportEnvironmentVersionKey, restrictEnvironment, retained] using
        agrees slot used
    · simp [supportEnvironmentVersionKey, restrictEnvironment, retained]

/-- Source-lifetime and plan coordinates without a binding version.  This is
useful for stating the tempting but insufficient reuse key explicitly. -/
structure SourceIdentityKey
    (Owner : Type uOwner) (Revision : Type uRevision)
    (Occurrence : Type uOccurrence) (Plan : Type uPlan) where
  owner : Owner
  revision : Revision
  occurrence : Occurrence
  generation : UInt32
  plan : Plan
deriving DecidableEq, Repr

/-- Forget the binding image while retaining the source and plan identity. -/
def sourceIdentityKey
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) :
    SourceIdentityKey Owner Revision Occurrence Plan where
  owner := view.owner
  revision := view.revision
  occurrence := view.occurrence
  generation := view.generation
  plan := view.plan

/-- A complete contextual reuse key.  Source syntax is recovered from the
plan witness, while the binding-version law recovers the logical environment.
Owner and revision guard the physical lifetime; occurrence and plan preserve
provenance-bearing observations. -/
structure ContextKey
    (Owner : Type uOwner) (Revision : Type uRevision)
    (Occurrence : Type uOccurrence) (Plan : Type uPlan)
    (Version : Type uVersion) where
  owner : Owner
  revision : Revision
  occurrence : Occurrence
  generation : UInt32
  bindingVersion : Version
  plan : Plan
deriving DecidableEq, Repr

/-- Extract the complete contextual key from a term view. -/
def contextKey {Version : Type uVersion}
    (version : SupportVersionKey (store := store) Version)
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) :
    ContextKey Owner Revision Occurrence Plan Version where
  owner := view.owner
  revision := view.revision
  occurrence := view.occurrence
  generation := view.generation
  bindingVersion :=
    version.key view.generation view.source view.bindings
  plan := view.plan

/-- Equality of complete contextual keys forces equality of complete term
values.  The proof uses plan evidence for source equality and the binding
version law for environment equality; it does not identify physical images. -/
theorem contextKey_eq_force_eq {Version : Type uVersion}
    (version : SupportVersionKey (store := store) Version)
    {left right :
      TermView Owner Revision Occurrence Plan Physical Update store projection}
    (equal : contextKey version left = contextKey version right) :
    left.force = right.force := by
  have generationEq : left.generation = right.generation := by
    simpa [contextKey] using
      congrArg
        (fun key : ContextKey Owner Revision Occurrence Plan Version =>
          key.generation) equal
  have bindingVersionEq :
      version.key left.generation left.source left.bindings =
        version.key right.generation right.source right.bindings := by
    simpa [contextKey] using
      congrArg
        (fun key : ContextKey Owner Revision Occurrence Plan Version =>
          key.bindingVersion) equal
  have planEq : left.plan = right.plan := by
    simpa [contextKey] using
      congrArg
        (fun key : ContextKey Owner Revision Occurrence Plan Version =>
          key.plan) equal
  have sourceEq : left.source = right.source := by
    calc
      left.source = projection.source left.plan := left.plan_source.symm
      _ = projection.source right.plan := congrArg projection.source planEq
      _ = right.source := right.plan_source
  have supportVersionEq :
      version.key left.generation left.source left.bindings =
        version.key left.generation left.source right.bindings := by
    simpa [generationEq, sourceEq] using bindingVersionEq
  have agrees :
      AgreesOn left.source (store.denote left.bindings)
        (store.denote right.bindings) :=
    version.key_exact supportVersionEq
  exact SourceView.force_eq_of_agreesOn left.toSourceView right.toSourceView
    generationEq sourceEq agrees

/-- The complete contextual key is sound for complete term forcing. -/
theorem contextKey_sound_for_force {Version : Type uVersion}
    (version : SupportVersionKey (store := store) Version) :
    SoundKey (contextKey version)
      (fun view : TermView Owner Revision Occurrence Plan Physical Update
        store projection => view.force) :=
  fun _ _ equal => contextKey_eq_force_eq version equal

/-- The same key is sound for the provenance-bearing public observation. -/
theorem contextKey_sound_for_observation {Version : Type uVersion}
    (version : SupportVersionKey (store := store) Version) :
    SoundKey (contextKey version)
      (fun view : TermView Owner Revision Occurrence Plan Physical Update
        store projection => observeSource view) := by
  intro left right equal
  apply CompleteObservation.ext
  · simpa [observeSource, contextKey] using
      congrArg
        (fun key : ContextKey Owner Revision Occurrence Plan Version =>
          key.occurrence) equal
  · simpa [observeSource, contextKey] using
      congrArg
        (fun key : ContextKey Owner Revision Occurrence Plan Version =>
          key.plan) equal
  · exact contextKey_eq_force_eq version equal

/-- A coherent contextual memo returns exactly the ordinary forced value. -/
theorem lookupOrCompute_force_exact {Version : Type uVersion}
    (version : SupportVersionKey (store := store) Version)
    (table : Table (ContextKey Owner Revision Occurrence Plan Version) OpenTerm)
    (coherent : Coherent (contextKey version)
      (fun view : TermView Owner Revision Occurrence Plan Physical Update
        store projection => view.force) table)
    (view : TermView Owner Revision Occurrence Plan Physical Update
      store projection) :
    lookupOrCompute (contextKey version) (fun termView => termView.force)
        table view = view.force :=
  lookupOrCompute_eq_obs coherent view

/-- Adding runtime-only coordinates refines rather than weakens the complete
key.  Such a key may lose reuse opportunities, but remains sound for forcing. -/
theorem refinedKey_sound_for_force {Version : Type uVersion}
    {RuntimeKey : Type uRuntimeKey}
    (version : SupportVersionKey (store := store) Version)
    (runtimeKey :
      TermView Owner Revision Occurrence Plan Physical Update store projection ->
        RuntimeKey)
    (project : RuntimeKey ->
      ContextKey Owner Revision Occurrence Plan Version)
    (factor : forall view, contextKey version view = project (runtimeKey view)) :
    SoundKey runtimeKey
      (fun view : TermView Owner Revision Occurrence Plan Physical Update
        store projection => view.force) :=
  soundKey_of_refines (contextKey_sound_for_force version)
    runtimeKey project factor

/-- The same refinement principle preserves provenance-bearing observation. -/
theorem refinedKey_sound_for_observation {Version : Type uVersion}
    {RuntimeKey : Type uRuntimeKey}
    (version : SupportVersionKey (store := store) Version)
    (runtimeKey :
      TermView Owner Revision Occurrence Plan Physical Update store projection ->
        RuntimeKey)
    (project : RuntimeKey ->
      ContextKey Owner Revision Occurrence Plan Version)
    (factor : forall view, contextKey version view = project (runtimeKey view)) :
    SoundKey runtimeKey
      (fun view : TermView Owner Revision Occurrence Plan Physical Update
        store projection => observeSource view) :=
  soundKey_of_refines (contextKey_sound_for_observation version)
    runtimeKey project factor

/-- If two differently forced views share a source-identity key, that key is
not sound for forcing. -/
theorem sourceIdentityKey_unsound_of_force_ne
    {left right :
      TermView Owner Revision Occurrence Plan Physical Update store projection}
    (same : sourceIdentityKey left = sourceIdentityKey right)
    (different : left.force ≠ right.force) :
    ¬ SoundKey sourceIdentityKey
      (fun view : TermView Owner Revision Occurrence Plan Physical Update
        store projection => view.force) := by
  intro sound
  exact different (sound left right same)

end ContextQualifiedMemoization

/-! ## Effect-delimited Region/Hole execution -/

namespace EffectDelimited

/-- Stable coordinates retained by both delayed and materialized executions.
The equalities prevent a source view from being paired with a plan for another
occurrence or program revision. -/
structure Coordinates
    (Owner : Type uOwner) (Revision : Type uRevision)
    (Occurrence : Type uOccurrence) (CompiledPlan : Type uPlan)
    (projection : PlanProjection Revision Occurrence CompiledPlan) where
  occurrence : Occurrence
  owner : Owner
  revision : Revision
  source : Term
  plan : CompiledPlan
  plan_source : projection.source plan = source
  plan_revision : projection.revision plan = revision
  plan_occurrence : projection.occurrence plan = occurrence

/-- A delayed execution state retains the authored source and its composed
environment.  Its trace contains observations made at explicit Holes only. -/
structure DelayedState
    (Owner : Type uOwner) (Revision : Type uRevision)
    (Occurrence : Type uOccurrence) (CompiledPlan : Type uPlan)
    (projection : PlanProjection Revision Occurrence CompiledPlan) where
  coordinates : Coordinates Owner Revision Occurrence CompiledPlan projection
  generation : UInt32
  environment : OpenEnvironment
  trace : List (Nat × OpenTerm)

/-- The eager reference carries the same source coordinates and the currently
materialized term. -/
structure EagerState
    (Owner : Type uOwner) (Revision : Type uRevision)
    (Occurrence : Type uOccurrence) (CompiledPlan : Type uPlan)
    (projection : PlanProjection Revision Occurrence CompiledPlan) where
  coordinates : Coordinates Owner Revision Occurrence CompiledPlan projection
  generation : UInt32
  value : OpenTerm
  trace : List (Nat × OpenTerm)

namespace DelayedState

variable {Owner : Type uOwner} {Revision : Type uRevision}
  {Occurrence : Type uOccurrence} {CompiledPlan : Type uPlan}
  {projection : PlanProjection Revision Occurrence CompiledPlan}

def toSourceView
    (state : DelayedState Owner Revision Occurrence CompiledPlan projection) :
    SourceView Owner Revision where
  owner := state.coordinates.owner
  revision := state.coordinates.revision
  generation := state.generation
  environment := state.environment
  source := state.coordinates.source

end DelayedState

variable {Owner : Type uOwner} {Revision : Type uRevision}
  {Occurrence : Type uOccurrence} {CompiledPlan : Type uPlan}
  {Physical : Type uPhysical} {Update : Type uUpdate}
  {store : BindingStore OpenEnvironment Physical Update}
  {projection : PlanProjection Revision Occurrence CompiledPlan}

/-- Enter effect-delimited execution without dropping source occurrence,
revision, or compiled-plan evidence. -/
def fromTermView
    (view : TermView Owner Revision Occurrence CompiledPlan Physical Update
      store projection) :
    DelayedState Owner Revision Occurrence CompiledPlan projection where
  coordinates :=
    { occurrence := view.occurrence
      owner := view.owner
      revision := view.revision
      source := view.source
      plan := view.plan
      plan_source := view.plan_source
      plan_revision := view.plan_revision
      plan_occurrence := view.plan_occurrence }
  generation := view.generation
  environment := store.denote view.bindings
  trace := []

/-- Materialization is an observation map, not an execution policy. -/
def forceState
    (state : DelayedState Owner Revision Occurrence CompiledPlan projection) :
    EagerState Owner Revision Occurrence CompiledPlan projection where
  coordinates := state.coordinates
  generation := state.generation
  value := state.toSourceView.force
  trace := state.trace

@[simp] theorem force_fromTermView
    (view : TermView Owner Revision Occurrence CompiledPlan Physical Update
      store projection) :
    (forceState (fromTermView view)).value = view.force := rfl

/-- Open substitutions form the deterministic Region category: identity is
the empty substitution and composition never builds the intermediate term. -/
def substitutionCategory :
    IndexedCategory Unit (fun _ _ : Unit => OpenSubstitution) where
  identity _ := emptyOpenSubstitution
  compose := composeOpen
  identity_compose := empty_composeOpen
  compose_identity := composeOpen_empty
  compose_assoc := composeOpen_assoc

def delayedRegion
    (substitution : OpenSubstitution) :
    Segment
      (DelayedState Owner Revision Occurrence CompiledPlan projection)
      (DelayedState Owner Revision Occurrence CompiledPlan projection) :=
  deterministic fun state =>
    { state with environment :=
        (composeEnvironment state.generation state.environment substitution) }

def eagerRegion
    (substitution : OpenSubstitution) :
    Segment
      (EagerState Owner Revision Occurrence CompiledPlan projection)
      (EagerState Owner Revision Occurrence CompiledPlan projection) :=
  deterministic fun state =>
    { state with value := substituteOpen substitution state.value }

/-- A Hole observes the complete current term and records its authored label.
The delayed realization forces only for that observation and retains its source
view for later Regions. -/
def delayedHole
    (label : Nat) :
    Segment
      (DelayedState Owner Revision Occurrence CompiledPlan projection)
      (DelayedState Owner Revision Occurrence CompiledPlan projection) :=
  fun state =>
    [{ state with trace :=
        state.trace ++ [(label, state.toSourceView.force)] }]

def eagerHole
    (label : Nat) :
    Segment
      (EagerState Owner Revision Occurrence CompiledPlan projection)
      (EagerState Owner Revision Occurrence CompiledPlan projection) :=
  fun state => [{ state with trace := state.trace ++ [(label, state.value)] }]

def delayedRealization :
    Realization substitutionCategory (fun _ _ : Unit => Nat)
      occurrenceKleisliCategory where
  objectMap _ := DelayedState Owner Revision Occurrence CompiledPlan projection
  mapRegion := delayedRegion
  mapHole := delayedHole
  map_identity _ := by
    funext state
    cases state
    simp [delayedRegion, substitutionCategory, occurrenceKleisliCategory,
      deterministic]
  map_compose first second := by
    funext state
    cases state
    simp [delayedRegion, substitutionCategory, occurrenceKleisliCategory,
      deterministic, thenSegment,
      Mettapedia.GSLT.Dynamics.OrderedOccurrenceBodyAlgebra.run,
      composeEnvironment_assoc]

def eagerRealization :
    Realization substitutionCategory (fun _ _ : Unit => Nat)
      occurrenceKleisliCategory where
  objectMap _ := EagerState Owner Revision Occurrence CompiledPlan projection
  mapRegion := eagerRegion
  mapHole := eagerHole
  map_identity _ := by
    funext state
    cases state
    simp [eagerRegion, substitutionCategory, occurrenceKleisliCategory,
      deterministic, substituteOpen_empty]
  map_compose first second := by
    funext state
    cases state
    simp [eagerRegion, substitutionCategory, occurrenceKleisliCategory,
      deterministic, thenSegment,
      Mettapedia.GSLT.Dynamics.OrderedOccurrenceBodyAlgebra.run,
      substituteOpen_comp]

def forceSegment :
    Segment
      (DelayedState Owner Revision Occurrence CompiledPlan projection)
      (EagerState Owner Revision Occurrence CompiledPlan projection) :=
  deterministic forceState

/-- Forcing commutes separately with every substitution Region and every
effect-observing Hole.  The Hole square is the exact boundary used by an
effect-delimited runtime realization. -/
def delayedToEager :
    RealizationTransformation
      (delayedRealization (Owner := Owner) (Revision := Revision)
        (Occurrence := Occurrence) (CompiledPlan := CompiledPlan)
        (projection := projection))
      (eagerRealization (Owner := Owner) (Revision := Revision)
        (Occurrence := Occurrence) (CompiledPlan := CompiledPlan)
        (projection := projection)) where
  component _ := forceSegment
  region_naturality substitution := by
    funext state
    cases state with
    | mk coordinates generation environment trace =>
        simp [delayedRealization, eagerRealization, forceSegment, forceState,
          delayedRegion, eagerRegion, DelayedState.toSourceView,
          occurrenceKleisliCategory, deterministic, thenSegment,
          Mettapedia.GSLT.Dynamics.OrderedOccurrenceBodyAlgebra.run]
        symm
        exact substituteOpen_instantiateOpen generation environment
          substitution coordinates.source
  hole_naturality label := by
    funext state
    cases state
    simp [delayedRealization, eagerRealization, forceSegment, forceState,
      delayedHole, eagerHole, DelayedState.toSourceView,
      occurrenceKleisliCategory, deterministic, thenSegment,
      Mettapedia.GSLT.Dynamics.OrderedOccurrenceBodyAlgebra.run]

abbrev ExecutionPlan :=
  Plan Unit (fun _ _ : Unit => OpenSubstitution)
    (fun _ _ : Unit => Nat) () ()

/-- Generator-level commutation extends to every authored sequence of pure
Regions and explicit effect/observation Holes. -/
theorem force_plan_exact (plan : ExecutionPlan) :
    occurrenceKleisliCategory.compose
        (Plan.denote
          (delayedRealization (Owner := Owner) (Revision := Revision)
            (Occurrence := Occurrence) (CompiledPlan := CompiledPlan)
            (projection := projection)) plan)
        (forceSegment (Owner := Owner) (Revision := Revision)
          (Occurrence := Occurrence) (CompiledPlan := CompiledPlan)
          (projection := projection)) =
      occurrenceKleisliCategory.compose
        (forceSegment (Owner := Owner) (Revision := Revision)
          (Occurrence := Occurrence) (CompiledPlan := CompiledPlan)
          (projection := projection))
        (Plan.denote
          (eagerRealization (Owner := Owner) (Revision := Revision)
            (Occurrence := Occurrence) (CompiledPlan := CompiledPlan)
            (projection := projection)) plan) :=
  RealizationTransformation.plan_naturality
    (delayedToEager (Owner := Owner) (Revision := Revision)
      (Occurrence := Occurrence) (CompiledPlan := CompiledPlan)
      (projection := projection)) plan

/-- Region fusion preserves both the term-view denotation and every Hole's
label, multiplicity, and authored order. -/
theorem normalize_force_and_holes_exact (plan : ExecutionPlan) :
    occurrenceKleisliCategory.compose
        (NormalForm.denote
          (delayedRealization (Owner := Owner) (Revision := Revision)
            (Occurrence := Occurrence) (CompiledPlan := CompiledPlan)
            (projection := projection))
          (normalize substitutionCategory plan))
        (forceSegment (Owner := Owner) (Revision := Revision)
          (Occurrence := Occurrence) (CompiledPlan := CompiledPlan)
          (projection := projection)) =
      occurrenceKleisliCategory.compose
        (forceSegment (Owner := Owner) (Revision := Revision)
          (Occurrence := Occurrence) (CompiledPlan := CompiledPlan)
          (projection := projection))
        (NormalForm.denote
          (eagerRealization (Owner := Owner) (Revision := Revision)
            (Occurrence := Occurrence) (CompiledPlan := CompiledPlan)
            (projection := projection))
          (normalize substitutionCategory plan)) ∧
      (normalize substitutionCategory plan).holeTrace =
        plan.holeTrace := by
  constructor
  · exact RealizationTransformation.normalize_naturality
      (delayedToEager (Owner := Owner) (Revision := Revision)
        (Occurrence := Occurrence) (CompiledPlan := CompiledPlan)
        (projection := projection)) plan
  · exact normalize_holeTrace substitutionCategory plan

end EffectDelimited

/-! ## Strategy-neutral pure search over term-view answers -/

/-- An emitted answer retains the occurrence and cursor path which produced an
ordinary open value. -/
@[ext] structure OccurrenceAnswer (Occurrence : Type uOccurrence) where
  occurrence : Occurrence
  path : List Nat
  value : OpenTerm
deriving DecidableEq, Repr

def Cursor.answer
    {Owner : Type uOwner} {Revision : Type uRevision}
    {Occurrence : Type uOccurrence} {Plan : Type uPlan}
    (cursor : Cursor Owner Revision Occurrence Plan) :
    OccurrenceAnswer Occurrence :=
  { occurrence := cursor.occurrence, path := cursor.path,
    value := cursor.denote }

/-- A pure term-view kernel is a strategy-independent branching kernel plus
the two certificates needed for scheduler freedom: a complete additive answer
denotation and preservation of the shared-world handle by every successor. -/
structure PureKernel
    (Owner : Type uOwner) (Revision : Type uRevision)
    (Occurrence : Type uOccurrence) (Plan : Type uPlan)
    (BranchBinding : Type uBranch) (WorldHandle : Type uWorld) where
  kernel : SearchStateStack.Kernel
    (Cursor Owner Revision Occurrence Plan) BranchBinding WorldHandle
    (OccurrenceAnswer Occurrence)
  denotation : AdditiveDenotation kernel.toBranchingSystem
  successors_preserve_world :
    forall continuation successor,
      successor ∈ kernel.successors continuation ->
        successor.world = continuation.world

namespace PureKernel

variable {Owner : Type uOwner} {Revision : Type uRevision}
  {Occurrence : Type uOccurrence} {Plan : Type uPlan}
  {BranchBinding : Type uBranch} {WorldHandle : Type uWorld}

/-- Any two completed occurrence-preserving strategies agree on the complete
bag of provenance-bearing answers. -/
theorem completed_strategies_occurrence_bag_agree
    (pure : PureKernel Owner Revision Occurrence Plan
      BranchBinding WorldHandle)
    {FirstMemory SecondMemory : Type*}
    (first : pure.kernel.Strategy FirstMemory)
    (second : pure.kernel.Strategy SecondMemory)
    (roots : List (Continuation
      (Cursor Owner Revision Occurrence Plan) BranchBinding WorldHandle))
    (firstFuel secondFuel : Nat)
    (firstComplete :
      (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
        pure.kernel.toBranchingSystem first firstFuel
        (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial first roots)).search.frontier = [])
    (secondComplete :
      (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
        pure.kernel.toBranchingSystem second secondFuel
        (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial second roots)).search.frontier = []) :
    eventBag
        (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
          pure.kernel.toBranchingSystem first firstFuel
          (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial first roots)).search.events =
      eventBag
        (Mettapedia.GSLT.Core.InferenceControl.Snapshot.run
          pure.kernel.toBranchingSystem second secondFuel
          (Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial second roots)).search.events :=
  pure.kernel.completed_strategies_bag_agree first second pure.denotation roots
    firstFuel secondFuel firstComplete secondComplete

/-- The same certificate separately exposes that scheduler freedom does not
authorize a world transition. -/
theorem successor_world_exact
    (pure : PureKernel Owner Revision Occurrence Plan
      BranchBinding WorldHandle)
    (continuation successor : Continuation
      (Cursor Owner Revision Occurrence Plan) BranchBinding WorldHandle)
    (generated : successor ∈ pure.kernel.successors continuation) :
    successor.world = continuation.world :=
  pure.successors_preserve_world continuation successor generated

end PureKernel

/-! ## Effect and commitment boundaries -/

/-- Exact binding-view equivalence cannot justify reordering two competing
writes to shared world state. -/
theorem competing_world_writes_remain_observable :
    ¬ SerializableCounterAt id 0
      [CounterAction.set 1, CounterAction.set 2] :=
  competing_sets_are_not_serializable

/-- Exact binding-view equivalence also cannot erase scoped commitment: two
lawful schedulers may commit different witnesses. -/
theorem competing_commits_remain_observable :
    (ScopedSnapshot.run SearchStateStack.Canaries.commitKernel
        Scheduler.breadthFirst 2
        (ScopedSnapshot.initial [SearchStateStack.Canaries.CommitNode.root])).events.map
        Emission.value ≠
      (ScopedSnapshot.run SearchStateStack.Canaries.commitKernel
        Scheduler.reverseBreadthFirst 2
        (ScopedSnapshot.initial [SearchStateStack.Canaries.CommitNode.root])).events.map
        Emission.value :=
  SearchStateStack.Canaries.competing_commits_are_strategy_observable

/-! ## Honest structural cost refinement -/

mutual

/-- Number of source constructors inspected by a complete structural demand. -/
def sourceNodeCount : Term -> Nat
  | .symbol _ => 1
  | .variable _ => 1
  | .string _ => 1
  | .integer _ => 1
  | .application _ children => 1 + sourceNodesCount children

def sourceNodesCount : Terms -> Nat
  | .nil => 0
  | .cons head tail => sourceNodeCount head + sourceNodesCount tail

end

/-- A semantic accounting grade for term observation.  `layers` counts source
constructors inspected; `wholeTerms` counts requests that explicitly demand a
complete materialized result. -/
@[ext] structure ObservationGrade where
  layers : Nat
  wholeTerms : Nat
deriving DecidableEq, Repr

/-- One root observation inspects one layer and requests no complete term. -/
def rootObservationGrade : ObservationGrade :=
  { layers := 1, wholeTerms := 0 }

/-- A complete demand visits every source node and requests one complete term. -/
def completeObservationGrade (source : Term) : ObservationGrade :=
  { layers := sourceNodeCount source, wholeTerms := 1 }

theorem sourceNodeCount_positive (source : Term) :
    0 < sourceNodeCount source := by
  cases source <;> simp [sourceNodeCount]

/-- Root observation never requires more constructor inspections than complete
forcing in the structural grade. -/
theorem root_layers_le_complete (source : Term) :
    rootObservationGrade.layers <= (completeObservationGrade source).layers := by
  change 1 <= sourceNodeCount source
  exact Nat.succ_le_iff.mpr (sourceNodeCount_positive source)

/-- For every nonempty application, observing only the root strictly avoids at
least one constructor inspection. -/
theorem root_layers_lt_complete_application
    (head : List UInt8) (first : Term) (rest : Terms) :
    rootObservationGrade.layers <
      (completeObservationGrade
        (.application head (.cons first rest))).layers := by
  have positive := sourceNodeCount_positive first
  change 1 < 1 + (sourceNodeCount first + sourceNodesCount rest)
  omega

/-- Root observation and complete forcing are distinct cost observations even
for a leaf, because only the latter requests a materialized whole term. -/
theorem root_does_not_request_whole_term (source : Term) :
    rootObservationGrade.wholeTerms = 0 ∧
      (completeObservationGrade source).wholeTerms = 1 := by
  constructor <;> rfl

/-! ### Whole-execution work admission

The structural observation grade above proves how much term structure an
observer demands.  It does not by itself predict whether retaining a delayed
term view is cheaper for a complete execution.  A delayed state may remain
live across several scheduler boundaries and may resume at several Holes.

The account below therefore keeps four measured quantities separate:

* construction performed by the eager reference;
* construction still performed by the delayed realization;
* the retained continuation footprint at each scheduler boundary;
* the exact number of Hole resumptions.

Unit prices are supplied by a concrete runtime qualification.  They prevent
node counts, retained slot-steps, and resumption counts from being added as if
they had the same physical cost.  This is a cost model over measured inputs,
not a theorem identifying the model with elapsed time.
-/

/-- Resource trace for one complete eager/delayed comparison.  The ordered
footprint list admits depth-first, breadth-first, parallel, and mixed
schedulers without selecting one as the language semantics. -/
@[ext] structure DelayedResourceTrace where
  eagerConstructedNodes : Nat
  delayedConstructedNodes : Nat
  liveContinuationFootprints : List Nat
  holeResumptions : Nat
deriving DecidableEq, Repr

/-- Runtime-qualified prices which map heterogeneous structural counters into
one predicted-work coordinate. -/
@[ext] structure DelayedUnitPrices where
  constructedNode : Nat
  retainedSlotStep : Nat
  holeResumption : Nat
deriving DecidableEq, Repr

namespace DelayedResourceTrace

/-- Space-time exposure of delayed continuations over the observed schedule. -/
def continuationExposure (trace : DelayedResourceTrace) : Nat :=
  trace.liveContinuationFootprints.sum

/-- Largest retained continuation footprint seen at a scheduler boundary.
This coordinate remains separate from predicted work so an RSS qualification
need not pretend that peak space is additive. -/
def peakContinuationFootprint (trace : DelayedResourceTrace) : Nat :=
  trace.liveContinuationFootprints.foldl max 0

def eagerConstructionWork (trace : DelayedResourceTrace)
    (prices : DelayedUnitPrices) : Nat :=
  prices.constructedNode * trace.eagerConstructedNodes

def delayedConstructionWork (trace : DelayedResourceTrace)
    (prices : DelayedUnitPrices) : Nat :=
  prices.constructedNode * trace.delayedConstructedNodes

def continuationWork (trace : DelayedResourceTrace)
    (prices : DelayedUnitPrices) : Nat :=
  prices.retainedSlotStep * trace.continuationExposure

def resumptionWork (trace : DelayedResourceTrace)
    (prices : DelayedUnitPrices) : Nat :=
  prices.holeResumption * trace.holeResumptions

/-- The extra work paid for delayed lifetime and control transfer. -/
def delayedOverhead (trace : DelayedResourceTrace)
    (prices : DelayedUnitPrices) : Nat :=
  trace.continuationWork prices + trace.resumptionWork prices

/-- Predicted work of the eager reference on the measured trace. -/
def eagerWork (trace : DelayedResourceTrace)
    (prices : DelayedUnitPrices) : Nat :=
  trace.eagerConstructionWork prices

/-- Predicted work of delayed execution, including both residual construction
and the costs introduced by retaining and resuming continuations. -/
def delayedWork (trace : DelayedResourceTrace)
    (prices : DelayedUnitPrices) : Nat :=
  trace.delayedConstructionWork prices + trace.delayedOverhead prices

/-- Cost-side admission.  Semantic exactness and effect authorization are
independent premises supplied by the term-view and Region/Hole theorems. -/
def WorkImproving (trace : DelayedResourceTrace)
    (prices : DelayedUnitPrices) : Prop :=
  trace.delayedWork prices < trace.eagerWork prices

/-- Build an account whose resumption count is obtained from the exact Hole
occurrences of a typed Region/Hole plan. -/
def forPlan
    {Obj : Type*} {Region Hole : Obj → Obj → Type*} {X Y : Obj}
    (plan : Mettapedia.GSLT.Dynamics.RegionHolePlan.Plan
      Obj Region Hole X Y)
    (eagerConstructedNodes delayedConstructedNodes : Nat)
    (liveContinuationFootprints : List Nat) : DelayedResourceTrace where
  eagerConstructedNodes := eagerConstructedNodes
  delayedConstructedNodes := delayedConstructedNodes
  liveContinuationFootprints := liveContinuationFootprints
  holeResumptions := plan.holeCount

@[simp] theorem forPlan_holeResumptions
    {Obj : Type*} {Region Hole : Obj → Obj → Type*} {X Y : Obj}
    (plan : Mettapedia.GSLT.Dynamics.RegionHolePlan.Plan
      Obj Region Hole X Y)
    (eagerConstructedNodes delayedConstructedNodes : Nat)
    (liveContinuationFootprints : List Nat) :
    (forPlan plan eagerConstructedNodes delayedConstructedNodes
      liveContinuationFootprints).holeResumptions = plan.holeCount :=
  rfl

@[simp] theorem continuationExposure_append
    (trace : DelayedResourceTrace) (later : List Nat) :
    ({ trace with liveContinuationFootprints :=
        trace.liveContinuationFootprints ++ later }).continuationExposure =
      trace.continuationExposure + later.sum := by
  simp [continuationExposure]

@[simp] theorem constantContinuationExposure
    (trace : DelayedResourceTrace) (footprint liveSteps : Nat) :
    ({ trace with liveContinuationFootprints :=
        List.replicate liveSteps footprint }).continuationExposure =
      liveSteps * footprint := by
  simp [continuationExposure]

/-- Exact admission threshold: priced continuation and resumption overhead
must be strictly smaller than priced construction work actually avoided. -/
theorem workImproving_iff_overhead_lt_saved
    (trace : DelayedResourceTrace) (prices : DelayedUnitPrices) :
    trace.WorkImproving prices ↔
      trace.delayedOverhead prices <
        trace.eagerWork prices - trace.delayedConstructionWork prices := by
  rw [Nat.lt_sub_iff_add_lt]
  simp only [WorkImproving, delayedWork]
  rw [Nat.add_comm]

/-- A larger delayed construction count, continuation exposure, or resumption
count cannot reduce predicted delayed work at fixed unit prices. -/
theorem delayedWork_mono
    {first second : DelayedResourceTrace} (prices : DelayedUnitPrices)
    (construction : first.delayedConstructedNodes ≤
      second.delayedConstructedNodes)
    (exposure : first.continuationExposure ≤ second.continuationExposure)
    (resumptions : first.holeResumptions ≤ second.holeResumptions) :
    first.delayedWork prices ≤ second.delayedWork prices := by
  unfold delayedWork delayedConstructionWork delayedOverhead
    continuationWork resumptionWork
  exact Nat.add_le_add
    (Nat.mul_le_mul_left prices.constructedNode construction)
    (Nat.add_le_add
      (Nat.mul_le_mul_left prices.retainedSlotStep exposure)
      (Nat.mul_le_mul_left prices.holeResumption resumptions))

/-- If continuation exposure alone costs at least the entire eager reference,
delayed execution cannot be admitted, irrespective of construction savings. -/
theorem not_workImproving_of_continuation_dominates
    (trace : DelayedResourceTrace) (prices : DelayedUnitPrices)
    (dominates : trace.eagerWork prices ≤ trace.continuationWork prices) :
    ¬ trace.WorkImproving prices := by
  intro improving
  have continuationLe : trace.continuationWork prices ≤
      trace.delayedWork prices := by
    unfold delayedWork delayedOverhead
    omega
  exact (not_lt_of_ge (dominates.trans continuationLe)) improving

end DelayedResourceTrace

/-! ## Positive and negative controls -/

namespace Canaries

def unitDelayedPrices : DelayedUnitPrices where
  constructedNode := 1
  retainedSlotStep := 1
  holeResumption := 1

/-- A small delayed region can construct far fewer nodes yet lose overall
when its continuation remains large and live across two scheduler boundaries. -/
def singletonDelayedTrace : DelayedResourceTrace where
  eagerConstructedNodes := 100
  delayedConstructedNodes := 10
  liveContinuationFootprints := [60, 60]
  holeResumptions := 1

/-- Negative control: construction counters alone are not a work-admission
certificate. -/
theorem construction_reduction_is_not_sufficient :
    singletonDelayedTrace.delayedConstructedNodes <
        singletonDelayedTrace.eagerConstructedNodes ∧
      ¬ singletonDelayedTrace.WorkImproving unitDelayedPrices := by
  norm_num [singletonDelayedTrace, unitDelayedPrices,
    DelayedResourceTrace.WorkImproving, DelayedResourceTrace.delayedWork,
    DelayedResourceTrace.eagerWork,
    DelayedResourceTrace.eagerConstructionWork,
    DelayedResourceTrace.delayedConstructionWork,
    DelayedResourceTrace.delayedOverhead,
    DelayedResourceTrace.continuationWork,
    DelayedResourceTrace.resumptionWork,
    DelayedResourceTrace.continuationExposure]

/-- Reuse across a larger binding region can amortize the same retained
continuation exposure over construction work avoided repeatedly. -/
def batchedDelayedTrace : DelayedResourceTrace where
  eagerConstructedNodes := 400
  delayedConstructedNodes := 40
  liveContinuationFootprints := [60, 60]
  holeResumptions := 4

/-- Positive control: the whole-execution threshold admits the batched region
for the same qualified unit prices. -/
theorem batched_region_is_work_improving :
    batchedDelayedTrace.WorkImproving unitDelayedPrices := by
  norm_num [batchedDelayedTrace, unitDelayedPrices,
    DelayedResourceTrace.WorkImproving, DelayedResourceTrace.delayedWork,
    DelayedResourceTrace.eagerWork,
    DelayedResourceTrace.eagerConstructionWork,
    DelayedResourceTrace.delayedConstructionWork,
    DelayedResourceTrace.delayedOverhead,
    DelayedResourceTrace.continuationWork,
    DelayedResourceTrace.resumptionWork,
    DelayedResourceTrace.continuationExposure]

/-- The two controls differ in total work rather than semantic authority:
the singleton is rejected and the batched region is admitted by the same
cost algebra and unit prices. -/
theorem whole_execution_admission_separates_controls :
    ¬ singletonDelayedTrace.WorkImproving unitDelayedPrices ∧
      batchedDelayedTrace.WorkImproving unitDelayedPrices := by
  exact ⟨construction_reduction_is_not_sufficient.2,
    batched_region_is_work_improving⟩

inductive SampleOccurrence
  | left
  | right
deriving DecidableEq, Repr

inductive SamplePlan
  | first
  | duplicate
  | stale
deriving DecidableEq, Repr

def sampleProjection : PlanProjection Nat SampleOccurrence SamplePlan where
  source
    | .first => .application [1]
        (.cons (.variable 0) (.cons (.symbol [2]) .nil))
    | .duplicate => .application [1]
        (.cons (.variable 0) (.cons (.symbol [2]) .nil))
    | .stale => .symbol [9]
  revision
    | .first => 5
    | .duplicate => 5
    | .stale => 8
  occurrence
    | .first => .left
    | .duplicate => .right
    | .stale => .right

def sampleStore : BindingStore OpenEnvironment OpenEnvironment
    (UInt32 × OpenTerm) where
  denote := id
  logicalWrite environment update :=
    writeOpen environment update.1 update.2
  write environment update :=
    writeOpen environment update.1 update.2
  write_exact _ _ := rfl

def sampleEnvironment : OpenEnvironment
  | 0 => some (.symbol [7])
  | _ => none

def sampleView : TermView Unit Nat SampleOccurrence SamplePlan
    OpenEnvironment (UInt32 × OpenTerm) sampleStore sampleProjection where
  occurrence := .left
  owner := ()
  revision := 5
  generation := 11
  bindings := sampleEnvironment
  source := .application [1]
    (.cons (.variable 0) (.cons (.symbol [2]) .nil))
  plan := .first
  plan_source := rfl
  plan_revision := rfl
  plan_occurrence := rfl

def duplicateSampleView : TermView Unit Nat SampleOccurrence SamplePlan
    OpenEnvironment (UInt32 × OpenTerm) sampleStore sampleProjection where
  occurrence := .right
  owner := ()
  revision := 5
  generation := 11
  bindings := sampleEnvironment
  source := .application [1]
    (.cons (.variable 0) (.cons (.symbol [2]) .nil))
  plan := .duplicate
  plan_source := rfl
  plan_revision := rfl
  plan_occurrence := rfl

/-- The canary uses the logical environment itself as an exact version key.
Concrete runtimes may replace it with any identifier satisfying `key_exact`. -/
def sampleSupportVersionKey :
    ContextQualifiedMemoization.SupportVersionKey
      (store := sampleStore) OpenEnvironment :=
  ContextQualifiedMemoization.supportEnvironmentVersionKey

/-- A binding update outside the selected source support. -/
def irrelevantSampleView :=
  sampleView.writeBinding (99, .symbol [12])

/-- The update at slot 99 agrees with the original environment on the sole
source-observable slot, slot zero. -/
theorem irrelevant_write_agrees_on_source :
    AgreesOn sampleView.source
      (sampleStore.denote sampleView.bindings)
      (sampleStore.denote irrelevantSampleView.bindings) := by
  intro slot used
  have slotEq : slot = 0 := by
    simpa [sampleView,
      Mettapedia.GSLT.LanguageDef.CompiledPlanActivationViewCompilation.usedSlots,
      Mettapedia.GSLT.LanguageDef.CompiledPlanActivationViewCompilation.usedSlotsTerms]
      using used
  subst slot
  rfl

/-- Positive reuse control: a write outside source support leaves the complete
contextual key unchanged. -/
theorem irrelevant_write_preserves_context_key :
    ContextQualifiedMemoization.contextKey sampleSupportVersionKey sampleView =
      ContextQualifiedMemoization.contextKey sampleSupportVersionKey
        irrelevantSampleView := by
  have bindingKeyEq :=
    (ContextQualifiedMemoization.supportEnvironmentVersionKey_eq_iff_agreesOn
      (store := sampleStore) sampleView.generation sampleView.source
      sampleView.bindings irrelevantSampleView.bindings).2
        irrelevant_write_agrees_on_source
  simpa [sampleSupportVersionKey,
    ContextQualifiedMemoization.contextKey, irrelevantSampleView,
    TermView.writeBinding] using bindingKeyEq

/-- The same source occurrence and plan after one binding-version update. -/
def reboundSampleView :=
  sampleView.writeBinding (0, .symbol [8])

/-- Positive: the complete contextual key serves value forcing. -/
theorem sample_context_key_sound_for_force :
    Mettapedia.GSLT.Dynamics.MemoizationObserver.SoundKey
      (ContextQualifiedMemoization.contextKey
        (Owner := Unit) (Revision := Nat)
        (Occurrence := SampleOccurrence) (Plan := SamplePlan)
        (projection := sampleProjection) sampleSupportVersionKey)
      (fun view : TermView Unit Nat SampleOccurrence SamplePlan
        OpenEnvironment (UInt32 × OpenTerm) sampleStore sampleProjection =>
          view.force) :=
  ContextQualifiedMemoization.contextKey_sound_for_force
    sampleSupportVersionKey

/-- Positive: the complete contextual key also serves the observation which
retains occurrence and plan provenance. -/
theorem sample_context_key_sound_for_observation :
    Mettapedia.GSLT.Dynamics.MemoizationObserver.SoundKey
      (ContextQualifiedMemoization.contextKey
        (Owner := Unit) (Revision := Nat)
        (Occurrence := SampleOccurrence) (Plan := SamplePlan)
        (projection := sampleProjection) sampleSupportVersionKey)
      (fun view : TermView Unit Nat SampleOccurrence SamplePlan
        OpenEnvironment (UInt32 × OpenTerm) sampleStore sampleProjection =>
          observeSource view) :=
  ContextQualifiedMemoization.contextKey_sound_for_observation
    sampleSupportVersionKey

/-- The source-identity key is unchanged by a binding update. -/
theorem source_identity_key_ignores_binding_version :
    ContextQualifiedMemoization.sourceIdentityKey sampleView =
      ContextQualifiedMemoization.sourceIdentityKey reboundSampleView :=
  rfl

/-- The omitted binding version is semantically observable. -/
theorem rebound_changes_forced_value :
    sampleView.force ≠ reboundSampleView.force := by
  decide

/-- Negative: source occurrence, lifetime, generation, and plan together are
still an unsound memo key when the binding version is omitted. -/
theorem source_identity_key_unsound_for_force :
    ¬ Mettapedia.GSLT.Dynamics.MemoizationObserver.SoundKey
      ContextQualifiedMemoization.sourceIdentityKey
      (fun view : TermView Unit Nat SampleOccurrence SamplePlan
        OpenEnvironment (UInt32 × OpenTerm) sampleStore sampleProjection =>
          view.force) :=
  ContextQualifiedMemoization.sourceIdentityKey_unsound_of_force_ne
    source_identity_key_ignores_binding_version rebound_changes_forced_value

/-- The unsound key has an executable failure: after storing the first view,
looking up the rebound view returns the stale forced value. -/
theorem source_identity_memo_returns_stale_force :
    let table :=
      Mettapedia.GSLT.Dynamics.MemoizationObserver.store
        ContextQualifiedMemoization.sourceIdentityKey
        (fun view : TermView Unit Nat SampleOccurrence SamplePlan
          OpenEnvironment (UInt32 × OpenTerm) sampleStore sampleProjection =>
            view.force)
        Mettapedia.GSLT.Dynamics.MemoizationObserver.Table.empty sampleView
    Mettapedia.GSLT.Dynamics.MemoizationObserver.lookupOrCompute
        ContextQualifiedMemoization.sourceIdentityKey
        (fun view : TermView Unit Nat SampleOccurrence SamplePlan
          OpenEnvironment (UInt32 × OpenTerm) sampleStore sampleProjection =>
            view.force)
        table reboundSampleView = sampleView.force ∧
      sampleView.force ≠ reboundSampleView.force := by
  decide

/-- Negative observer control: a forced value is not a sound key for a
consumer that also observes source occurrence and compiled plan. -/
theorem forced_value_key_unsound_for_observation :
    ¬ Mettapedia.GSLT.Dynamics.MemoizationObserver.SoundKey
      (fun view : TermView Unit Nat SampleOccurrence SamplePlan
        OpenEnvironment (UInt32 × OpenTerm) sampleStore sampleProjection =>
          view.force)
      (fun view => observeSource view) := by
  intro sound
  have equalValue : sampleView.force = duplicateSampleView.force := rfl
  have equalObservation := sound sampleView duplicateSampleView equalValue
  have differentObservation :
      observeSource sampleView ≠ observeSource duplicateSampleView := by
    intro equal
    have occurrenceEq := congrArg CompleteObservation.occurrence equal
    simp [observeSource, sampleView, duplicateSampleView] at occurrenceEq
  exact differentObservation equalObservation

/-- Support capture changes representation and retains the complete
provenance-bearing observation. -/
example :
    (supportCaptureRealization (store := sampleStore)
      (projection := sampleProjection)).observeArtifact ()
        ((supportCaptureRealization (store := sampleStore)
          (projection := sampleProjection)).compile () sampleView) =
      (supportCaptureRealization (store := sampleStore)
        (projection := sampleProjection)).observeSource () sampleView :=
  (supportCaptureRealization (store := sampleStore)
    (projection := sampleProjection)).adequate () sampleView

/-- Two equal values from different source occurrences remain different
answers; complete-bag observation therefore preserves multiplicity and
provenance. -/
example :
    let value : OpenTerm := .symbol [7]
    let left : OccurrenceAnswer SampleOccurrence :=
      { occurrence := .left, path := [], value }
    let right : OccurrenceAnswer SampleOccurrence :=
      { occurrence := .right, path := [], value }
    left ≠ right := by
  decide

/-- An occurrence index retains two equal forced payloads because their stable
source identities differ. -/
example :
    Mettapedia.GSLT.Dynamics.StableOccurrenceIdentityIndex.index
        (fun _ : OpenTerm => true)
        [sampleView.toStableOccurrence,
          duplicateSampleView.toStableOccurrence] =
      [SampleOccurrence.left, SampleOccurrence.right] := by
  rfl

def leftAnswer : OccurrenceAnswer SampleOccurrence :=
  { occurrence := .left, path := [], value := .symbol [7] }

def rightAnswer : OccurrenceAnswer SampleOccurrence :=
  { occurrence := .right, path := [], value := .symbol [7] }

def duplicateValueSearch : FiniteSearch (OccurrenceAnswer SampleOccurrence) :=
  .choice (.answer leftAnswer) (.answer rightAnswer)

/-- Two lawful schedulers expose opposite streams but the same completed bag,
and the bag retains both equal-valued source occurrences. -/
theorem duplicate_occurrence_streams_differ_bags_agree :
    (Mettapedia.GSLT.Core.BranchingTemporal.run FiniteSearch.system
          Scheduler.breadthFirst 3
          (Mettapedia.GSLT.Core.BranchingTemporal.initial
            [duplicateValueSearch])).events.map Emission.value ≠
        (Mettapedia.GSLT.Core.BranchingTemporal.run FiniteSearch.system
          Scheduler.reverseBreadthFirst 3
          (Mettapedia.GSLT.Core.BranchingTemporal.initial
            [duplicateValueSearch])).events.map Emission.value ∧
      eventBag
          (Mettapedia.GSLT.Core.BranchingTemporal.run FiniteSearch.system
            Scheduler.breadthFirst 3
            (Mettapedia.GSLT.Core.BranchingTemporal.initial
              [duplicateValueSearch])).events =
        eventBag
          (Mettapedia.GSLT.Core.BranchingTemporal.run FiniteSearch.system
            Scheduler.reverseBreadthFirst 3
            (Mettapedia.GSLT.Core.BranchingTemporal.initial
              [duplicateValueSearch])).events := by
  decide

/-! ### Effect-delimited source-view controls -/

inductive EffectOccurrence
  | body
deriving DecidableEq, Repr

inductive EffectCompiledPlan
  | body
deriving DecidableEq, Repr

def effectProjection :
    PlanProjection Nat EffectOccurrence EffectCompiledPlan where
  source
    | .body => .application [1]
        (.cons (.variable 0) (.cons (.variable 1) .nil))
  revision
    | .body => 13
  occurrence
    | .body => .body

def emptyEnvironment : OpenEnvironment := fun _ => none

def effectView :
    TermView Unit Nat EffectOccurrence EffectCompiledPlan
      OpenEnvironment (UInt32 × OpenTerm) sampleStore effectProjection where
  occurrence := .body
  owner := ()
  revision := 13
  generation := 11
  bindings := emptyEnvironment
  source := .application [1]
    (.cons (.variable 0) (.cons (.variable 1) .nil))
  plan := .body
  plan_source := rfl
  plan_revision := rfl
  plan_occurrence := rfl

def bindSlot (slot : UInt32) (value : OpenTerm) : OpenSubstitution :=
  fun logicVariable =>
    if logicVariable = { generation := 11, slot := slot }
    then some value
    else none

def effectPlan : EffectDelimited.ExecutionPlan :=
  .region (X := ()) (Y := ()) (Z := ())
    (bindSlot 0 (.symbol [7]))
    (.hole (X := ()) (Y := ()) (Z := ()) 10
      (.region (X := ()) (Y := ()) (Z := ())
        (bindSlot 1 (.symbol [8]))
        (.hole (X := ()) (Y := ()) (Z := ()) 20 (.nil ()))))

def holesErasedPlan : EffectDelimited.ExecutionPlan :=
  .region (X := ()) (Y := ()) (Z := ())
    (bindSlot 0 (.symbol [7]))
    (.region (X := ()) (Y := ()) (Z := ())
      (bindSlot 1 (.symbol [8])) (.nil ()))

def holesSwappedPlan : EffectDelimited.ExecutionPlan :=
  .region (X := ()) (Y := ()) (Z := ())
    (bindSlot 0 (.symbol [7]))
    (.hole (X := ()) (Y := ()) (Z := ()) 20
      (.region (X := ()) (Y := ()) (Z := ())
        (bindSlot 1 (.symbol [8]))
        (.hole (X := ()) (Y := ()) (Z := ()) 10 (.nil ()))))

def runEffectPlan (plan : EffectDelimited.ExecutionPlan) :
    List (OpenTerm × List (Nat × OpenTerm)) :=
  (occurrenceKleisliCategory.compose
      (Plan.denote
        (EffectDelimited.delayedRealization
          (Owner := Unit) (Revision := Nat)
          (Occurrence := EffectOccurrence)
          (CompiledPlan := EffectCompiledPlan)
          (projection := effectProjection)) plan)
      (EffectDelimited.forceSegment
        (Owner := Unit) (Revision := Nat)
        (Occurrence := EffectOccurrence)
        (CompiledPlan := EffectCompiledPlan)
        (projection := effectProjection))
      (EffectDelimited.fromTermView effectView)).map
    fun state => (state.value, state.trace)

def partiallyBoundValue : OpenTerm :=
  .application [1]
    (.cons (.symbol [7])
      (.cons (.variable { generation := 11, slot := 1 }) .nil))

def completelyBoundValue : OpenTerm :=
  .application [1]
    (.cons (.symbol [7]) (.cons (.symbol [8]) .nil))

/-- Positive: the first Hole observes the partially bound term, the second
observes the fully bound term, and final forcing returns the latter. -/
theorem effect_delimited_plan_result :
    runEffectPlan effectPlan =
      [(completelyBoundValue,
        [(10, partiallyBoundValue), (20, completelyBoundValue)])] := by
  decide

/-- The concrete source-view execution is related to eager materialization by
the generic Region/Hole naturality theorem, not by a specimen-specific proof. -/
theorem effect_delimited_plan_exact :
    occurrenceKleisliCategory.compose
        (Plan.denote
          (EffectDelimited.delayedRealization
            (Owner := Unit) (Revision := Nat)
            (Occurrence := EffectOccurrence)
            (CompiledPlan := EffectCompiledPlan)
            (projection := effectProjection)) effectPlan)
        (EffectDelimited.forceSegment
          (Owner := Unit) (Revision := Nat)
          (Occurrence := EffectOccurrence)
          (CompiledPlan := EffectCompiledPlan)
          (projection := effectProjection)) =
      occurrenceKleisliCategory.compose
        (EffectDelimited.forceSegment
          (Owner := Unit) (Revision := Nat)
          (Occurrence := EffectOccurrence)
          (CompiledPlan := EffectCompiledPlan)
          (projection := effectProjection))
        (Plan.denote
          (EffectDelimited.eagerRealization
            (Owner := Unit) (Revision := Nat)
            (Occurrence := EffectOccurrence)
            (CompiledPlan := EffectCompiledPlan)
            (projection := effectProjection)) effectPlan) :=
  EffectDelimited.force_plan_exact effectPlan

/-- Negative: retaining the final value while deleting both observing Holes
is not an exact realization because it erases the authored trace. -/
theorem erasing_holes_changes_observation :
    runEffectPlan holesErasedPlan ≠ runEffectPlan effectPlan := by
  decide

/-- Negative: retaining both Holes but swapping their labels is also visible;
Hole multiplicity alone is insufficient without authored order. -/
theorem swapping_holes_changes_observation :
    runEffectPlan holesSwappedPlan ≠ runEffectPlan effectPlan := by
  decide

/-- The first child is selected as a delayed cursor, retains source
provenance, and denotes the bound value without rebuilding its parent. -/
example :
    ((Cursor.root (capture sampleView)).child? 0).map
        (fun child =>
          (child.occurrence, child.plan, child.path, child.denote)) =
      some (SampleOccurrence.left, SamplePlan.first, [0], .symbol [7]) := by
  rfl

/-- A plan from another revision cannot supply the required plan witness for
this source occurrence. -/
example :
    sampleProjection.revision SamplePlan.stale ≠ sampleView.revision := by
  decide

/-- Exact occurrence evidence rejects attaching the duplicate occurrence's
plan to the left source occurrence. -/
example :
    ¬ ∃ candidate : TermView Unit Nat SampleOccurrence SamplePlan
        OpenEnvironment (UInt32 × OpenTerm) sampleStore sampleProjection,
      candidate.plan = SamplePlan.duplicate ∧
        candidate.occurrence = SampleOccurrence.left := by
  rintro ⟨candidate, plan, occurrence⟩
  have exact := candidate.plan_occurrence
  rw [plan, occurrence] at exact
  simp [sampleProjection] at exact

/-- Root shape remains insufficient for complete reconstruction, so consumers
such as serialization must force explicitly. -/
example :
    ¬ (∃ rebuild : TermLayer Unit -> OpenTerm,
      ∀ value, rebuild (rootShape value) = value) :=
  no_complete_reconstruction_from_rootShape

end Canaries

#print axioms supportCaptureRealization
#print axioms TermView.writeBinding_force_exact
#print axioms TermView.writeBindings_force_exact
#print axioms capture_force_exact
#print axioms DestinationMaterialization.publicationTrace_exact
#print axioms DestinationMaterialization.publicationTrace_rooted
#print axioms DestinationMaterialization.publicationTrace_outputClosed
#print axioms DestinationMaterialization.retainedIntermediatePublication_exact
#print axioms DestinationMaterialization.retainedIntermediatePublication_rooted
#print axioms DestinationMaterialization.retainedIntermediatePublication_not_outputClosed
#print axioms captureFamily_observe_exact
#print axioms Cursor.out_exact
#print axioms Cursor.child_denote_exact
#print axioms Cursor.child_occurrence_preserved
#print axioms Cursor.child_plan_preserved
#print axioms Cursor.child_path_exact
#print axioms traverseCursors_exact
#print axioms substituteOpen_comp
#print axioms composeOpen_assoc
#print axioms composeEnvironment_assoc
#print axioms substituteOpen_instantiateOpen
#print axioms extendSourceView_force_exact
#print axioms DestinationMaterialization.publish_exact
#print axioms DestinationMaterialization.publish_rooted
#print axioms ContextQualifiedMemoization.supportEnvironmentVersionKey_eq_iff_agreesOn
#print axioms ContextQualifiedMemoization.contextKey_eq_force_eq
#print axioms ContextQualifiedMemoization.contextKey_sound_for_force
#print axioms ContextQualifiedMemoization.contextKey_sound_for_observation
#print axioms ContextQualifiedMemoization.lookupOrCompute_force_exact
#print axioms ContextQualifiedMemoization.refinedKey_sound_for_force
#print axioms ContextQualifiedMemoization.refinedKey_sound_for_observation
#print axioms ContextQualifiedMemoization.sourceIdentityKey_unsound_of_force_ne
#print axioms EffectDelimited.force_plan_exact
#print axioms EffectDelimited.normalize_force_and_holes_exact
#print axioms PureKernel.completed_strategies_occurrence_bag_agree
#print axioms competing_world_writes_remain_observable
#print axioms competing_commits_remain_observable
#print axioms root_layers_le_complete
#print axioms root_layers_lt_complete_application
#print axioms DelayedResourceTrace.workImproving_iff_overhead_lt_saved
#print axioms DelayedResourceTrace.delayedWork_mono
#print axioms DelayedResourceTrace.not_workImproving_of_continuation_dominates
#print axioms Canaries.construction_reduction_is_not_sufficient
#print axioms Canaries.batched_region_is_work_improving
#print axioms Canaries.whole_execution_admission_separates_controls
#print axioms Canaries.duplicate_occurrence_streams_differ_bags_agree
#print axioms Canaries.sample_context_key_sound_for_force
#print axioms Canaries.sample_context_key_sound_for_observation
#print axioms Canaries.irrelevant_write_preserves_context_key
#print axioms Canaries.source_identity_key_unsound_for_force
#print axioms Canaries.source_identity_memo_returns_stale_force
#print axioms Canaries.forced_value_key_unsound_for_observation
#print axioms Canaries.effect_delimited_plan_result
#print axioms Canaries.effect_delimited_plan_exact
#print axioms Canaries.erasing_holes_changes_observation
#print axioms Canaries.swapping_holes_changes_observation

end Mettapedia.Languages.MeTTa.TermViewCompilation
