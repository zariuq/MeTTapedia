import Mettapedia.GSLT.Core.BindingStoreCapabilityAlgebra
import Mettapedia.GSLT.Dynamics.CollapseObservationContract
import Mettapedia.Languages.MeTTa.SubstitutionAlgebra

/-!
# Flat borrowed-term-view compilation

This module isolates the representation-independent law used by a matcher or
index which reads a source term together with a substitution environment.  On
the admitted flat fragment, resolving only the immediate child roots is equal
to constructing the complete one-pass substituted term.  Consequently every
observer of the term sees the same result.

The source language is a term paired with its environment, the target is an
ordinary materialized term, and the declared observation is supplied by the
consumer.  No evaluator, search strategy, or machine calculus occurs in the
statement, so a BN machine, CBPV machine, or another evaluator can reuse it by
providing its own source-to-view adapter.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.FlatTermViewCompilation

open Mettapedia.GSLT.Core.BindingStoreCapabilityAlgebra
open Mettapedia.GSLT.Dynamics.Collapse
open Mettapedia.GSLT.Dynamics.CollapseObservationContract
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra

universe uTerm uEnvironment uObservation

/-! ## Representation-independent root projection -/

namespace RootProjection

/-- Operations and adequacy laws needed to observe only the immediate roots of
a suspended term.  The carrier may be an AST, a compiled-plan cursor, a BN
closure, a CBPV thunk, or another evaluator representation. -/
structure Algebra (Term : Type uTerm) (Environment : Type uEnvironment) where
  children? : Term → Option (List Term)
  rebuild : Term → List Term → Term
  force : Environment → Term → Term
  resolveRoot : Environment → Term → Term
  rootProjectable : Term → Prop
  force_node : ∀ environment source children,
    children? source = some children →
      force environment source =
        rebuild source (children.map (force environment))
  force_root : ∀ environment source,
    rootProjectable source →
      force environment source = resolveRoot environment source

/-- A suspended source in an evaluator-independent root-projection algebra. -/
structure View {Term : Type uTerm} {Environment : Type uEnvironment}
    (algebra : Algebra Term Environment) where
  source : Term
  environment : Environment

/-- Admission exposes one application layer and certifies every child root. -/
def Admitted {Term : Type uTerm} {Environment : Type uEnvironment}
    (algebra : Algebra Term Environment) (view : View algebra) : Prop :=
  ∃ children, algebra.children? view.source = some children ∧
    ∀ child, child ∈ children → algebra.rootProjectable child

/-- Rebuild one application layer from resolved or borrowed child roots.  The
non-application case is outside admission and has no optimized meaning. -/
def project {Term : Type uTerm} {Environment : Type uEnvironment}
    (algebra : Algebra Term Environment) (view : View algebra) : Term :=
  match algebra.children? view.source with
  | some children =>
      algebra.rebuild view.source
        (children.map (algebra.resolveRoot view.environment))
  | none => algebra.resolveRoot view.environment view.source

/-- The root projection square commutes with complete forcing. -/
theorem projection_exact
    {Term : Type uTerm} {Environment : Type uEnvironment}
    (algebra : Algebra Term Environment) (view : View algebra)
    (admitted : Admitted algebra view) :
    project algebra view = algebra.force view.environment view.source := by
  obtain ⟨children, childrenEq, childrenProjectable⟩ := admitted
  calc
    project algebra view =
        algebra.rebuild view.source
          (children.map (algebra.resolveRoot view.environment)) := by
      simp [project, childrenEq]
    _ = algebra.rebuild view.source
          (children.map (algebra.force view.environment)) := by
      apply congrArg (algebra.rebuild view.source)
      exact List.map_congr_left fun child member =>
        (algebra.force_root view.environment child
          (childrenProjectable child member)).symm
    _ = algebra.force view.environment view.source :=
      (algebra.force_node view.environment view.source children
        childrenEq).symm

/-- Every observer is natural across a lawful root projection. -/
theorem observe_projection_exact
    {Term : Type uTerm} {Environment : Type uEnvironment}
    {Observation : Type uObservation}
    (algebra : Algebra Term Environment) (observe : Term → Observation)
    (view : View algebra) (admitted : Admitted algebra view) :
    observe (project algebra view) =
      observe (algebra.force view.environment view.source) :=
  congrArg observe (projection_exact algebra view admitted)

/-- Package root projection through the common materialization-free observer
interface. -/
def delayedObservation
    {Term : Type uTerm} {Environment : Type uEnvironment}
    {Observation : Type uObservation}
    (algebra : Algebra Term Environment) (observe : Term → Observation) :
    DelayedObservation { view : View algebra // Admitted algebra view }
      Term Observation where
  materialize request :=
    algebra.force request.1.environment request.1.source
  observeMaterialized _ materialized := observe materialized
  observeDirect request := observe (project algebra request.1)
  commutes request :=
    observe_projection_exact algebra observe request.1 request.2

/-- Reference producer over materialized terms. -/
def materializedProducer {Term : Type uTerm} {Observation : Type}
    (produce : Term → List Observation) : Producer Term Observation where
  materialize := produce

/-- Physical producer over admitted suspended views. -/
def projectedProducer
    {Term : Type uTerm} {Environment : Type uEnvironment}
    {Observation : Type}
    (algebra : Algebra Term Environment)
    (produce : Term → List Observation) :
    Producer { view : View algebra // Admitted algebra view } Observation where
  materialize request := produce (project algebra request.1)

/-- Root projection is an exact source presentation for every producer.  Thus
an existing count, existence, bag, provenance, probability, or cost fold can
be transported to a new evaluator representation without changing the fold. -/
def producerPresentation
    {Term : Type uTerm} {Environment : Type uEnvironment}
    {Observation : Type}
    (algebra : Algebra Term Environment)
    (produce : Term → List Observation) :
    Producer.Presentation
      (materializedProducer produce)
      (projectedProducer algebra produce) where
  denote request :=
    algebra.force request.1.environment request.1.source
  exact request := by
    change produce (project algebra request.1) =
      produce (algebra.force request.1.environment request.1.source)
    rw [projection_exact algebra request.1 request.2]

/-! ## Observer/index composition -/

/-- A storage realization of Boolean existence.  Its physical representation
may be a hash table, trie, relation, or another index; the sole contract is
agreement with the positive-row `Any` fold of its semantic observations. -/
structure ExistenceIndex (Term : Type uTerm) (Answer Receipt : Type) where
  observations : Term → List (Obs Answer Receipt)
  contains : Term → Bool
  exact : ∀ term,
    contains term = collapseWith (AnyAlg Answer Receipt) (observations term)

/-- Run an existence index directly on the projected coordinates of an
admitted suspended term. -/
def viewContains
    {Term : Type uTerm} {Environment : Type uEnvironment}
    {Answer Receipt : Type}
    (algebra : Algebra Term Environment)
    (index : ExistenceIndex Term Answer Receipt)
    (view : View algebra) : Bool :=
  index.contains (project algebra view)

/-- Term-view projection and exact indexed existence compose.  An evaluator
may therefore replace its BN, CBPV, AST, or closure representation without
changing the storage proof: only its root-projection adapter is replaced. -/
theorem viewContains_exact
    {Term : Type uTerm} {Environment : Type uEnvironment}
    {Answer Receipt : Type}
    (algebra : Algebra Term Environment)
    (index : ExistenceIndex Term Answer Receipt)
    (view : View algebra) (admitted : Admitted algebra view) :
    viewContains algebra index view =
      collapseWith (AnyAlg Answer Receipt)
        (index.observations (algebra.force view.environment view.source)) := by
  rw [viewContains, index.exact, projection_exact algebra view admitted]

/-- The transported Boolean observer also inherits the lawful first-result
demand whenever the index's semantic rows carry positive multiplicity. -/
theorem viewContains_first_adequate
    {Term : Type uTerm} {Environment : Type uEnvironment}
    {Answer Receipt : Type}
    (algebra : Algebra Term Environment)
    (index : ExistenceIndex Term Answer Receipt)
    (view : View algebra)
    (positive : ∀ observation,
      observation ∈ index.observations
        (algebra.force view.environment view.source) →
      observation.multiplicity ≠ 0) :
    AdequateOn (AnyAlg Answer Receipt) .first
      (index.observations
        (algebra.force view.environment view.source)) :=
  any_first_adequate _ positive

end RootProjection

/-- A source occurrence together with the environment through which a
consumer observes it. -/
structure FlatAtomView where
  source : Atom
  environment : Subst

/-- Resolve one variable root, leaving an unbound variable unchanged.  A
non-variable subtree is borrowed as a whole. -/
def resolveRoot (environment : Subst) : Atom → Atom
  | .var name => (environment name).getD (.var name)
  | source => source

/-- Immediate observation is exact for a variable root and for a subtree
whose own variable support is empty. -/
def RootProjectable (source : Atom) : Prop :=
  match source with
  | .var _ => True
  | _ => vars source = []

/-- The bounded native fragment: one expression whose immediate children can
all be resolved or borrowed without traversing a variable-bearing subtree. -/
def FlatExpression (view : FlatAtomView) : Prop :=
  match view.source with
  | .expression children =>
      ∀ child, child ∈ children → RootProjectable child
  | _ => False

/-- Physical view projection.  Only the expression header and its immediate
coordinates are rebuilt; child terms remain borrowed. -/
def project (view : FlatAtomView) : Atom :=
  match view.source with
  | .expression children =>
      .expression (children.map (resolveRoot view.environment))
  | source => resolveRoot view.environment source

/-- The materializing reference semantics. -/
def force (view : FlatAtomView) : Atom :=
  subst view.environment view.source

theorem subst_eq_resolveRoot_of_rootProjectable
    (environment : Subst) (source : Atom)
    (safe : RootProjectable source) :
    subst environment source = resolveRoot environment source := by
  cases source with
  | symbol value => rfl
  | var name => rfl
  | grounded value => rfl
  | expression children =>
      have ground : vars (.expression children) = [] := by
        simpa [RootProjectable] using safe
      simpa [resolveRoot] using
        subst_of_vars_eq_nil environment (.expression children) ground

theorem substList_eq_map_resolveRoot
    (environment : Subst) (sources : List Atom)
    (safe : ∀ source, source ∈ sources → RootProjectable source) :
    subst.substList environment sources =
      sources.map (resolveRoot environment) := by
  induction sources with
  | nil => rfl
  | cons source rest inductionHypothesis =>
      simp only [subst.substList, List.map_cons]
      rw [subst_eq_resolveRoot_of_rootProjectable environment source
        (safe source (by simp))]
      rw [inductionHypothesis (fun item member =>
        safe item (by simp [member]))]

theorem substList_eq_map_subst
    (environment : Subst) (sources : List Atom) :
    subst.substList environment sources =
      sources.map (subst environment) := by
  induction sources with
  | nil => rfl
  | cons source rest inductionHypothesis =>
      simp only [subst.substList, List.map_cons]
      rw [inductionHypothesis]

def atomChildren? : Atom → Option (List Atom)
  | .expression children => some children
  | _ => none

def atomRebuild (_source : Atom) (children : List Atom) : Atom :=
  .expression children

/-- The shared OSLF atom/substitution model is one instance of the evaluator-
independent root-projection interface. -/
def atomRootProjectionAlgebra : RootProjection.Algebra Atom Subst where
  children? := atomChildren?
  rebuild := atomRebuild
  force := subst
  resolveRoot := resolveRoot
  rootProjectable := RootProjectable
  force_node := by
    intro environment source children childrenEq
    cases source with
    | symbol value => simp [atomChildren?] at childrenEq
    | var name => simp [atomChildren?] at childrenEq
    | grounded value => simp [atomChildren?] at childrenEq
    | expression sourceChildren =>
        simp [atomChildren?] at childrenEq
        subst children
        simp [atomRebuild, subst, substList_eq_map_subst]
  force_root := subst_eq_resolveRoot_of_rootProjectable

def FlatAtomView.toRootProjectionView (view : FlatAtomView) :
    RootProjection.View atomRootProjectionAlgebra where
  source := view.source
  environment := view.environment

theorem flatExpression_admitted
    (view : FlatAtomView) (safe : FlatExpression view) :
    RootProjection.Admitted atomRootProjectionAlgebra
      view.toRootProjectionView := by
  rcases view with ⟨source, environment⟩
  cases source with
  | symbol value => simp [FlatExpression] at safe
  | var name => simp [FlatExpression] at safe
  | grounded value => simp [FlatExpression] at safe
  | expression children =>
      refine ⟨children, rfl, ?_⟩
      simpa [FlatExpression, atomRootProjectionAlgebra] using safe

@[simp] theorem rootProjection_project_eq_project (view : FlatAtomView) :
    RootProjection.project atomRootProjectionAlgebra
      view.toRootProjectionView = project view := by
  rcases view with ⟨source, environment⟩
  cases source <;>
    rfl

@[simp] theorem rootProjection_force_eq_force (view : FlatAtomView) :
    atomRootProjectionAlgebra.force
      view.toRootProjectionView.environment
      view.toRootProjectionView.source = force view :=
  rfl

/-- Two-sided adequacy of the physical projection: it is exactly the
materialized term, not merely a sound approximation of it. -/
theorem project_eq_force (view : FlatAtomView) (safe : FlatExpression view) :
    project view = force view := by
  rw [← rootProjection_project_eq_project view,
    ← rootProjection_force_eq_force view]
  exact RootProjection.projection_exact atomRootProjectionAlgebra
    view.toRootProjectionView (flatExpression_admitted view safe)

/-- Observer naturality.  Any future evaluator can change its internal
machine while reusing this theorem, provided its adapter presents the same
term view and it declares the observation it consumes. -/
theorem observe_project_eq_force
    {Observation : Type} (observe : Atom -> Observation)
    (view : FlatAtomView) (safe : FlatExpression view) :
    observe (project view) = observe (force view) :=
  congrArg observe (project_eq_force view safe)

/-- Package the result through the common delayed-observation interface.  The
direct implementation projects immediate roots; the reference implementation
forces the substitution and then observes. -/
def flatTermViewObservation {Observation : Type}
    (observe : Atom -> Observation) :
    DelayedObservation { view : FlatAtomView // FlatExpression view }
      Atom Observation where
  materialize request := force request.1
  observeMaterialized _ materialized := observe materialized
  observeDirect request := observe (project request.1)
  commutes request := observe_project_eq_force observe request.1 request.2

theorem direct_observation_eq_materialized
    {Observation : Type} (observe : Atom -> Observation)
    (request : { view : FlatAtomView // FlatExpression view }) :
    (flatTermViewObservation observe).observeDirect request =
      (flatTermViewObservation observe).observeMaterialized request
        ((flatTermViewObservation observe).materialize request) :=
  (flatTermViewObservation observe).observeDirect_exact request

/-! ## Positive and negative controls -/

namespace Canary

def pairEnvironment : Subst := fun name =>
  if name = "left" then some (.grounded (.int 1))
  else if name = "right" then some (.grounded (.int 3))
  else none

def flatPairView : FlatAtomView where
  source := .expression
    [.var "left", .symbol "!=", .var "right"]
  environment := pairEnvironment

theorem flatPairView_admitted : FlatExpression flatPairView := by
  simp [FlatExpression, flatPairView, RootProjectable, vars]

/-- Positive: the physical projection obtains the fully substituted flat
query while borrowing its three child coordinates. -/
theorem flatPairView_projects_exactly :
    project flatPairView =
      .expression
        [.grounded (.int 1), .symbol "!=", .grounded (.int 3)] := by
  simp [project, flatPairView, resolveRoot, pairEnvironment]

def nestedView : FlatAtomView where
  source := .expression [.expression [.var "left"]]
  environment := pairEnvironment

/-- Negative admission control: root projection cannot see a variable below
an immediate expression child. -/
theorem nestedView_refused : ¬ FlatExpression nestedView := by
  simp [FlatExpression, nestedView, RootProjectable, vars, vars.varsList]

/-- The negative premise is semantic: admitting the nested source would
produce a visibly different term from full substitution. -/
theorem nestedView_projection_is_not_force :
    project nestedView ≠ force nestedView := by
  simp [project, force, nestedView, resolveRoot, pairEnvironment, subst,
    subst.substList]

/-- A small exact index used to exercise the composition boundary. -/
def exactAtomIndex (target : Atom) :
    RootProjection.ExistenceIndex Atom Unit Unit where
  observations term :=
    if term = target then [{ answer := (), multiplicity := 1, receipt := () }]
    else []
  contains term := decide (term = target)
  exact term := by
    by_cases equal : term = target <;>
      simp [equal, collapseWith, foldStream, AnyAlg]

/-- Positive: the borrowed flat view and the fully forced term make the same
existence decision through an independently specified exact index. -/
theorem flatPairView_existence_exact :
    RootProjection.viewContains atomRootProjectionAlgebra
        (exactAtomIndex (force flatPairView))
        flatPairView.toRootProjectionView = true := by
  rw [RootProjection.viewContains_exact atomRootProjectionAlgebra
    (exactAtomIndex (force flatPairView)) flatPairView.toRootProjectionView
    (flatExpression_admitted flatPairView flatPairView_admitted)]
  simp [exactAtomIndex, collapseWith, foldStream, AnyAlg]

/-- Negative: dropping flat admission is observable even through the very
weak Boolean existence algebra. -/
theorem nestedView_existence_is_not_exact :
    (exactAtomIndex (force nestedView)).contains (project nestedView) ≠
      (exactAtomIndex (force nestedView)).contains (force nestedView) := by
  simp only [exactAtomIndex]
  simp [nestedView_projection_is_not_force]

end Canary

#print axioms project_eq_force
#print axioms observe_project_eq_force
#print axioms direct_observation_eq_materialized
#print axioms RootProjection.projection_exact
#print axioms RootProjection.observe_projection_exact
#print axioms RootProjection.producerPresentation
#print axioms RootProjection.viewContains_exact
#print axioms RootProjection.viewContains_first_adequate
#print axioms Canary.flatPairView_projects_exactly
#print axioms Canary.flatPairView_existence_exact
#print axioms Canary.nestedView_refused
#print axioms Canary.nestedView_projection_is_not_force
#print axioms Canary.nestedView_existence_is_not_exact

end Mettapedia.GSLT.LanguageDef.FlatTermViewCompilation
