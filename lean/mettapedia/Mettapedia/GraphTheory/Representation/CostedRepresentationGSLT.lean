import Mettapedia.GSLT.Core.CostedOperational
import Mettapedia.GSLT.Core.SemanticTransport
import Mettapedia.GraphTheory.Representation.RevisionPortfolio
import Mettapedia.GraphTheory.Representation.SemanticInvariant

/-!
# Selected cost grading for abstract graph-refinement paths

Representation conversion forms an abstract path GSLT whose legs are the
proved total constructions in `Transformations`.  This module equips those
same legs with a selected structural resource schedule by instantiating the
generic writer lift.  Cost never selects a target and never changes graph
meaning.

```text
costed representation GSLT -- natural erasure --> representation GSLT
            |                                         |
            +---------- composed realization --------+
                              |
                              v
                    discrete SimpleGraph GSLT
```

The resource accounts are formulas selected for the complete refinement
functions.  They are not derived from local rewrite events, and they are not
wall-clock measurements.  A detailed conversion machine may justify or revise
one of these schedules; a later physical realization may further relate its
events to cache, allocator, or machine costs without changing graph meaning.
-/

namespace Mettapedia.GraphTheory.Representation.CostedRepresentationGSLT

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GraphTheory.Representation
open Mettapedia.GraphTheory.Representation.RepresentationGSLT
open Mettapedia.GraphTheory.Representation.RevisionPortfolio

set_option autoImplicit false

/-- Structural account for constructing a matrix from a represented graph.
Every declared probe is charged once; the dense target is newly allocated. -/
def toMatrixResources {n : Nat} (source : State n) : Resources :=
  let visits := canonicalizationTime source
  let targetCells := AdjacencyMatrix.storageCells (canonicalMatrix source)
  { time := visits + targetCells
    reads := visits
    writes := targetCells
    allocated := targetCells
    peakTemporary := targetCells }

/-- Structural account for materializing a selected layout from a matrix. -/
def fromMatrixResources {n : Nat} (layout : Layout)
    (graph : AdjacencyMatrix.Rep n) : Resources :=
  let visits := materializationTime layout graph
  let targetCells := stateStorageCells (materialize layout graph)
  { time := visits + targetCells
    reads := visits
    writes := targetCells
    allocated := targetCells
    peakTemporary := targetCells }

/-- Packing already materialized rows into CSR reads the row carrier and
writes the packed carrier exactly once in this structural schedule. -/
def rowsToCSRResources {n : Nat} (graph : AdjacencyRows.Rep n) : Resources :=
  let sourceCells := AdjacencyRows.storageCells graph
  let targetCells := CSR.storageCells (Transformations.rowsToCSR graph)
  { time := sourceCells + targetCells
    reads := sourceCells
    writes := targetCells
    allocated := targetCells
    peakTemporary := targetCells }

/-- A proof-relevant occurrence of one representation rule together with its
structurally computed resource grade.  This is extra syntax, as it must be:
Lean proofs of the proposition-valued base step relation are proof-irrelevant
and cannot themselves be inspected to manufacture cost data. -/
inductive GradedStep {n : Nat} : State n → State n → Resources → Type where
  | edgeListToMatrix (graph : EdgeList.Rep n) :
      GradedStep (.edgeList graph)
        (.matrix (Transformations.toMatrix (EdgeList.presentation n) graph))
        (toMatrixResources (.edgeList graph))
  | matrixToEdgeList (graph : AdjacencyMatrix.Rep n) :
      GradedStep (.matrix graph)
        (.edgeList (Transformations.matrixToEdgeList graph))
        (fromMatrixResources .edgeList graph)
  | matrixToRows (graph : AdjacencyMatrix.Rep n) :
      GradedStep (.matrix graph)
        (.adjacencyRows (Transformations.matrixToRows graph))
        (fromMatrixResources .adjacencyRows graph)
  | rowsToMatrix (graph : AdjacencyRows.Rep n) :
      GradedStep (.adjacencyRows graph)
        (.matrix (Transformations.rowsToMatrix graph))
        (toMatrixResources (.adjacencyRows graph))
  | rowsToCSR (graph : AdjacencyRows.Rep n) :
      GradedStep (.adjacencyRows graph)
        (.csr (Transformations.rowsToCSR graph))
        (rowsToCSRResources graph)
  | matrixToNeighborFinsets (graph : AdjacencyMatrix.Rep n) :
      GradedStep (.matrix graph)
        (.neighborFinsets (Transformations.matrixToNeighborFinsets graph))
        (fromMatrixResources .neighborFinsets graph)
  | neighborFinsetsToMatrix (graph : NeighborFinsets.Rep n) :
      GradedStep (.neighborFinsets graph)
        (.matrix
          (Transformations.toMatrix (NeighborFinsets.presentation n) graph))
        (toMatrixResources (.neighborFinsets graph))
  | matrixToIncidence (graph : AdjacencyMatrix.Rep n) :
      GradedStep (.matrix graph)
        (.incidence (Transformations.matrixToIncidence graph).2)
        (fromMatrixResources .incidence graph)
  | incidenceToMatrix {m : Nat} (graph : IncidenceMatrix.Rep n m) :
      GradedStep (.incidence graph)
        (.matrix
          (Transformations.toMatrix (IncidenceMatrix.presentation n m) graph))
        (toMatrixResources (.incidence graph))
  | csrToMatrix (graph : CSR.Rep n) :
      GradedStep (.csr graph)
        (.matrix (Transformations.toMatrix (CSR.presentation n) graph))
        (toMatrixResources (.csr graph))

/-- Forget only the resource grade of one rule occurrence. -/
def GradedStep.toStep {n : Nat} {source target : State n}
    {resources : Resources} :
    GradedStep source target resources → Step source target
  | .edgeListToMatrix graph => .edgeListToMatrix graph
  | .matrixToEdgeList graph => .matrixToEdgeList graph
  | .matrixToRows graph => .matrixToRows graph
  | .rowsToMatrix graph => .rowsToMatrix graph
  | .rowsToCSR graph => .rowsToCSR graph
  | .matrixToNeighborFinsets graph => .matrixToNeighborFinsets graph
  | .neighborFinsetsToMatrix graph => .neighborFinsetsToMatrix graph
  | .matrixToIncidence graph => .matrixToIncidence graph
  | .incidenceToMatrix graph => .incidenceToMatrix graph
  | .csrToMatrix graph => .csrToMatrix graph

/-- Each graph-representation step has exactly its structurally computed
resource grade. -/
def spend (n : Nat) : (theory n).StepSpend Resources where
  graded := fun source target resources =>
    Nonempty (GradedStep source target resources)
  sound := by
    rintro source target resources ⟨step⟩
    exact step.toStep
  resp_left := by
    rintro source source' target resources equivalent graded
    subst source'
    exact ⟨target, graded, rfl⟩
  resp_right := by
    rintro source target target' resources graded equivalent
    subst target'
    exact graded

/-- Every abstract representation leg has a selected grade. -/
theorem spend_total (n : Nat) : (spend n).Total := by
  intro source target step
  cases step with
  | edgeListToMatrix graph => exact ⟨_, ⟨.edgeListToMatrix graph⟩⟩
  | matrixToEdgeList graph => exact ⟨_, ⟨.matrixToEdgeList graph⟩⟩
  | matrixToRows graph => exact ⟨_, ⟨.matrixToRows graph⟩⟩
  | rowsToMatrix graph => exact ⟨_, ⟨.rowsToMatrix graph⟩⟩
  | rowsToCSR graph => exact ⟨_, ⟨.rowsToCSR graph⟩⟩
  | matrixToNeighborFinsets graph =>
      exact ⟨_, ⟨.matrixToNeighborFinsets graph⟩⟩
  | neighborFinsetsToMatrix graph =>
      exact ⟨_, ⟨.neighborFinsetsToMatrix graph⟩⟩
  | matrixToIncidence graph => exact ⟨_, ⟨.matrixToIncidence graph⟩⟩
  | incidenceToMatrix graph => exact ⟨_, ⟨.incidenceToMatrix graph⟩⟩
  | csrToMatrix graph => exact ⟨_, ⟨.csrToMatrix graph⟩⟩

/-- The graph representation system as an object of the category of
cost-graded operational theories. -/
def costedObject (n : Nat) : CostedTheory Resources :=
  ⟨theory n, spend n⟩

/-- Writer-enriched graph representation dynamics. -/
abbrev costedTheory (n : Nat) : GSLT :=
  (theory n).spendLift (spend n)

/-- Erasing the resource account preserves one abstract refinement leg,
supplied by the generic natural writer erasure. -/
def eraseTranslation (n : Nat) :
    OperationalTranslation (costedTheory n) (theory n) :=
  CostedTranslation.erase (costedObject n)

/-- A proof-relevant route of graded representation-rule occurrences. -/
inductive GradedRoute {n : Nat} : State n → State n → Type where
  | nil (state : State n) : GradedRoute state state
  | cons {source middle target : State n} (resources : Resources)
      (step : GradedStep source middle resources)
      (rest : GradedRoute middle target) : GradedRoute source target

namespace GradedRoute

/-- Forget costs while retaining the exact ordered base-rule occurrences. -/
def toBasePath {n : Nat} : {source target : State n} →
    GradedRoute source target → (theory n).RewritePath source target
  | _, _, .nil state => GSLT.RewritePath.nil (S := theory n) state
  | _, _, .cons _ step rest =>
      GSLT.RewritePath.cons step.toStep (toBasePath rest)

/-- Sequential resource account of one graded route. -/
def resources {n : Nat} : {source target : State n} →
    GradedRoute source target → Resources
  | _, _, .nil _ => Resources.zero
  | _, _, .cons cost _ rest => cost.seq (resources rest)

/-- The account produced by executing a route from a given initial account.
This recursive form follows the writer machine definitionally; its closed
monoidal form is proved below. -/
def finalAccount {n : Nat} (before : Resources) :
    {source target : State n} → GradedRoute source target → Resources
  | _, _, .nil _ => before
  | _, _, .cons cost _ rest => finalAccount (before.seq cost) rest

/-- Concatenate graded routes without losing occurrences. -/
def append {n : Nat} {source middle target : State n}
    (first : GradedRoute source middle)
    (second : GradedRoute middle target) : GradedRoute source target :=
  match first with
  | .nil _ => second
  | .cons cost step rest => .cons cost step (append rest second)

theorem toBasePath_append {n : Nat} {source middle target : State n}
    (first : GradedRoute source middle)
    (second : GradedRoute middle target) :
    toBasePath (append first second) =
      RepresentationGSLT.appendPath (toBasePath first) (toBasePath second) := by
  induction first with
  | nil _ => simp [append, toBasePath, RepresentationGSLT.appendPath]
  | cons cost step rest inductionHypothesis =>
      simp only [append, toBasePath, RepresentationGSLT.appendPath]
      rw [inductionHypothesis]

theorem resources_append {n : Nat} {source middle target : State n}
    (first : GradedRoute source middle)
    (second : GradedRoute middle target) :
    resources (append first second) =
      (resources first).seq (resources second) := by
  induction first with
  | nil _ => simp [append, resources]
  | cons cost step rest inductionHypothesis =>
      simp only [append, resources]
      rw [inductionHypothesis, Resources.seq_assoc]

/-- Structural execution agrees with the closed writer-account formula. -/
theorem finalAccount_eq {n : Nat} (before : Resources) :
    {source target : State n} → (route : GradedRoute source target) →
      finalAccount before route = before.seq (resources route)
  | _, _, .nil _ => (Resources.seq_zero before).symm
  | _, _, .cons cost _ rest => by
      rw [finalAccount, finalAccount_eq, resources, Resources.seq_assoc]

/-- Lift one proof-relevant graded occurrence into the writer GSLT. -/
def toCostedStep {n : Nat} {source target : State n}
    {cost : Resources} (before : Resources)
    (step : GradedStep source target cost) :
    (costedTheory n).Step (source, before) (target, before.seq cost) := by
  exact ⟨cost, ⟨step⟩, rfl⟩

/-- Execute a graded route in the writer-enriched GSLT. -/
def toCostedPath {n : Nat} (before : Resources) :
    {source target : State n} → (route : GradedRoute source target) →
      (costedTheory n).RewritePath (source, before)
        (target, finalAccount before route)
  | _, _, .nil state =>
      GSLT.RewritePath.nil (S := costedTheory n) (state, before)
  | _, _, .cons cost step rest =>
      .cons (toCostedStep before step)
        (toCostedPath (before.seq cost) rest)

end GradedRoute

/-- Erase a costed path without losing the ordered underlying rewrite
occurrences. -/
def erasePath {n : Nat} :
    {source target : (costedTheory n).Term} →
      (costedTheory n).RewritePath source target →
        (theory n).RewritePath source.1 target.1
  | _, _, .nil source => .nil source.1
  | _, _, .cons step rest =>
      .cons ((eraseTranslation n).mapStep step) (erasePath rest)

/-- Executing then erasing a graded route returns its exact base path. -/
theorem erase_toCostedPath {n : Nat} (before : Resources) :
    {source target : State n} → (route : GradedRoute source target) →
      erasePath (route.toCostedPath before) = route.toBasePath
  | _, _, .nil _ => rfl
  | _, _, .cons cost step rest => by
      simp only [GradedRoute.toCostedPath, GradedRoute.toBasePath, erasePath]
      change GSLT.RewritePath.cons (S := theory n) step.toStep
          (erasePath (rest.toCostedPath (before.seq cost))) =
        GSLT.RewritePath.cons (S := theory n) step.toStep rest.toBasePath
      rw [erase_toCostedPath (before.seq cost) rest]

/-- Graded route into the canonical matrix waist. -/
def toCanonicalMatrixRoute {n : Nat} :
    (source : State n) →
      GradedRoute source (.matrix (canonicalMatrix source))
  | .edgeList graph =>
      .cons _ (.edgeListToMatrix graph) (.nil _)
  | .matrix graph => .nil (.matrix graph)
  | .adjacencyRows graph =>
      .cons _ (.rowsToMatrix graph) (.nil _)
  | .neighborFinsets graph =>
      .cons _ (.neighborFinsetsToMatrix graph) (.nil _)
  | .incidence graph =>
      .cons _ (.incidenceToMatrix graph) (.nil _)
  | .csr graph => .cons _ (.csrToMatrix graph) (.nil _)

/-- Graded materialization route out of the matrix waist. -/
def fromMatrixRoute {n : Nat} :
    (layout : Layout) → (graph : AdjacencyMatrix.Rep n) →
      GradedRoute (.matrix graph) (materialize layout graph)
  | .edgeList, graph => .cons _ (.matrixToEdgeList graph) (.nil _)
  | .matrix, graph => .nil (.matrix graph)
  | .adjacencyRows, graph => .cons _ (.matrixToRows graph) (.nil _)
  | .neighborFinsets, graph =>
      .cons _ (.matrixToNeighborFinsets graph) (.nil _)
  | .incidence, graph => .cons _ (.matrixToIncidence graph) (.nil _)
  | .csr, graph =>
      .cons _ (.matrixToRows graph)
        (.cons _ (.rowsToCSR (Transformations.matrixToRows graph)) (.nil _))

/-- Canonical source-to-layout route with proof-relevant selected grades. -/
def convertRoute {n : Nat} (source : State n) (target : Layout) :
    GradedRoute source (materialize target (canonicalMatrix source)) :=
  (toCanonicalMatrixRoute source).append
    (fromMatrixRoute target (canonicalMatrix source))

theorem toBasePath_toCanonicalMatrixRoute {n : Nat} (source : State n) :
    (toCanonicalMatrixRoute source).toBasePath =
      toCanonicalMatrixPath source := by
  cases source <;>
    simp [toCanonicalMatrixRoute, GradedRoute.toBasePath,
      toCanonicalMatrixPath]

theorem toBasePath_fromMatrixRoute {n : Nat} (layout : Layout)
    (graph : AdjacencyMatrix.Rep n) :
    (fromMatrixRoute layout graph).toBasePath = fromMatrixPath layout graph := by
  cases layout <;>
    simp [fromMatrixRoute, GradedRoute.toBasePath, fromMatrixPath]

/-- Graded and ungraded canonical routes have exactly the same ordered
refinement path after erasure. -/
theorem toBasePath_convertRoute {n : Nat} (source : State n)
    (target : Layout) :
    (convertRoute source target).toBasePath = convertPath source target := by
  rw [convertRoute, GradedRoute.toBasePath_append,
    toBasePath_toCanonicalMatrixRoute, toBasePath_fromMatrixRoute]
  rfl

/-- The selected composite grade of the canonical source-to-layout route. -/
def convertCost {n : Nat} (source : State n) (target : Layout) : Resources :=
  (convertRoute source target).resources

/-- The selected grades travel on the exact abstract itinerary.  This theorem
does not claim that the grade was derived from a detailed conversion loop. -/
def convertPathCosted {n : Nat} (source : State n) (target : Layout) :
    (costedTheory n).RewritePath (source, Resources.zero)
      (materialize target (canonicalMatrix source),
        (convertRoute source target).finalAccount Resources.zero) :=
  (convertRoute source target).toCostedPath Resources.zero

@[simp] theorem convertPathCosted_finalAccount {n : Nat}
    (source : State n) (target : Layout) :
    (convertRoute source target).finalAccount Resources.zero =
      convertCost source target := by
  rw [GradedRoute.finalAccount_eq, convertCost, Resources.zero_seq]

/-- Cost erasure recovers the exact canonical refinement path. -/
theorem erase_convertPathCosted {n : Nat} (source : State n)
    (target : Layout) :
    erasePath (convertPathCosted source target) = convertPath source target := by
  change erasePath ((convertRoute source target).toCostedPath Resources.zero) = _
  rw [erase_toCostedPath, toBasePath_convertRoute]

/-- Representation conversion as an explicit realization into the discrete
GSLT of mathematical graph meanings. -/
def graphMeaningRealization (n : Nat) :
    OperationalRealization (theory n)
      (GSLT.discrete (SimpleGraph (Fin n))) :=
  (SemanticInvariant.graphMeaning n).toDiscreteRealization

/-- The complete costed-to-mathematical chain is the composition of natural
cost erasure with the graph-denotation realization. -/
def costedMeaningRealization (n : Nat) :
    OperationalRealization (costedTheory n)
      (GSLT.discrete (SimpleGraph (Fin n))) :=
  (OperationalRealization.ofTranslation (eraseTranslation n)).comp
    (graphMeaningRealization n)

@[simp] theorem costedMeaningRealization_mapTerm {n : Nat}
    (state : State n) (resources : Resources) :
    (costedMeaningRealization n).mapTerm (state, resources) = state.denote :=
  rfl

/-- Every costed representation rewrite becomes a zero-length semantic path:
conversion changes layout and resources, not the mathematical graph. -/
theorem costed_step_semantically_silent {n : Nat}
    {source target : (costedTheory n).Term}
    (step : (costedTheory n).Step source target) :
    ((costedMeaningRealization n).mapStep step).length = 0 :=
  Mettapedia.GSLT.IndexedOperational.discreteExecutionPath_length _

namespace Canary

open EdgeList.Canary

/-- The path-to-CSR route is a three-leg graded refinement itinerary whose
erasure is the original abstract path.  This is not a claim that CSR
construction takes three algorithmic operations. -/
theorem path3_csr_erases_exactly :
    erasePath (convertPathCosted (.edgeList path3) .csr) =
      convertPath (.edgeList path3) .csr :=
  erase_convertPathCosted (.edgeList path3) .csr

/-- Resource information is not recoverable from graph meaning: two distinct
writer states can denote the same mathematical graph. -/
theorem same_graph_different_resources :
    (costedMeaningRealization 3).mapTerm
        ((.edgeList path3 : State 3), Resources.zero) =
      (costedMeaningRealization 3).mapTerm
        ((.edgeList path3 : State 3), { time := 1 }) ∧
    ((.edgeList path3 : State 3), Resources.zero) ≠
      ((.edgeList path3 : State 3), { time := 1 }) := by
  constructor
  · rfl
  · intro equal
    have resourcesEqual := congrArg Prod.snd equal
    exact (by decide : Resources.zero ≠ ({ time := 1 } : Resources))
      resourcesEqual

end Canary

#print axioms spend_total
#print axioms GradedRoute.resources_append
#print axioms erase_toCostedPath
#print axioms erase_convertPathCosted
#print axioms costedMeaningRealization
#print axioms costed_step_semantically_silent
#print axioms Canary.same_graph_different_resources

end Mettapedia.GraphTheory.Representation.CostedRepresentationGSLT
