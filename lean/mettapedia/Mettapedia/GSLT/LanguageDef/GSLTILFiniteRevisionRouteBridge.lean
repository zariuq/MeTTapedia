import Mettapedia.GSLT.Dynamics.IndexedQueryRevisionOSLF
import Mettapedia.GSLT.Dynamics.SemanticPhysicalRouteBinding
import Mettapedia.GSLT.LanguageDef.GSLTILOperationalEquipment
import Mettapedia.GSLT.LanguageDef.GSLTILSemanticPredicateInstitution

/-!
# Finite revision routes in the GSLT-IL operational waist

Queryable revision theories retain named revision histories and physical
occurrence routes.  Their generated GSLT intentionally hides the revision
label at the proposition-valued one-step boundary.  This module relates those
layers without confusing them.

An existing proposition-valued history proves that an exact-length execution
path exists, but cannot be eliminated into a path object.  `NamedHistoryPath`
is the stronger, genuinely proof-relevant object: it retains intermediate
worlds and chronological step structure, maps constructively into the GSLT-IL
execution-path fibre, and erases to the existing history.

`PathRetainingFiniteRoute` aligns that path with physical occurrence and
revision identity.  It is a loose operational arrow, and an explicit
refinement cell forgets the displayed identities to the ordinary execution
path.  Reachability is then the further extensional shadow in the semantic
institution.

The erasure is deliberately not faithful.  A concrete counterexample has two
different revision labels and physical occurrences inducing the same generated
GSLT path.  Occurrence identity and named-event identity must therefore remain
displayed execution data.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.FiniteRevisionRouteBridge

open CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics.IndexedQueryRevision
open Mettapedia.GSLT.Dynamics.QueryRevision
open Mettapedia.GSLT.Dynamics.SemanticPhysicalRouteBinding
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.LanguageDef.GSLTIL.OperationalEquipment
open Mettapedia.GSLT.LanguageDef.GSLTIL.SemanticPredicateInstitution
open Mettapedia.OSLF.Framework.LanguageIndexedModalFunctor
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

universe u

/-! ## The existing proposition-valued history has an exact path witness -/

/-- Erasing named revisions gives proposition-valued reachability in the
generated revision GSLT. -/
def historyToMultiStep
    {theory : Theory.{u, u, u, u}}
    {revisions : List theory.Revision} {source target : theory.World} :
    theory.HistoryStep revisions source target ->
      (revisionGSLT theory).MultiStep source target
  | .nil world =>
      @GSLT.MultiStep.refl (revisionGSLT theory) world
  | .cons step rest =>
      .step (revision_is_step step) (historyToMultiStep rest)

/-- A proposition-valued history proves existence of a proof-relevant path of
the exact named length.  The result remains existential: no path object is
silently reconstructed by eliminating a proposition into data. -/
theorem history_has_exact_executionPath
    {theory : Theory.{u, u, u, u}}
    {revisions : List theory.Revision} {source target : theory.World}
    (history : theory.HistoryStep revisions source target) :
    ∃ path : ExecutionPath (revisionGSLT theory) source target,
      path.length = revisions.length := by
  induction history with
  | nil world => exact ⟨.refl world, rfl⟩
  | cons step rest inductionHypothesis =>
      rcases inductionHypothesis with ⟨path, pathLength⟩
      refine ⟨.cons ⟨revision_is_step step⟩ path, ?_⟩
      simp [Mettapedia.GSLT.Ultrainfinite.Route.length, pathLength]

/-- The existing finite route therefore proves an execution path with one edge
per physical occurrence, while retaining that path only existentially. -/
theorem finiteRoute_has_occurrence_aligned_executionPath
    {theory : Theory.{u, u, u, u}} {Occurrence : Type u}
    {source : theory.World} (route : FiniteRoute theory Occurrence source) :
    ∃ path : ExecutionPath (revisionGSLT theory) source route.target,
      path.length = route.occurrences.length := by
  rcases history_has_exact_executionPath route.execution with
    ⟨path, pathLength⟩
  exact ⟨path, pathLength.trans route.aligned.symm⟩

/-! ## A genuinely path-retaining named history -/

/-- Chronological revision execution as data.  Intermediate worlds and the
constructor spine remain available to later compilation and explanation. -/
inductive NamedHistoryPath (theory : Theory.{u, u, u, u}) :
    List theory.Revision -> theory.World -> theory.World -> Type u where
  | nil (world : theory.World) : NamedHistoryPath theory [] world world
  | cons {revision : theory.Revision} {revisions : List theory.Revision}
      {source middle target : theory.World} :
      PLift (theory.Step revision source middle) ->
      NamedHistoryPath theory revisions middle target ->
      NamedHistoryPath theory (revision :: revisions) source target

namespace NamedHistoryPath

/-- Forget intermediate path data to the established proposition-valued
history. -/
def erase {theory : Theory.{u, u, u, u}}
    {revisions : List theory.Revision} {source target : theory.World} :
    NamedHistoryPath theory revisions source target ->
      theory.HistoryStep revisions source target
  | .nil world => .nil world
  | .cons step rest => .cons step.down rest.erase

/-- Forget revision labels while retaining the complete execution-path
constructor spine. -/
def toExecutionPath {theory : Theory.{u, u, u, u}}
    {revisions : List theory.Revision} {source target : theory.World} :
    NamedHistoryPath theory revisions source target ->
      ExecutionPath (revisionGSLT theory) source target
  | .nil world => .refl world
  | .cons step rest =>
      .cons ⟨revision_is_step step.down⟩ rest.toExecutionPath

/-- A named path has exactly one generated GSLT edge per revision label. -/
@[simp] theorem toExecutionPath_length
    {theory : Theory.{u, u, u, u}}
    {revisions : List theory.Revision} {source target : theory.World}
    (path : NamedHistoryPath theory revisions source target) :
    path.toExecutionPath.length = revisions.length := by
  induction path with
  | nil => rfl
  | cons step rest inductionHypothesis =>
      simp [toExecutionPath, Mettapedia.GSLT.Ultrainfinite.Route.length,
        inductionHypothesis]

/-- Compose named histories while retaining their complete constructor
spines. -/
def append {theory : Theory.{u, u, u, u}}
    {first second : List theory.Revision}
    {source middle target : theory.World} :
    NamedHistoryPath theory first source middle ->
      NamedHistoryPath theory second middle target ->
      NamedHistoryPath theory (first ++ second) source target
  | .nil _, later => later
  | .cons step rest, later => .cons step (rest.append later)

/-- Path projection preserves named-history composition exactly. -/
@[simp] theorem toExecutionPath_append
    {theory : Theory.{u, u, u, u}}
    {first second : List theory.Revision}
    {source middle target : theory.World}
    (earlier : NamedHistoryPath theory first source middle)
    (later : NamedHistoryPath theory second middle target) :
    (earlier.append later).toExecutionPath =
      earlier.toExecutionPath.append later.toExecutionPath := by
  induction earlier with
  | nil => rfl
  | cons step rest inductionHypothesis =>
      simp [append, toExecutionPath,
        Mettapedia.GSLT.Ultrainfinite.Route.append, inductionHypothesis]

/-- Proposition-valued erasure also preserves composition. -/
theorem erase_append
    {theory : Theory.{u, u, u, u}}
    {first second : List theory.Revision}
    {source middle target : theory.World}
    (earlier : NamedHistoryPath theory first source middle)
    (later : NamedHistoryPath theory second middle target) :
    (earlier.append later).erase = earlier.erase.append later.erase := by
  cases earlier <;> rfl

end NamedHistoryPath

/-! ## Occurrence-aligned path-retaining routes -/

/-- A finite semantic route whose execution path is retained as data, aligned
positionally with both physical occurrence identities and revision labels. -/
structure PathRetainingFiniteRoute
    (theory : Theory.{u, u, u, u}) (Occurrence : Type u)
    (source : theory.World) where
  occurrences : List Occurrence
  revisions : List theory.Revision
  target : theory.World
  aligned : occurrences.length = revisions.length
  execution : NamedHistoryPath theory revisions source target

namespace PathRetainingFiniteRoute

/-- Erase only the proof-relevant execution spine into the existing finite
route interface. -/
def erase {theory : Theory.{u, u, u, u}} {Occurrence : Type u}
    {source : theory.World}
    (route : PathRetainingFiniteRoute theory Occurrence source) :
    FiniteRoute theory Occurrence source where
  occurrences := route.occurrences
  revisions := route.revisions
  target := route.target
  aligned := route.aligned
  execution := route.execution.erase

/-- One occurrence, one named revision, and one checked step form an atomic
path-retaining route. -/
def single {theory : Theory.{u, u, u, u}} {Occurrence : Type u}
    {source target : theory.World}
    (occurrence : Occurrence) (revision : theory.Revision)
    (step : theory.Step revision source target) :
    PathRetainingFiniteRoute theory Occurrence source where
  occurrences := [occurrence]
  revisions := [revision]
  target := target
  aligned := rfl
  execution := .cons ⟨step⟩ (.nil target)

/-- Concatenate occurrence identity, named revisions, and execution evidence
together. -/
def append {theory : Theory.{u, u, u, u}} {Occurrence : Type u}
    {source : theory.World}
    (earlier : PathRetainingFiniteRoute theory Occurrence source)
    (later : PathRetainingFiniteRoute theory Occurrence earlier.target) :
    PathRetainingFiniteRoute theory Occurrence source where
  occurrences := earlier.occurrences ++ later.occurrences
  revisions := earlier.revisions ++ later.revisions
  target := later.target
  aligned := by
    simp only [List.length_append]
    rw [earlier.aligned, later.aligned]
  execution := earlier.execution.append later.execution

/-- The direct GSLT-IL execution-path projection. -/
def executionPath {theory : Theory.{u, u, u, u}} {Occurrence : Type u}
    {source : theory.World}
    (route : PathRetainingFiniteRoute theory Occurrence source) :
    ExecutionPath (revisionGSLT theory) source route.target :=
  route.execution.toExecutionPath

/-- Projection preserves the exact number of occurrence positions. -/
@[simp] theorem executionPath_length
    {theory : Theory.{u, u, u, u}} {Occurrence : Type u}
    {source : theory.World}
    (route : PathRetainingFiniteRoute theory Occurrence source) :
    route.executionPath.length = route.occurrences.length := by
  rw [executionPath, NamedHistoryPath.toExecutionPath_length]
  exact route.aligned.symm

/-- Projection turns route append into path-category composition exactly. -/
@[simp] theorem executionPath_append
    {theory : Theory.{u, u, u, u}} {Occurrence : Type u}
    {source : theory.World}
    (earlier : PathRetainingFiniteRoute theory Occurrence source)
    (later : PathRetainingFiniteRoute theory Occurrence earlier.target) :
    (earlier.append later).executionPath =
      earlier.executionPath.append later.executionPath :=
  NamedHistoryPath.toExecutionPath_append earlier.execution later.execution

/-- Erasing after composition agrees with composing the existing finite-route
shadows. -/
theorem erase_append
    {theory : Theory.{u, u, u, u}} {Occurrence : Type u}
    {source : theory.World}
    (earlier : PathRetainingFiniteRoute theory Occurrence source)
    (later : PathRetainingFiniteRoute theory Occurrence earlier.target) :
    (earlier.append later).erase = earlier.erase.append later.erase := by
  apply FiniteRoute.ext <;> rfl

end PathRetainingFiniteRoute

/-! ## The path-retaining route inhabits the loose operational equipment -/

/-- Path-retaining finite revisions as a loose endomorphism of the generated
revision GSLT. -/
def retainedFiniteRoute (theory : Theory.{u, u, u, u})
    (Occurrence : Type u) :
    LooseRoute (revisionGSLT theory) (revisionGSLT theory) :=
  fun source target =>
    { route : PathRetainingFiniteRoute theory Occurrence source //
      route.target = target }

/-- The ordinary execution-path relation on the same generated GSLT. -/
def executionPathRoute (theory : Theory.{u, u, u, u}) :
    LooseRoute (revisionGSLT theory) (revisionGSLT theory) :=
  fun source target => ExecutionPath (revisionGSLT theory) source target

/-- Explicitly erase displayed occurrence and revision identity into the
ordinary execution-path fibre. -/
def retainedToExecutionPathSquare (theory : Theory.{u, u, u, u})
    (Occurrence : Type u) :
    RefinementSquare (tightId (revisionGSLT theory))
      (tightId (revisionGSLT theory))
      (retainedFiniteRoute theory Occurrence)
      (executionPathRoute theory) where
  map witness := by
    rcases witness with ⟨route, rfl⟩
    exact route.executionPath

/-- The equipment cell preserves exact occurrence count. -/
theorem retainedToExecutionPathSquare_length
    {theory : Theory.{u, u, u, u}} {Occurrence : Type u}
    {source target : theory.World}
    (witness : retainedFiniteRoute theory Occurrence source target) :
    ((retainedToExecutionPathSquare theory Occurrence).map witness).length =
      witness.1.occurrences.length := by
  rcases witness with ⟨route, rfl⟩
  exact route.executionPath_length

/-! ## Extensional reachability is the institutional shadow -/

/-- The generated revision GSLT as a signature of the semantic predicate
institution. -/
def revisionSignature (theory : Theory.{u, u, u, u}) :
    ModallyCoveredTheory :=
  { theory := revisionGSLT theory }

/-- Worlds from which a target is reachable by finite generated execution. -/
def reachesTargetSentence (theory : Theory.{u, u, u, u})
    (target : theory.World) : Set theory.World :=
  { source | (revisionGSLT theory).MultiStep source target }

/-- Reachability is invariant under the revision GSLT's equation theory. -/
def reachesTargetEquationPredicate (theory : Theory.{u, u, u, u})
    (target : theory.World) : EquationPredicate (revisionGSLT theory) where
  val := reachesTargetSentence theory target
  property := by
    intro left right equal
    cases equal
    rfl

/-- The same predicate at the exact institutional sentence type. -/
def reachesTargetInstitutionSentence (theory : Theory.{u, u, u, u})
    (target : theory.World) :
    predicateSentence.obj (Opposite.op (revisionSignature theory)) :=
  descendPredicate (revisionGSLT theory)
    (reachesTargetEquationPredicate theory target)

/-- Every existing occurrence-retaining finite route projects to truth of the
target reachability sentence, even though its execution path is only
existential at that interface. -/
theorem finiteRoute_in_reachesTargetSentence
    {theory : Theory.{u, u, u, u}} {Occurrence : Type u}
    {source : theory.World} (route : FiniteRoute theory Occurrence source) :
    source ∈ reachesTargetSentence theory route.target :=
  historyToMultiStep route.execution

/-- Reachability from no premises is an institutional theorem only if every
world reaches the target.  Installing the sentence cannot manufacture global
progress. -/
theorem institution_derives_reachesTarget_iff_all_sources
    (theory : Theory.{u, u, u, u}) (target : theory.World) :
    institution.Derives (Opposite.op (revisionSignature theory)) ∅
        (reachesTargetInstitutionSentence theory target) ↔
      ∀ source : theory.World,
        (revisionGSLT theory).MultiStep source target := by
  rw [derives_iff_entails]
  constructor
  · intro entails source
    exact entails (Quotient.mk (revisionGSLT theory).equations source)
      (by intro predicate impossible; exact False.elim impossible)
  · intro universal sourceClass _
    induction sourceClass using Quotient.inductionOn with
    | _ source => exact universal source

/-! ## Negative control: the path cannot recover displayed identity -/

namespace Canary

def collisionTheory : Theory where
  World := Unit
  Revision := Bool
  Query := Unit
  Observation := Unit
  Step := fun _revision _source _target => True
  query := fun _world _query => ()

def falseRoute : PathRetainingFiniteRoute collisionTheory Nat () :=
  PathRetainingFiniteRoute.single (target := ()) 0 false trivial

def trueRoute : PathRetainingFiniteRoute collisionTheory Nat () :=
  PathRetainingFiniteRoute.single (target := ()) 1 true trivial

def falseWitness : retainedFiniteRoute collisionTheory Nat () () :=
  ⟨falseRoute, rfl⟩

def trueWitness : retainedFiniteRoute collisionTheory Nat () () :=
  ⟨trueRoute, rfl⟩

theorem retained_witnesses_distinct : falseWitness ≠ trueWitness := by
  intro equal
  have occurrencesEqual :
      falseWitness.1.occurrences = trueWitness.1.occurrences :=
    congrArg
      (fun witness : retainedFiniteRoute collisionTheory Nat () () =>
        witness.1.occurrences) equal
  simp [falseWitness, trueWitness, falseRoute, trueRoute,
    PathRetainingFiniteRoute.single] at occurrencesEqual

/-- Revision labels are hidden in the proposition-valued generated step, so
the two one-edge projections are equal by proof irrelevance. -/
theorem projected_paths_equal :
    (retainedToExecutionPathSquare collisionTheory Nat).map falseWitness =
      (retainedToExecutionPathSquare collisionTheory Nat).map trueWitness := by
  simp [retainedToExecutionPathSquare, falseWitness, trueWitness, falseRoute,
    trueRoute, PathRetainingFiniteRoute.single,
    PathRetainingFiniteRoute.executionPath, NamedHistoryPath.toExecutionPath]

/-- The occurrence-retaining loose route is not recoverable from its ordinary
generated-GSLT path. -/
theorem retained_projection_not_injective :
    ¬ Function.Injective
      (fun witness : retainedFiniteRoute collisionTheory Nat () () =>
        (retainedToExecutionPathSquare collisionTheory Nat).map witness) := by
  intro injective
  exact retained_witnesses_distinct (injective projected_paths_equal)

/-- No function of the projected path can recover both exact physical
occurrence lists. -/
theorem occurrences_do_not_factor_through_projected_path :
    ¬ ∃ recover : executionPathRoute collisionTheory () () -> List Nat,
      recover
          ((retainedToExecutionPathSquare collisionTheory Nat).map
            falseWitness) = falseRoute.occurrences ∧
        recover
          ((retainedToExecutionPathSquare collisionTheory Nat).map
            trueWitness) = trueRoute.occurrences := by
  rintro ⟨recover, falseRecovers, trueRecovers⟩
  have equalRecovered := congrArg recover projected_paths_equal
  have occurrencesEqual : falseRoute.occurrences = trueRoute.occurrences :=
    falseRecovers.symm.trans (equalRecovered.trans trueRecovers)
  simp [falseRoute, trueRoute, PathRetainingFiniteRoute.single] at occurrencesEqual

end Canary

#print axioms history_has_exact_executionPath
#print axioms finiteRoute_has_occurrence_aligned_executionPath
#print axioms NamedHistoryPath.toExecutionPath_length
#print axioms NamedHistoryPath.toExecutionPath_append
#print axioms PathRetainingFiniteRoute.executionPath_length
#print axioms PathRetainingFiniteRoute.executionPath_append
#print axioms retainedToExecutionPathSquare_length
#print axioms finiteRoute_in_reachesTargetSentence
#print axioms institution_derives_reachesTarget_iff_all_sources
#print axioms Canary.retained_projection_not_injective
#print axioms Canary.occurrences_do_not_factor_through_projected_path

end Mettapedia.GSLT.LanguageDef.GSLTIL.FiniteRevisionRouteBridge
