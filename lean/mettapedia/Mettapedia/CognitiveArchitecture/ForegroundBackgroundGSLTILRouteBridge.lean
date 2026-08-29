import Mettapedia.CognitiveArchitecture.ForegroundBackgroundSemanticRouteBinding
import Mettapedia.GSLT.LanguageDef.GSLTILFiniteRevisionRouteBridge

/-!
# Foreground/background execution in the GSLT-IL operational waist

The foreground chaining step and background premise-index refresh already form
a physically bound, serializable two-occurrence article.  This module retains
that article's chronological execution as proof-relevant data and maps it into
the common GSLT-IL operational equipment.

The positive bridge relates all four relevant views of the same execution:

* the certified bulk wave;
* the physical occurrence route;
* the named semantic revision history;
* the generated GSLT execution path and reachability sentence.

The shifted physical article is a negative control.  It has the same semantic
revisions and terminal state but different occurrence identities.  Both
articles therefore induce the same ordinary execution path, while remaining
distinct in the occurrence-retaining route fibre.  Operational explanation
does not collapse physical provenance.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.ForegroundBackgroundGSLTILRouteBridge

open Mettapedia.CognitiveArchitecture.ForegroundBackgroundParallelWave
open Mettapedia.CognitiveArchitecture.ForegroundBackgroundSemanticRouteBinding
open Mettapedia.CognitiveArchitecture.ProtectedForegroundBackgroundNIKArticle
open Mettapedia.GSLT.Dynamics.OperatorRealization
open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.GSLTIL.FiniteRevisionRouteBridge
open Mettapedia.GSLT.LanguageDef.GSLTIL.OperationalEquipment
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKDefaultProfile

noncomputable section

/-! ## The actual foreground/background route as retained data -/

/-- The physical foreground occurrence and its exact semantic revision. -/
def retainedForegroundRoute :
    PathRetainingFiniteRoute WorkspaceTheory (OccurrenceId Unit Nat)
      initialWorkspace :=
  PathRetainingFiniteRoute.single
    (target := workspaceStep initialWorkspace .foregroundBridge)
    foregroundPhysicalOccurrence .foregroundBridge rfl

/-- The physical index-refresh occurrence and its exact semantic revision. -/
def retainedIndexerRoute :
    PathRetainingFiniteRoute WorkspaceTheory (OccurrenceId Unit Nat)
      retainedForegroundRoute.target :=
  PathRetainingFiniteRoute.single
    (target := semanticTarget physicalClaim)
    indexerPhysicalOccurrence .refreshPremiseIndex rfl

/-- The complete proof-relevant route of the useful two-occurrence article. -/
def retainedUsefulRoute :
    PathRetainingFiniteRoute WorkspaceTheory (OccurrenceId Unit Nat)
      initialWorkspace :=
  retainedForegroundRoute.append retainedIndexerRoute

/-- The stronger route erases exactly to the established physically bound
finite route; it is not a parallel reconstruction of the article. -/
theorem retainedUsefulRoute_erases_to_bound :
    retainedUsefulRoute.erase = usefulFiniteBoundRoute.route := by
  rw [useful_finite_route_decomposes]
  exact PathRetainingFiniteRoute.erase_append
    retainedForegroundRoute retainedIndexerRoute

/-- The chronological explanation contains exactly the two authored physical
occurrences. -/
@[simp] theorem retainedUsefulRoute_executionPath_length :
    retainedUsefulRoute.executionPath.length = 2 := by
  calc
    retainedUsefulRoute.executionPath.length =
        retainedUsefulRoute.occurrences.length :=
      PathRetainingFiniteRoute.executionPath_length retainedUsefulRoute
    _ = 2 := rfl

/-- The GSLT path is exactly foreground composition followed by background
index refresh. -/
theorem retainedUsefulRoute_executionPath_decomposes :
    retainedUsefulRoute.executionPath =
      retainedForegroundRoute.executionPath.append
        retainedIndexerRoute.executionPath :=
  PathRetainingFiniteRoute.executionPath_append
    retainedForegroundRoute retainedIndexerRoute

/-- The useful article as a witness in the occurrence-retaining loose route. -/
def retainedUsefulWitness :
    retainedFiniteRoute WorkspaceTheory (OccurrenceId Unit Nat)
      initialWorkspace (semanticTarget physicalClaim) :=
  ⟨retainedUsefulRoute, rfl⟩

/-- The equipment cell forgets displayed route identity while preserving the
exact two-step execution spine. -/
theorem retainedUsefulWitness_projects_two_steps :
    ((retainedToExecutionPathSquare WorkspaceTheory
      (OccurrenceId Unit Nat)).map retainedUsefulWitness).length = 2 := by
  calc
    ((retainedToExecutionPathSquare WorkspaceTheory
      (OccurrenceId Unit Nat)).map retainedUsefulWitness).length =
        retainedUsefulWitness.1.occurrences.length :=
      retainedToExecutionPathSquare_length retainedUsefulWitness
    _ = 2 := rfl

/-- The same execution simultaneously earns bulk admission, inhabits the
GSLT-IL path fibre, and satisfies the target-reachability sentence. -/
theorem certified_parallel_wave_enters_operational_waist :
    (wave.certified.plan .general).activation = .bulk ∧
      ((retainedToExecutionPathSquare WorkspaceTheory
        (OccurrenceId Unit Nat)).map retainedUsefulWitness).length = 2 ∧
      initialWorkspace ∈
        reachesTargetSentence WorkspaceTheory (semanticTarget physicalClaim) := by
  refine ⟨wave.completeBag_dispatches_bulk rfl,
    retainedUsefulWitness_projects_two_steps, ?_⟩
  exact finiteRoute_in_reachesTargetSentence retainedUsefulRoute.erase

/-- NIK acceptance and the operational account share the same physically
bound article.  Hosting does not bypass the route or invent a second execution
semantics. -/
theorem nik_hosted_parallel_wave_enters_operational_waist :
    workspaceRouteFrontend.run
        (workspaceRouteFrontend.encode usefulRouteSubmission) =
      SubmissionOutcome.accepted
        (TypedSubmission.claim usefulRouteSubmission) ∧
      (wave.certified.plan .general).activation = .bulk ∧
      ((retainedToExecutionPathSquare WorkspaceTheory
        (OccurrenceId Unit Nat)).map retainedUsefulWitness).length = 2 ∧
      initialWorkspace ∈
        reachesTargetSentence WorkspaceTheory (semanticTarget physicalClaim) :=
  ⟨useful_route_article_defaultNIK_accepts,
    certified_parallel_wave_enters_operational_waist⟩

/-! ## Real provenance collision after path projection -/

/-- The shifted foreground occurrence performs the same semantic revision. -/
def retainedShiftedForegroundRoute :
    PathRetainingFiniteRoute WorkspaceTheory (OccurrenceId Unit Nat)
      initialWorkspace :=
  PathRetainingFiniteRoute.single
    (target := workspaceStep initialWorkspace .foregroundBridge)
    shiftedForegroundOccurrence .foregroundBridge rfl

/-- The shifted index occurrence performs the same semantic revision. -/
def retainedShiftedIndexerRoute :
    PathRetainingFiniteRoute WorkspaceTheory (OccurrenceId Unit Nat)
      retainedShiftedForegroundRoute.target :=
  PathRetainingFiniteRoute.single
    (target := semanticTarget physicalClaim)
    shiftedIndexerOccurrence .refreshPremiseIndex rfl

/-- The shifted physical article retains its distinct occurrence route. -/
def retainedShiftedRoute :
    PathRetainingFiniteRoute WorkspaceTheory (OccurrenceId Unit Nat)
      initialWorkspace :=
  retainedShiftedForegroundRoute.append retainedShiftedIndexerRoute

def retainedShiftedWitness :
    retainedFiniteRoute WorkspaceTheory (OccurrenceId Unit Nat)
      initialWorkspace (semanticTarget physicalClaim) :=
  ⟨retainedShiftedRoute, rfl⟩

theorem retained_witnesses_have_distinct_occurrences :
    retainedUsefulWitness.1.occurrences ≠
      retainedShiftedWitness.1.occurrences := by
  decide

theorem retained_witnesses_distinct :
    retainedUsefulWitness ≠ retainedShiftedWitness := by
  intro equal
  exact retained_witnesses_have_distinct_occurrences
    (congrArg (fun witness => witness.1.occurrences) equal)

/-- The generated GSLT path explains semantic chronology, not physical store
position.  The two real articles therefore have the same projected path. -/
theorem projected_execution_paths_equal :
    (retainedToExecutionPathSquare WorkspaceTheory
      (OccurrenceId Unit Nat)).map retainedUsefulWitness =
    (retainedToExecutionPathSquare WorkspaceTheory
      (OccurrenceId Unit Nat)).map retainedShiftedWitness := by
  rfl

/-- The operational-waist projection is genuinely non-faithful even on the
worked foreground/background articles. -/
theorem actual_retained_projection_not_injective :
    ¬ Function.Injective
      (fun witness : retainedFiniteRoute WorkspaceTheory
          (OccurrenceId Unit Nat) initialWorkspace
          (semanticTarget physicalClaim) =>
        (retainedToExecutionPathSquare WorkspaceTheory
          (OccurrenceId Unit Nat)).map witness) := by
  intro injective
  exact retained_witnesses_distinct
    (injective projected_execution_paths_equal)

/-- Neither the terminal observation nor the projected semantic path can
reconstruct physical occurrence identity. -/
theorem observation_and_path_do_not_recover_occurrence_route :
    Not (Exists fun recover :
        Option WorkspaceView -> List (OccurrenceId Unit Nat) =>
      recover (workspaceCodec.toFinite.result? physicalClaim) =
          usefulFiniteBoundRoute.route.occurrences ∧
        recover (workspaceCodec.toFinite.result? shiftedPhysicalClaim) =
          shiftedFiniteBoundRoute.route.occurrences) ∧
      ¬ Function.Injective
        (fun witness : retainedFiniteRoute WorkspaceTheory
            (OccurrenceId Unit Nat) initialWorkspace
            (semanticTarget physicalClaim) =>
          (retainedToExecutionPathSquare WorkspaceTheory
            (OccurrenceId Unit Nat)).map witness) :=
  ⟨finite_terminal_observation_does_not_recover_occurrence_route,
    actual_retained_projection_not_injective⟩

#print axioms retainedUsefulRoute_erases_to_bound
#print axioms retainedUsefulRoute_executionPath_decomposes
#print axioms certified_parallel_wave_enters_operational_waist
#print axioms nik_hosted_parallel_wave_enters_operational_waist
#print axioms retained_witnesses_have_distinct_occurrences
#print axioms projected_execution_paths_equal
#print axioms actual_retained_projection_not_injective
#print axioms observation_and_path_do_not_recover_occurrence_route

end

end Mettapedia.CognitiveArchitecture.ForegroundBackgroundGSLTILRouteBridge
