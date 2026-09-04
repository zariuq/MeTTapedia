import Mettapedia.TypeTheory.CategoryIndexedFamilyCwf
import Mettapedia.GSLT.Core.ProofRelevantGSLT
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.TypedCommunicationProtocol
import Mettapedia.GraphTheory.Walk.ModeCellProofThinnessBoundary

/-!
# Proof-relevant route families for rho communication and graph walks

The category-indexed family CwF becomes operational when its morphisms are
actual proof objects.  This module supplies two such contexts:

* finite paths of revision-tagged, typed rho COMM occurrences;
* native graph reachability proofs, with composition given by walk append.

For either context, the dependent family at a state consists of retained
proofs from a fixed source to that state.  Transport is path composition.
The rho zero/one-revision receipts and the graph direct/detour proofs induce
different transport maps.  By the exact thin-descent criterion, neither
family can be reduced to proposition-valued route support.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ProofRelevantRouteFamilyBridge

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.ProofRelevant
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.TypeTheory.CategoryIndexedFamilyCwf

universe u

/-! ## The free path category of a proof-relevant GSLT -/

/-- A distinct context carrier for the states of a proof-relevant GSLT. -/
def EvidenceObject (system : ProofRelevantGSLT.{u}) :=
  system.theory.Term

/-- Finite paths retain every authored step-evidence occurrence. -/
abbrev EvidencePath (system : ProofRelevantGSLT.{u})
    (source target : EvidenceObject system) :=
  Route system.steps.Evidence source target

instance evidencePathCategory (system : ProofRelevantGSLT.{u}) :
    CategoryTheory.Category (EvidenceObject system) where
  Hom := EvidencePath system
  id point := .refl point
  comp earlier later := earlier.append later
  id_comp route := Route.refl_append route
  comp_id route := Route.append_refl route
  assoc first second third := Route.append_assoc first second third

/-- The free evidence-path category as a proof-relevant CwF context. -/
abbrev evidenceContext (system : ProofRelevantGSLT.{u}) :
    Context.{u} :=
  CategoryTheory.Cat.of (EvidenceObject system)

/-- The category-indexed family of retained evidence paths from one state. -/
def evidencePathFamily (system : ProofRelevantGSLT.{u})
    (start : EvidenceObject system) :
    IndexedFamily (evidenceContext system) where
  obj finish := EvidencePath system start finish
  map suffix := TypeCat.ofHom (fun initialPath => initialPath.append suffix)
  map_id finish := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext initialPath
    exact Route.append_refl initialPath
  map_comp first second := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext initialPath
    change initialPath.append (first.append second) =
      (initialPath.append first).append second
    exact (Route.append_assoc initialPath first second).symm

/-! ## Revision-tagged typed rho communication -/

namespace Rho

open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.TypedCommunicationProtocol
open Mettapedia.GSLT.Dynamics.ProofRelevantRelationProtocol

/-- One rho step retains both its semantic revision and its exact typed
strict-core COMM occurrence. -/
def revisionedTypedCommSteps : StepEvidence typedCommSystem where
  Evidence source target := Nat × StrictCoreCommOccurrence source target
  erases_iff source target := by
    constructor
    · rintro ⟨revision, occurrence⟩
      exact (lts_step_iff StrictCoreCommOccurrence).2 ⟨occurrence⟩
    · intro step
      obtain ⟨occurrence⟩ :=
        (lts_step_iff StrictCoreCommOccurrence).1 step
      exact ⟨0, occurrence⟩

/-- The typed direct-communication GSLT with revision-sensitive evidence. -/
def revisionedTypedCommSystem : ProofRelevantGSLT :=
  ⟨typedCommSystem, revisionedTypedCommSteps⟩

abbrev CommunicationObject := EvidenceObject revisionedTypedCommSystem

abbrev CommunicationPath (source target : CommunicationObject) :=
  EvidencePath revisionedTypedCommSystem source target

/-- The proof-relevant communication context. -/
abbrev communicationContext : Context.{0} :=
  evidenceContext revisionedTypedCommSystem

/-- The representable dependent family of typed communication histories from
the selected closed COMM source. -/
def communicationHistoryFamily : IndexedFamily communicationContext :=
  evidencePathFamily revisionedTypedCommSystem closedNilCommData.source

/-- A one-step typed communication path at revision zero. -/
noncomputable def zeroRevisionPath :
    CommunicationPath closedNilCommData.source closedNilCommData.target :=
  .cons (0, closedNilCommOccurrence) (.refl closedNilCommData.target)

/-- The same typed communication occurrence retained at revision one. -/
noncomputable def oneRevisionPath :
    CommunicationPath closedNilCommData.source closedNilCommData.target :=
  .cons (1, closedNilCommOccurrence) (.refl closedNilCommData.target)

/-- Read the first revision from a nonempty retained communication history. -/
def firstRevision {source target : CommunicationObject} :
    CommunicationPath source target → Option Nat
  | .refl _ => none
  | .cons evidence _ => some evidence.1

@[simp] theorem zeroRevisionPath_firstRevision :
    firstRevision zeroRevisionPath = some 0 :=
  rfl

@[simp] theorem oneRevisionPath_firstRevision :
    firstRevision oneRevisionPath = some 1 :=
  rfl

/-- The two paths have the same source, target, and typed occurrence, but
remain distinct because their semantic revisions differ. -/
theorem zeroRevisionPath_ne_oneRevisionPath :
    zeroRevisionPath ≠ oneRevisionPath := by
  intro equality
  have observed := congrArg firstRevision equality
  simp at observed

/-- Transporting the identity history along the two parallel receipts yields
different dependent results. -/
theorem communicationHistoryFamily_distinguishes_revisions :
    communicationHistoryFamily.map zeroRevisionPath
        (.refl closedNilCommData.source) ≠
      communicationHistoryFamily.map oneRevisionPath
        (.refl closedNilCommData.source) := by
  change zeroRevisionPath ≠ oneRevisionPath
  exact zeroRevisionPath_ne_oneRevisionPath

/-- The authentic revision-sensitive rho family cannot descend to mere
existence of a path between its endpoints. -/
theorem communicationHistoryFamily_does_not_descend :
    ¬ Nonempty (ThinDescent communicationHistoryFamily) := by
  intro descended
  have invariant : ParallelInvariant communicationHistoryFamily :=
    (ThinDescent.nonempty_iff_parallelInvariant
      communicationHistoryFamily).1 descended
  exact communicationHistoryFamily_distinguishes_revisions
    (invariant
      (source := closedNilCommData.source)
      (target := closedNilCommData.target)
      zeroRevisionPath oneRevisionPath (.refl closedNilCommData.source))

end Rho

/-! ## Native graph reachability proofs -/

namespace Graph

open Mettapedia.GraphTheory.Walk.ProofTheory
open Mettapedia.GraphTheory.Walk.ModeCellProofThinnessBoundary
open Mettapedia.GraphTheory.Walk.Examples
open SimpleGraph

/-- A graph vertex tagged by the graph whose native proofs will be its
morphisms. -/
structure NativeProofObject {n : Nat} (graph : SimpleGraph (Fin n)) where
  vertex : Fin n

/-- Insert an ordinary vertex into its graph-specific proof context. -/
def nativeProofObject {n : Nat} (graph : SimpleGraph (Fin n))
    (vertex : Fin n) : NativeProofObject graph :=
  ⟨vertex⟩

/-- Native graph proofs form a proof-relevant category under walk append. -/
instance nativeProofCategory {n : Nat} (graph : SimpleGraph (Fin n))
    [DecidableRel graph.Adj] :
    CategoryTheory.Category (NativeProofObject graph) where
  Hom source target := NativeProof graph source.vertex target.vertex
  id point := NativeProof.identity graph point.vertex
  comp earlier later := earlier.comp later
  id_comp proof := NativeProof.identity_comp proof
  comp_id proof := NativeProof.comp_identity proof
  assoc first second third :=
    (NativeProof.comp_assoc first second third).symm

/-- The native-proof category as a proof-relevant CwF context. -/
abbrev nativeProofContext {n : Nat} (graph : SimpleGraph (Fin n))
    [DecidableRel graph.Adj] : Context.{0} :=
  CategoryTheory.Cat.of (NativeProofObject graph)

/-- The category-indexed family of native reachability proofs from a fixed
start vertex. -/
def nativeProofFamily {n : Nat} (graph : SimpleGraph (Fin n))
    [DecidableRel graph.Adj] (start : Fin n) :
    IndexedFamily (nativeProofContext graph) where
  obj finish := NativeProof graph start finish.vertex
  map suffix := TypeCat.ofHom (fun initialProof => initialProof.comp suffix)
  map_id finish := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext initialProof
    exact NativeProof.comp_identity initialProof
  map_comp first second := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext initialProof
    exact NativeProof.comp_assoc initialProof first second

/-- The authentic path-graph family rooted at vertex zero. -/
def pathGraphProofFamily : IndexedFamily (nativeProofContext pathGraph) :=
  nativeProofFamily pathGraph vertex0

/-- Transporting the identity proof along the direct and detour paths
recovers those distinct native proofs. -/
theorem pathGraphProofFamily_distinguishes_work :
    pathGraphProofFamily.map directProof
        (NativeProof.identity pathGraph vertex0) ≠
      pathGraphProofFamily.map detourProof
        (NativeProof.identity pathGraph vertex0) := by
  change
    (NativeProof.identity pathGraph vertex0).comp directProof ≠
      (NativeProof.identity pathGraph vertex0).comp detourProof
  intro equality
  apply directProof_ne_detourProof
  calc
    directProof =
        (NativeProof.identity pathGraph vertex0).comp directProof :=
      (NativeProof.identity_comp directProof).symm
    _ = (NativeProof.identity pathGraph vertex0).comp detourProof := equality
    _ = detourProof := NativeProof.identity_comp detourProof

/-- Exact path work therefore prevents descent to reachability-as-a-
proposition. -/
theorem pathGraphProofFamily_does_not_descend :
    ¬ Nonempty (ThinDescent pathGraphProofFamily) := by
  intro descended
  have invariant : ParallelInvariant pathGraphProofFamily :=
    (ThinDescent.nonempty_iff_parallelInvariant pathGraphProofFamily).1
      descended
  exact pathGraphProofFamily_distinguishes_work
    (invariant
      (source := nativeProofObject pathGraph vertex0)
      (target := nativeProofObject pathGraph vertex2)
      directProof detourProof (NativeProof.identity pathGraph vertex0))

end Graph

/-! ## Axiom audit -/

#print axioms evidencePathFamily
#print axioms Rho.revisionedTypedCommSteps
#print axioms Rho.zeroRevisionPath_ne_oneRevisionPath
#print axioms Rho.communicationHistoryFamily_does_not_descend
#print axioms Graph.nativeProofCategory
#print axioms Graph.pathGraphProofFamily_does_not_descend

end Mettapedia.TypeTheory.ProofRelevantRouteFamilyBridge
