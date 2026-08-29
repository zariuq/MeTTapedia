import Mettapedia.GSLT.Core.LinkedInventoryLoader
import Mettapedia.GSLT.Core.TerminatingStreamingRowEmission

/-!
# Linked-inventory emission for terminating streaming GSLTs

A terminating streaming classifier already supplies a source-relative artifact
of target-row occurrences. This module makes the next reified transform
explicit: encode those rows, retain their occurrences, and package the finite
output as an exact linked inventory for a downstream target machine.

This is a data-transform boundary, not a claim that the stream classifier and
the downstream loader have the same state space. Their operational paths stay
separate and are joined only through the inspectable finite artifact.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.RowEmission.LinkedInventory

open Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming
open Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.RowEmission

variable {State Item Stop Class Row Output Result : Type}
variable {stage : Stage State Item Stop Class Row}

/-! ## OSLF/NTT boundary

The stream classifier and the linked inventory deliberately have distinct
state spaces.  The exact artifact below joins them as data; it is not coerced
into a fictitious state-space morphism.  Each actual GSLT instead receives
its own OSLF-native modal account. -/

/-- OSLF's forward native-modal object for the downstream linked-inventory
machine. -/
def inventoryNTT (Output : Type) :
    Mettapedia.OSLF.Framework.IndexedModalFunctor.ForwardModalPredicateTheory :=
  Mettapedia.OSLF.Framework.IndexedModalFunctor.oslfForwardModalObject
    (Mettapedia.GSLT.LinkedInventoryLoader.gslt Output)

/-- The terminating stream's existing path-valued GSLT realization, observed
through OSLF.  This remains separate from `inventoryNTT` until an explicit
state-machine realization is supplied. -/
def sourceReachabilityNTT
    (stage : Stage State Item Stop Class Row) :
    Mettapedia.OSLF.Framework.IndexedModalFunctor.ForwardModalPredicateTheory.Hom
      (Mettapedia.OSLF.Framework.IndexedModalFunctor.oslfForwardModalObject
        (targetGSLT stage).closure)
      (Mettapedia.OSLF.Framework.IndexedModalFunctor.oslfForwardModalObject
        (sourceGSLT stage).closure) :=
  Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.RowEmission.reachabilityNTT
    stage

/-- A later opaque output representation map is an actual linked-loader GSLT
transform, so OSLF supplies its contravariant native-modal map directly. -/
def outputRepresentationNTT (later : Output -> Result) :
    Mettapedia.OSLF.Framework.IndexedModalFunctor.ForwardModalPredicateTheory.Hom
      (inventoryNTT Result) (inventoryNTT Output) :=
  Mettapedia.GSLT.LinkedInventoryLoader.valueMapNTT later

/-- The native-modal account of later output representations composes in the
same order as the exact reified data transformation. -/
theorem outputRepresentationNTT_comp {Final : Type}
    (earlier : Output -> Result) (later : Result -> Final) :
    (outputRepresentationNTT later).comp (outputRepresentationNTT earlier) =
      outputRepresentationNTT (later ∘ earlier) :=
  Mettapedia.GSLT.LinkedInventoryLoader.valueMapNTT_comp earlier later

/-- The output values of a source-relative row artifact. The outer list is
ordered by the artifact's explicit source occurrence sequence. -/
def outputRows (encoder : Row -> Output) (artifact : Artifact stage) :
    List Output :=
  (encodeArtifact encoder artifact).events.map (fun event => event.output)

/-- The linked-row target-data artifact emitted from the supplied stream
artifact. The generic linked-inventory codec is part of this transformation,
not a caller-provided assertion. -/
def linkedArtifact (encoder : Row -> Output) (artifact : Artifact stage) :
    Mettapedia.GSLT.LinkedInventoryLoader.ReifiedArtifact Output :=
  Mettapedia.GSLT.LinkedInventoryLoader.reify (outputRows encoder artifact)

/-- Apply the reified row-to-inventory transform directly to a certified
stream run. Its source and classifier paths remain available through `run`. -/
def lowerRun (encoder : Row -> Output)
    {state : State} {remaining : List Item}
    (run : Run stage state remaining) :
    Mettapedia.GSLT.LinkedInventoryLoader.ReifiedArtifact Output :=
  linkedArtifact encoder run.artifact

/-- Encoding has one output value per emitted source occurrence. -/
theorem outputRows_length (encoder : Row -> Output) (artifact : Artifact stage) :
    (outputRows encoder artifact).length = artifact.events.length := by
  simp [outputRows, encodeArtifact]

/-- The inventory codec decodes the exact encoded output sequence. -/
theorem linkedArtifact_decodes_exact (encoder : Row -> Output)
    (artifact : Artifact stage) :
    Mettapedia.GSLT.LinkedInventoryLoader.decodeInventory?
      (linkedArtifact encoder artifact).target =
        some (outputRows encoder artifact) := by
  exact Mettapedia.GSLT.LinkedInventoryLoader.decodeInventory?_reify
    (outputRows encoder artifact)

/-- Reified linked rows have one target occurrence per emitted source event. -/
theorem linkedArtifact_length (encoder : Row -> Output)
    (artifact : Artifact stage) :
    (linkedArtifact encoder artifact).target.length = artifact.events.length := by
  change (Mettapedia.GSLT.LinkedInventoryLoader.encodeInventory
    (outputRows encoder artifact)).length = artifact.events.length
  rw [Mettapedia.GSLT.LinkedInventoryLoader.encodeInventory_length]
  exact outputRows_length encoder artifact

/-- A downstream opaque-value transform distributes through source-relative
row emission. This is the data-level composition law used when a later MM2
adapter changes a classifier row into its target representation. -/
theorem outputRows_map (encoder : Row -> Output) (later : Output -> Result)
    (artifact : Artifact stage) :
    (outputRows encoder artifact).map later =
      outputRows (later ∘ encoder) artifact := by
  simp [outputRows, encodeArtifact, encodeEvent, Function.comp_def,
    List.map_map]

/-- Successive reified transforms compose without dropping source positions,
row cardinality, or linked-row cursor discipline. -/
theorem linkedArtifact_map (encoder : Row -> Output) (later : Output -> Result)
    (artifact : Artifact stage) :
    (linkedArtifact encoder artifact).map later =
      linkedArtifact (later ∘ encoder) artifact := by
  simp only [linkedArtifact]
  rw [
    Mettapedia.GSLT.LinkedInventoryLoader.reify_map,
    outputRows_map]

/-- The certified stream run's emitted inventory is exact at the same
source-relative boundary. -/
theorem lowerRun_decodes_exact (encoder : Row -> Output)
    {state : State} {remaining : List Item}
    (run : Run stage state remaining) :
    Mettapedia.GSLT.LinkedInventoryLoader.decodeInventory?
      (lowerRun encoder run).target =
        some (outputRows encoder run.artifact) :=
  linkedArtifact_decodes_exact encoder run.artifact

/-- A later value representation may be changed after the terminating stream
has run, and the resulting linked data remain exactly compositional. -/
theorem lowerRun_map (encoder : Row -> Output) (later : Output -> Result)
    {state : State} {remaining : List Item}
    (run : Run stage state remaining) :
    (lowerRun encoder run).map later =
      lowerRun (later ∘ encoder) run :=
  linkedArtifact_map encoder later run.artifact

#print axioms inventoryNTT
#print axioms sourceReachabilityNTT
#print axioms outputRepresentationNTT
#print axioms outputRepresentationNTT_comp
#print axioms outputRows_length
#print axioms linkedArtifact_decodes_exact
#print axioms linkedArtifact_length
#print axioms outputRows_map
#print axioms linkedArtifact_map
#print axioms lowerRun_decodes_exact
#print axioms lowerRun_map

end Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.RowEmission.LinkedInventory
