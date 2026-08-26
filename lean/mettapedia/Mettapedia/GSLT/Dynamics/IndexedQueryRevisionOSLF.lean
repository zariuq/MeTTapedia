import Mettapedia.GSLT.Dynamics.IndexedQueryRevision
import Mettapedia.OSLF.Framework.IndexedModalFunctor

/-!
# Indexed OSLF for growing query/revision theories

Theory growth and world revision are distinct axes.  `IndexedQueryRevision`
already sends a growing query/revision family to an operational GSLT diagram.
This module applies indexed OSLF to that generated diagram.

The result is intentionally lax.  A later theory stage may introduce new
revision events at a transported world, so old possibilities persist while
new possibilities need not reflect into the earlier stage.  Query naturality
continues to be carried by the original stage translation; it is not erased
into the proposition-valued step relation.
-/

namespace Mettapedia.GSLT.Dynamics.IndexedQueryRevision

open CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.IndexedModalFunctor

universe uWorld uRevision uQuery uObservation uIndex vIndex

/-- Pointwise OSLF/NTT for a growing query/revision family.  The index is
opposed because native predicates pull back along stage translations. -/
def Diagram.indexedOSLF
    {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]
    (diagram : Diagram Index) :
    CategoryTheory.Functor Indexᵒᵖ
      ForwardModalPredicateTheory.{uWorld} :=
  forwardIndexedOSLF diagram.toOperational

@[simp] theorem Diagram.indexedOSLF_obj
    {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]
    (diagram : Diagram Index)
    (stage : Index) :
    diagram.indexedOSLF.obj (Opposite.op stage) =
      oslfForwardModalObject (revisionGSLT (diagram.obj stage).theory) :=
  rfl

/-- Forward theory growth preserves every old revision possibility. -/
theorem Diagram.revision_diamond_lax
    {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]
    (diagram : Diagram Index)
    {sourceStage targetStage : Index} (route : sourceStage ⟶ targetStage)
    (predicate : Set (diagram.obj targetStage).theory.World) :
    gsltDiamond (revisionGSLT (diagram.obj sourceStage).theory)
        (Set.preimage (diagram.map route).mapWorld predicate) <=
      Set.preimage (diagram.map route).mapWorld
        (gsltDiamond (revisionGSLT (diagram.obj targetStage).theory)
          predicate) :=
  OperationalTranslation.preimage_diamond_le
    (diagram.map route).toOperational predicate

/-- The dual must-law surviving forward theory growth: if the transported
world satisfies a target box, then the source world satisfies the pulled-back
box. -/
theorem Diagram.revision_box_lax
    {Index : Type uIndex} [CategoryTheory.Category.{vIndex} Index]
    (diagram : Diagram Index)
    {sourceStage targetStage : Index} (route : sourceStage ⟶ targetStage)
    (predicate : Set (diagram.obj targetStage).theory.World) :
    Set.preimage (diagram.map route).mapWorld
        (gsltBox (revisionGSLT (diagram.obj targetStage).theory) predicate) <=
      gsltBox (revisionGSLT (diagram.obj sourceStage).theory)
        (Set.preimage (diagram.map route).mapWorld predicate) :=
  OperationalTranslation.preimage_box_le
    (diagram.map route).toOperational predicate

/-- A named revision occurrence inhabits the exact native target predicate
generated in its own theory fibre. -/
theorem revision_inhabits_exactTargetNativeType
    {theory : QueryRevision.Theory.{uWorld, uRevision, uQuery, uObservation}}
    {revision : theory.Revision} {source target : theory.World}
    (step : theory.Step revision source target) :
    (gsltOSLF (revisionGSLT theory)).satisfies source
      (exactTargetNativeType (revisionGSLT theory) target).pred := by
  apply (satisfies_exactTargetNativeType_iff_step
    (revisionGSLT theory) source target).2
  exact revision_is_step step

section AxiomAudit

#print axioms Diagram.indexedOSLF
#print axioms Diagram.revision_diamond_lax
#print axioms Diagram.revision_box_lax
#print axioms revision_inhabits_exactTargetNativeType

end AxiomAudit

end Mettapedia.GSLT.Dynamics.IndexedQueryRevision
