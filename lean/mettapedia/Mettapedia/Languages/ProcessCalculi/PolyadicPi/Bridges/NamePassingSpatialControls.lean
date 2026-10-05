import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingSpine
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnarySpatial

/-!
# Spatial readout of actual lambda-compiler prefixes

The complete compiler's existing prefix receipt supplies the occurrence
witness consumed by spatial transport. Duplicate activity occurrences remain
two components. The cuts describe supplied runtime states; no independence,
purse funding or unrestricted extension theorem is inferred from them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingSpatialControls

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.RhoBagReactiveSystem
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.OSLF.StructuralModal.SeparatingConjunction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open NamePassingLambda RhoUnaryActive RhoUnaryWorld RhoUnaryReadback RhoUnarySpatial

/-- The arbitrary supplied target prefix has an actual occurrence readout
and every spatial cut agrees with it, at its literal final endpoint. -/
theorem every_lambda_prefix_has_spatial_readout {Γ : Ctx sig} (source : Expr Γ)
    (world : NamePassingSpine.World Γ) (code : RhoUnaryCode.Code 0)
    (supplied : NamePassingRho.compile source (NamePassingUnaryForward.references Γ) .zero
      world.world = some code)
    {final : TargetProcess} (actual : ExecutionPath Target (runtimeProcess code world.available) final) :
    ∃ (Δ : Ctx sig) (phaseWorld : SeedWorld Δ) (activities : List (Activity Δ)),
      components final.1 = resourceMap phaseWorld.world (activities : Multiset (Activity Δ)) ∧
      (components final.1).card = activities.length ∧
      ∀ P Q : Multiset Pattern → Prop,
        SepConj StructuralCongruence .hashBag (fun process => P (components process))
          (fun process => Q (components process)) final.1 ↔
        sepConj ((resourceMap phaseWorld.world).pull P) ((resourceMap phaseWorld.world).pull Q)
          (activities : Multiset (Activity Δ)) := by
  obtain ⟨receipt⟩ := NamePassingSpine.compiled_prefix_accounted source world code supplied actual
  refine ⟨receipt.rho.context, receipt.rho.world, receipt.rho.activities,
    witness_components receipt.rho, ?_, witness_cut_iff receipt.rho⟩
  rw [witness_components receipt.rho]
  exact (Multiset.card_map _ _).trans (Multiset.coe_card _)

/-- The actual emitter retains two equal occurrences, even if their
canonical names and complete messages are equal. -/
theorem duplicate_activity_components {Γ : Ctx sig}
    (world : RhoUnaryCompiler.World Γ 0) (activity : Activity Γ) :
    components (RhoUnaryActive.actual world [activity, activity]) =
      {atomImage world activity, atomImage world activity} ∧
      (components (RhoUnaryActive.actual world [activity, activity])).card = 2 := by
  refine ⟨?_, actual_card world [activity, activity]⟩
  rw [actual_components]
  simp [resourceMap, Mettapedia.GSLT.Logic.SeparationTransport.bagMap]
  rfl

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingSpatialControls
