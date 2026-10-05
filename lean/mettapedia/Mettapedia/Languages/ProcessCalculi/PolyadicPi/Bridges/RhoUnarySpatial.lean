import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryReadback
import Mettapedia.GSLT.Logic.SeparationTransport
import Mettapedia.OSLF.Bridges.GSLT.RhoSeparation

/-!
# Spatial observations of the compiler's actual runtime phases

Every retained activity is one actual input/output header occurrence. Its
canonical component map lifts every bag split, including duplicate headers.
Consequently the existing OSLF spatial cut is exactly the separating predicate
of the supplied runtime witness's activity occurrences. This covers allocator,
tuple-protocol and persistent-server phases, not only flat guest networks.

Extension lifting is a separate obligation. Dropped-name processes provide
compatible rho extensions outside this header image, so unrestricted wands
do not transport. Cuts by themselves do not imply operational independence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnarySpatial

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.RhoBagReactiveSystem
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.SeparationTransport
open Mettapedia.OSLF.StructuralModal.SeparatingConjunction
open Mettapedia.OSLF.Bridges.GSLT.RhoSeparation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalStepperCompleteness
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open RhoUnaryActive RhoUnaryCode RhoUnaryCompiler RhoUnaryWorld RhoUnaryReadback

noncomputable def atomImage {Γ : Ctx sig} (world : World Γ 0) (activity : Activity Γ) : Pattern :=
  canonicalize (activity.header world).pattern

noncomputable def resourceMap {Γ : Ctx sig} (world : World Γ 0) :
    Hom (Multiset (Activity Γ)) (Multiset Pattern) := bagMap (atomImage world)

theorem activity_components {Γ : Ctx sig} (world : World Γ 0) (activity : Activity Γ) :
    components (activity.header world).pattern = {atomImage world activity} := by
  unfold atomImage
  generalize activity.header world = header
  cases header with
  | input channel body =>
      simpa only [HeaderInversion.Header.pattern, canonicalize_input] using components_input channel body
  | output channel payload =>
      simpa only [HeaderInversion.Header.pattern, canonicalize_output] using components_output channel payload

theorem actual_components {Γ : Ctx sig} (world : World Γ 0) (activities : List (Activity Γ)) :
    components (actual world activities) = resourceMap world (activities : Multiset (Activity Γ)) := by
  rw [actual, HeaderInversion.parallel, components_parallel]
  simp only [headers, List.map_map]
  induction activities with
  | nil => rfl
  | cons activity rest ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp_apply]
      rw [activity_components, ih]
      change {atomImage world activity} + (rest : Multiset (Activity Γ)).map (atomImage world) =
        (activity ::ₘ (rest : Multiset (Activity Γ))).map (atomImage world)
      rw [Multiset.map_cons, Multiset.singleton_add]

theorem actual_card {Γ : Ctx sig} (world : World Γ 0) (activities : List (Activity Γ)) :
    (components (actual world activities)).card = activities.length := by
  rw [actual_components]
  exact (Multiset.card_map _ _).trans (Multiset.coe_card _)

theorem pull_sepConj {Γ : Ctx sig} (world : World Γ 0) (P Q : Multiset Pattern → Prop) :
    (resourceMap world).pull (sepConj P Q) =
      sepConj ((resourceMap world).pull P) ((resourceMap world).pull Q) :=
  bagMap_pull_sepConj (atomImage world) P Q

theorem witness_components {Γ : Ctx sig} {world : SeedWorld Γ} {origin : Proc Γ}
    {current : TargetProcess} (witness : Witness world origin current) :
    components current.1 = resourceMap witness.world.world
      (witness.activities : Multiset (Activity witness.context)) := by
  have same : components current.1 = components (actual witness.world.world witness.activities) :=
    components_eq_iff_canonicalize_eq.mpr witness.endpoint
  exact same.trans (actual_components witness.world.world witness.activities)

/-- The comparison uses the independently supplied target endpoint and its
retained phase witness; it does not substitute an alternate compiler image. -/
theorem witness_cut_iff {Γ : Ctx sig} {world : SeedWorld Γ} {origin : Proc Γ}
    {current : TargetProcess} (witness : Witness world origin current) (P Q : Multiset Pattern → Prop) :
    SepConj StructuralCongruence .hashBag (fun process => P (components process))
      (fun process => Q (components process)) current.1 ↔
    sepConj ((resourceMap witness.world.world).pull P) ((resourceMap witness.world.world).pull Q)
      (witness.activities : Multiset (Activity witness.context)) := by
  have pure := PureBoundary.rhoProcWellSorted_hashSetFree
    ((ParameterizedRewriteSystem.process_iff _ _).mp current.2).1
  rw [sepConj_iff_components P Q pure, witness_components witness]
  exact congrFun (pull_sepConj witness.world.world P Q)
    (witness.activities : Multiset (Activity witness.context)) |>.to_iff

theorem atomImage_ne_drop {Γ : Ctx sig} (world : World Γ 0) (activity : Activity Γ) (name : String) :
    atomImage world activity ≠ .apply "PDrop" [.fvar name] := by
  unfold atomImage
  generalize activity.header world = header
  cases header <;> simp [HeaderInversion.Header.pattern, canonicalize_input, canonicalize_output]

def droppedExtension : Multiset Pattern := {.apply "PDrop" [.fvar "spatial-extension"]}

/-- The excluded extension is an actual sorted rho process at the same free
name context as the runtime, rather than an ill-formed resource token. -/
def droppedProcess : TargetProcess := by
  refine ⟨.apply "PDrop" [.fvar "spatial-extension"],
    (ParameterizedRewriteSystem.process_iff _ _).mpr ⟨?_, ?_⟩⟩
  · exact .drop (.fvar rfl)
  · rfl

theorem dropped_extension_well_formed :
    ∃ process : TargetProcess, components process.1 = droppedExtension := by
  exact ⟨droppedProcess, rfl⟩

theorem dropped_extension_not_image {Γ : Ctx sig} (world : World Γ 0)
    (source : Multiset (Activity Γ)) : resourceMap world source ≠ droppedExtension := by
  intro equal
  have member : .apply "PDrop" [.fvar "spatial-extension"] ∈
      source.map (atomImage world) := by
    change _ ∈ resourceMap world source
    rw [equal]
    exact Multiset.mem_singleton_self _
  obtain ⟨activity, _, image⟩ := Multiset.mem_map.mp member
  exact atomImage_ne_drop world activity "spatial-extension" image

theorem does_not_lift_all_extensions {Γ : Ctx sig} (world : World Γ 0) :
    ¬ (resourceMap world).LiftsExtensions := by
  intro lifts
  obtain ⟨source, _, equal⟩ := lifts 0 droppedExtension trivial
  exact dropped_extension_not_image world source equal

theorem source_dropped_wand {Γ : Ctx sig} (world : World Γ 0) :
    wand ((resourceMap world).pull (fun bag => bag = droppedExtension))
      ((resourceMap world).pull (fun _ => False)) (0 : Multiset (Activity Γ)) := by
  intro extension _ equal
  exact dropped_extension_not_image world extension equal

theorem target_dropped_wand_fails :
    ¬ wand (fun bag : Multiset Pattern => bag = droppedExtension) (fun _ => False) 0 := by
  intro holds
  exact holds droppedExtension trivial rfl

theorem wand_boundary {Γ : Ctx sig} (world : World Γ 0) :
    wand ((resourceMap world).pull (fun bag => bag = droppedExtension))
      ((resourceMap world).pull (fun _ => False)) (0 : Multiset (Activity Γ)) ∧
    ¬ (resourceMap world).pull (wand (fun bag => bag = droppedExtension) (fun _ => False))
      (0 : Multiset (Activity Γ)) := by
  refine ⟨source_dropped_wand world, ?_⟩
  change ¬ wand (fun bag : Multiset Pattern => bag = droppedExtension) (fun _ => False)
    (resourceMap world 0)
  rw [(resourceMap world).map_zero]
  exact target_dropped_wand_fails

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnarySpatial
