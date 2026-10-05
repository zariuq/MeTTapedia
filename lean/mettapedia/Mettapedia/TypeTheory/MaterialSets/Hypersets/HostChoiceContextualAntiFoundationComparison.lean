import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualObserverComparison
import Mettapedia.TypeTheory.MaterialSets.Hypersets.WellFoundedFamilies
import Mettapedia.TypeTheory.MaterialSets.Hypersets.UnfoldingIdentityComparison
import Mettapedia.SetTheory.AntiFoundation.Core

/-!
# Graph anti-foundation and the well-founded material embedding

An arbitrary original-small graph gives a genuine contextual coalgebra with
its actual child subtypes as small covers at every future. Material graph
decoration followed by the constructed embedding into the final set family
satisfies the whole coalgebra equation. Every natural solution of those
complete-future equations is equal to that decoration.

Its exact graph identification is ordinary bisimilarity. Every regular
identification is respected, but reflection of a smaller identification
requires its actual equality with bisimilarity. This does not construct a
Scott, Finsler or Boffa universe from a graph criterion.

At each world, membership accessibility of an embedded bare material value
is exactly its original well-foundedness. The comparison covers this actual
embedding; it does not identify all varying contextual well-founded values
with constant bare values. The host-Choice model remains explicitly optional.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualAntiFoundationComparison

open _root_.CategoryTheory PowerClassPresheafBaseChange
open Mettapedia.TypeTheory.ContextualWitnessCover
open HostChoiceContextualSetInterpretation HostChoiceContextualSetInterpretation.Finality

universe u
variable {D : Type u} [Category.{u} D]

def nodes (α : Type u) : D ⥤ Type u where
  obj _ := α
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def graphPredicate {α : Type u} (edge : α → α → Prop) (point : D) (root : α) :
    CoveredFuturePowerFamilies.Predicate (nodes α) point where
  holds argument := edge root argument.2
  closed {_ _} move available := move.2 ▸ available

def graphEnumeration {α : Type u} (edge : α → α → Prop) (point : D) (root : α) :
    CoveredFuturePowerFamilies.Enumeration (graphPredicate edge point root) where
  Carrier _ := {child : α // edge root child}
  value _ child := child.val
  covered _ argument := by
    constructor
    · intro available
      exact ⟨⟨argument, available⟩, rfl⟩
    · rintro ⟨child, rfl⟩
      exact child.property

def graphCoalgebra {α : Type u} (edge : α → α → Prop) :
    NaturalHom (nodes (D := D) α) (CoveredFuturePowerFamilies.family (nodes α)) where
  app point root := ⟨graphPredicate edge point root, ⟨graphEnumeration edge point root⟩⟩
  naturality _ _ := by
    apply Subtype.ext
    apply CoveredFuturePowerFamilies.Predicate.ext
    intro _
    exact Iff.rfl

def materialDecoration {α : Type u} (edge : α → α → Prop) :
    NaturalHom (nodes (D := D) α) ContextualMaterialCoalgebra.ambient where
  app _ := HSet.decorate edge
  naturality _ _ := rfl

theorem materialDecoration_square {α : Type u} (edge : α → α → Prop) :
    (graphCoalgebra (D := D) edge).comp
      (CoveredFuturePowerFunctor.imageHom (materialDecoration edge)) =
    (materialDecoration edge).comp ContextualMaterialCoalgebra.coalgebra := by
  apply NaturalHom.ext
  intro point root
  apply Subtype.ext
  apply CoveredFuturePowerFamilies.Predicate.ext
  rintro ⟨future, child⟩
  change (∃ original, HSet.decorate edge original = child ∧ edge root original) ↔
    child ∈ HSet.decorate edge root
  exact ⟨fun ⟨original, same, available⟩ => HSet.mem_decorate.mpr ⟨original, available, same⟩,
    fun available => by
      obtain ⟨original, step, same⟩ := HSet.mem_decorate.mp available
      exact ⟨original, same, step⟩⟩

noncomputable def decoration {α : Type u} (edge : α → α → Prop) :
    NaturalHom (nodes (D := D) α) sets :=
  (materialDecoration edge).comp HostChoiceContextualSetInfinity.reading

theorem decoration_square {α : Type u} (edge : α → α → Prop) :
    (graphCoalgebra (D := D) edge).comp
      (CoveredFuturePowerFunctor.imageHom (decoration edge)) = (decoration edge).comp unfold :=
  ContextualSmallCoalgebraComparisons.compose_square _ _ _ _ _
    (materialDecoration_square edge) HostChoiceContextualSetInfinity.reading_square

theorem decoration_future {α : Type u} (edge : α → α → Prop)
    {point target : D} (arrow : point ⟶ target) (root : α) (child : sets.obj target) :
    FutureMember arrow child ((decoration edge).app point root) ↔
      ∃ original : α, (decoration edge).app target original = child ∧ edge root original :=
  ContextualCoalgebraBisimulation.coalgebra_map_truth _ (decoration edge) unfold
    (decoration_square edge) point root ⟨target, arrow⟩ child

theorem decoration_member {α : Type u} (edge : α → α → Prop)
    (point : D) (root : α) (child : sets.obj point) :
    Member point child ((decoration edge).app point root) ↔
      ∃ original : α, (decoration edge).app point original = child ∧ edge root original :=
  decoration_future edge (𝟙 point) root child

def FullDecoration {α : Type u} (edge : α → α → Prop)
    (operation : NaturalHom (nodes (D := D) α) sets) : Prop :=
  ∀ (point target : D) (arrow : point ⟶ target) (root : α) (child : sets.obj target),
    FutureMember arrow child (operation.app point root) ↔
      ∃ original : α, operation.app target original = child ∧ edge root original

theorem fullDecoration_iff_square {α : Type u} (edge : α → α → Prop)
    (operation : NaturalHom (nodes (D := D) α) sets) :
    FullDecoration edge operation ↔
      (graphCoalgebra edge).comp (CoveredFuturePowerFunctor.imageHom operation) =
        operation.comp unfold := by
  constructor
  · intro equations
    apply NaturalHom.ext
    intro point root
    apply Subtype.ext
    apply CoveredFuturePowerFamilies.Predicate.ext
    rintro ⟨⟨target, arrow⟩, child⟩
    exact (equations point target arrow root child).symm
  · intro square point target arrow root child
    exact ContextualCoalgebraBisimulation.coalgebra_map_truth _ operation unfold square
      point root ⟨target, arrow⟩ child

/-- Uniqueness compares every admitted future, including actual context arrows. -/
theorem graph_AFA {α : Type u} (edge : α → α → Prop) :
    ∃! operation : NaturalHom (nodes (D := D) α) sets, FullDecoration edge operation := by
  refine ⟨decoration edge, fun _ _ arrow => decoration_future edge arrow, ?_⟩
  intro candidate equations
  exact HostChoiceContextualCoalgebraFinality.maps_equal_into_lift _ _
    ContextualSmallCoalgebraGenerators.quotient_separated candidate (decoration edge)
      ((fullDecoration_iff_square edge candidate).mp equations) (decoration_square edge)

theorem decoration_kernel {α : Type u} (edge : α → α → Prop)
    (point : D) (first second : α) :
    (decoration edge).app point first = (decoration edge).app point second ↔
      Bisimilar edge edge first second :=
  (show (decoration edge).app point first = (decoration edge).app point second ↔
      HSet.decorate edge first = HSet.decorate edge second from
    ⟨fun same => HostChoiceContextualSetInfinity.reading_injective point same,
      congrArg (HostChoiceContextualSetInfinity.reading.app point)⟩).trans
      HSet.bisimilar_iff_decorate_eq.symm

theorem constant_graph_bisimilarity {α : Type u} (edge : α → α → Prop)
    (point : D) (first second : α) :
    ContextualCoalgebraBisimulation.Bisimilar (graphCoalgebra edge) point first second ↔
      Bisimilar edge edge first second := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    refine ⟨relation point, ?_, related⟩
    intro left right same
    exact ⟨fun child available => bisimulation.forth same ⟨point, 𝟙 point⟩ available,
      fun child available => bisimulation.back same ⟨point, 𝟙 point⟩ available⟩
  · rintro ⟨relation, bisimulation, related⟩
    refine ⟨fun _ => relation, ?_, related⟩
    constructor
    · intro _ _ _ _ _ same
      exact same
    · intro _ _ _ same _ child available
      exact (bisimulation same).1 child available
    · intro _ _ _ same _ child available
      exact (bisimulation same).2 child available

theorem regular_identification_respected {α : Type u} {edge : α → α → Prop}
    (identification : Mettapedia.SetTheory.AntiFoundation.RegularIdentification edge)
    (point : D) {first second : α} (related : identification.ident first second) :
    (decoration edge).app point first = (decoration edge).app point second :=
  (decoration_kernel edge point first second).mpr (identification.toBisimilar related)

/-- Reflection of a regular identification has exactly the missing reverse
inclusion into that identification; regularity alone only supplies coarsening. -/
theorem regular_identification_reflected_iff {α : Type u} {edge : α → α → Prop}
    (identification : Mettapedia.SetTheory.AntiFoundation.RegularIdentification edge) (point : D) :
    (∀ first second, (decoration edge).app point first = (decoration edge).app point second →
      identification.ident first second) ↔
    (∀ first second, Bisimilar edge edge first second → identification.ident first second) := by
  constructor
  · intro reflects first second related
    exact reflects first second ((decoration_kernel edge point first second).mpr related)
  · intro contains first second same
    exact contains first second ((decoration_kernel edge point first second).mp same)

theorem injective_decoration_iff {α : Type u} (edge : α → α → Prop) (point : D) :
    Function.Injective ((decoration edge).app point) ↔
      (∀ first second, Bisimilar edge edge first second → first = second) := by
  constructor
  · intro injective first second related
    exact injective ((decoration_kernel edge point first second).mpr related)
  · intro strong first second same
    exact strong first second ((decoration_kernel edge point first second).mp same)

/-- A natural Quine value solves its singleton equation at every future. -/
def FutureQuine (value : (sets (D := D)).sections) : Prop :=
  ∀ (point target : D) (arrow : point ⟶ target) (child : sets.obj target),
    FutureMember arrow child (value.val point) ↔ value.val target = child

noncomputable def quineSection : (sets (D := D)).sections :=
  HostChoiceContextualSetInfinity.reading.mapSection ⟨fun _ => HSet.quineAtom, fun _ => rfl⟩

theorem quineSection_law : FutureQuine (quineSection (D := D)) := by
  intro point target arrow child
  refine (HostChoiceContextualSetInfinity.reading_future arrow HSet.quineAtom child).trans ?_
  constructor
  · rintro ⟨material, same, belongs⟩
    exact (congrArg (HostChoiceContextualSetInfinity.reading.app target)
      (HSet.mem_quineAtom.mp belongs)).symm.trans same
  · intro same
    exact ⟨HSet.quineAtom, same, HSet.quineAtom_mem_self⟩

/-- The unique whole-context loop solution excludes multiple distinct
natural future-Quine readings. It is not a present-only uniqueness claim. -/
theorem futureQuine_unique (value : (sets (D := D)).sections) (law : FutureQuine value) :
    value = quineSection := by
  let operation : NaturalHom (nodes (D := D) HSet.loop.{u}.Node) sets := {
    app := fun point _ => value.val point
    naturality := fun arrow _ => value.property arrow }
  have equations : FullDecoration HSet.loop.edge operation := by
    intro point target arrow root child
    refine (law point target arrow child).trans ?_
    exact ⟨fun same => ⟨HSet.loop.point, same, True.intro⟩,
      fun ⟨_, same, _⟩ => same⟩
  have unique := (graph_AFA (D := D) HSet.loop.edge).unique equations
    (show FullDecoration HSet.loop.edge (decoration HSet.loop.edge) from
      fun _ _ arrow => decoration_future HSet.loop.edge arrow)
  apply Subtype.ext
  funext point
  have atRoot := congrArg
    (fun map : NaturalHom (nodes (D := D) HSet.loop.Node) sets => map.app point HSet.loop.point) unique
  exact atRoot.trans (congrArg (HostChoiceContextualSetInfinity.reading.app point) (HSet.decorate_loop _))

/-- Accessibility is membership accessibility at one actual model world.
It is separate from all-future identity reflection. -/
def ContextualWF (point : D) (value : sets.obj point) : Prop := Acc (Member point) value

/-- Well-foundedness stable under all actual future substitutions. -/
def PersistentWF (point : D) (value : sets.obj point) : Prop :=
  ∀ (target : D) (arrow : point ⟶ target), ContextualWF target (sets.map arrow value)

theorem persistentWF_current {point : D} {value : sets.obj point}
    (persistent : PersistentWF point value) : ContextualWF point value := by
  have current := persistent point (𝟙 point)
  have identity : sets.map (𝟙 point) value = value := congrArg (fun map => map value) (sets.map_id point)
  exact identity ▸ current

theorem persistentWF_transport {point target : D} (arrow : point ⟶ target)
    {value : sets.obj point} (persistent : PersistentWF point value) :
    PersistentWF target (sets.map arrow value) := by
  intro later step
  have future := persistent later (arrow ≫ step)
  have compose : sets.map (arrow ≫ step) value = sets.map step (sets.map arrow value) :=
    congrArg (fun map => map value) (sets.map_comp arrow step)
  exact compose ▸ future

theorem wellFounded_reading_iff (point : D) (material : HSet.{u}) :
    ContextualWF point (HostChoiceContextualSetInfinity.reading.app point material) ↔ material.WF := by
  constructor
  · intro accessible
    have reflects : ∀ value : sets.obj point, ContextualWF point value →
        ∀ source : HSet.{u}, HostChoiceContextualSetInfinity.reading.app point source = value → source.WF := by
      intro value proof
      induction proof with
      | intro value _ hypothesis =>
        rintro source rfl
        apply HSet.wf_of_forall_mem
        intro child belongs
        exact hypothesis (HostChoiceContextualSetInfinity.reading.app point child)
          ((HostChoiceContextualSetInfinity.reading_material_member point child source).mpr belongs)
          child rfl
    exact reflects _ accessible material rfl
  · intro accessible
    induction accessible with
    | intro material _ hypothesis =>
      apply Acc.intro
      intro child belongs
      obtain ⟨source, same, member⟩ :=
        (HostChoiceContextualSetInfinity.reading_member point material child).mp belongs
      exact same ▸ hypothesis source member

theorem wellFounded_decoration_iff {α : Type u} (edge : α → α → Prop)
    (point : D) (root : α) :
    ContextualWF point ((decoration edge).app point root) ↔ Acc (flip edge) root :=
  (wellFounded_reading_iff point _).trans HSet.wf_decorate_iff

theorem wellFounded_embedded_transport {point target : D} (arrow : point ⟶ target)
    (material : HSet.{u}) :
    ContextualWF target (sets.map arrow (HostChoiceContextualSetInfinity.reading.app point material)) ↔
      ContextualWF point (HostChoiceContextualSetInfinity.reading.app point material) := by
  have natural : sets.map arrow (HostChoiceContextualSetInfinity.reading.app point material) =
      HostChoiceContextualSetInfinity.reading.app target material :=
    HostChoiceContextualSetInfinity.reading.naturality arrow material
  rw [natural]
  exact (wellFounded_reading_iff target material).trans (wellFounded_reading_iff point material).symm

theorem persistentWF_reading_iff (point : D) (material : HSet.{u}) :
    PersistentWF point (HostChoiceContextualSetInfinity.reading.app point material) ↔ material.WF := by
  constructor
  · intro persistent
    exact (wellFounded_reading_iff point material).mp (persistentWF_current persistent)
  · intro accessible target arrow
    have same : sets.map arrow (HostChoiceContextualSetInfinity.reading.app point material) =
        HostChoiceContextualSetInfinity.reading.app target material :=
      HostChoiceContextualSetInfinity.reading.naturality arrow material
    exact same.symm ▸ (wellFounded_reading_iff target material).mpr accessible

noncomputable def wellFoundedMemberForward (point : D) (parent : WellFoundedPart.{u})
    (child : {child : WellFoundedPart.{u} // child.val ∈ parent.val}) :
    {child : sets.obj point // Member point child (HostChoiceContextualSetInfinity.reading.app point parent.val)} :=
  ⟨HostChoiceContextualSetInfinity.reading.app point child.val.val,
    (HostChoiceContextualSetInfinity.reading_material_member point _ _).mpr child.property⟩

theorem wellFoundedMemberForward_bijective (point : D) (parent : WellFoundedPart.{u}) :
    Function.Bijective (wellFoundedMemberForward point parent) := by
  constructor
  · intro first second same
    apply Subtype.ext
    apply Subtype.ext
    exact HostChoiceContextualSetInfinity.reading_injective point (congrArg Subtype.val same)
  · intro child
    obtain ⟨material, same, belongs⟩ :=
      (HostChoiceContextualSetInfinity.reading_member point parent.val child.val).mp child.property
    exact ⟨⟨⟨material, parent.property.mem belongs⟩, belongs⟩, Subtype.ext same⟩

/-- Optional host inverse of the proved bijection. Its additional choice is
visible in this declaration; the forward map and onto proof select no member. -/
noncomputable def wellFoundedMemberEquiv (point : D) (parent : WellFoundedPart.{u}) :
    {child : WellFoundedPart.{u} // child.val ∈ parent.val} ≃
    {child : sets.obj point // Member point child (HostChoiceContextualSetInfinity.reading.app point parent.val)} :=
  Equiv.ofBijective (wellFoundedMemberForward point parent)
    (wellFoundedMemberForward_bijective point parent)

theorem wellFoundedMemberEquiv_value (point : D) (parent : WellFoundedPart.{u})
    (child : {child : WellFoundedPart.{u} // child.val ∈ parent.val}) :
    (wellFoundedMemberEquiv point parent child).val =
      HostChoiceContextualSetInfinity.reading.app point child.val.val := rfl

/-! ## Full unfolding and actual material identification -/

/-- The terminal-node map lifts every original child to its actual extended
path. It is a bounded morphism of the entire unfolding, not a truncation. -/
theorem unfoldingProjection {α : Type u} (edge : α → α → Prop) (root : α) :
    IsBoundedMorphism (UnfoldingIdentityComparison.PathEdge edge root) edge
      (fun node : UnfoldingIdentityComparison.PathNode edge root => node.1) where
  map {_ _} available := by
    cases available with
    | extend _ step => exact step
  lift {source target} available :=
    ⟨⟨target, .snoc source.2 available⟩, .extend source.2 available, rfl⟩

theorem full_unfolding_value {α : Type u} (edge : α → α → Prop) (root : α) :
    HSet.mk (UnfoldingIdentityComparison.unfold edge root) = HSet.decorate edge root :=
  (HSet.mk_eq_decorate _).trans
    ((unfoldingProjection edge root).decorate_apply ⟨root, .nil⟩).symm

/-- Full-tree isomorphism implies Aczel identification. Reflection would
require a separate strength condition on the graph identification. -/
theorem full_unfolding_iso_bisimilar {α : Type u} {edge : α → α → Prop}
    {first second : α}
    (isomorphism : PresentationIso (UnfoldingIdentityComparison.unfold edge first)
      (UnfoldingIdentityComparison.unfold edge second)) : Bisimilar edge edge first second :=
  HSet.bisimilar_iff_decorate_eq.mpr
    ((full_unfolding_value edge first).symm.trans
      (isomorphism.material_eq.trans (full_unfolding_value edge second)))

theorem full_unfolding_iso_contextual_value {α : Type u} {edge : α → α → Prop}
    {first second : α} (point : D)
    (isomorphism : PresentationIso (UnfoldingIdentityComparison.unfold edge first)
      (UnfoldingIdentityComparison.unfold edge second)) :
    (decoration edge).app point first = (decoration edge).app point second :=
  (decoration_kernel edge point first second).mpr (full_unfolding_iso_bisimilar isomorphism)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualAntiFoundationComparison
