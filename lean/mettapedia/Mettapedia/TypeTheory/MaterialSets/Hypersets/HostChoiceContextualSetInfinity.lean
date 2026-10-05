import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetInterpretation
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialCoalgebra
import Mettapedia.TypeTheory.MaterialSets.Hypersets.NaturalOrdinalModel

/-!
# Internal infinity through the material membership embedding

Constant bare material membership has original-bound small child covers.
The optional full final coalgebra supplies its natural injective reading into
the contextual set family. Its whole coalgebra equation compares every future
child, not only children known at the present context.

The constructed material natural ordinals yield an actual internal infinite
set. Its successor is built from the proved internal pairing and union
operations. This embedding does not make constant material membership a
contextual final coalgebra or erase the external host-Choice dependency.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetInfinity

open _root_.CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open HostChoiceContextualSetInterpretation HostChoiceContextualSetInterpretation.Finality
open Mettapedia.TypeTheory.ContextualWitnessCover

universe u
variable {D : Type u} [Category.{u} D]

noncomputable def reading : NaturalHom (ContextualMaterialCoalgebra.ambient (D := D)) sets :=
  (HostChoiceContextualCoalgebraFinality.readout ContextualMaterialCoalgebra.coalgebra).comp
    (HostChoiceContextualCoalgebraFinality.raise.{u,0,u+1}
      (ContextualSmallCoalgebraGenerators.quotient (D := D)))

theorem reading_square :
    (ContextualMaterialCoalgebra.coalgebra (D := D)).comp (imageHom reading) = reading.comp unfold :=
  ContextualSmallCoalgebraComparisons.compose_square _ _ _ _ _
    (HostChoiceContextualCoalgebraFinality.readout_square _)
    (HostChoiceContextualCoalgebraFinality.raise_square.{u,0,u+1} _)

theorem reading_injective (point : D) : Function.Injective (reading.app point) := by
  intro first second same
  have raw := congrArg ULift.down same
  exact ContextualMaterialCoalgebra.separated point first second
    ((HostChoiceContextualCoalgebraFinality.readout_kernel _ point first second).mp raw)

theorem reading_future {point target : D} (arrow : point ⟶ target)
    (parent : HSet.{u}) (child : sets.obj target) :
    FutureMember arrow child (reading.app point parent) ↔
      ∃ material : HSet.{u}, reading.app target material = child ∧ material ∈ parent :=
  ContextualCoalgebraBisimulation.coalgebra_map_truth _ reading unfold reading_square
    point parent ⟨target, arrow⟩ child

theorem reading_member (point : D) (parent : HSet.{u}) (child : sets.obj point) :
    Member point child (reading.app point parent) ↔
      ∃ material : HSet.{u}, reading.app point material = child ∧ material ∈ parent :=
  reading_future (𝟙 point) parent child

theorem reading_material_member (point : D) (child parent : HSet.{u}) :
    Member point (reading.app point child) (reading.app point parent) ↔ child ∈ parent := by
  refine (reading_member point parent _).trans ?_
  constructor
  · rintro ⟨material, same, belongs⟩
    exact reading_injective point same ▸ belongs
  · intro belongs
    exact ⟨child, rfl, belongs⟩

theorem reading_empty (point : D) : reading.app point (∅ : HSet.{u}) = emptySet.val point := by
  have powers : unfold.app point (reading.app point (∅ : HSet.{u})) = emptyPower point := by
    apply Subtype.ext
    apply Predicate.ext
    rintro ⟨⟨target, arrow⟩, child⟩
    constructor
    · rintro available
      obtain ⟨material, _, belongs⟩ := (reading_future arrow ∅ child).mp available
      exact HSet.notMem_empty material belongs
    · exact False.elim
  exact (assemble_unfold point _).symm.trans (congrArg (assemble.app point) powers)

noncomputable def successorArguments : NaturalHom (sets (D := D)) (CoveredFuturePowerClassifier.product sets sets) where
  app point parent := (parent, singletonSet.app point parent)
  naturality arrow parent := Prod.ext rfl (singletonSet.naturality arrow parent)

/-- The material successor `x ∪ {x}` uses actual contextual pair and union. -/
noncomputable def successorSet : NaturalHom (sets (D := D)) sets :=
  (successorArguments.comp pairSet).comp unionSet

theorem future_successor {point target : D} (arrow : point ⟶ target)
    (parent : sets.obj point) (child : sets.obj target) :
    FutureMember arrow child (successorSet.app point parent) ↔
      FutureMember arrow child parent ∨ sets.map arrow parent = child := by
  refine (future_union arrow child _).trans ?_
  constructor
  · rintro ⟨middle, supplied, belongs⟩
    obtain (same | same) := (future_pair arrow middle parent (singletonSet.app point parent)).mp supplied
    · exact Or.inl ((futureMember_iff arrow child parent).mpr (same.symm ▸ belongs))
    · have inner : Member target child (singletonSet.app target (sets.map arrow parent)) :=
        ((singletonSet.naturality arrow parent).symm.trans same).symm ▸ belongs
      exact Or.inr ((member_singleton target child _).mp inner)
  · rintro (belongs | same)
    · exact ⟨sets.map arrow parent, (future_pair arrow _ _ _).mpr (Or.inl rfl),
        (futureMember_iff arrow child parent).mp belongs⟩
    · refine ⟨sets.map arrow (singletonSet.app point parent),
        (future_pair arrow _ _ _).mpr (Or.inr rfl), ?_⟩
      rw [singletonSet.naturality]
      exact (member_singleton target child _).mpr same

theorem reading_successor (point : D) (parent : HSet.{u}) :
    reading.app point (NaturalOrdinalModel.successor parent) =
      successorSet.app point (reading.app point parent) := by
  have powers : unfold.app point (reading.app point (NaturalOrdinalModel.successor parent)) =
      unfold.app point (successorSet.app point (reading.app point parent)) := by
    apply Subtype.ext
    apply Predicate.ext
    rintro ⟨⟨target, arrow⟩, child⟩
    refine (reading_future arrow _ child).trans ?_
    refine (show (∃ material : HSet.{u}, reading.app target material = child ∧
        material ∈ NaturalOrdinalModel.successor parent) ↔
        ((∃ material : HSet.{u}, reading.app target material = child ∧ material ∈ parent) ∨
          reading.app target parent = child) from ?_).trans ?_
    · constructor
      · rintro ⟨material, same, belongs⟩
        obtain (equal | belongs) := HSet.mem_insert_iff.mp belongs
        · exact Or.inr (equal ▸ same)
        · exact Or.inl ⟨material, same, belongs⟩
      · rintro (⟨material, same, belongs⟩ | same)
        · exact ⟨material, same, HSet.mem_insert_iff.mpr (Or.inr belongs)⟩
        · exact ⟨parent, same, HSet.mem_insert_iff.mpr (Or.inl rfl)⟩
    · have natural := reading.naturality arrow parent
      exact (or_congr (reading_future arrow parent child).symm
        (iff_of_eq (congrArg (fun value => value = child) natural.symm))).trans
          (future_successor arrow (reading.app point parent) child).symm
  exact (assemble_unfold point _).symm.trans
    ((congrArg (assemble.app point) powers).trans (assemble_unfold point _))

noncomputable def naturals : (sets (D := D)).sections :=
  reading.mapSection ⟨fun _ => NaturalOrdinalModel.naturals, fun _ => rfl⟩

noncomputable def ordinal (point : D) (number : Nat) : sets.obj point :=
  reading.app point (NaturalOrdinalModel.ordinal number)

theorem member_naturals (point : D) (child : sets.obj point) :
    Member point child (naturals.val point) ↔ ∃ number : Nat, ordinal point number = child := by
  refine (reading_member point _ child).trans ?_
  constructor
  · rintro ⟨material, same, belongs⟩
    obtain ⟨number, materialEq⟩ := (NaturalOrdinalModel.member_naturals material).mp belongs
    exact ⟨number, (congrArg (reading.app point) materialEq).trans same⟩
  · rintro ⟨number, same⟩
    exact ⟨NaturalOrdinalModel.ordinal number, same, NaturalOrdinalModel.ordinal_member_naturals number⟩

theorem ordinal_injective (point : D) : Function.Injective (ordinal point) := by
  intro first second same
  exact NaturalOrdinalModel.ordinal_injective (reading_injective point same)

theorem ordinal_zero (point : D) : ordinal point 0 = emptySet.val point :=
  (congrArg (reading.app point) NaturalOrdinalModel.ordinal_zero).trans (reading_empty point)

theorem ordinal_successor (point : D) (number : Nat) :
    ordinal point (number+1) = successorSet.app point (ordinal point number) :=
  (congrArg (reading.app point) (NaturalOrdinalModel.ordinal_successor number)).trans
    (reading_successor point _)

theorem internal_infinity (point : D) :
    Member point (emptySet.val point) (naturals.val point) ∧
      ∀ child, Member point child (naturals.val point) →
        Member point (successorSet.app point child) (naturals.val point) := by
  refine ⟨(member_naturals point _).mpr ⟨0, ordinal_zero point⟩, ?_⟩
  intro child belongs
  obtain ⟨number, same⟩ := (member_naturals point child).mp belongs
  exact (member_naturals point _).mpr ⟨number+1,
    (ordinal_successor point number).trans (congrArg (successorSet.app point) same)⟩

/-- Induction is local to the constructed natural set, including arbitrary
proposition-valued predicates on the current internal set fibre. -/
theorem internal_induction (point : D) (predicate : sets.obj point → Prop)
    (zero : predicate (emptySet.val point))
    (step : ∀ child, Member point child (naturals.val point) → predicate child →
      predicate (successorSet.app point child)) :
    ∀ child, Member point child (naturals.val point) → predicate child := by
  have numbered : ∀ number : Nat, predicate (ordinal point number) := by
    intro number
    induction number with
    | zero => exact (ordinal_zero point).symm ▸ zero
    | succ number previous =>
      exact (ordinal_successor point number).symm ▸
        step (ordinal point number) ((member_naturals point _).mpr ⟨number, rfl⟩) previous
  intro child belongs
  obtain ⟨number, same⟩ := (member_naturals point child).mp belongs
  exact same ▸ numbered number

theorem ordinal_not_self_member (point : D) (number : Nat) :
    ¬ Member point (ordinal point number) (ordinal point number) :=
  fun belongs => NaturalOrdinalModel.ordinal_not_selfMember number
    ((reading_material_member point _ _).mp belongs)

theorem naturals_transport {point target : D} (arrow : point ⟶ target) :
    sets.map arrow (naturals.val point) = naturals.val target :=
  naturals.property arrow

theorem ordinal_transport {point target : D} (arrow : point ⟶ target) (number : Nat) :
    sets.map arrow (ordinal point number) = ordinal target number :=
  reading.naturality arrow (NaturalOrdinalModel.ordinal number)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetInfinity
