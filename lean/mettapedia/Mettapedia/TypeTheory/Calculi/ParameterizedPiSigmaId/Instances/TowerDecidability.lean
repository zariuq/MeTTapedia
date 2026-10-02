import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.Tower
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Decidability

/-!
# Decidable conversion in the cumulative tower

The tower declares no constants, so its constants are semantic for the
algorithmic equality as well, and its head equality, equality of level
expressions under every valuation, is decided through level normal forms. So
for dependent functions and pairs, identity types, η for functions and pairs,
and cumulative universes at explicit levels over any level order, the
conversion algorithm is complete and the typed equality is decided between
terms of a type.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

namespace TowerModel

variable {L : Type} [UniverseLevel.LevelOrder L]

/-- The tower's constants are semantic for the algorithmic equality: it has none. -/
theorem algorithmicConstants (valuation : Nat → L) :
    SemanticConstants (algorithmicSetting (setting valuation)) := by
  intro name type u declared
  cases declared

/-- **The algorithmic equality is complete for the tower**, by the normalization
model over it. -/
theorem complete : AlgorithmicComplete (LevelTower.rules L) roles :=
  AlgorithmicComplete.ofSemantic (S := setting fun _ => (UniverseLevel.LevelOrder.bot : L))
    (laws _) (constants _) roots heads algebra (algorithmicConstants _)

/-- Head equality of the tower is decided. -/
theorem decideHeads (h h' : LevelTower.Head L) :
    HeadSame (LevelTower.rules L) h h' ∨ ¬ HeadSame (LevelTower.rules L) h h' := by
  rcases Decidable.em (LevelTower.HeadEq h h') with same | different
  · exact .inl (.inr same)
  · rcases Decidable.em (h = h') with equal | unequal
    · exact .inl (.inl equal)
    · exact .inr fun same => same.elim unequal different

end TowerModel

section Consequences

open TowerModel

variable {L : Type} [UniverseLevel.LevelOrder L] {n : Nat} {Γ : Ctx (LevelTower.Head L) n}

/-- Completeness of the conversion algorithm for the tower. -/
theorem LevelTower.algorithm_complete {t u T : Tm (LevelTower.Head L) n}
    (formed : CtxFormed (LevelTower.rules L) Γ)
    (equal : Equal (LevelTower.rules L) Γ t u T) :
    Algorithm (LevelTower.rules L) (.compare Γ t u T) :=
  Equal.algorithm (S := setting fun _ => (UniverseLevel.LevelOrder.bot : L)) complete equal formed

/-- The typed equality of the tower is decided between two terms of a type. -/
theorem LevelTower.equal_decide {t u T : Tm (LevelTower.Head L) n}
    (formed : CtxFormed (LevelTower.rules L) Γ)
    (typedT : Typed (LevelTower.rules L) Γ t T) (typedU : Typed (LevelTower.rules L) Γ u T) :
    Equal (LevelTower.rules L) Γ t u T ∨ ¬ Equal (LevelTower.rules L) Γ t u T :=
  Equal.decide (S := setting fun _ => (UniverseLevel.LevelOrder.bot : L)) facts roots heads
    algebra decideHeads complete formed typedT typedU

/-- The equality of two types of the tower is decided. -/
theorem LevelTower.typeEq_decide {A B : Tm (LevelTower.Head L) n}
    (formed : CtxFormed (LevelTower.rules L) Γ)
    (typeA : IsType (LevelTower.rules L) Γ A) (typeB : IsType (LevelTower.rules L) Γ B) :
    TypeEq (LevelTower.rules L) Γ A B ∨ ¬ TypeEq (LevelTower.rules L) Γ A B :=
  TypeEq.decide (S := setting fun _ => (UniverseLevel.LevelOrder.bot : L)) facts roots heads
    algebra decideHeads complete formed typeA typeB

end Consequences

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
