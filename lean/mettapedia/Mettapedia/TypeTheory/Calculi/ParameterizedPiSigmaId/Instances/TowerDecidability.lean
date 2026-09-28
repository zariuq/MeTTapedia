import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.Tower
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Decidability

/-!
# Decidable conversion in the cumulative tower

The tower declares no constants, so its constants are semantic for the
algorithmic equality as well, and its head equality, equality of level
expressions under every valuation, is decided through level normal forms. So
for dependent functions and pairs, identity types, η for functions and pairs,
and cumulative universes at explicit levels, the conversion algorithm is
complete and the typed equality is decided between terms of a type.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

namespace TowerModel

/-- The tower's constants are semantic for the algorithmic equality: it has none. -/
theorem algorithmicConstants (valuation : Nat → Nat) :
    SemanticConstants (algorithmicSetting (setting valuation)) := by
  intro name type u declared
  cases declared

/-- **The algorithmic equality is complete for the tower**, by the normalization
model over it. -/
theorem complete : AlgorithmicComplete Tower.rules roles :=
  AlgorithmicComplete.ofSemantic (S := setting fun _ => 0) (laws _) (constants _) roots heads
    algebra (algorithmicConstants _)

/-- Head equality of the tower is decided. -/
theorem decideHeads (h h' : Tower.Head) :
    HeadSame Tower.rules h h' ∨ ¬ HeadSame Tower.rules h h' := by
  rcases Decidable.em (Tower.HeadEq h h') with same | different
  · exact .inl (.inr same)
  · rcases Decidable.em (h = h') with equal | unequal
    · exact .inl (.inl equal)
    · exact .inr fun same => same.elim unequal different

end TowerModel

section Consequences

open TowerModel

variable {n : Nat} {Γ : Ctx Tower.Head n}

/-- Completeness of the conversion algorithm for the tower. -/
theorem Tower.algorithm_complete {t u T : Tm Tower.Head n} (formed : CtxFormed Tower.rules Γ)
    (equal : Equal Tower.rules Γ t u T) : Algorithm Tower.rules (.compare Γ t u T) :=
  Equal.algorithm (S := setting fun _ => 0) complete equal formed

/-- The typed equality of the tower is decided between two terms of a type. -/
theorem Tower.equal_decide {t u T : Tm Tower.Head n} (formed : CtxFormed Tower.rules Γ)
    (typedT : Typed Tower.rules Γ t T) (typedU : Typed Tower.rules Γ u T) :
    Equal Tower.rules Γ t u T ∨ ¬ Equal Tower.rules Γ t u T :=
  Equal.decide (S := setting fun _ => 0) facts roots heads algebra decideHeads complete formed
    typedT typedU

/-- The equality of two types of the tower is decided. -/
theorem Tower.typeEq_decide {A B : Tm Tower.Head n} (formed : CtxFormed Tower.rules Γ)
    (typeA : IsType Tower.rules Γ A) (typeB : IsType Tower.rules Γ B) :
    TypeEq Tower.rules Γ A B ∨ ¬ TypeEq Tower.rules Γ A B :=
  TypeEq.decide (S := setting fun _ => 0) facts roots heads algebra decideHeads complete formed
    typeA typeB

end Consequences

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
