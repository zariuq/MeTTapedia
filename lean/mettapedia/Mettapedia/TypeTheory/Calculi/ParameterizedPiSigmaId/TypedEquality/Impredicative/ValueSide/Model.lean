import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Algebra
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Levels
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Consistency.InterpLaws

/-!
# The value model

The value side reads a rule package with the consistency model's reduction,
roles, numbers, codes, decoder and universe levels in a level order `L`, and adds
two things: a daimon `⋆` and a realizer algebra. Codes are read by the candidate
reading of the algebra, whose neutral codes are the daimonic ones.

The laws are the consistency model's, with the daimon rigid and distinct from
the type of codes and from the decoder, the laws of the algebra, and the
constructors that inductive types list declared as constructors. The last is
needed: without it the relation of an inductive type need not be transitive
(`UndeclaredControl.interpAt_facts_needs_declared`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ValueSide

open Normalization
open UniverseLevel (LevelOrder)
open Consistency (Reading)
open Realizability (Daimonic)

/-- The value model: the consistency model's reading of the package, with its
universe levels in `L`, a daimon, and a realizer algebra. -/
structure Model (Head L : Type) [LevelOrder L] extends Consistency.Model Head L where
  star : DeclName
  alg : RealizerAlgebra Head

variable {Head L : Type} [LevelOrder L]

namespace Model

variable (V : Model Head L)

/-- The reading of codes: the candidate reading of the model's algebra. -/
abbrev reading : Reading Head := algebraReading V.toSetting V.star V.num V.alg

/-- The laws of the value model: those of the consistency model, the daimon
rigid and distinct from the type of codes and from the decoder, the laws of
the algebra, and the listed constructors of inductive types declared as
constructors. -/
structure Laws : Prop where
  values : V.toModel.Laws
  star : V.roles V.star = .rigid
  starNotProp : V.star ≠ V.prop
  starNotHolds : V.star ≠ V.holds
  alg : V.alg.Laws
  declared : ConstructorsDeclared V.roles

variable {V}

namespace Laws

variable (laws : V.Laws)
include laws

/-- The value side's root steps occur at computing spines of exact arity. -/
theorem shape : RootShape V.rules V.roles := laws.values.shape

/-- A type has at most one weak-head normal form. -/
theorem unique {n : Nat} {A t t' : Tm Head n} (red : WhRed V.rules V.roles A t)
    (red' : WhRed V.rules V.roles A t') (normal : Whnf V.rules V.roles t)
    (normal' : Whnf V.rules V.roles t') : t = t' :=
  WhRed.whnf_unique laws.shape red red' normal normal'

/-- The daimon is not the type of numbers, which is inductive. -/
theorem starNotNum : V.star ≠ V.num := by
  intro equal
  have role := laws.values.num
  rw [← equal, laws.star] at role
  cases role

end Laws

/-- A daimonic term is weak-head normal. -/
theorem Laws.daimonic_whnf (laws : V.Laws) {n : Nat} {t : Tm Head n}
    (daimonic : Daimonic V.roles V.star t) : Whnf V.rules V.roles t :=
  (daimonic.neutral laws.star).whnf laws.shape

end Model

end ValueSide
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
