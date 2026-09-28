import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Instance

/-!
# Completeness of the algorithmic equality

The model is built over any generic equality with the laws. Over the
algorithmic one, the fundamental lemma compares every derivable equality of a
formed context algorithmically: its sides are reducibly equal, escape turns
reducible equality into the generic equality, and in the identity world the
generic equality contains the comparison. The comparison refines to the
conversion algorithm, which is sound for the typed equality; so on typed
terms of a formed context the algorithm derives exactly the equalities the
declarative judgment derives.

The declared constants must be semantic for the algorithmic equality too. A
rule package obtains this from the same declaration records that make them
semantic for the typed equality, since the records hold over any generic
equality with the laws.

Completeness is a property of a rule package (`AlgorithmicComplete`), which the
normalization model supplies for semantic constants
(`AlgorithmicComplete.ofSemantic`). Completeness of the conversion algorithm,
and its agreement with the typed equality on typed terms, follow from it and
from the facts about weak-head forms of types, whichever model supplies them.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L]

/-- The setting whose generic equality is the algorithmic equality. -/
def algorithmicSetting (S : Setting Head L) : Setting Head L :=
  { S with E := algorithmic S.R S.roles }

/-- **Completeness of the algorithmic equality**: derivably equal terms of a
formed context are algorithmically equal. -/
def AlgorithmicComplete (R : Rules Head) (roles : Roles Head) : Prop :=
  ∀ {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n}, CtxFormed R Γ → Equal R Γ t u A →
    Algorithmic R roles (.terms Γ t u A)

variable {S : Setting Head L}

/-- Completeness for types: equal types of a formed context are algorithmically
equal. -/
theorem AlgorithmicComplete.types (complete : AlgorithmicComplete S.R S.roles) {n : Nat}
    {Γ : Ctx Head n} {A B : Tm Head n} (equal : TypeEq S.R Γ A B) (formed : CtxFormed S.R Γ) :
    Algorithmic S.R S.roles (.types Γ A B) := by
  obtain ⟨u, hu, e⟩ := equal
  exact Algorithmic.types_of_universe hu (complete formed e)

section Completeness

variable (laws : S.E.Laws S.R S.roles) (constants : SemanticConstants S)
  (roots : RootPreserving S.R) (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
include laws constants roots heads algebra

/-- The algorithmic setting satisfies the laws of the model. -/
theorem algorithmicSetting_laws :
    (algorithmicSetting S).E.Laws (algorithmicSetting S).R (algorithmicSetting S).roles :=
  algorithmic_laws (.ofSemantic laws constants) roots heads algebra
    (SpineLift.ofSemantic laws constants roots heads algebra)

variable (constantsA : SemanticConstants (algorithmicSetting S))
include constantsA

/-- **The algorithmic equality is complete** for a setting whose declared
constants are semantic for the typed and for the algorithmic equality: the
sides of a derivable equality are reducibly equal in the model over the
algorithmic equality, and escape at the identity world compares them. -/
theorem AlgorithmicComplete.ofSemantic : AlgorithmicComplete S.R S.roles := by
  intro n Γ t u A formed equal
  have lawsA := algorithmicSetting_laws laws constants roots heads algebra
  obtain ⟨r, e⟩ := Equal.reducible (S := algorithmicSetting S) lawsA constantsA equal formed
  have d := ((r.escape lawsA).eqTm e).2 (CtxRen.id Γ) formed
  rwa [rename_id, rename_id, rename_id] at d

end Completeness

section Consequences

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (complete : AlgorithmicComplete S.R S.roles)

include complete in
/-- Completeness of the conversion algorithm for terms. -/
theorem Equal.algorithm {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n}
    (equal : Equal S.R Γ t u A) (formed : CtxFormed S.R Γ) :
    Algorithm S.R (.compare Γ t u A) :=
  (complete formed equal).refines

include complete in
/-- Completeness of the conversion algorithm for types. -/
theorem TypeEq.algorithm {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n}
    (equal : TypeEq S.R Γ A B) (formed : CtxFormed S.R Γ) :
    Algorithm S.R (.types Γ A B) :=
  (complete.types equal formed).refines

include facts roots heads algebra complete

/-- On typed terms of a formed context, the conversion algorithm derives
exactly the equalities of the typed equality. -/
theorem algorithm_iff_equal {n : Nat} {Γ : Ctx Head n} {t u A : Tm Head n}
    (formed : CtxFormed S.R Γ) (typedT : Typed S.R Γ t A) (typedU : Typed S.R Γ u A) :
    Algorithm S.R (.compare Γ t u A) ↔ Equal S.R Γ t u A :=
  ⟨fun derivation =>
      Algorithm.sound facts roots heads algebra derivation formed typedT typedU,
    fun equal => Equal.algorithm complete equal formed⟩

/-- On types of a formed context in a common universe, the conversion
algorithm derives exactly the equalities of the typed equality. -/
theorem algorithm_iff_typeEq {n : Nat} {Γ : Ctx Head n} {A B : Tm Head n} {u : Head}
    (formed : CtxFormed S.R Γ) (hu : S.R.isUniverse u) (typedA : Typed S.R Γ A (.head u))
    (typedB : Typed S.R Γ B (.head u)) :
    Algorithm S.R (.types Γ A B) ↔ Equal S.R Γ A B (.head u) :=
  ⟨fun derivation =>
      Algorithm.sound facts roots heads algebra derivation formed hu typedA typedB,
    fun equal => TypeEq.algorithm complete ⟨u, hu, equal⟩ formed⟩

end Consequences

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
