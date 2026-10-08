import Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifierInterpretation

/-!
# Independent full readings of the six generated quantifier diagrams

These computations inspect the actual authored raw parallel pairs. They
retain the entire route, its complete function inputs and the ordered-pair
equalizer. Equations between these independent readings descend to the
actual quotient functor, and conversely quotient equations recover them.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Interpretation

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open RelativeClosedSyntax GeneratedCategory

universe k w z
variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable (original : Signature (C := C) (symbols := symbols))
variable (language : PredicateSyntax original)
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (meanings : RelativeClosedSyntax.Interpretation.Assignment C symbols D)
variable (old : RelativeClosedSyntax.Interpretation.Realization original meanings)
variable (operations : InternalConjunctiveObject.Operations D)
variable (meaning : Meaning original meanings old operations)
variable (propositionRead : RawInterpretation.ObjectReads meanings language.proposition operations.proposition)
variable (conjunctionRead : RawInterpretation.Reads meanings language.conjunction operations.conjunction)

include propositionRead conjunctionRead

theorem monotonicity_read (kind : Kind) (route : Route original) :
    RawInterpretation.Reads (assignment original meanings old operations meaning)
      (monotonicityPair original language kind route).left
      ((functions original meanings old operations route.target).meet
        (InternalPredicateQuantifier.secondInput operations (value original meanings old route.source) ≫
          operator original meanings old operations meaning kind route)
        (InternalPredicateQuantifier.firstInput operations (value original meanings old route.source) ≫
          operator original meanings old operations meaning kind route)) ∧
    RawInterpretation.Reads (assignment original meanings old operations meaning)
      (monotonicityPair original language kind route).right
      (InternalPredicateQuantifier.firstInput operations (value original meanings old route.source) ≫
        operator original meanings old operations meaning kind route) := by
  let current := assignment original meanings old operations meaning
  have first := RawInterpretation.compose current
    (smaller_read original language meanings old operations meaning propositionRead conjunctionRead route.source)
    (operator_read original language meanings old operations meaning kind route)
  have second := RawInterpretation.compose current
    (larger_read original language meanings old operations meaning propositionRead conjunctionRead route.source)
    (operator_read original language meanings old operations meaning kind route)
  exact ⟨Readout.powerMeet_read (argumentSyntax original language) current operations
    (proposition_read original language meanings old operations meaning propositionRead)
    (conjunction_read original language meanings old operations meaning conjunctionRead)
    (object_original original language meanings old operations meaning route.target) second first, first⟩

theorem universal_unit_read (route : Route original) :
    RawInterpretation.Reads (assignment original meanings old operations meaning)
      (universalUnitPair original language route).left
      ((functions original meanings old operations route.target).meet
        (InternalPredicateQuantifier.precomposition operations (routeValue original meanings old route) ≫ meaning.universal route)
        (𝟙 (power original meanings old operations route.target))) ∧
    RawInterpretation.Reads (assignment original meanings old operations meaning)
      (universalUnitPair original language route).right (𝟙 (power original meanings old operations route.target)) := by
  let current := assignment original meanings old operations meaning
  have identityRead := RawInterpretation.identity current
    (power_read original language meanings old operations meaning propositionRead route.target)
  have complete := RawInterpretation.compose current
    (precomposition_read original language meanings old operations meaning propositionRead route)
    (operator_read original language meanings old operations meaning .universal route)
  exact ⟨Readout.powerMeet_read (argumentSyntax original language) current operations
    (proposition_read original language meanings old operations meaning propositionRead)
    (conjunction_read original language meanings old operations meaning conjunctionRead)
    (object_original original language meanings old operations meaning route.target) complete identityRead, identityRead⟩

theorem universal_counit_read (route : Route original) :
    RawInterpretation.Reads (assignment original meanings old operations meaning)
      (universalCounitPair original language route).left
      ((functions original meanings old operations route.source).meet (𝟙 (power original meanings old operations route.source))
        (meaning.universal route ≫ InternalPredicateQuantifier.precomposition operations (routeValue original meanings old route))) ∧
    RawInterpretation.Reads (assignment original meanings old operations meaning)
      (universalCounitPair original language route).right
      (meaning.universal route ≫ InternalPredicateQuantifier.precomposition operations (routeValue original meanings old route)) := by
  let current := assignment original meanings old operations meaning
  have identityRead := RawInterpretation.identity current
    (power_read original language meanings old operations meaning propositionRead route.source)
  have complete := RawInterpretation.compose current
    (operator_read original language meanings old operations meaning .universal route)
    (precomposition_read original language meanings old operations meaning propositionRead route)
  exact ⟨Readout.powerMeet_read (argumentSyntax original language) current operations
    (proposition_read original language meanings old operations meaning propositionRead)
    (conjunction_read original language meanings old operations meaning conjunctionRead)
    (object_original original language meanings old operations meaning route.source) identityRead complete, complete⟩

theorem existential_unit_read (route : Route original) :
    RawInterpretation.Reads (assignment original meanings old operations meaning)
      (existentialUnitPair original language route).left
      ((functions original meanings old operations route.source).meet
        (meaning.existential route ≫ InternalPredicateQuantifier.precomposition operations (routeValue original meanings old route))
        (𝟙 (power original meanings old operations route.source))) ∧
    RawInterpretation.Reads (assignment original meanings old operations meaning)
      (existentialUnitPair original language route).right (𝟙 (power original meanings old operations route.source)) := by
  let current := assignment original meanings old operations meaning
  have identityRead := RawInterpretation.identity current
    (power_read original language meanings old operations meaning propositionRead route.source)
  have complete := RawInterpretation.compose current
    (operator_read original language meanings old operations meaning .existential route)
    (precomposition_read original language meanings old operations meaning propositionRead route)
  exact ⟨Readout.powerMeet_read (argumentSyntax original language) current operations
    (proposition_read original language meanings old operations meaning propositionRead)
    (conjunction_read original language meanings old operations meaning conjunctionRead)
    (object_original original language meanings old operations meaning route.source) complete identityRead, identityRead⟩

theorem existential_counit_read (route : Route original) :
    RawInterpretation.Reads (assignment original meanings old operations meaning)
      (existentialCounitPair original language route).left
      ((functions original meanings old operations route.target).meet (𝟙 (power original meanings old operations route.target))
        (InternalPredicateQuantifier.precomposition operations (routeValue original meanings old route) ≫ meaning.existential route)) ∧
    RawInterpretation.Reads (assignment original meanings old operations meaning)
      (existentialCounitPair original language route).right
      (InternalPredicateQuantifier.precomposition operations (routeValue original meanings old route) ≫ meaning.existential route) := by
  let current := assignment original meanings old operations meaning
  have identityRead := RawInterpretation.identity current
    (power_read original language meanings old operations meaning propositionRead route.target)
  have complete := RawInterpretation.compose current
    (precomposition_read original language meanings old operations meaning propositionRead route)
    (operator_read original language meanings old operations meaning .existential route)
  exact ⟨Readout.powerMeet_read (argumentSyntax original language) current operations
    (proposition_read original language meanings old operations meaning propositionRead)
    (conjunction_read original language meanings old operations meaning conjunctionRead)
    (object_original original language meanings old operations meaning route.target) identityRead complete, complete⟩

end Mettapedia.CategoryTheory.RelativeClosedGeneratedQuantifier.Interpretation

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.RawInterpretation

open _root_.CategoryTheory
open GeneratedCategory Interpretation

universe k w z
variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [_root_.CategoryTheory.Limits.HasFiniteLimits D]

/-- Independently successful complete readings characterize an actual quotient equation. -/
theorem parallel_readings_iff (meanings : Assignment C symbols D) (realized : Realization signature meanings)
    {source target : Object signature} {before after : RawHom source target}
    {first second : D} {f g : first ⟶ second}
    (beforeRead : Reads meanings before f) (afterRead : Reads meanings after g) :
    (Interpretation.functor meanings realized).map (classOf before) =
      (Interpretation.functor meanings realized).map (classOf after) ↔ f = g := by
  have firstRead := functor_complete_readout meanings realized before
  have secondRead := functor_complete_readout meanings realized after
  constructor
  · intro same
    have complete := beforeRead.symm.trans (firstRead.trans
      ((congrArg (fun arrow => some (⟨_, _, arrow⟩ : ArrowValue D)) same).trans (secondRead.symm.trans afterRead)))
    exact ArrowValue.arrow_injective (Option.some.inj complete)
  · intro same
    have complete := firstRead.symm.trans (beforeRead.trans
      ((congrArg (fun arrow => some (⟨first, second, arrow⟩ : ArrowValue D)) same).trans
        (afterRead.symm.trans secondRead)))
    exact ArrowValue.arrow_injective (Option.some.inj complete)

end Mettapedia.CategoryTheory.RelativeClosedSyntax.RawInterpretation
