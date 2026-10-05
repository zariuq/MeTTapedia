import Mettapedia.GSLT.Logic.EnumerationMetric
import Mettapedia.GSLT.Logic.HennessyMilnerAdequacy

/-!
# Finding Mind's enumerated HML metric on an admitted system

The formula enumeration is supplied with coverage. Its least distinguishing
index has exactly the dyadic distance of Definition 16.3. Distance zero is
logical equivalence; under the existing image-finiteness hypothesis it is
bisimilarity, so the ultrapseudometric descends to an ultrametric on those
classes. Numerical distance retains the chosen enumeration.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.HennessyMilner

open Mettapedia.GSLT.Logic

universe u a l

variable {S : GSLT.{u}} (system : System.{a, l} S)
  (enumeration : Nat → Formula system.Atom system.Label)

namespace System

noncomputable def enumeratedObservations : BudgetedObservations S.Term :=
  enumeratedTests (fun index => system.sat (enumeration index))

theorem enumerated_zero_iff_logical (covers : Function.Surjective enumeration) (left right : S.Term) :
    (system.enumeratedObservations enumeration).distance left right = 0 ↔
      system.LogicallyEquivalent left right :=
  enumerated_zero_iff system.sat enumeration covers left right

theorem enumerated_zero_iff_bisimilar (covers : Function.Surjective enumeration)
    (finite : system.ImageFiniteModulo) (left right : S.Term) :
    (system.enumeratedObservations enumeration).distance left right = 0 ↔
      system.Bisimilar left right :=
  (system.enumerated_zero_iff_logical enumeration covers left right).trans
    (system.logicallyEquivalent_iff_bisimilar finite left right)

theorem enumerated_distance_respects_bisimilarity {left left' right right' : S.Term}
    (before : system.Bisimilar left left') (after : system.Bisimilar right right') :
    (system.enumeratedObservations enumeration).distance left right =
      (system.enumeratedObservations enumeration).distance left' right' :=
  BudgetedObservations.distance_congr _
    (fun index => system.logicallyEquivalent_of_bisimilar before (enumeration index))
    (fun index => system.logicallyEquivalent_of_bisimilar after (enumeration index))

theorem enumerated_distance_first (left right : S.Term) (first : Nat)
    (different : ¬ (system.sat (enumeration first) left ↔ system.sat (enumeration first) right))
    (before : ∀ index, index < first →
      (system.sat (enumeration index) left ↔ system.sat (enumeration index) right)) :
    (system.enumeratedObservations enumeration).distance left right = (1 / 2 : ℝ) ^ first :=
  Mettapedia.GSLT.Logic.enumerated_distance_first _ left right first different before

end System

end Mettapedia.GSLT.HennessyMilner
