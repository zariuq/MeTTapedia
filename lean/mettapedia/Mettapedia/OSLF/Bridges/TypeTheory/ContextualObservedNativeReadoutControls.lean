import Mettapedia.OSLF.Bridges.TypeTheory.ContextualObservedNativeReadout
import Mettapedia.GSLT.Logic.ContextualObservedCoalgebraControls

/-!
# Native predicate controls with infinitely many declared result values

Each result predicate factors through the full observed quotient, and the
result classifiers are pairwise distinct. A predicate inspecting a forgotten
receipt tag has no such factorization, although it is a genuine stable native
predicate. Omitting readings makes all terminal results ordinary bisimilar
and therefore loses the positive result classifier.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Bridges.TypeTheory.ContextualObservedNativeReadoutControls

open _root_.CategoryTheory
open Mettapedia.GSLT ContextualObservedCoalgebraControls
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open PowerClassPresheafDescent.Controls
open ContextualObservedNativeReadout

abbrev transition := emptyCoalgebra source

def resultPredicate (desired : Nat) : Subfunctor source where
  obj _ := {argument | argument.1.1 = desired}
  map _ _ holds := holds

theorem result_invariant (desired : Nat) : Invariant transition observes (resultPredicate desired) := by
  intro point left right related
  have same := equality_preserves_reading point left right
    ((ContextualObservedCoalgebra.value_eq_iff transition observes worlds arrows atomCoding point left right).mpr related)
    ⟨0, by decide⟩
  change left.1.1 = right.1.1 at same
  exact Iff.of_eq (congrArg (fun value => value = desired) same)

abbrev resultClassifier (desired : Nat) :=
  descendedClassifier transition observes worlds arrows atomCoding (resultPredicate desired)

theorem resultClassifier_factors (desired : Nat) :
    ∀ point argument, (resultClassifier desired).app point
      ((projection transition observes worlds arrows atomCoding).app point argument) =
        (ContextualObservedNativeTypes.Classifier.characteristic (resultPredicate desired)).app point argument :=
  descendedClassifier_square transition observes worlds arrows atomCoding _ (result_invariant desired)

theorem infinitely_many_native_result_classifiers : Function.Injective resultClassifier := by
  intro first second same
  let argument := state 0 first 0 false false
  have sieves := congrArg (fun classifier => classifier.app (world 0)
    ((projection transition observes worlds arrows atomCoding).app (world 0) argument)) same
  have predicates := (resultClassifier_factors first (world 0) argument).symm.trans
    (sieves.trans (resultClassifier_factors second (world 0) argument))
  have truths := congrArg (fun sieve : Sieve (world 0).unop => sieve.arrows (𝟙 (world 0).unop)) predicates
  have agrees := (ContextualObservedNativeTypes.Classifier.characteristic_truth
    (resultPredicate first) (world 0) argument).symm.trans
      ((Iff.of_eq truths).trans (ContextualObservedNativeTypes.Classifier.characteristic_truth
        (resultPredicate second) (world 0) argument))
  exact agrees.mp rfl

def receiptPredicate : Subfunctor source where
  obj _ := {argument | argument.2.2 = true}
  map _ _ holds := holds

theorem receipt_not_invariant : ¬ Invariant transition observes receiptPredicate := by
  intro invariant
  have related := (ContextualObservedCoalgebra.value_eq_iff transition observes worlds arrows atomCoding
    (world 0) _ _).mp (unobserved_receipt_aliases 0 0 0 false).2
  exact Bool.noConfusion (invariant (world 0) _ _ related |>.mp rfl)

theorem receipt_classifier_cannot_factor :
    ¬ ∃ classifier : NatTrans (observed transition observes worlds arrows atomCoding)
        (Mettapedia.GSLT.Topos.omegaFunctor (C := Stages)),
      ∀ point argument, classifier.app point ((projection transition observes worlds arrows atomCoding).app point argument) =
        (ContextualObservedNativeTypes.Classifier.characteristic receiptPredicate).app point argument :=
  fun factor => receipt_not_invariant
    ((classifier_factors_iff transition observes worlds arrows atomCoding receiptPredicate).mp factor)

theorem future_only_bisimulation_loses_result_predicate :
    ContextualCoalgebraBisimulation.Bisimilar transition (world 0)
      (state 0 0 0 false false) (state 0 1 0 false false) ∧
      ¬ (state 0 0 0 false false ∈ (resultPredicate 0).obj (world 0) ↔
        state 0 1 0 false false ∈ (resultPredicate 0).obj (world 0)) :=
  ⟨omitted_children_lose_every_result _ _, fun agree => Nat.one_ne_zero (agree.mp rfl)⟩

end Mettapedia.OSLF.Bridges.TypeTheory.ContextualObservedNativeReadoutControls
