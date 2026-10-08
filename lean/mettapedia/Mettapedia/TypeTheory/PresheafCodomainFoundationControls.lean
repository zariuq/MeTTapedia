import Mettapedia.TypeTheory.PresheafCodomainFoundation
import Mettapedia.TypeTheory.PresheafSliceClassifierReadout
import Mettapedia.GSLT.Topos.PresheafPredicateHigherOrderControls
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Witness and future controls for presheaf codomain comprehension

A nonidentity base map retains genuinely dependent finite witnesses in
the canonical strong sum and in complete dependent-function evaluation.
A future-sensitive classifier distinguishes predicates that agree on
present truth. A commuting square fails Cartesian universality, and a
presently empty argument object does not make the actual dependent
product of falsehood inhabited.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.TypeTheory.PresheafCodomainFoundationControls

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open Mettapedia.CategoryTheory
open Mettapedia.GSLT.Topos
open PresheafCodomainFoundation PresheafSliceClassifierReadout

namespace Varying

abbrev Context := WalkingParallelPairᵒᵖ
abbrev programs : Contextᵒᵖ ⥤ Type := (Functor.const _).obj Nat
abbrev witnesses : Contextᵒᵖ ⥤ Type :=
  (Functor.const _).obj (Σ n : Nat, Fin (n + 2))

def forget : witnesses ⟶ programs where
  app _ := TypeCat.ofHom Sigma.fst
  naturality := by intros; rfl

def advance : programs ⟶ programs where
  app _ := TypeCat.ofHom Nat.succ
  naturality := by intros; rfl

instance advance_mono : Mono advance := by
  rw [NatTrans.mono_iff_mono_app]
  intro world
  exact (mono_iff_injective _).mpr Nat.succ_injective

theorem advance_nonidentity : advance ≠ 𝟙 programs := by
  intro same
  have readout := congrArg
    (fun arrow : programs ⟶ programs =>
      arrow.app (op (op (.zero : WalkingParallelPair))) (0 : Nat)) same
  exact Nat.zero_ne_one readout.symm

def display : Over programs := Over.mk forget

/-- This map is the domain of the actual adjunction unit followed by
the actual Cartesian lift. Its readout retains the complete supplied pair. -/
theorem strong_sum_complete (world : Contextᵒᵖ) (supplied : Σ n : Nat, Fin (n + 2)) :
    (PresheafCodomainFoundation.strongSum advance display).hom.app world supplied = supplied :=
  congrArg (fun arrow => arrow.app world supplied)
    (CodomainComprehension.canonicalSumSquare_domain advance display)

theorem strong_sum_changed_base (world : Contextᵒᵖ) (supplied : Σ n : Nat, Fin (n + 2)) :
    ((Over.map advance).obj display).hom.app world
      ((PresheafCodomainFoundation.strongSum advance display).hom.app world supplied) =
        supplied.1 + 1 := by
  rw [strong_sum_complete]
  rfl

def firstWitness : Σ n : Nat, Fin (n + 2) := ⟨0, ⟨0, by decide⟩⟩
def secondWitness : Σ n : Nat, Fin (n + 2) := ⟨0, ⟨1, by decide⟩⟩

theorem equal_base_distinct_strong_sum (world : Contextᵒᵖ) :
    forget.app world firstWitness = forget.app world secondWitness ∧
      (PresheafCodomainFoundation.strongSum advance display).hom.app world firstWitness ≠
        (PresheafCodomainFoundation.strongSum advance display).hom.app world secondWitness := by
  constructor
  · rfl
  · rw [strong_sum_complete, strong_sum_complete]
    intro same
    have readout := congrArg (fun value : Σ n : Nat, Fin (n + 2) => value.2.val) same
    exact Nat.zero_ne_one readout

def body : (Over.pullback advance).obj ((Over.map advance).obj display) ⟶ display :=
  Over.homMk (pullback.fst (forget ≫ advance) advance) (by
    apply (cancel_mono advance).mp
    rw [Category.assoc]
    exact pullback.condition)

def completeFunction : (Over.map advance).obj display ⟶
    ((closedComprehension Context).dependentProduct advance).obj display :=
  CodomainClosedComprehension.abstraction (closedComprehension Context) advance body

/-- The new closed-comprehension abstraction is evaluated at the exact
unit-supplied argument and returns the supplied dependent finite witness. -/
theorem complete_function_application (world : Contextᵒᵖ)
    (supplied : Σ n : Nat, Fin (n + 2)) :
    ((Over.pullback advance).map completeFunction ≫
        CodomainClosedComprehension.evaluation (closedComprehension Context) advance display).left.app
      world (((Over.mapPullbackAdj advance).unit.app display).left.app world supplied) = supplied := by
  have computes := CodomainClosedComprehension.beta
    (closedComprehension Context) advance body
  have readout := congrArg (fun arrow => arrow.left.app world
    (((Over.mapPullbackAdj advance).unit.app display).left.app world supplied)) computes
  change _ = body.left.app world
    (((Over.mapPullbackAdj advance).unit.app display).left.app world supplied) at readout
  refine readout.trans ?_
  have retained : ((Over.mapPullbackAdj advance).unit.app display).left ≫ body.left =
      𝟙 witnesses :=
    pullback.lift_fst (f := forget ≫ advance) (g := advance) (𝟙 witnesses) forget (by simp)
  exact congrArg (fun arrow => arrow.app world supplied) retained

theorem two_functions_readouts_differ (world : Contextᵒᵖ) :
    ((Over.pullback advance).map completeFunction ≫
        CodomainClosedComprehension.evaluation (closedComprehension Context) advance display).left.app
        world (((Over.mapPullbackAdj advance).unit.app display).left.app world firstWitness) ≠
      ((Over.pullback advance).map completeFunction ≫
        CodomainClosedComprehension.evaluation (closedComprehension Context) advance display).left.app
        world (((Over.mapPullbackAdj advance).unit.app display).left.app world secondWitness) := by
  rw [complete_function_application, complete_function_application]
  intro same
  exact Nat.zero_ne_one
    (congrArg (fun value : Σ n : Nat, Fin (n + 2) => value.2.val) same)

end Varying

namespace Future

open Mettapedia.GSLT.Topos.PresheafPredicateHigherOrderControls

def display : Over programs := Over.mk (𝟙 programs)

def selectedCharacteristic : display ⟶ (PresheafSliceLogicalAction.sliceTopos programs).classifier.Ω :=
  characteristic display proper

theorem selected_sieve_contains_future :
    ((selectedCharacteristic.left ≫ prod.fst).app spot ()).arrows restriction.unop := by
  rw [show selectedCharacteristic.left ≫ prod.fst = chiOfSubfunctor programs proper from
    characteristic_sieve display proper]
  exact classifier_contains_future

theorem selected_sieve_excludes_present :
    ¬ ((selectedCharacteristic.left ≫ prod.fst).app spot ()).arrows (𝟙 spot.unop) := by
  rw [show selectedCharacteristic.left ≫ prod.fst = chiOfSubfunctor programs proper from
    characteristic_sieve display proper]
  exact classifier_excludes_present

theorem present_equal_complete_slice_classifiers_differ :
    (() ∈ proper.obj spot ↔ () ∈ (⊥ : Subfunctor programs).obj spot) ∧
      characteristic display proper ≠ characteristic display (⊥ : Subfunctor programs) := by
  refine ⟨same_present_truth_different_classifier.1, ?_⟩
  intro same
  have readout := congrArg (fun arrow => arrow.left ≫ prod.fst) same
  rw [characteristic_sieve, characteristic_sieve] at readout
  exact same_present_truth_different_classifier.2 readout

def booleanDisplay : Over booleans := Over.mk (𝟙 booleans)

def booleanFuture : Subfunctor booleans where
  obj world := {value | value = true ∧ () ∈ proper.obj world}
  map arrow := by
    intro value holds
    exact ⟨holds.1, proper.map arrow holds.2⟩

def suppliedBoolean : booleans ⟶ ((Over.pullback negate).obj booleanDisplay).left :=
  pullback.lift negate (𝟙 booleans) (by
    change negate ≫ 𝟙 booleans = 𝟙 booleans ≫ negate
    simp)

def substitutedBooleanClassifier : booleans ⟶ omegaFunctor (C := Context) :=
  suppliedBoolean ≫ ((Over.pullback negate).map
      (characteristic booleanDisplay booleanFuture)).left ≫
    (PresheafSliceLogicalAction.classifierComparison negate).hom.left ≫ prod.fst

theorem substituted_boolean_readout :
    substitutedBooleanClassifier = negate ≫ chiOfSubfunctor booleans booleanFuture := by
  change suppliedBoolean ≫ _ = _
  rw [substitution_sieve]
  change pullback.lift negate (𝟙 booleans) _ ≫ (pullback.fst _ negate ≫ _) = _
  rw [← Category.assoc, pullback.lift_fst]
  rfl

/-- The actual classifier pullback reads the changed Boolean input and its
complete future sieve, including a discriminator in the opposite input. -/
theorem nonidentity_classifier_future_readout :
    (substitutedBooleanClassifier.app spot false).arrows restriction.unop ∧
      ¬ (substitutedBooleanClassifier.app spot true).arrows restriction.unop := by
  rw [substituted_boolean_readout]
  constructor
  · change true = true ∧ () ∈ proper.obj future
    exact ⟨rfl, future_proper_true⟩
  · change ¬ (false = true ∧ () ∈ proper.obj future)
    intro holds
    exact Bool.false_ne_true holds.1

def commutingSquare : Arrow.mk forgetGrowth ⟶ Arrow.mk (𝟙 programs) :=
  Arrow.homMk forgetGrowth (𝟙 programs) (by simp)

theorem commuting_square_not_pullback :
    ¬ IsPullback commutingSquare.left (Arrow.mk forgetGrowth).hom
      (Arrow.mk (𝟙 programs)).hom commutingSquare.right := by
  intro square
  let impossible : programs ⟶ growing := square.lift (𝟙 programs) (𝟙 programs) (by
    change 𝟙 programs ≫ 𝟙 programs = 𝟙 programs ≫ 𝟙 programs
    rfl)
  exact Empty.elim (impossible.app spot ())

theorem commuting_square_not_cartesian :
    ¬ (PresheafCodomainFoundation.codomain Context).IsCartesian
      commutingSquare.right commutingSquare := by
  intro cartesian
  exact commuting_square_not_pullback
    ((PresheafCodomainFoundation.cartesian_iff_pullback Context commutingSquare).mp cartesian)

abbrev empty : Contextᵒᵖ ⥤ Type := (Functor.const _).obj Empty

def emptyProjection : empty ⟶ growing where
  app _ := TypeCat.ofHom Empty.elim
  naturality := by intros; ext value; exact Empty.elim value

def falseDisplay : Over growing := Over.mk emptyProjection

def universalFalse : Over programs :=
  ((closedComprehension Context).dependentProduct forgetGrowth).obj falseDisplay

/-- The actual presheaf slice product is empty at the present world because
its evaluation must also accommodate the supplied future argument. -/
theorem actual_product_future_obstruction : IsEmpty (universalFalse.left.obj spot) := by
  refine ⟨fun function => ?_⟩
  let later := universalFalse.left.map restriction function
  have square := (IsPullback.of_hasPullback universalFalse.hom forgetGrowth).map
    ((evaluation (Contextᵒᵖ) (Type)).obj future)
  let argument :
      ((Over.pullback forgetGrowth).obj universalFalse).left.obj future :=
    square.lift (TypeCat.ofHom fun (_ : Unit) => later)
      (TypeCat.ofHom fun (_ : Unit) => ()) (by ext; rfl) ()
  exact Empty.elim
    ((CodomainClosedComprehension.evaluation (closedComprehension Context)
      forgetGrowth falseDisplay).left.app future argument)

theorem present_arguments_do_not_supply_product :
    (∀ argument : growing.obj spot, argument ∈ (⊥ : Subfunctor growing).obj spot) ∧
      IsEmpty (universalFalse.left.obj spot) :=
  ⟨present_arguments_vacuous, actual_product_future_obstruction⟩

end Future
end Mettapedia.TypeTheory.PresheafCodomainFoundationControls
