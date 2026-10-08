import Mettapedia.GSLT.Topos.PresheafPredicateQuantifierBaseChange
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Quantifier substitution with lifting and future arguments

An actual pullback supplies both quantifier comparisons. A commuting square
that omits matching pairs fails the universal comparison. A growing presheaf
has no present arguments but acquires an argument after a genuine restriction;
its universal predicate therefore differs from a test of present inhabitants.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.PresheafPredicateQuantifierBaseChangeControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits

abbrev Context := WalkingParallelPairᵒᵖ

def spot : Contextᵒᵖ := Opposite.op (Opposite.op (.zero : WalkingParallelPair))

def future : Contextᵒᵖ := Opposite.op (Opposite.op (.one : WalkingParallelPair))

def restriction : spot ⟶ future :=
  (show (.zero : WalkingParallelPair) ⟶ .one from WalkingParallelPairHom.left).op.op

abbrev booleans : Contextᵒᵖ ⥤ Type := (Functor.const _).obj Bool

def trueOnly : Subfunctor booleans where
  obj _ := {value | value = true}
  map _ := by intro value holds; exact holds

def alwaysTrue : booleans ⟶ booleans where
  app _ := TypeCat.ofHom fun _ => true
  naturality := by intros; rfl

theorem genuine_square : IsPullback (𝟙 booleans) alwaysTrue alwaysTrue (𝟙 booleans) :=
  IsPullback.of_id_fst

/-- The independently constructed quantifiers commute through the
actual square, even though one of its maps erases a Boolean. -/
theorem both_quantifiers_follow_pullback :
    (forallAlong alwaysTrue trueOnly).preimage (𝟙 booleans) =
        forallAlong alwaysTrue (trueOnly.preimage (𝟙 booleans)) ∧
      (trueOnly.image alwaysTrue).preimage (𝟙 booleans) =
        (trueOnly.preimage (𝟙 booleans)).image alwaysTrue :=
  ⟨forallAlong_beckChevalley _ _ _ _ genuine_square trueOnly,
    image_beckChevalley _ _ _ _ genuine_square trueOnly⟩

theorem missing_pairs_square_commutes :
    CommSq alwaysTrue alwaysTrue (𝟙 booleans) (𝟙 booleans) := ⟨by simp⟩

theorem right_hand_false_member :
    false ∈ (forallAlong alwaysTrue (trueOnly.preimage alwaysTrue)).obj spot := by
  intro next arrow argument over
  rfl

theorem left_hand_false_excluded :
    false ∉ ((forallAlong (𝟙 booleans) trueOnly).preimage (𝟙 booleans)).obj spot := by
  intro holds
  have impossible := holds spot (𝟙 spot) false rfl
  exact Bool.false_ne_true impossible

/-- Commutativity alone does not supply the missing matching pairs. -/
theorem commuting_square_does_not_give_universal_comparison :
    ((forallAlong (𝟙 booleans) trueOnly).preimage (𝟙 booleans)) ≠
      forallAlong alwaysTrue (trueOnly.preimage alwaysTrue) := by
  intro same
  exact left_hand_false_excluded (same.symm ▸ right_hand_false_member)

theorem missing_pairs_square_is_not_pullback :
    ¬ IsPullback alwaysTrue alwaysTrue (𝟙 booleans) (𝟙 booleans) := by
  intro square
  exact commuting_square_does_not_give_universal_comparison
    (forallAlong_beckChevalley _ _ _ _ square trueOnly)

def emptyToUnit : Empty ⟶ Unit := TypeCat.ofHom Empty.elim

/-- A real context arrow acquires an inhabitant: the initial object
component is Empty, and its later object component is Unit. -/
abbrev growing : Contextᵒᵖ ⥤ Type :=
  (opOpEquivalence WalkingParallelPair).functor ⋙ parallelPair emptyToUnit emptyToUnit

abbrev unitPrograms : Contextᵒᵖ ⥤ Type := (Functor.const _).obj Unit

def forgetGrowth : growing ⟶ unitPrograms where
  app _ := TypeCat.ofHom fun _ => ()
  naturality := by intros; ext value; rfl

theorem present_arguments_are_empty :
    ∀ value : growing.obj spot, value ∈ (⊥ : Subfunctor growing).obj spot :=
  fun value => Empty.elim value

theorem a_future_argument_exists : Nonempty (growing.obj future) := ⟨()⟩

/-- A predicate cannot ignore the future argument simply because the
present world has no argument lying over the supplied base value. -/
theorem present_test_does_not_establish_universal :
    () ∉ (forallAlong forgetGrowth (⊥ : Subfunctor growing)).obj spot := by
  intro holds
  exact holds future restriction () rfl

end Mettapedia.GSLT.Topos.PresheafPredicateQuantifierBaseChangeControls
