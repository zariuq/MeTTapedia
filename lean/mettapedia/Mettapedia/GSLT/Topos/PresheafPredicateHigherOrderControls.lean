import Mettapedia.GSLT.Topos.PresheafPredicateHigherOrder
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Future-sensitive controls for the higher-order predicate fibration

A predicate gains truth after a real indexing arrow. Its characteristic sieve
records that arrow even at the earlier world where present truth is false.
Neither a present Boolean nor a natural map to constant Booleans classifies
that predicate. The same growing argument presheaf distinguishes the actual
universal quantifier from a present-world vacuity test. The positive controls
use the complete Cartesian classification and parameter equality laws.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.PresheafPredicateHigherOrderControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Functor
  Opposite MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory.PredicateDoctrine
open scoped _root_.CategoryTheory.SemilatticeInf
  Mettapedia.CategoryTheory.PredicateDoctrine.HeytingClosed

abbrev Context := WalkingParallelPairᵒᵖ

def spot : Contextᵒᵖ := op (op (.zero : WalkingParallelPair))
def future : Contextᵒᵖ := op (op (.one : WalkingParallelPair))
def restriction : spot ⟶ future :=
  (show (.zero : WalkingParallelPair) ⟶ .one from WalkingParallelPairHom.left).op.op

abbrev programs : Contextᵒᵖ ⥤ Type := (Functor.const _).obj Unit
abbrev booleans : Contextᵒᵖ ⥤ Type := (Functor.const _).obj Bool

def emptyToUnit : Empty ⟶ Unit := TypeCat.ofHom Empty.elim

abbrev growing : Contextᵒᵖ ⥤ Type :=
  (opOpEquivalence WalkingParallelPair).functor ⋙ parallelPair emptyToUnit emptyToUnit

def forgetGrowth : growing ⟶ programs where
  app _ := TypeCat.ofHom fun _ => ()
  naturality := by intros; ext value; rfl

/-- The predicate is an actual image with a genuinely changing witness fibre. -/
def proper : Subfunctor programs := Subfunctor.range forgetGrowth

theorem present_proper_false : () ∉ proper.obj spot := by
  rintro ⟨argument, _⟩
  exact Empty.elim argument

theorem future_proper_true : () ∈ proper.obj future := ⟨(), rfl⟩

theorem proper_ne_bottom : proper ≠ ⊥ := by
  intro same
  have holds := future_proper_true
  rw [same] at holds
  exact holds

theorem proper_ne_top : proper ≠ ⊤ := by
  intro same
  exact present_proper_false (same.symm ▸ (show () ∈ (⊤ : Subfunctor programs).obj spot
    from trivial))

noncomputable def futureClassifier : programs ⟶ omegaFunctor (C := Context) :=
  chiOfSubfunctor programs proper

noncomputable def presentSieve : Sieve spot.unop := futureClassifier.app spot ()

/-- The complete future arrow is retained before present truth is available. -/
theorem classifier_contains_future :
    presentSieve.arrows restriction.unop := by
  change () ∈ proper.obj future
  exact future_proper_true

theorem classifier_excludes_present :
    ¬ presentSieve.arrows (𝟙 spot.unop) := by
  change () ∉ proper.obj spot
  exact present_proper_false

theorem present_sieve_is_proper :
    presentSieve ≠ ⊥ ∧ presentSieve ≠ ⊤ := by
  constructor
  · intro same
    have holds := classifier_contains_future
    rw [same] at holds
    exact holds
  · intro same
    apply classifier_excludes_present
    rw [same]
    trivial

theorem bottom_classifier_sieve :
    (chiOfSubfunctor programs (⊥ : Subfunctor programs)).app spot () =
      (⊥ : Sieve spot.unop) := by
  apply Sieve.ext
  intro next arrow
  change False ↔ False
  rfl

/-- The two predicates agree on present falsehood but have different complete
characteristic maps. The discriminator reads the actual future sieve member. -/
theorem same_present_truth_different_classifier :
    (() ∈ proper.obj spot ↔ () ∈ (⊥ : Subfunctor programs).obj spot) ∧
      futureClassifier ≠ chiOfSubfunctor programs (⊥ : Subfunctor programs) := by
  constructor
  · exact iff_of_false present_proper_false (by intro impossible; exact impossible)
  · intro same
    apply present_sieve_is_proper.1
    exact (congrArg (fun χ => χ.app spot ()) same).trans bottom_classifier_sieve

/-- The actual truth predicate recovers the complete future-sensitive image. -/
theorem actual_generic_classifies_proper :
    (PresheafPredicateGenericTruth.truthPredicate Context).preimage futureClassifier = proper :=
  PresheafPredicateGenericTruth.characteristic_classifies programs proper

/-- The actual whole total arrow is uniquely determined among all Cartesian
arrows, not merely among names of characteristic-map implementations. -/
theorem actual_cartesian_classification_unique :
    ∃! arrow : totalOfPredicate programs proper ⟶
      PresheafPredicateGenericTruth.totalTruth Context,
      IsStronglyCartesian (presheafPredicateProjection Context) arrow.base arrow :=
  PresheafPredicateHigherOrder.generic_cartesian_unique _

def trueOnly : Subfunctor booleans where
  obj _ := {value | value = true}
  map _ := by intro value holds; exact holds

/-- A natural constant-Boolean truth map cannot classify a predicate whose
truth changes along the supplied restriction. -/
theorem no_constant_boolean_classifier :
    ¬ ∃ χ : programs ⟶ booleans, trueOnly.preimage χ = proper := by
  rintro ⟨χ, same⟩
  have later : χ.app future () = true := by
    change () ∈ (trueOnly.preimage χ).obj future
    rw [same]
    exact future_proper_true
  have natural := χ.naturality_apply restriction ()
  change χ.app future () = χ.app spot () at natural
  apply present_proper_false
  rw [← same]
  change χ.app spot () = true
  exact natural.symm.trans later

/-- At the present world every actual argument vacuously satisfies falsehood. -/
theorem present_arguments_vacuous :
    ∀ argument : growing.obj spot, argument ∈ (⊥ : Subfunctor growing).obj spot :=
  fun argument => Empty.elim argument

/-- The quantifier in the new first-order structure still sees the future
argument, so the present vacuity control cannot establish it. -/
theorem actual_forall_sees_future :
    () ∉ ((PresheafPredicateFirstOrder.firstOrder Context).forallAlong forgetGrowth
      (⊥ : Subfunctor growing)).obj spot := by
  intro allFuture
  exact allFuture future restriction () rfl

/-- The actual Heyting exponential also sees the future antecedent. Present
falsehood of the antecedent alone cannot establish this implication. -/
theorem actual_implication_sees_future : () ∉ (proper ⇨ ⊥).obj spot := by
  rw [← himpPointwise_eq_himp]
  intro impliesFalse
  exact impliesFalse future restriction future_proper_true

/-- An actual nonidentity input change also preserves both simple quantifiers
through the genuinely proved parameter pullback. -/
def negate : booleans ⟶ booleans where
  app _ := TypeCat.ofHom Bool.not
  naturality := by intros; rfl

theorem negate_nonidentity : negate ≠ 𝟙 booleans := by
  intro same
  have read := congrArg (fun η => η.app spot false) same
  exact Bool.false_ne_true read.symm

theorem both_simple_quantifiers_substitute :
    ((PresheafPredicateFirstOrder.firstOrder Context).existsAlong
      (fst booleans programs) (proper.preimage (snd booleans programs))).preimage negate =
      (PresheafPredicateFirstOrder.firstOrder Context).existsAlong (fst booleans programs)
        ((proper.preimage (snd booleans programs)).preimage (negate ⊗ₘ 𝟙 programs)) ∧
    ((PresheafPredicateFirstOrder.firstOrder Context).forallAlong
      (fst booleans programs) (proper.preimage (snd booleans programs))).preimage negate =
      (PresheafPredicateFirstOrder.firstOrder Context).forallAlong (fst booleans programs)
        ((proper.preimage (snd booleans programs)).preimage (negate ⊗ₘ 𝟙 programs)) :=
  ⟨(PresheafPredicateFirstOrder.firstOrder Context).simple_exists_substitution _ _ _,
    (PresheafPredicateFirstOrder.firstOrder Context).simple_forall_substitution _ _ _⟩

theorem contextual_equality_distinguishes_supplied_booleans :
    ((), (false, false)) ∈
        (PresheafPredicateHigherOrder.contextualEquality programs booleans).obj future ∧
      ((), (false, true)) ∉
        (PresheafPredicateHigherOrder.contextualEquality programs booleans).obj future := by
  constructor
  · exact (PresheafPredicateHigherOrder.contextualEquality_readout _ _ _ _).mpr rfl
  · intro holds
    exact Bool.false_ne_true
      ((PresheafPredicateHigherOrder.contextualEquality_readout _ _ _ _).mp holds)

theorem contextual_equality_follows_nonidentity_parameter :
    (PresheafPredicateHigherOrder.contextualEquality booleans programs).preimage
      (negate ⊗ₘ 𝟙 (programs ⊗ programs)) =
        PresheafPredicateHigherOrder.contextualEquality booleans programs :=
  PresheafPredicateHigherOrder.contextualEquality_substitution negate programs

/-- Implication substitution is the actual categorical exponential comparison. -/
theorem actual_implication_comparison {P Q : Contextᵒᵖ ⥤ Type} (f : P ⟶ Q)
    (φ ψ : Subfunctor Q) :
    (expComparison ((PresheafPredicateFirstOrder.firstOrder Context).toIndexedHeyting.reindexFunctor
      f) φ).natTrans.app ψ = eqToHom (preimage_himp φ ψ f) :=
  (PresheafPredicateFirstOrder.firstOrder Context).exponentialComparison_eq f φ ψ

end Mettapedia.GSLT.Topos.PresheafPredicateHigherOrderControls
