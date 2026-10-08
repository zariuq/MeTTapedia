import Mettapedia.GSLT.Topos.YonedaPredicateReadout
import Mettapedia.CategoryTheory.PredicateDoctrineClosed
import Mathlib.CategoryTheory.Limits.Preorder
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Varying Yoneda predicate controls and a nonrepresentability boundary

A genuine Boolean-lattice base has a proper predicate which becomes true
after an actual nonidentity substitution. Its function predicate retains
that restriction through base evaluation. A separate parallel-pair base
has a presheaf exponential with two distinct generalized elements where
neither representable has two, so representability requires a hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.GSLT.Topos.YonedaPredicateControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory
open scoped _root_.CategoryTheory.SemilatticeInf
open scoped Mettapedia.CategoryTheory.PredicateDoctrine.HeytingClosed

namespace Varying

abbrev Base := Set Bool

def safe : Base := {true}

def inclusion : safe ⟶ (⊤ : Base) := homOfLE le_top

def allowed : Subfunctor (yoneda.obj (⊤ : Base)) where
  obj U := { _point | U.unop ≤ safe }
  map f := by intro point held; exact f.unop.le.trans held

theorem safe_membership : inclusion ∈ allowed.obj (op safe) := by
  change safe ≤ safe
  exact le_rfl

theorem top_not_membership : ¬ (𝟙 (⊤ : Base)) ∈ allowed.obj (op (⊤ : Base)) := by
  intro included
  have impossible := included (show false ∈ (⊤ : Base) from Set.mem_univ _)
  simp only [safe, Set.mem_singleton_iff] at impossible
  cases impossible

theorem allowed_proper : allowed ≠ ⊤ := by
  intro equality
  apply top_not_membership
  rw [equality]
  exact Set.mem_univ _

theorem allowed_inhabited : allowed ≠ ⊥ := by
  intro equality
  have membership := safe_membership
  rw [equality] at membership
  exact membership

/-- An actual nonidentity substitution makes the proper predicate true. -/
theorem substitution_changes_predicate : allowed.preimage (yoneda.map inclusion) = ⊤ := by
  apply Subfunctor.ext
  funext U
  ext point
  constructor
  · intro _; exact Set.mem_univ _
  · intro _; exact point.le

theorem inclusion_not_identity_domain : safe ≠ (⊤ : Base) := by
  intro equality
  apply top_not_membership
  change (⊤ : Base) ≤ safe
  rw [equality]

/-- The complete future-sensitive function predicate reads the actual varying
world condition, including the identity future. -/
theorem function_readout (U : Base) (function : U ⟶ (ihom (⊤ : Base)).obj (⊤ : Base)) :
    function ∈ (canonicalYonedaExpPredicate (⊤ : Subfunctor (yoneda.obj (⊤ : Base)))
      allowed).obj (op U) ↔ U ≤ safe := by
  rw [YonedaPredicate.mem_canonicalExponential]
  constructor
  · intro held
    exact held U (𝟙 U) (homOfLE le_top) (Set.mem_univ _)
  · intro included V future _argument _admissible
    exact future.le.trans included

def fullFunction (U : Base) : U ⟶ (ihom (⊤ : Base)).obj (⊤ : Base) :=
  homOfLE (by change U ≤ (⊤ : Base) ⇨ ⊤; rw [himp_self]; exact le_top)

theorem safe_function_admitted :
    fullFunction safe ∈
      (canonicalYonedaExpPredicate (⊤ : Subfunctor (yoneda.obj (⊤ : Base))) allowed).obj
        (op safe) := (function_readout _ _).mpr le_rfl

theorem unrestricted_function_rejected :
    ¬ fullFunction (⊤ : Base) ∈
      (canonicalYonedaExpPredicate (⊤ : Subfunctor (yoneda.obj (⊤ : Base))) allowed).obj
        (op (⊤ : Base)) := by
  intro admitted
  exact top_not_membership ((function_readout _ _).mp admitted)

abbrev input : YonedaPredicate.Total Base := YonedaPredicate.ofPredicate (⊤ : Base) ⊤
abbrev output : YonedaPredicate.Total Base := YonedaPredicate.ofPredicate (⊤ : Base) allowed
abbrev scope : YonedaPredicate.Total Base := YonedaPredicate.ofPredicate safe ⊤

/-- A supplied body earns its result guard from the actual product-domain
map, rather than from an independent assumption of the desired entailment. -/
def scopedBody : YonedaPredicate.product input scope ⟶ output :=
  YonedaPredicate.homOfEntailment (fst (⊤ : Base) safe) (by
    intro U point _held
    exact point.le.trans inf_le_right)

def scopedLambda : scope ⟶ YonedaPredicate.exponentialObject input output :=
  YonedaPredicate.curry scopedBody

theorem scoped_beta : YonedaPredicate.uncurry scopedLambda = scopedBody :=
  YonedaPredicate.uncurry_curry scopedBody

abbrev smallerScope : YonedaPredicate.Total Base := YonedaPredicate.ofPredicate (⊥ : Base) ⊤

def smallerInclusion : smallerScope ⟶ scope :=
  YonedaPredicate.homOfEntailment (homOfLE bot_le) le_top

/-- This is actual nonidentity context substitution of the supplied admitted
body and its full transpose. -/
theorem scoped_substitution :
    YonedaPredicate.curry
      (YonedaPredicate.productMap (𝟙 input) smallerInclusion ≫ scopedBody) =
      smallerInclusion ≫ scopedLambda :=
  YonedaPredicate.curry_naturality smallerInclusion scopedBody

/-- The finite limits are earned from the complete lattice's actual greatest
lower bounds; they are then lifted by the general restricted construction. -/
noncomputable instance baseHasLimits : HasLimits Base where
  has_limits_of_shape _ := { has_limit := fun K => ⟨⟨Preorder.limitConeOfIsGLB K
    (isGLB_sInf (Set.range K.obj))⟩⟩ }

example : HasFiniteLimits (YonedaPredicate.Total Base) := inferInstance
example : MonoidalClosed (YonedaPredicate.Total Base) := inferInstance
example : MonoidalClosedFunctor (YonedaPredicate.projection Base) := inferInstance

end Varying

namespace Nonrepresentable

open WalkingParallelPair WalkingParallelPairHom

abbrev exponential := (ihom (yoneda.obj zero)).obj (yoneda.obj one)

def leftBody : yoneda.obj zero ⊗ yoneda.obj one ⟶ yoneda.obj one :=
  fst (yoneda.obj zero) (yoneda.obj one) ≫ yoneda.map left

def rightBody : yoneda.obj zero ⊗ yoneda.obj one ⟶ yoneda.obj one :=
  fst (yoneda.obj zero) (yoneda.obj one) ≫ yoneda.map right

noncomputable def leftFunction : exponential.obj (op one) :=
  _root_.CategoryTheory.yonedaEquiv (MonoidalClosed.curry leftBody)

noncomputable def rightFunction : exponential.obj (op one) :=
  _root_.CategoryTheory.yonedaEquiv (MonoidalClosed.curry rightBody)

theorem functions_distinct : leftFunction ≠ rightFunction := by
  intro equality
  have transposes := _root_.CategoryTheory.yonedaEquiv.injective equality
  have bodies := MonoidalClosed.curry_injective transposes
  have reading := congrArg (fun transformation => transformation.app (op zero)
    (𝟙 zero, left)) bodies
  change (left : zero ⟶ one) = right at reading
  cases reading

/-- Neither actual representable can carry the two exponential elements.
This is a failure of representability, not merely a missing chosen witness. -/
theorem no_representation (X : WalkingParallelPair) :
    ¬ Nonempty (yoneda.obj X ≅ exponential) := by
  rintro ⟨representation⟩
  cases X with
  | zero =>
    have impossible := representation.inv.app (op one) leftFunction
    change WalkingParallelPairHom one zero at impossible
    cases impossible
  | one =>
    apply functions_distinct
    have unique : Subsingleton (one ⟶ one) := ⟨by intro first second; cases first; cases second; rfl⟩
    have same : representation.inv.app (op one) leftFunction =
        representation.inv.app (op one) rightFunction := unique.elim _ _
    have injective := (asIso (representation.inv.app (op one))).toEquiv.injective
    exact injective same

end Nonrepresentable

end Mettapedia.GSLT.Topos.YonedaPredicateControls
