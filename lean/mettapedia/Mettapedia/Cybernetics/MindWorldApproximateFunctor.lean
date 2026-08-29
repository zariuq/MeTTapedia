import Mettapedia.GSLT.Dynamics.TypedValueGeometry
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Goal- and cost-sensitive mind--world correspondences

The mind--world correspondence principle asks for a compositional map from
world processes to cognitive processes.  Requiring an exact functor is often
too strong: a bounded mind compresses, approximates, and sometimes pays more
to preserve one composition than another.  Merely giving unrelated object and
arrow maps is too weak.

This module places the useful middle object between those extremes.  A
`PathCorrespondence` maps objects and arrows and equips every cognitive hom
with an authored directed geometry.  `BoundedPathCorrespondence` bounds the
identity and composition defects.  `MindWorldCorrespondence` adds goal weight
and resource cost without identifying either with geometric error.

An exact functor embeds with zero defect.  Conversely, a positive defect
forbids exactness and forces a positive budget.  These controls prevent an
arbitrary learned mapping from being called compositional merely because its
source and target types line up.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.MindWorldApproximateFunctor

open CategoryTheory
open Mettapedia.GSLT.Dynamics.TypedValueGeometry

universe uWorld vWorld uMind vMind

variable (World : Type uWorld) [Category.{vWorld} World]
variable (Mind : Type uMind) [Category.{vMind} Mind]

/-! ## Geometric maps of process paths -/

/-- An object/arrow correspondence with a local geometry on every cognitive
hom.  No functor law is assumed yet; its failure is observable as defect. -/
structure PathCorrespondence where
  obj : World → Mind
  map : {source target : World} →
    (source ⟶ target) → (obj source ⟶ obj target)
  geometry : ∀ source target,
    ValueGeometry (obj source ⟶ obj target)

namespace PathCorrespondence

variable {World Mind}

/-- Failure to preserve an identity path. -/
def identityDefect (correspondence : PathCorrespondence World Mind)
    (object : World) : ℝ :=
  (correspondence.geometry object object).distance
    (correspondence.map (𝟙 object)) (𝟙 (correspondence.obj object))

/-- Failure to map a composite as the composite of mapped paths. -/
def compositionDefect (correspondence : PathCorrespondence World Mind)
    {first middle last : World} (earlier : first ⟶ middle)
    (later : middle ⟶ last) : ℝ :=
  (correspondence.geometry first last).distance
    (correspondence.map (earlier ≫ later))
    (correspondence.map earlier ≫ correspondence.map later)

def PreservesIdentity (correspondence : PathCorrespondence World Mind) : Prop :=
  ∀ object, correspondence.map (𝟙 object) = 𝟙 (correspondence.obj object)

def PreservesComposition
    (correspondence : PathCorrespondence World Mind) : Prop :=
  ∀ {first middle last : World} (earlier : first ⟶ middle)
    (later : middle ⟶ last),
    correspondence.map (earlier ≫ later) =
      correspondence.map earlier ≫ correspondence.map later

/-- Exactness is stated independently of the geometry. -/
def Exact (correspondence : PathCorrespondence World Mind) : Prop :=
  correspondence.PreservesIdentity ∧ correspondence.PreservesComposition

/-- An exact correspondence is an ordinary functor. -/
def toFunctor (correspondence : PathCorrespondence World Mind)
    (exact : correspondence.Exact) : World ⥤ Mind where
  obj := correspondence.obj
  map := correspondence.map
  map_id := exact.1
  map_comp := exact.2

theorem identityDefect_nonnegative
    (correspondence : PathCorrespondence World Mind) (object : World) :
    0 ≤ correspondence.identityDefect object :=
  (correspondence.geometry object object).nonnegative _ _

theorem compositionDefect_nonnegative
    (correspondence : PathCorrespondence World Mind)
    {first middle last : World} (earlier : first ⟶ middle)
    (later : middle ⟶ last) :
    0 ≤ correspondence.compositionDefect earlier later :=
  (correspondence.geometry first last).nonnegative _ _

theorem identityDefect_eq_zero_of_exact
    (correspondence : PathCorrespondence World Mind)
    (exact : correspondence.Exact) (object : World) :
    correspondence.identityDefect object = 0 := by
  rw [identityDefect, exact.1 object]
  exact (correspondence.geometry object object).self _

theorem compositionDefect_eq_zero_of_exact
    (correspondence : PathCorrespondence World Mind)
    (exact : correspondence.Exact)
    {first middle last : World} (earlier : first ⟶ middle)
    (later : middle ⟶ last) :
    correspondence.compositionDefect earlier later = 0 := by
  rw [compositionDefect, exact.2 earlier later]
  exact (correspondence.geometry first last).self _

/-- Negative control: a visibly positive identity defect rules out exact
functoriality. -/
theorem positive_identityDefect_not_exact
    (correspondence : PathCorrespondence World Mind) (object : World)
    (positive : 0 < correspondence.identityDefect object) :
    ¬ correspondence.Exact := by
  intro exact
  rw [correspondence.identityDefect_eq_zero_of_exact exact object] at positive
  exact (lt_irrefl 0 positive)

/-- Negative control: so does a visibly positive composition defect. -/
theorem positive_compositionDefect_not_exact
    (correspondence : PathCorrespondence World Mind)
    {first middle last : World} (earlier : first ⟶ middle)
    (later : middle ⟶ last)
    (positive : 0 < correspondence.compositionDefect earlier later) :
    ¬ correspondence.Exact := by
  intro exact
  rw [correspondence.compositionDefect_eq_zero_of_exact
    exact earlier later] at positive
  exact (lt_irrefl 0 positive)

end PathCorrespondence

/-! ## Bounded approximation -/

/-- A correspondence whose identity and composition defects have explicit
nonnegative budgets. -/
structure BoundedPathCorrespondence extends PathCorrespondence World Mind where
  identityBudget : World → ℝ
  compositionBudget :
    {first middle last : World} →
      (first ⟶ middle) → (middle ⟶ last) → ℝ
  identityBudget_nonnegative : ∀ object, 0 ≤ identityBudget object
  compositionBudget_nonnegative :
    ∀ {first middle last : World} (earlier : first ⟶ middle)
      (later : middle ⟶ last), 0 ≤ compositionBudget earlier later
  identity_bounded : ∀ object,
    toPathCorrespondence.identityDefect object ≤ identityBudget object
  composition_bounded :
    ∀ {first middle last : World} (earlier : first ⟶ middle)
      (later : middle ⟶ last),
      toPathCorrespondence.compositionDefect earlier later ≤
        compositionBudget earlier later

namespace BoundedPathCorrespondence

variable {World Mind}

/-- Every exact functor embeds as a zero-defect correspondence once a
geometry on its target homs has been selected. -/
noncomputable def ofFunctor (functor : World ⥤ Mind)
    (geometry : ∀ source target,
      ValueGeometry (functor.obj source ⟶ functor.obj target)) :
    BoundedPathCorrespondence World Mind where
  obj := functor.obj
  map := functor.map
  geometry := geometry
  identityBudget := fun _ => 0
  compositionBudget := fun _ _ => 0
  identityBudget_nonnegative := fun _ => le_rfl
  compositionBudget_nonnegative := fun _ _ => le_rfl
  identity_bounded := by
    intro object
    change (geometry object object).distance
      (functor.map (𝟙 object)) (𝟙 (functor.obj object)) ≤ 0
    rw [functor.map_id]
    exact le_of_eq ((geometry object object).self _)
  composition_bounded := by
    intro first middle last earlier later
    change (geometry first last).distance
      (functor.map (earlier ≫ later))
      (functor.map earlier ≫ functor.map later) ≤ 0
    rw [functor.map_comp]
    exact le_of_eq ((geometry first last).self _)

theorem ofFunctor_exact (functor : World ⥤ Mind)
    (geometry : ∀ source target,
      ValueGeometry (functor.obj source ⟶ functor.obj target)) :
    (ofFunctor functor geometry).toPathCorrespondence.Exact := by
  constructor
  · exact functor.map_id
  · exact functor.map_comp

/-- A positive measured defect cannot be hidden behind a zero budget. -/
theorem positive_identityDefect_forces_positive_budget
    (correspondence : BoundedPathCorrespondence World Mind)
    (object : World)
    (positive : 0 < correspondence.toPathCorrespondence.identityDefect object) :
    0 < correspondence.identityBudget object :=
  lt_of_lt_of_le positive (correspondence.identity_bounded object)

theorem positive_compositionDefect_forces_positive_budget
    (correspondence : BoundedPathCorrespondence World Mind)
    {first middle last : World} (earlier : first ⟶ middle)
    (later : middle ⟶ last)
    (positive :
      0 < correspondence.toPathCorrespondence.compositionDefect earlier later) :
    0 < correspondence.compositionBudget earlier later :=
  lt_of_lt_of_le positive
    (correspondence.composition_bounded earlier later)

end BoundedPathCorrespondence

/-! ## Goal and resource sensitivity -/

/-- A mind--world correspondence keeps approximation error, goal relevance,
and resource cost as three independent observations on world paths. -/
structure MindWorldCorrespondence extends
    BoundedPathCorrespondence World Mind where
  goalWeight : {source target : World} → (source ⟶ target) → ℝ
  resourceCost : {source target : World} → (source ⟶ target) → ℝ
  goalWeight_nonnegative : ∀ {source target : World}
    (path : source ⟶ target), 0 ≤ goalWeight path
  resourceCost_nonnegative : ∀ {source target : World}
    (path : source ⟶ target), 0 ≤ resourceCost path

namespace MindWorldCorrespondence

variable {World Mind}

/-- A simple authored attention score.  The theory does not require this
specific resolver; it only demonstrates that goal and cost remain separate. -/
noncomputable def attention
    (correspondence : MindWorldCorrespondence World Mind)
    {source target : World} (path : source ⟶ target) : ℝ :=
  correspondence.goalWeight path / (1 + correspondence.resourceCost path)

theorem attention_nonnegative
    (correspondence : MindWorldCorrespondence World Mind)
    {source target : World} (path : source ⟶ target) :
    0 ≤ correspondence.attention path := by
  apply div_nonneg (correspondence.goalWeight_nonnegative path)
  linarith [correspondence.resourceCost_nonnegative path]

/-- Cost is not approximation error: changing only the cost readout leaves
the mapped path and all geometric defects definitionally unchanged. -/
def withResourceCost
    (correspondence : MindWorldCorrespondence World Mind)
    (newCost : {source target : World} → (source ⟶ target) → ℝ)
    (newCostNonnegative : ∀ {source target : World}
      (path : source ⟶ target), 0 ≤ newCost path) :
    MindWorldCorrespondence World Mind :=
  { correspondence with
    resourceCost := newCost
    resourceCost_nonnegative := newCostNonnegative }

@[simp] theorem withResourceCost_map
    (correspondence : MindWorldCorrespondence World Mind)
    (newCost : {source target : World} → (source ⟶ target) → ℝ)
    (newCostNonnegative : ∀ {source target : World}
      (path : source ⟶ target), 0 ≤ newCost path)
    {source target : World} (path : source ⟶ target) :
    (correspondence.withResourceCost newCost newCostNonnegative).map path =
      correspondence.map path :=
  rfl

@[simp] theorem withResourceCost_compositionDefect
    (correspondence : MindWorldCorrespondence World Mind)
    (newCost : {source target : World} → (source ⟶ target) → ℝ)
    (newCostNonnegative : ∀ {source target : World}
      (path : source ⟶ target), 0 ≤ newCost path)
    {first middle last : World} (earlier : first ⟶ middle)
    (later : middle ⟶ last) :
    PathCorrespondence.compositionDefect
        (correspondence.withResourceCost newCost newCostNonnegative).toPathCorrespondence
        earlier later =
      correspondence.toPathCorrespondence.compositionDefect earlier later :=
  rfl

end MindWorldCorrespondence

/-! ## Axiom audit -/

#print axioms PathCorrespondence.positive_identityDefect_not_exact
#print axioms PathCorrespondence.positive_compositionDefect_not_exact
#print axioms BoundedPathCorrespondence.ofFunctor_exact
#print axioms BoundedPathCorrespondence.positive_identityDefect_forces_positive_budget
#print axioms MindWorldCorrespondence.attention_nonnegative
#print axioms MindWorldCorrespondence.withResourceCost_compositionDefect

end Mettapedia.Cybernetics.MindWorldApproximateFunctor
