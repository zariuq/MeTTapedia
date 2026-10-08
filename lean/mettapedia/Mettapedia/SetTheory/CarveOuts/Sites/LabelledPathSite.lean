import Mettapedia.SetTheory.CarveOuts.Sites.SiteProjections
import Mettapedia.SetTheory.CarveOuts.Sites.RegionReadingFiber
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualArgumentCodings

/-!
# The product site on labelled context paths

The product site was stated for an arbitrary context category. The category instantiated here
is the category of labelled context paths: an object is a context length, and an arrow is a
finite history of labels whose length makes up the difference of the endpoints. The identity
history is empty. Extending the empty context by the label `0` and by the label `1` are
distinct arrows with the same endpoints, and the two orders of a two-step history are
distinct arrows. A category of families over a parameter, and a substitution category whose
arrows are natural transformations of a parameter base, do not exhibit such an arrow.

On this category, every intuitionistic derivation is sound for product-site forcing, by the
general soundness theorem. Excluded middle of membership in the left half of Cantor space is
forced on the whole space by the cover of the two halves, and is not forced by contextual
forcing, which has no covers. Reflexivity of equality is forced by both readings.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts.Sites

open CategoryTheory
open Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogic
open Mettapedia.TypeTheory.MaterialSets.Hypersets.LabelledContextPaths

universe v

/-- The empty context and the context of length one are distinct objects, so an
extension from one to the other is not an identity arrow. -/
theorem initial_ne_next : initial ≠ next := by
  intro same
  exact Nat.zero_ne_one (congrArg World.length same)

/-- An extension history is not the empty identity history. -/
theorem extension_history_nonempty (label : Nat) : (extension label).val ≠ [] :=
  List.cons_ne_nil label []

/-- Two labels give two arrows between the same contexts. -/
theorem parallel_extensions : extension 0 ≠ extension 1 := by
  intro same
  have paths : (extension 0).val = (extension 1).val := congrArg Subtype.val same
  exact Nat.zero_ne_one (List.cons.inj paths).1

/-- The order of labels is part of the arrow. -/
theorem ordered_histories_ne :
    extension 0 ≫ laterExtension 1 ≠ extension 1 ≫ laterExtension 0 := by
  intro same
  have paths := congrArg Subtype.val same
  exact Nat.zero_ne_one (List.cons.inj paths).1

/-- **Soundness on labelled context paths.** Every intuitionistic derivation is sound for
product-site forcing over this category. -/
theorem world_site_derivation_sound
    {H : Type} [Order.Frame H]
    {values : (World × Hᵒᵈ) ⥤ Type v}
    (model : Model values)
    {n : ℕ} {assumptions : List (Formula n)} {conclusion : Formula n}
    (derivation : Derivation assumptions conclusion)
    (p : World × Hᵒᵈ) (env : Environment values n p)
    (admitted : ∀ formula, formula ∈ assumptions → siteForce values model formula p env) :
    siteForce values model conclusion p env :=
  site_derivation_sound derivation p env admitted

/-- The top proposition, as a point of the opposite frame. -/
def propTop (c : World) : World × Propᵒᵈ :=
  (c, (⊤ : Prop))

/-- Reflexivity, derived and then read on the product site at any context of this category. -/
theorem world_refl_sound (c : World) :
    siteForce unitValues (regionModel (⊤ : Prop)) (.equal (0 : Fin 1) 0) (propTop c)
      (unitEnv (propTop c)) :=
  closed_site_derivation_sound (Derivation.equalRefl (0 : Fin 1)) (propTop c) (unitEnv _)

/-- **The two readings agree on reflexivity.** Equality of a value with itself is forced by the
product site and by contextual forcing. -/
theorem world_equality_agrees (c : World) :
    siteForce unitValues (regionModel (⊤ : Prop)) (.equal (0 : Fin 1) 0) (propTop c) (unitEnv _) ∧
      force unitValues (regionModel (⊤ : Prop)) (.equal (0 : Fin 1) 0) (propTop c) (unitEnv _) :=
  ⟨covered_self rfl, rfl⟩

/-- **Covers separate the two readings.** On the whole space, excluded middle of membership in
the left half of Cantor space is forced by the cover of the two halves, and is not forced by
contextual forcing over the same category. -/
theorem world_halves_excluded_middle :
    siteForce unitValues (regionModel leftHalf) insideOrOutside (whole initial) (unitEnv _) ∧
      ¬ force unitValues (regionModel leftHalf) insideOrOutside (whole initial) (unitEnv _) :=
  halves_excluded_middle initial

end Mettapedia.SetTheory.CarveOuts.Sites
