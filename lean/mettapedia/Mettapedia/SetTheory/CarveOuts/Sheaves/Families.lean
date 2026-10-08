import Mettapedia.SetTheory.CarveOuts.Sheaves.LocalIsos
import Mettapedia.SetTheory.CarveOuts.Sites.SiteProjections
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Families over the contexts, valued in sheaves on a space

Let `D` be a context category and `X` a topological space. A **family** is a functor
`D ⥤ Sheaf (Opens.grothendieckTopology X) (Type u)`: a sheaf on `X` at every context, and a map
of sheaves along every arrow of `D`. The topology lives on `X` only; the arrows of `D` keep their
symmetries, substitutions and histories.

**From the product site.** A value family on the product site `D × (Opens X)ᵒᵈ` (the models of
`Sites.ProductSite`) is, at each context `c`, a presheaf on the open sets (`fibre`), and along each
arrow of `D` a map of presheaves (`presheafFamily`). Sheafifying pointwise in `D` gives a family
(`sheafFamily`). Conversely a family is read back on the product site (`underlying`). The unit of
sheafification, pointwise in `D`, is a map of value families on the product site (`sheafUnit`):
it commutes with the arrows of `D` as well as with restriction (its naturality), so the passage
commutes with context arrows.

**Covers.** A sieve of the open-cover topology is covering exactly when its open sets cover in
the sense of the product site (`covered_iff_mem`). With it, the unit is locally injective and
locally surjective in the sense of `Sheaves.LocalIsos` (`sheafUnit_locallyInjective`,
`sheafUnit_locallySurjective`), from Mathlib's local injectivity and surjectivity of
`toSheafify`.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts.Sheaves

open CategoryTheory TopologicalSpace Opposite
open Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogic
open Mettapedia.SetTheory.CarveOuts.Sites

universe u

variable {X : Type u} [TopologicalSpace X]

/-! ## Covering sieves are covers -/

section Covers

/-- A sieve on an open set covers it exactly when its open sets cover it on the product
site. -/
theorem covered_iff_mem {U : Opens X} (S : Sieve U) :
    (Covered U fun _ h => S (homOfLE h)) ↔ S ∈ Opens.grothendieckTopology X U := by
  rw [covered_opens_iff, Opens.mem_grothendieckTopology]
  constructor
  · intro h x hx
    obtain ⟨V, hV, hS, hxV⟩ := h x hx
    exact ⟨V, homOfLE hV, hS, hxV⟩
  · intro h x hx
    obtain ⟨V, f, hS, hxV⟩ := h x hx
    exact ⟨V, leOfHom f, hS, hxV⟩

/-- A covering sieve whose arrows satisfy `P` covers by `P`. -/
theorem covered_of_mem {U : Opens X} {S : Sieve U} (hS : S ∈ Opens.grothendieckTopology X U)
    {P : (V : Opens X) → V ≤ U → Prop} (hP : ∀ V (f : V ⟶ U), S f → P V (leOfHom f)) :
    Covered U P :=
  covered_mono (fun V h hV => hP V (homOfLE h) hV) ((covered_iff_mem S).mpr hS)

end Covers

/-! ## Families and the product site -/

section Families

variable {D : Type u} [Category.{u} D]

/-- The fibre of a value family of the product site at a context: a presheaf on the open
sets. -/
def fibre (values : (D × (Opens X)ᵒᵈ) ⥤ Type u) (c : D) : (Opens X)ᵒᵖ ⥤ Type u where
  obj U := values.obj (c, unop U)
  map f := values.map (shrink ((c, unop _) : D × (Opens X)ᵒᵈ) (leOfHom f.unop))
  map_id U := by
    rw [shrink_self]
    exact values.map_id _
  map_comp f g := by
    rw [← values.map_comp, shrink_comp_shrink]

/-- Along an arrow of `D`, a map of the fibres. -/
def fibreMap (values : (D × (Opens X)ᵒᵈ) ⥤ Type u) {c c' : D} (f : c ⟶ c') :
    fibre values c ⟶ fibre values c' where
  app U := values.map (forwardArrow ((c, unop U) : D × (Opens X)ᵒᵈ) f)
  naturality U V g := by
    show values.map _ ≫ values.map _ = values.map _ ≫ values.map _
    rw [← values.map_comp, ← values.map_comp]
    congr 1
    exact Prod.ext (by simp [shrink, forwardArrow]) (Subsingleton.elim _ _)

/-- A value family on the product site, as a functor from the contexts to presheaves on the open
sets. -/
def presheafFamily (values : (D × (Opens X)ᵒᵈ) ⥤ Type u) : D ⥤ ((Opens X)ᵒᵖ ⥤ Type u) where
  obj c := fibre values c
  map f := fibreMap values f
  map_id c := by
    ext U : 2
    exact values.map_id _
  map_comp f g := by
    ext U : 2
    show values.map _ = values.map _ ≫ values.map _
    rw [← values.map_comp]
    rfl

/-- **Sheafification, pointwise in the contexts.** -/
noncomputable def sheafFamily (values : (D × (Opens X)ᵒᵈ) ⥤ Type u) :
    D ⥤ Sheaf (Opens.grothendieckTopology X) (Type u) :=
  presheafFamily values ⋙ presheafToSheaf (Opens.grothendieckTopology X) (Type u)

/-- A family read back on the product site. -/
def underlying (F : D ⥤ Sheaf (Opens.grothendieckTopology X) (Type u)) :
    (D × (Opens X)ᵒᵈ) ⥤ Type u where
  obj p := (F.obj p.1).obj.obj (op (region p))
  map {p q} a := (F.map a.1).hom.app (op (region p)) ≫ (F.obj q.1).obj.map (homOfLE (region_le a)).op
  map_id p := by
    show (F.map (𝟙 p.1)).hom.app _ ≫ _ = _
    rw [F.map_id]
    show 𝟙 _ ≫ (F.obj p.1).obj.map (𝟙 _) = 𝟙 _
    rw [(F.obj p.1).obj.map_id, Category.comp_id]
  map_comp {p q r} a b := by
    show (F.map (a.1 ≫ b.1)).hom.app _ ≫ _ = _
    rw [F.map_comp]
    show ((F.map a.1).hom ≫ (F.map b.1).hom).app _ ≫ _ = _
    rw [NatTrans.comp_app, Category.assoc, Category.assoc]
    congr 1
    rw [(F.map b.1).hom.naturality_assoc, ← (F.obj r.1).obj.map_comp]
    rfl

theorem underlying_map_apply (F : D ⥤ Sheaf (Opens.grothendieckTopology X) (Type u))
    {p q : D × (Opens X)ᵒᵈ} (a : p ⟶ q) (s : (underlying F).obj p) :
    (underlying F).map a s =
      (F.obj q.1).obj.map (homOfLE (region_le a)).op ((F.map a.1).hom.app (op (region p)) s) :=
  rfl

/-- Restriction on the product site is restriction of the sheaf at the context. -/
theorem underlying_map_shrink (F : D ⥤ Sheaf (Opens.grothendieckTopology X) (Type u))
    (p : D × (Opens X)ᵒᵈ) {V : Opens X} (h : V ≤ region p) (s : (underlying F).obj p) :
    (underlying F).map (shrink p h) s = (F.obj p.1).obj.map (homOfLE h).op s := by
  rw [underlying_map_apply]
  show (F.obj p.1).obj.map _ ((F.map (𝟙 p.1)).hom.app _ s) = _
  rw [F.map_id]
  rfl

variable (values : (D × (Opens X)ᵒᵈ) ⥤ Type u)

/-- **The unit of sheafification, pointwise in the contexts**, as a map of value families on the
product site. Its naturality says that it commutes with the arrows of `D` and with
restriction. -/
noncomputable def sheafUnit : values ⟶ underlying (sheafFamily values) where
  app p := (toSheafify (Opens.grothendieckTopology X) (fibre values p.1)).app (op (region p))
  naturality p q a := by
    have key := congrArg (fun k => NatTrans.app k (op (region p)))
      (toSheafify_naturality (Opens.grothendieckTopology X) (fibreMap values a.1))
    simp only [NatTrans.comp_app] at key
    show values.map a ≫ _ = (toSheafify _ (fibre values p.1)).app _ ≫
      (sheafifyMap (Opens.grothendieckTopology X) (fibreMap values a.1)).app _ ≫
        (sheafify (Opens.grothendieckTopology X) (fibre values q.1)).map (homOfLE (region_le a)).op
    rw [← Category.assoc, ← key, Category.assoc,
      ← (toSheafify (Opens.grothendieckTopology X) (fibre values q.1)).naturality, ← Category.assoc]
    congr 1
    show values.map a = values.map _ ≫ values.map _
    rw [← values.map_comp]
    congr 1
    exact Prod.ext (Category.comp_id _).symm (Subsingleton.elim _ _)

/-- The unit at a point is the unit of sheafification of the fibre. -/
theorem sheafUnit_app (p : D × (Opens X)ᵒᵈ) :
    (sheafUnit values).app p =
      (toSheafify (Opens.grothendieckTopology X) (fibre values p.1)).app (op (region p)) :=
  rfl

/-- The unit, as a map of value families. -/
noncomputable abbrev sheafUnitMap : ValueMap values (underlying (sheafFamily values)) :=
  ValueMap.ofNatTrans (sheafUnit values)

/-- **The unit is locally injective**: two values with the same image in the sheafification
agree on a cover. -/
theorem sheafUnit_locallyInjective : LocallyInjective (sheafUnitMap values) := by
  intro p s t same
  have hmem := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
    (toSheafify (Opens.grothendieckTopology X) (fibre values p.1)) (X := op (region p)) s t same
  exact covered_of_mem hmem fun V f hf => hf

/-- **The unit is locally surjective**: every value of the sheafification is, on a cover, the
image of values of the presheaf. -/
theorem sheafUnit_locallySurjective : LocallySurjective (sheafUnitMap values) := by
  intro p x
  have hmem := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    (toSheafify (Opens.grothendieckTopology X) (fibre values p.1)) (U := op (region p)) x
  refine covered_of_mem hmem fun V f ⟨t, ht⟩ => ⟨t, ?_⟩
  rw [underlying_map_shrink]
  exact ht

end Families

end Mettapedia.SetTheory.CarveOuts.Sheaves
