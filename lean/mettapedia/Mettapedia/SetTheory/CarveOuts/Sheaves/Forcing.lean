import Mettapedia.SetTheory.CarveOuts.Sheaves.Families
import Mettapedia.SetTheory.CarveOuts.Sites.SiteProjections
import Mathlib.CategoryTheory.Sites.Subsheaf

/-!
# Sheaf forcing, and its agreement with forcing on the product site

**Sheaf models.** A sheaf model (`SheafModel`) is a family `D ⥤ Sheaf (Opens X)` together with a
membership relation on its sections that persists along every arrow of the product site and is
local: a pair that is a member on a cover of a region is a member on the region.

**Sheaf forcing** (`sheafForce`) is Kripke–Joyal forcing in sheaves, with the textbook clauses:
equality is equality of sections and membership is the local relation itself; falsity holds on
the empty open set only; conjunction is pointwise; disjunction and the existential quantifier
hold on a cover; implication and the universal quantifier look along every arrow, to later
contexts and smaller open sets, and the universal quantifier ranges over the sections of the
sheaves.

* On a sheaf model, sheaf forcing is the forcing of the product site read on its underlying value
  family (`sheafForce_iff_siteForce`): the cover clauses for the atoms of the product site
  collapse because sections of a sheaf are determined locally and membership is local. So sheaf
  forcing persists, is local, and is sound for every intuitionistic derivation
  (`sheafForce_transport`, `sheafForce_local`, `sheaf_derivation_sound`).
* At a context, the sections forcing a formula form a subfunctor of the presheaf of environments
  that equals its own closure for the open-cover topology (`extension_sheafify_eq`): the
  interpretation of a formula is a closed subpresheaf, as Kripke–Joyal forcing requires.

**Sheafification of a model** (`sheafifyModel`): the family is sheafified pointwise in the
contexts, and membership is the local image of the presheaf membership.

**Agreement** (`siteForce_iff_sheafForce`): for every formula of contextual material logic,
every point of the product site and every environment, forcing on the product site of a presheaf
model is sheaf forcing of its sheafification, at the environment carried by the unit. No class of
formulas is excluded. Forcing commutes with the arrows of the contexts
(`sheafForce_sheafify_forward`), and the frame reading at a context is unchanged
(`regionValue_eq_sheafRegionValue`).

**The covers are needed.** Contextual forcing without covers does not agree with sheaf forcing
on the sheafification, already for an atomic formula: on Cantor space, a presheaf with two
sections on the whole space that agree on each half forces their equality on the product site
and in sheaves, while forcing without covers refutes it (`cover_free_disagrees` in
`Sheaves.Cantor`). The sheafification identifies the two sections (`sheafUnit_identifies`).
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts.Sheaves

open CategoryTheory TopologicalSpace Opposite
open Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogic
open Mettapedia.SetTheory.CarveOuts.Sites

universe u

variable {X : Type u} [TopologicalSpace X]

/-! ## Separation -/

/-- Sections of a sheaf on a space that agree on a cover are equal. -/
theorem sheaf_eq_of_covered (F : Sheaf (Opens.grothendieckTopology X) (Type u)) {U : Opens X}
    {s t : F.obj.obj (op U)}
    (covered : Covered U fun _ h => F.obj.map (homOfLE h).op s = F.obj.map (homOfLE h).op t) :
    s = t := by
  have hsheaf := (isSheaf_iff_isSheaf_of_type _ F.obj).mp F.property
  have hmem : Presheaf.equalizerSieve (F := F.obj) (X := op U) s t ∈
      Opens.grothendieckTopology X U :=
    (covered_iff_mem _).mp covered
  exact (hsheaf.isSeparated _ hmem).ext fun _ _ hf => hf

variable {D : Type u} [Category.{u} D]

/-- Values of a family read on the product site that agree on a cover are equal. -/
theorem underlying_eq_of_covered (F : D ⥤ Sheaf (Opens.grothendieckTopology X) (Type u))
    (p : D × (Opens X)ᵒᵈ) {s t : (underlying F).obj p}
    (covered : Covered (region p) fun _ h =>
      (underlying F).map (shrink p h) s = (underlying F).map (shrink p h) t) :
    s = t := by
  refine sheaf_eq_of_covered (F.obj p.1) (covered_mono (fun V h same => ?_) covered)
  rwa [underlying_map_shrink, underlying_map_shrink] at same

/-! ## Sheaf models and sheaf forcing -/

/-- **A sheaf model**: a family of sheaves over the contexts with a membership relation that
persists along every arrow of the product site and is local. -/
structure SheafModel (D : Type u) [Category.{u} D] (X : Type u) [TopologicalSpace X] where
  family : D ⥤ Sheaf (Opens.grothendieckTopology X) (Type u)
  model : Model (underlying family)
  member_local : ∀ (p : D × (Opens X)ᵒᵈ) (x y : (underlying family).obj p),
    Covered (region p) (fun V h => model.member (below p V)
      ((underlying family).map (shrink p h) x) ((underlying family).map (shrink p h) y)) →
    model.member p x y

variable (M : SheafModel D X)

/-- **Sheaf forcing (Kripke–Joyal).** -/
def sheafForce {n : ℕ} : Formula n → (p : D × (Opens X)ᵒᵈ) →
    Environment (underlying M.family) n p → Prop
  | .bottom, p, _ => region p ≤ ⊥
  | .equal first second, _, env => env first = env second
  | .member child parent, p, env => M.model.member p (env child) (env parent)
  | .both left right, p, env => sheafForce left p env ∧ sheafForce right p env
  | .either left right, p, env => Covered (region p) fun V h =>
      sheafForce left (below p V) (transport (underlying M.family) (shrink p h) env) ∨
        sheafForce right (below p V) (transport (underlying M.family) (shrink p h) env)
  | .imply left right, p, env => ∀ (q : D × (Opens X)ᵒᵈ) (a : p ⟶ q),
      sheafForce left q (transport (underlying M.family) a env) →
        sheafForce right q (transport (underlying M.family) a env)
  | .all body, p, env => ∀ (q : D × (Opens X)ᵒᵈ) (a : p ⟶ q) (value : (underlying M.family).obj q),
      sheafForce body q (extend (underlying M.family) (transport (underlying M.family) a env) value)
  | .exist body, p, env => Covered (region p) fun V h =>
      ∃ value : (underlying M.family).obj (below p V),
        sheafForce body (below p V)
          (extend (underlying M.family) (transport (underlying M.family) (shrink p h) env) value)

/-- **On a sheaf model, sheaf forcing is forcing on the product site.** The cover clauses for
falsity, equality and membership collapse: sections of a sheaf are determined locally, and
membership is local. -/
theorem sheafForce_iff_siteForce {n : ℕ} (φ : Formula n) (p : D × (Opens X)ᵒᵈ)
    (env : Environment (underlying M.family) n p) :
    sheafForce M φ p env ↔ siteForce (underlying M.family) M.model φ p env := by
  induction φ generalizing p with
  | bottom => exact covered_false_iff.symm
  | equal first second =>
    constructor
    · intro same
      exact covered_self (congrArg ((underlying M.family).map (shrink p le_rfl)) same)
    · exact underlying_eq_of_covered M.family p
  | member child parent =>
    constructor
    · intro belongs
      exact covered_self (M.model.member_transport (shrink p le_rfl) belongs)
    · exact M.member_local p _ _
  | both left right leftIH rightIH => exact and_congr (leftIH p env) (rightIH p env)
  | either left right leftIH rightIH =>
    exact covered_congr fun _ _ => or_congr (leftIH _ _) (rightIH _ _)
  | imply left right leftIH rightIH =>
    exact forall_congr' fun _ => forall_congr' fun _ => imp_congr (leftIH _ _) (rightIH _ _)
  | all body bodyIH =>
    exact forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ => bodyIH _ _
  | exist body bodyIH =>
    exact covered_congr fun _ _ => exists_congr fun _ => bodyIH _ _

/-- Sheaf forcing persists along every arrow of the product site. -/
theorem sheafForce_transport {n : ℕ} (φ : Formula n) {p q : D × (Opens X)ᵒᵈ} (a : p ⟶ q)
    (env : Environment (underlying M.family) n p) (holds : sheafForce M φ p env) :
    sheafForce M φ q (transport (underlying M.family) a env) :=
  (sheafForce_iff_siteForce M φ q _).mpr
    (siteForce_transport φ a env ((sheafForce_iff_siteForce M φ p env).mp holds))

/-- Sheaf forcing is local. -/
theorem sheafForce_local {n : ℕ} (φ : Formula n) (p : D × (Opens X)ᵒᵈ)
    (env : Environment (underlying M.family) n p)
    (covered : Covered (region p) fun V h =>
      sheafForce M φ (below p V) (transport (underlying M.family) (shrink p h) env)) :
    sheafForce M φ p env :=
  (sheafForce_iff_siteForce M φ p env).mpr (siteForce_local φ p env
    (covered_mono (fun _ _ holds => (sheafForce_iff_siteForce M φ _ _).mp holds) covered))

/-- **Soundness of sheaf forcing** for every intuitionistic derivation. -/
theorem sheaf_derivation_sound {n : ℕ} {assumptions : List (Formula n)} {conclusion : Formula n}
    (derivation : Derivation assumptions conclusion) (p : D × (Opens X)ᵒᵈ)
    (env : Environment (underlying M.family) n p)
    (admitted : ∀ formula, formula ∈ assumptions → sheafForce M formula p env) :
    sheafForce M conclusion p env :=
  (sheafForce_iff_siteForce M conclusion p env).mpr (site_derivation_sound derivation p env
    fun formula included => (sheafForce_iff_siteForce M formula p env).mp
      (admitted formula included))

/-! ## The extension of a formula is a closed subpresheaf -/

/-- The presheaf of `n`-tuples of sections at a context. -/
def envPresheaf (c : D) (n : ℕ) : (Opens X)ᵒᵖ ⥤ Type u where
  obj U := Fin n → (M.family.obj c).obj.obj U
  map f := TypeCat.ofHom fun env index => (M.family.obj c).obj.map f (env index)
  map_id U := by
    ext env index
    exact (M.family.obj c).obj.map_id_apply U (env index)
  map_comp f g := by
    ext env index
    exact (M.family.obj c).obj.map_comp_apply f g (env index)

theorem envPresheaf_map_eq (c : D) {n : ℕ} {U : Opens X} {V : Opens X} (h : V ≤ U)
    (env : (envPresheaf M c n).obj (op U)) :
    (envPresheaf M c n).map (homOfLE h).op env =
      transport (underlying M.family) (shrink ((c, U) : D × (Opens X)ᵒᵈ) h) env := by
  funext index
  exact (underlying_map_shrink M.family ((c, U) : D × (Opens X)ᵒᵈ) h (env index)).symm

/-- **The extension of a formula at a context**: the tuples of sections forcing it, a
subpresheaf of the presheaf of tuples. -/
def extension (c : D) {n : ℕ} (φ : Formula n) : Subfunctor (envPresheaf M c n) where
  obj U := {env | sheafForce M φ ((c, unop U) : D × (Opens X)ᵒᵈ) env}
  map {U V} f env holds := by
    have moved := sheafForce_transport M φ (shrink ((c, unop U) : D × (Opens X)ᵒᵈ)
      (leOfHom f.unop)) env holds
    rw [← envPresheaf_map_eq] at moved
    exact moved

/-- **The extension of a formula is closed for the open-cover topology**: it equals its
sheafification as a subpresheaf. -/
theorem extension_sheafify_eq (c : D) {n : ℕ} (φ : Formula n) :
    (extension M c φ).sheafify (Opens.grothendieckTopology X) = extension M c φ := by
  refine le_antisymm (fun U env hmem => ?_) (Subfunctor.le_sheafify _ _)
  refine sheafForce_local M φ ((c, unop U) : D × (Opens X)ᵒᵈ) env
    (covered_of_mem hmem fun V f hf => ?_)
  have hf' : sheafForce M φ ((c, V) : D × (Opens X)ᵒᵈ) ((envPresheaf M c n).map f.op env) := hf
  rw [show f = homOfLE (leOfHom f) from rfl, envPresheaf_map_eq] at hf'
  exact hf'

/-! ## The frame reading of a sheaf model -/

/-- The region value of a formula on a sheaf model. -/
def sheafRegionValue {n : ℕ} (φ : Formula n) (p : D × (Opens X)ᵒᵈ)
    (env : Environment (underlying M.family) n p) : Opens X :=
  sSup {V | ∃ h : V ≤ region p,
    sheafForce M φ (below p V) (transport (underlying M.family) (shrink p h) env)}

theorem sheafRegionValue_eq_regionValue {n : ℕ} (φ : Formula n) (p : D × (Opens X)ᵒᵈ)
    (env : Environment (underlying M.family) n p) :
    sheafRegionValue M φ p env = regionValue M.model φ p env := by
  unfold sheafRegionValue regionValue
  congr 1
  ext V
  exact exists_congr fun h => sheafForce_iff_siteForce M φ _ _

/-- **The frame reading of a sheaf model is exact.** -/
theorem sheafForce_shrink_iff {n : ℕ} (φ : Formula n) (p : D × (Opens X)ᵒᵈ)
    (env : Environment (underlying M.family) n p) {V : Opens X} (h : V ≤ region p) :
    sheafForce M φ (below p V) (transport (underlying M.family) (shrink p h) env) ↔
      V ≤ sheafRegionValue M φ p env := by
  rw [sheafForce_iff_siteForce, sheafRegionValue_eq_regionValue]
  exact siteForce_shrink_iff φ p env h

/-! ## Sheafification of a model, and agreement -/

variable (values : (D × (Opens X)ᵒᵈ) ⥤ Type u)

/-- **The sheafification of a presheaf model**: the sheafified family, with the local image of
the membership. -/
noncomputable def sheafifyModel (model : Model values) : SheafModel D X where
  family := sheafFamily values
  model := imageModel model (sheafUnitMap values)
  member_local := imageModel_member_local model (sheafUnitMap values)

/-- **Agreement.** Forcing on the product site of a presheaf model is sheaf forcing of its
sheafification, for every formula, point and environment. -/
theorem siteForce_iff_sheafForce (model : Model values) {n : ℕ} (φ : Formula n)
    (p : D × (Opens X)ᵒᵈ) (env : Environment values n p) :
    siteForce values model φ p env ↔
      sheafForce (sheafifyModel values model) φ p (pushEnv (sheafUnitMap values) env) :=
  (siteForce_iff_of_local (sheafUnitMap values) (sheafUnit_locallyInjective values)
    (sheafUnit_locallySurjective values) model φ p env).trans
    (sheafForce_iff_siteForce (sheafifyModel values model) φ p _).symm

/-- **Agreement commutes with the arrows of the contexts.** Carrying an environment along an
arrow of `D` and then into the sheafification is carrying its image along the arrow of the
sheafified family, and forcing agrees at the later context. -/
theorem sheafForce_sheafify_forward (model : Model values) {n : ℕ} (φ : Formula n)
    (p : D × (Opens X)ᵒᵈ) {c : D} (f : p.1 ⟶ c) (env : Environment values n p) :
    sheafForce (sheafifyModel values model) φ (forward p c)
        (transport (underlying (sheafFamily values)) (forwardArrow p f)
          (pushEnv (sheafUnitMap values) env)) ↔
      siteForce values model φ (forward p c) (transport values (forwardArrow p f) env) := by
  rw [transport_pushEnv]
  exact (siteForce_iff_sheafForce values model φ _ _).symm

/-- **The frame reading at a context is unchanged by sheafification.** -/
theorem regionValue_eq_sheafRegionValue (model : Model values) {n : ℕ} (φ : Formula n)
    (p : D × (Opens X)ᵒᵈ) (env : Environment values n p) :
    regionValue model φ p env =
      sheafRegionValue (sheafifyModel values model) φ p (pushEnv (sheafUnitMap values) env) := by
  unfold sheafRegionValue regionValue
  congr 1
  ext V
  refine exists_congr fun h => (siteForce_iff_sheafForce values model φ _ _).trans ?_
  rw [← transport_pushEnv (sheafUnitMap values) (shrink p h) env]
  rfl

end Mettapedia.SetTheory.CarveOuts.Sheaves
