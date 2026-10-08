import Mettapedia.SetTheory.CarveOuts.Sites.ProductSite

/-!
# Kripke–Joyal forcing is invariant under local isomorphisms

On the product site of a context category `D` and the regions of a frame `H`, a map of value
families (`ValueMap`: a function at every point, natural along every arrow; every natural
transformation gives one, `ValueMap.ofNatTrans`) is

* **locally injective** (`LocallyInjective`) when two values with the same image agree on a
  cover of their region, and
* **locally surjective** (`LocallySurjective`) when every value of `values'` is, on a cover of
  its region, the image of values of `values`.

Membership is carried along `η` by its **local image** (`imageModel`): two values of `values'`
are members of each other on a region when, on a cover of it, they are the images of two
members.

**Invariance.** If `η` is locally injective and locally surjective, every formula of contextual
material logic is forced on `values` exactly when it is forced on `values'`, with the
environment carried along `η` (`siteForce_iff_of_local`). No class of formulas is excluded:
implication and the universal quantifier range over every later point, and the universal and
existential quantifiers range over all values of `values'`, which local surjectivity reduces to
the images of values of `values` through locality.

Sheafification on a space is such a map (module `Sheaves.Families`), so this is the step from
presheaf forcing to sheaf forcing.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts.Sheaves

open CategoryTheory
open Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogic
open Mettapedia.SetTheory.CarveOuts.Sites

universe u v

/-! ## Covers by two stable predicates -/

section Covers

variable {H : Type u} [Order.Frame H]

/-- Two covers, by predicates stable under shrinking, give a cover by their conjunction. -/
theorem covered_and {U : H} {P Q : (V : H) → V ≤ U → Prop}
    (hPmono : ∀ V W (hV : V ≤ U) (hW : W ≤ V), P V hV → P W (le_trans hW hV))
    (hQmono : ∀ V W (hV : V ≤ U) (hW : W ≤ V), Q V hV → Q W (le_trans hW hV))
    (hP : Covered U P) (hQ : Covered U Q) : Covered U fun V h => P V h ∧ Q V h :=
  covered_trans hP fun V h hPV => covered_restrict hQ h fun W hW hQW =>
    ⟨hPmono V (V ⊓ W) h inf_le_left hPV, hQmono W (V ⊓ W) hW inf_le_right hQW⟩

end Covers

/-! ## Locally injective and locally surjective maps -/

section Maps

variable {D : Type u} [Category.{u} D] {H : Type u} [Order.Frame H]
variable {values values' : (D × Hᵒᵈ) ⥤ Type v}

theorem shrink_self (p : D × Hᵒᵈ) (h : region p ≤ region p) : shrink p h = 𝟙 p :=
  Prod.ext rfl (Subsingleton.elim _ _)

theorem map_shrink_self (p : D × Hᵒᵈ) (h : region p ≤ region p) (s : values.obj p) :
    values.map (shrink p h) s = s := by
  rw [shrink_self, Functor.map_id_apply]

theorem map_shrink_shrink (p : D × Hᵒᵈ) {V W : H} (h : V ≤ region p) (h' : W ≤ V)
    (s : values.obj p) :
    values.map (shrink (below p V) h') (values.map (shrink p h) s) =
      values.map (shrink p (le_trans h' h)) s := by
  rw [← Functor.map_comp_apply, shrink_comp_shrink]

theorem map_shrink_across {p q : D × Hᵒᵈ} (a : p ⟶ q) {V : H} (h : V ≤ region p)
    (s : values.obj p) :
    values.map (shrink q inf_le_left) (values.map a s) =
      values.map (across a V) (values.map (shrink p h) s) := by
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, shrink_comp_across]

/-- **A map of value families**: a function at every point, natural along every arrow. -/
structure ValueMap (values values' : (D × Hᵒᵈ) ⥤ Type v) where
  app : ∀ p, values.obj p → values'.obj p
  naturality : ∀ {p q : D × Hᵒᵈ} (a : p ⟶ q) (s : values.obj p),
    app q (values.map a s) = values'.map a (app p s)

/-- A natural transformation, as a map of value families. -/
def ValueMap.ofNatTrans (η : values ⟶ values') : ValueMap values values' where
  app p s := η.app p s
  naturality a s := NatTrans.naturality_apply η a s

/-- `η` is locally injective: two values with the same image agree on a cover. -/
def LocallyInjective (η : ValueMap values values') : Prop :=
  ∀ (p : D × Hᵒᵈ) (s t : values.obj p), η.app p s = η.app p t →
    Covered (region p) fun _ h => values.map (shrink p h) s = values.map (shrink p h) t

/-- `η` is locally surjective: every value is, on a cover, an image. -/
def LocallySurjective (η : ValueMap values values') : Prop :=
  ∀ (p : D × Hᵒᵈ) (x : values'.obj p), Covered (region p) fun V h =>
    ∃ s : values.obj (below p V), η.app (below p V) s = values'.map (shrink p h) x

/-- An environment carried along `η`. -/
def pushEnv (η : ValueMap values values') {n : ℕ} {p : D × Hᵒᵈ} (env : Environment values n p) :
    Environment values' n p :=
  fun index => η.app p (env index)

theorem transport_pushEnv (η : ValueMap values values') {n : ℕ} {p q : D × Hᵒᵈ} (a : p ⟶ q)
    (env : Environment values n p) :
    transport values' a (pushEnv η env) = pushEnv η (transport values a env) := by
  funext index
  exact (η.naturality a (env index)).symm

theorem pushEnv_extend (η : ValueMap values values') {n : ℕ} {p : D × Hᵒᵈ}
    (env : Environment values n p) (s : values.obj p) :
    pushEnv η (extend values env s) = extend values' (pushEnv η env) (η.app p s) := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index

/-- **Membership along `η`: its local image.** Two values are members of each other on a region
when, on a cover of it, they are the images of two members. -/
def imageModel (model : Model values) (η : ValueMap values values') : Model values' where
  member p x y := Covered (region p) fun V h => ∃ s t : values.obj (below p V),
    model.member (below p V) s t ∧ η.app (below p V) s = values'.map (shrink p h) x ∧
      η.app (below p V) t = values'.map (shrink p h) y
  member_transport := by
    intro p q a x y hxy
    refine covered_restrict hxy (region_le a) fun V h ⟨s, t, hst, hs, ht⟩ => ?_
    refine ⟨values.map (across a V) s, values.map (across a V) t,
      model.member_transport (across a V) hst, ?_, ?_⟩
    · rw [η.naturality, hs, map_shrink_across a h]
    · rw [η.naturality, ht, map_shrink_across a h]

/-- The membership of the local image holds on a region when it holds on a cover of it. -/
theorem imageModel_member_local (model : Model values) (η : ValueMap values values') (p : D × Hᵒᵈ)
    (x y : values'.obj p)
    (covered : Covered (region p) fun V h =>
      (imageModel model η).member (below p V) (values'.map (shrink p h) x)
        (values'.map (shrink p h) y)) :
    (imageModel model η).member p x y := by
  refine covered_trans covered fun V h inner => covered_mono (fun W hW ⟨s, t, hst, hs, ht⟩ => ?_)
    inner
  refine ⟨s, t, hst, ?_, ?_⟩
  · rw [hs, map_shrink_shrink]
  · rw [ht, map_shrink_shrink]

/-- The images of two members are members of the local image. -/
theorem imageModel_member_of_member (model : Model values) (η : ValueMap values values') (p : D × Hᵒᵈ)
    {s t : values.obj p} (hst : model.member p s t) :
    (imageModel model η).member p (η.app p s) (η.app p t) := by
  refine covered_self ⟨values.map (shrink p le_rfl) s, values.map (shrink p le_rfl) t,
    model.member_transport _ hst, ?_, ?_⟩
  · rw [η.naturality]
  · rw [η.naturality]

variable (η : ValueMap values values')

/-- **Forcing is invariant under local isomorphisms.** For a locally injective and locally
surjective `η`, a formula is forced on `values` exactly when it is forced on `values'` with the
membership of the local image, for every formula. -/
theorem siteForce_iff_of_local (hinj : LocallyInjective η) (hsurj : LocallySurjective η)
    (model : Model values) {n : ℕ} (φ : Formula n) (p : D × Hᵒᵈ) (env : Environment values n p) :
    siteForce values model φ p env ↔
      siteForce values' (imageModel model η) φ p (pushEnv η env) := by
  induction φ generalizing p with
  | bottom => exact Iff.rfl
  | equal first second =>
    show Covered _ _ ↔ Covered _ _
    constructor
    · intro hc
      refine covered_mono (fun V h same => ?_) hc
      rw [transport_pushEnv]
      exact congrArg (η.app (below p V)) same
    · intro hc
      refine covered_trans hc fun V h same => ?_
      rw [transport_pushEnv] at same
      refine covered_mono (fun W hW eq => ?_) (hinj _ _ _ same)
      have eq' := eq
      simp only [transport] at eq'
      simp only [transport]
      rwa [map_shrink_shrink, map_shrink_shrink] at eq'
  | member child parent =>
    show Covered _ _ ↔ Covered _ _
    constructor
    · intro hc
      refine covered_mono (fun V h belongs => ?_) hc
      rw [transport_pushEnv]
      exact imageModel_member_of_member model η _ belongs
    · intro hc
      -- First, the images: on a cover, two members whose images are those of the environment.
      have images : Covered (region p) fun W hW => ∃ s t : values.obj (below p W),
          model.member (below p W) s t ∧
            η.app (below p W) s = η.app (below p W) (values.map (shrink p hW) (env child)) ∧
            η.app (below p W) t = η.app (below p W) (values.map (shrink p hW) (env parent)) := by
        refine covered_trans hc fun V h inner => covered_mono (fun W hW ⟨s, t, hst, hs, ht⟩ => ?_)
          inner
        refine ⟨s, t, hst, ?_, ?_⟩
        · rw [hs]
          simp only [transport, pushEnv]
          rw [map_shrink_shrink, η.naturality]
        · rw [ht]
          simp only [transport, pushEnv]
          rw [map_shrink_shrink, η.naturality]
      refine covered_trans images fun W hW ⟨s, t, hst, hs, ht⟩ => ?_
      have both := covered_and
        (P := fun V h => values.map (shrink (below p W) h) s =
          values.map (shrink (below p W) h) (values.map (shrink p hW) (env child)))
        (Q := fun V h => values.map (shrink (below p W) h) t =
          values.map (shrink (below p W) h) (values.map (shrink p hW) (env parent)))
        (fun V W' hV hW' eq => by rw [← map_shrink_shrink _ hV hW', eq, map_shrink_shrink])
        (fun V W' hV hW' eq => by rw [← map_shrink_shrink _ hV hW', eq, map_shrink_shrink])
        (hinj _ _ _ hs) (hinj _ _ _ ht)
      refine covered_mono (fun V hV ⟨es, et⟩ => ?_) both
      have moved := model.member_transport (shrink (below p W) hV) hst
      rw [es, et, map_shrink_shrink, map_shrink_shrink] at moved
      exact moved
  | both left right leftIH rightIH =>
    exact and_congr (leftIH p env) (rightIH p env)
  | either left right leftIH rightIH =>
    refine covered_congr fun V h => ?_
    rw [transport_pushEnv]
    exact or_congr (leftIH _ _) (rightIH _ _)
  | imply left right leftIH rightIH =>
    refine forall_congr' fun q => forall_congr' fun a => ?_
    rw [transport_pushEnv]
    exact imp_congr (leftIH _ _) (rightIH _ _)
  | all body bodyIH =>
    show (∀ (q : D × Hᵒᵈ) (a : p ⟶ q) (value : values.obj q),
        siteForce values model body q (extend values (transport values a env) value)) ↔
      ∀ (q : D × Hᵒᵈ) (a : p ⟶ q) (value : values'.obj q),
        siteForce values' (imageModel model η) body q
          (extend values' (transport values' a (pushEnv η env)) value)
    constructor
    · intro holds q a x
      refine siteForce_local body q _ (covered_mono (fun V h ⟨s, hs⟩ => ?_) (hsurj q x))
      have step := (bodyIH _ _).mp (holds (below q V) (a ≫ shrink q h) s)
      rw [pushEnv_extend, hs, transport_comp, ← transport_pushEnv η (shrink q h),
        ← transport_pushEnv η a] at step
      rw [transport_extend]
      exact step
    · intro holds q a s
      have step := holds q a (η.app q s)
      rw [transport_pushEnv, ← pushEnv_extend] at step
      exact (bodyIH _ _).mpr step
  | exist body bodyIH =>
    show Covered _ _ ↔ Covered _ _
    constructor
    · intro hc
      refine covered_mono (fun V h ⟨s, holds⟩ => ⟨η.app _ s, ?_⟩) hc
      rw [transport_pushEnv, ← pushEnv_extend]
      exact (bodyIH _ _).mp holds
    · intro hc
      refine covered_trans hc fun V h ⟨x, holds⟩ =>
        covered_mono (fun W hW ⟨s, hs⟩ => ⟨s, ?_⟩) (hsurj (below p V) x)
      have later := siteForce_transport body (shrink (below p V) hW) _ holds
      rw [transport_extend, ← hs, transport_pushEnv, transport_pushEnv, transport_shrink_shrink,
        ← pushEnv_extend] at later
      exact (bodyIH _ _).mpr later

end Maps

end Mettapedia.SetTheory.CarveOuts.Sheaves
