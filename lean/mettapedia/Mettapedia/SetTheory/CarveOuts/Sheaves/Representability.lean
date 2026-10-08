import Mettapedia.SetTheory.CarveOuts.Sheaves.PowerClasses

/-!
# Representability (R) for small maps of sheaves on a space, and where it fails

**The positive result** (`sheafSmall_representable`). Let the sheaves take values in a universe
strictly above `w` (the space lives in `Type (max u (w + 1))`), and let the open sets form a
`w`-small type. Then there is one small map `π` of which every small map is a pullback, already
globally (the epimorphism of axiom (R) is the identity):

* **Codes.** `SmallCode` is the type of pairs of a type of the universe `w` and an element of it.
  Every element of a `w`-small set has a code, injectively, through `Shrink` (`fibreCode`).
* **The generic sheaf** `genericSheaf` is the sheafification of the presheaf whose sections on `W`
  give a code on every open `V ≤ W`. A small map `f : A ⟶ B` gives a map `encode f : A ⟶ G`
  that is injective on each fibre of `f`: on `V`, a section is sent to the code of its
  restriction in its own fibre (`encode_jointlyInjective`). Injectivity survives
  sheafification because the unit is locally injective and `A` is separated.
* **The universal small map** `universalMap` is membership over the power class of the generic
  sheaf (`Sheaves.PowerClasses`), which is small. The relation `(f, encode f) : A ⟶ B ⨯ G` is
  classified by a map `B ⟶ powerSheaf G`, and the square is a pullback
  (`small_isPullback_universal`).

Host choice enters through `Shrink` (a chosen equivalence), the classifying maps
(`Classical.choose` in gluing) and Mathlib's sheafification.

**The negative result** (`not_representable_of_small_terminal`). On a nonempty space, if every map
to the terminal sheaf is small then (R) fails, by Cantor's theorem: the sheaf of all functions
from points into the power set of the sections of `El` has, on a nonempty open set, more sections
than any fibre of `π`. When the sheaves take values in a universe whose types are all `w`-small
(`UnivLE.{u, w}`), every map is small and (R) fails (`sheafSmall_not_representable_of_univLE`).
This is the case of Cantor space `ℕ → Bool : Type`, whose sheaves of sets take values in `Type`.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts.Sheaves

open CategoryTheory Limits TopologicalSpace Opposite
open Mettapedia.SetTheory.CarveOuts.Sites
open Mettapedia.SetTheory.CarveOuts.Sites.SmallMaps

universe w u

/-! ## Codes for small sets -/

/-- **Codes for `w`-small sets**: a type of the universe `w` and an element of it. -/
def SmallCode : Type (w + 1) :=
  Σ α : Type w, α

/-! ## The generic sheaf -/

section Positive

variable {X : Type (max u (w + 1))} [TopologicalSpace X]

-- The space lives in a universe at least `w + 1`, so `u` and `w` occur only in `max u (w + 1)`.
set_option linter.checkUnivs false in
/-- On an open set, a code on every smaller open set. -/
def codePresheaf : (Opens X)ᵒᵖ ⥤ Type (max u (w + 1)) where
  obj W := ∀ V : Opens X, V ≤ unop W → SmallCode.{w}
  map k := TypeCat.ofHom fun g V hV => g V (le_trans hV (leOfHom k.unop))
  map_id _ := by
    ext g
    rfl
  map_comp _ _ := by
    ext g
    rfl

set_option linter.checkUnivs false in
/-- **The generic sheaf**: the sheafification of the codes. -/
noncomputable def genericSheaf : SheafOn X :=
  (presheafToSheaf (Opens.grothendieckTopology X) (Type (max u (w + 1)))).obj
    (codePresheaf.{w, u} (X := X))

variable {A B : SheafOn X} (f : A ⟶ B) (hf : sheafSmall.{w} f)

/-- The code of an element of a small fibre of `f`. -/
noncomputable def fibreCode {V : Opens X} (b : B.obj.obj (op V))
    (a : {a // f.hom.app (op V) a = b}) : SmallCode.{w} :=
  ⟨@Shrink.{w} _ (hf (op V) b), @equivShrink _ (hf (op V) b) a⟩

/-- Codes are injective on each fibre. -/
theorem fibreCode_eq {V : Opens X} {b b' : B.obj.obj (op V)} (hb : b = b')
    (a : {a // f.hom.app (op V) a = b}) (a' : {a // f.hom.app (op V) a = b'})
    (h : fibreCode f hf b a = fibreCode f hf b' a') : a.1 = a'.1 := by
  subst hb
  have := (Sigma.mk.inj_iff.mp h).2
  exact congrArg Subtype.val ((@equivShrink _ (hf (op V) b)).injective (eq_of_heq this))

/-- Each section of `A`, sent to the codes of its restrictions in their fibres. -/
noncomputable def encodePre : A.obj ⟶ codePresheaf.{w, u} (X := X) where
  app W := TypeCat.ofHom fun a V hV =>
    fibreCode f hf (f.hom.app (op V) (res A.obj hV a)) ⟨res A.obj hV a, rfl⟩
  naturality W W' k := by
    ext a
    refine funext fun V => funext fun hV => ?_
    change fibreCode f hf (f.hom.app (op V) (res A.obj hV (res A.obj (leOfHom k.unop) a)))
        ⟨_, rfl⟩ =
      fibreCode f hf (f.hom.app (op V) (res A.obj (le_trans hV (leOfHom k.unop)) a)) ⟨_, rfl⟩
    rw [res_res]

/-- **The encoding** `A ⟶ genericSheaf`. -/
noncomputable def encode : A ⟶ genericSheaf.{w, u} (X := X) :=
  ObjectProperty.homMk
    (encodePre f hf ≫ toSheafify (Opens.grothendieckTopology X) (codePresheaf.{w, u} (X := X)))

/-- **The encoding is injective on each fibre of `f`.** -/
theorem encode_jointlyInjective : JointlyInjective genericSheaf.{w, u} f (encode f hf) := by
  intro U a a' hb he
  have hmem := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
    (toSheafify (Opens.grothendieckTopology X) (codePresheaf.{w, u} (X := X)))
    (X := op U) ((encodePre f hf).app (op U) a) ((encodePre f hf).app (op U) a') he
  refine sheaf_eq_of_covered A (covered_of_mem hmem fun V k hk => ?_)
  have h₁ : fibreCode f hf (f.hom.app (op V) (res A.obj (le_trans le_rfl (leOfHom k)) a))
        ⟨_, rfl⟩ =
      fibreCode f hf (f.hom.app (op V) (res A.obj (le_trans le_rfl (leOfHom k)) a')) ⟨_, rfl⟩ :=
    congrArg (fun g : (∀ V' : Opens X, V' ≤ V → SmallCode.{w}) => g V le_rfl) hk
  have hb' : f.hom.app (op V) (res A.obj (le_trans le_rfl (leOfHom k)) a) =
      f.hom.app (op V) (res A.obj (le_trans le_rfl (leOfHom k)) a') := by
    rw [res_nat, res_nat, hb]
  exact fibreCode_eq f hf hb' _ _ h₁

variable [Small.{w} (Opens X)]

/-- The base of the universal small map: the power class of the generic sheaf. -/
noncomputable abbrev universeBase : SheafOn X :=
  powerSheaf.{w} (genericSheaf.{w, u} (X := X))

/-- The total object of the universal small map: membership in that power class. -/
noncomputable abbrev universeTotal : SheafOn X :=
  memSheaf.{w} (genericSheaf.{w, u} (X := X))

/-- **The universal small map.** -/
noncomputable abbrev universalMap : universeTotal.{w, u} (X := X) ⟶ universeBase :=
  memFst.{w} (genericSheaf.{w, u} (X := X))

theorem universalMap_small : sheafSmall.{w} (universalMap.{w, u} (X := X)) :=
  memFst_small _

/-- The classifying map of a small map. -/
noncomputable abbrev classifySmall : B ⟶ universeBase.{w, u} (X := X) :=
  classifyMap genericSheaf f (encode f hf) hf (encode_jointlyInjective f hf)

/-- **Every small map is a pullback of the universal small map.** -/
theorem small_isPullback_universal :
    IsPullback (graphMap genericSheaf f (encode f hf) hf (encode_jointlyInjective f hf)) f
      (universalMap.{w, u} (X := X)) (classifySmall f hf) :=
  classify_isPullback _ _ _ _ _

/-- **(R) Representability for small maps of sheaves**, with values in a universe above `w` and
open sets forming a small type. The epimorphism is the identity. -/
theorem sheafSmall_representable :
    RepresentabilityAxiom (sheafSmall.{w} : MorphismProperty (SheafOn X)) :=
  ⟨universeBase.{w, u}, universeTotal, universalMap, universalMap_small, fun {_ B} f hf =>
    ⟨B, _, 𝟙 B, classifySmall f hf, f, 𝟙 _, _, inferInstance, IsPullback.id_horiz f,
      small_isPullback_universal f hf⟩⟩

end Positive

/-! ## Where representability fails -/

section Negative

variable {X : Type u} [TopologicalSpace X]

/-- Functions on the points of an open set, with values in a type. -/
def funPresheaf (T : Type u) : (Opens X)ᵒᵖ ⥤ Type u where
  obj U := ↥(unop U) → T
  map k := TypeCat.ofHom fun g x => g ⟨x.1, leOfHom k.unop x.2⟩
  map_id _ := by
    ext g
    rfl
  map_comp _ _ := by
    ext g
    rfl

theorem funPresheaf_isSheaf (T : Type u) :
    Presieve.IsSheaf (Opens.grothendieckTopology X) (funPresheaf (X := X) T) := by
  refine isSheaf_of_covered _ (fun U s t hst => ?_) (fun U P Pmono hP s compat => ?_)
  · refine funext fun x => ?_
    obtain ⟨V, hV, e, hxV⟩ := covered_opens_iff.mp hst x.1 x.2
    exact congrArg (fun g : ↥V → T => g ⟨x.1, hxV⟩) e
  · have pick : ∀ x : ↥U, ∃ (V : Opens X) (h : V ≤ U), P V h ∧ x.1 ∈ V :=
      fun x => covered_opens_iff.mp hP x.1 x.2
    have agree : ∀ (V V' : Opens X) (h : V ≤ U) (h' : V' ≤ U) (p : P V h) (p' : P V' h')
        (x : X) (hx : x ∈ V) (hx' : x ∈ V'), s V h p ⟨x, hx⟩ = s V' h' p' ⟨x, hx'⟩ := by
      intro V V' h h' p p' x hx hx'
      have e₁ := compat V (V ⊓ V') h inf_le_left p (Pmono V _ h inf_le_left p)
      have e₂ := compat V' (V ⊓ V') h' inf_le_right p' (Pmono V' _ h' inf_le_right p')
      have hx₂ : x ∈ V ⊓ V' := ⟨hx, hx'⟩
      exact (congrArg (fun g : ↥(V ⊓ V') → T => g ⟨x, hx₂⟩) e₁).trans
        (congrArg (fun g : ↥(V ⊓ V') → T => g ⟨x, hx₂⟩) e₂).symm
    refine ⟨fun x => s _ (pick x).choose_spec.fst (pick x).choose_spec.snd.1
      ⟨x.1, (pick x).choose_spec.snd.2⟩, fun V h p => funext fun x => agree _ _ _ _ _ _ _ _ _⟩

/-- **The sheaf of functions on points** with values in `T`. -/
def funSheaf (T : Type u) : SheafOn X :=
  ⟨funPresheaf T, (isSheaf_iff_isSheaf_of_type _ _).mpr (funPresheaf_isSheaf T)⟩

/-- **No universal map when every map to the terminal sheaf is in the class.** On a nonempty
space, a universal `π : El ⟶ U` would give, on some nonempty open set `V`, an injection of the
functions from `V` into the power set of the sections of `El` into those sections: Cantor's
theorem forbids it. -/
theorem not_representable_of_small_terminal [Nonempty X] (S : MorphismProperty (SheafOn X))
    (hS : ∀ A : SheafOn X, S (terminal.from A)) : ¬ RepresentabilityAxiom S := by
  rintro ⟨Ub, El, π, -, rep⟩
  let E := Σ V : Opens X, El.obj.obj (op V)
  obtain ⟨B', A', q, k, f', l, m, hq, sq₁, sq₂⟩ :=
    rep (terminal.from (funSheaf (X := X) (Set E))) (hS _)
  obtain ⟨x₀⟩ := ‹Nonempty X›
  obtain ⟨pt⟩ := terminal_sections_nonempty (X := X) ⊤
  have hcov := covered_surjective_of_epi q ⊤ pt
  obtain ⟨V, -, ⟨c, -⟩, hx₀⟩ := covered_opens_iff.mp hcov x₀ trivial
  have sq₁V := isPullback_sections sq₁ V
  have sq₂V := isPullback_sections sq₂ V
  have hsub := terminal_sections_subsingleton (X := X) V
  have lift : ∀ g : (funSheaf (X := X) (Set E)).obj.obj (op V), ∃ a' : A'.obj.obj (op V),
      l.hom.app (op V) a' = g ∧ f'.hom.app (op V) a' = c :=
    fun g => Types.exists_of_isPullback sq₁V g c (Subsingleton.elim _ _)
  let code : Set E → E := fun T =>
    ⟨V, m.hom.app (op V) (lift (fun _ => T)).choose⟩
  refine Function.cantor_injective code fun T T' e => ?_
  have e' : m.hom.app (op V) (lift fun _ => T).choose =
      m.hom.app (op V) (lift fun _ => T').choose :=
    eq_of_heq (Sigma.mk.inj_iff.mp e).2
  have same := Types.ext_of_isPullback sq₂V e'
    ((lift _).choose_spec.2.trans (lift _).choose_spec.2.symm)
  have hl := congrArg (l.hom.app (op V)) same
  rw [(lift fun _ => T).choose_spec.1, (lift fun _ => T').choose_spec.1] at hl
  exact congrFun hl ⟨x₀, hx₀⟩

/-- When every type of the universe of the values is `w`-small, every map is small. -/
theorem sheafSmall_terminal_of_univLE [UnivLE.{u, w}] (A : SheafOn X) :
    sheafSmall.{w} (terminal.from A) :=
  fun _ _ => inferInstance

/-- **(R) fails** for sheaves with values in a universe whose types are all `w`-small, on any
nonempty space. -/
theorem sheafSmall_not_representable_of_univLE [UnivLE.{u, w}] [Nonempty X] :
    ¬ RepresentabilityAxiom (sheafSmall.{w} : MorphismProperty (SheafOn X)) :=
  not_representable_of_small_terminal _ sheafSmall_terminal_of_univLE

end Negative

end Mettapedia.SetTheory.CarveOuts.Sheaves
