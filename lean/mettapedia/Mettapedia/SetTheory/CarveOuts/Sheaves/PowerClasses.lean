import Mettapedia.SetTheory.CarveOuts.Sheaves.Sections

/-!
# Power classes of sheaves on a space: axiom (P1)

For a sheaf `A` of sets on a space whose open sets form a `w`-small type, the **power class**
`powerSheaf A` has as sections on an open set `U` the small local families of sections of `A`
below `U` (`SmallSub`): on every open `V ≤ U`, a `w`-small set of sections of `A` on `V`, closed
under restriction and local (a section that is in the family on a cover is in it). Restriction
is restriction of the family to smaller open sets.

* `powerSheaf A` is a sheaf (`powerPresheaf_isSheaf`): compatible families glue to the family of
  sections that are locally in the pieces. The glued family is small because a section of it is
  determined by its restrictions to the pieces, and the pieces are indexed by pairs of open sets,
  a small type.
* **Membership** (`memSheaf A`) is the subsheaf of pairs `(R, a)` with `a ∈ R` on the whole open
  set; it is a sheaf because the families are local. Its projection to `powerSheaf A` is small
  (`memFst_small`): the fibre over `R` is the set `R` itself.
* **Classifying maps.** A pair of maps `p : R ⟶ I` (small) and `q : R ⟶ A`, jointly injective,
  is classified by `classifyMap : I ⟶ powerSheaf A`, sending `i` to the sections of `A` that are
  `q`-images of `p`-preimages of `i`. The square from `R` to membership is a pullback
  (`classify_isPullback`).
* **(P1)** (`sheafPowerClass`, `sheafSmall_powerClassAxiom`): membership, as a subobject of
  `powerSheaf A ⨯ A`, classifies every small relation into `A` by pullback along a unique map.

**What makes it small.** The sections of `powerSheaf A` on `U` form a type in the same universe
as the sections of `A`, because a set of sections is a predicate and Lean's `Prop` is
impredicative: this is the full power class, and no predicative variant (fullness) is needed.
Smallness is asked of each member family and is preserved by gluing because the open sets form a
small type; it is what makes membership a small map.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts.Sheaves

open CategoryTheory Limits TopologicalSpace Opposite
open Mettapedia.SetTheory.CarveOuts.Sites
open Mettapedia.SetTheory.CarveOuts.Sites.SmallMaps

universe w u

variable {X : Type u} [TopologicalSpace X]

/-! ## Small local families -/

section SmallSub

variable (A : SheafOn X)

/-- **A small local family of sections below `U`**: on every open `V ≤ U`, a `w`-small set of
sections of `A` on `V`, closed under restriction and local. -/
structure SmallSub (U : Opens X) : Type u where
  carrier : ∀ V : Opens X, V ≤ U → Set (A.obj.obj (op V))
  restrict : ∀ (V W : Opens X) (hV : V ≤ U) (hW : W ≤ V) (a : A.obj.obj (op V)),
    a ∈ carrier V hV → res A.obj hW a ∈ carrier W (le_trans hW hV)
  isLocal : ∀ (V : Opens X) (hV : V ≤ U) (a : A.obj.obj (op V)),
    Covered V (fun W hW => res A.obj hW a ∈ carrier W (le_trans hW hV)) → a ∈ carrier V hV
  small : ∀ (V : Opens X) (hV : V ≤ U), Small.{w} (carrier V hV)

variable {A}

theorem SmallSub.ext' {U : Opens X} {R R' : SmallSub.{w} A U}
    (h : ∀ (V : Opens X) (hV : V ≤ U), R.carrier V hV = R'.carrier V hV) : R = R' := by
  cases R
  cases R'
  congr
  funext V hV
  exact h V hV

variable (A)

/-- Restriction of a family to a smaller open set. -/
def SmallSub.restrictTo {U U' : Opens X} (h : U' ≤ U) (R : SmallSub.{w} A U) :
    SmallSub.{w} A U' where
  carrier V hV := R.carrier V (le_trans hV h)
  restrict V W hV hW a ha := R.restrict V W (le_trans hV h) hW a ha
  isLocal V hV a ha := R.isLocal V (le_trans hV h) a ha
  small V hV := R.small V (le_trans hV h)

/-- **The power class presheaf**: small local families, restricted to smaller open sets. -/
def powerPresheaf : (Opens X)ᵒᵖ ⥤ Type u where
  obj U := SmallSub.{w} A (unop U)
  map k := TypeCat.ofHom (SmallSub.restrictTo A (leOfHom k.unop))
  map_id _ := by
    ext R
    rfl
  map_comp _ _ := by
    ext R
    rfl

theorem powerPresheaf_res_carrier {U U' : Opens X} (h : U' ≤ U) (R : SmallSub.{w} A U)
    (V : Opens X) (hV : V ≤ U') :
    (res (powerPresheaf.{w} A) h R).carrier V hV = R.carrier V (le_trans hV h) :=
  rfl

/-- **The power class presheaf is a sheaf.** -/
theorem powerPresheaf_isSheaf [Small.{w} (Opens X)] :
    Presieve.IsSheaf (Opens.grothendieckTopology X) (powerPresheaf.{w} A) := by
  refine isSheaf_of_covered _ (fun U R R' hRR' => ?_) (fun U P Pmono hP s compat => ?_)
  · -- Separation: two families equal on a cover are equal, by locality.
    have half : ∀ {R R' : SmallSub.{w} A U},
        Covered U (fun V h => res (powerPresheaf.{w} A) h R = res (powerPresheaf.{w} A) h R') →
          ∀ (V₀ : Opens X) (h₀ : V₀ ≤ U) (a : A.obj.obj (op V₀)),
            a ∈ R.carrier V₀ h₀ → a ∈ R'.carrier V₀ h₀ := by
      intro R R' hRR' V₀ h₀ a ha
      refine R'.isLocal _ h₀ a (covered_restrict hRR' h₀ fun V h e => ?_)
      have hc : R.carrier (V₀ ⊓ V) (le_trans inf_le_right h) =
          R'.carrier (V₀ ⊓ V) (le_trans inf_le_right h) :=
        congrArg (fun T : SmallSub.{w} A V => T.carrier (V₀ ⊓ V) inf_le_right) e
      exact (Set.ext_iff.mp hc _).mp (R.restrict _ _ h₀ inf_le_left _ ha)
    refine SmallSub.ext' fun V₀ h₀ => Set.ext fun a => ⟨half hRR' V₀ h₀ a, half ?_ V₀ h₀ a⟩
    exact covered_mono (fun V h e => e.symm) hRR'
  · -- Gluing.
    have agree : ∀ (V V' : Opens X) (h : V ≤ U) (h' : V' ≤ U) (p : P V h) (p' : P V' h')
        (Z : Opens X) (hZ : Z ≤ V) (hZ' : Z ≤ V'),
        (s V h p).carrier Z hZ = (s V' h' p').carrier Z hZ' := by
      intro V V' h h' p p' Z hZ hZ'
      have e₁ := compat V (V ⊓ V') h inf_le_left p (Pmono V _ h inf_le_left p)
      have e₂ := compat V' (V ⊓ V') h' inf_le_right p' (Pmono V' _ h' inf_le_right p')
      have c₁ := congrArg (fun T : SmallSub.{w} A (V ⊓ V') => T.carrier Z (le_inf hZ hZ')) e₁
      have c₂ := congrArg (fun T : SmallSub.{w} A (V ⊓ V') => T.carrier Z (le_inf hZ hZ')) e₂
      exact c₁.trans c₂.symm
    -- A section is in the glued family when it is, on a cover, in the pieces.
    have every : ∀ (V₀ : Opens X) (a : A.obj.obj (op V₀)),
        (Covered V₀ fun W hW => ∃ (V : Opens X) (h : V ≤ U) (p : P V h) (hWV : W ≤ V),
          res A.obj hW a ∈ (s V h p).carrier W hWV) →
        ∀ (V : Opens X) (h : V ≤ U) (p : P V h) (W : Opens X) (hW : W ≤ V₀) (hWV : W ≤ V),
          res A.obj hW a ∈ (s V h p).carrier W hWV := by
      intro V₀ a ha V h p W hW hWV
      refine (s V h p).isLocal _ hWV _ (covered_restrict ha hW fun Z hZ ⟨V', h', p', hZV', hm⟩ => ?_)
      have hm' := (s V' h' p').restrict _ _ hZV' (inf_le_right : W ⊓ Z ≤ Z) _ hm
      rw [res_res] at hm'
      rw [res_res, agree V V' h h' p p' (W ⊓ Z) _ (le_trans inf_le_right hZV')]
      exact hm'
    -- The pieces below `V₀`, indexed by pairs of open sets.
    let Piece : Opens X → Type u := fun V₀ =>
      {q : Opens X × Opens X // q.1 ≤ V₀ ∧ q.1 ≤ q.2 ∧ ∃ h : q.2 ≤ U, P q.2 h}
    refine ⟨{ carrier := fun V₀ _ => {a | Covered V₀ fun W hW => ∃ (V : Opens X) (h : V ≤ U)
                (p : P V h) (hWV : W ≤ V), res A.obj hW a ∈ (s V h p).carrier W hWV}
              restrict := ?_
              isLocal := ?_
              small := ?_ }, fun V h p => ?_⟩
    · intro V₀ W₀ _ hW₀ a ha
      simp only [Set.mem_ofPred_eq] at ha ⊢
      refine covered_restrict ha hW₀ fun W hW ⟨V, h, p, hWV, hm⟩ => ⟨V, h, p,
        le_trans inf_le_right hWV, ?_⟩
      have := (s V h p).restrict _ _ hWV (inf_le_right : W₀ ⊓ W ≤ W) _ hm
      rw [res_res] at this
      rw [res_res]
      exact this
    · intro V₀ _ a ha
      simp only [Set.mem_ofPred_eq] at ha ⊢
      refine covered_trans ha fun W hW hm => covered_mono (fun Z hZ ⟨V, h, p, hZV, hm'⟩ =>
        ⟨V, h, p, hZV, ?_⟩) hm
      rw [res_res] at hm'
      exact hm'
    · intro V₀ h₀
      have : Small.{w} (Piece V₀) := small_subtype _ _
      have : ∀ i : Piece V₀, Small.{w}
          ((s i.1.2 i.2.2.2.fst i.2.2.2.snd).carrier i.1.1 i.2.2.1) :=
        fun i => (s _ _ _).small _ _
      refine small_of_injective (β := ∀ i : Piece V₀,
          ((s i.1.2 i.2.2.2.fst i.2.2.2.snd).carrier i.1.1 i.2.2.1))
        (f := fun a i => ⟨res A.obj i.2.1 a.1,
          every V₀ a.1 a.2 i.1.2 i.2.2.2.fst i.2.2.2.snd i.1.1 i.2.1 i.2.2.1⟩) ?_
      intro a a' e
      refine Subtype.ext (sheaf_eq_of_covered A (covered_restrict hP h₀ fun V h p => ?_))
      let i : Piece V₀ := ⟨(V₀ ⊓ V, V), inf_le_left, inf_le_right, h, p⟩
      exact congrArg Subtype.val (congrFun e i)
    · refine SmallSub.ext' fun V₁ h₁ => Set.ext fun a => ⟨fun ha => ?_, fun ha => ?_⟩
      · change Covered V₁ _ at ha
        have := every V₁ a ha V h p V₁ le_rfl h₁
        rw [res_self] at this
        exact this
      · change Covered V₁ _
        refine covered_self ⟨V, h, p, h₁, ?_⟩
        rw [res_self]
        exact ha

/-- **The power class sheaf.** -/
def powerSheaf [Small.{w} (Opens X)] : SheafOn X :=
  ⟨powerPresheaf.{w} A, (isSheaf_iff_isSheaf_of_type _ _).mpr (powerPresheaf_isSheaf A)⟩

end SmallSub

/-! ## Membership -/

section Membership

variable (A : SheafOn X) [Small.{w} (Opens X)]

/-- The pairs `(R, a)` with `a ∈ R` on the whole open set. -/
def memSubfunctor : Subfunctor (pairPresheaf (powerSheaf.{w} A).obj A.obj) where
  obj U := {x | x.2 ∈ x.1.carrier (unop U) le_rfl}
  map {U V} k x hx := by
    change A.obj.map k x.2 ∈ x.1.carrier (unop V) (le_trans le_rfl (leOfHom k.unop))
    exact x.1.restrict _ _ le_rfl (leOfHom k.unop) _ hx

theorem memSubfunctor_isSheaf :
    Presieve.IsSheaf (Opens.grothendieckTopology X) (memSubfunctor.{w} A).toFunctor := by
  have hpair := pairPresheaf_isSheaf ((isSheaf_iff_isSheaf_of_type _ _).mp (powerSheaf.{w} A).property)
    ((isSheaf_iff_isSheaf_of_type _ _).mp A.property)
  refine ((memSubfunctor.{w} A).isSheaf_iff hpair).mpr fun U x hx => ?_
  refine x.1.isLocal _ le_rfl x.2 (covered_mono (fun V h hV => ?_)
    ((covered_iff_mem _).mpr hx))
  exact hV

/-- **Membership**, as a sheaf. -/
def memSheaf : SheafOn X :=
  ⟨(memSubfunctor.{w} A).toFunctor, (isSheaf_iff_isSheaf_of_type _ _).mpr (memSubfunctor_isSheaf A)⟩

/-- The family of a membership pair. -/
def memFst : memSheaf.{w} A ⟶ powerSheaf.{w} A :=
  ObjectProperty.homMk ((memSubfunctor.{w} A).ι ≫ pairFst _ _)

/-- The member of a membership pair. -/
def memSnd : memSheaf.{w} A ⟶ A :=
  ObjectProperty.homMk ((memSubfunctor.{w} A).ι ≫ pairSnd _ _)

/-- **Membership is small over the power class**: the fibre over a family is the family. -/
theorem memFst_small : sheafSmall.{w} (memFst.{w} A) := by
  intro U R
  have := R.small (unop U) le_rfl
  refine small_of_injective (β := R.carrier (unop U) le_rfl)
    (f := fun x => ⟨x.1.1.2, by
      have h : x.1.1.2 ∈ x.1.1.1.carrier (unop U) le_rfl := x.1.2
      have e : x.1.1.1 = R := x.2
      rw [e] at h
      exact h⟩) ?_
  intro x y e
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (x.2.trans y.2.symm) (congrArg Subtype.val e)

/-- Membership as a map into the product. -/
noncomputable def memArrow : memSheaf.{w} A ⟶ powerSheaf.{w} A ⨯ A :=
  prod.lift (memFst A) (memSnd A)

theorem memArrow_fst (U : Opens X) (x : (memSheaf.{w} A).obj.obj (op U)) :
    (prod.fst : powerSheaf.{w} A ⨯ A ⟶ _).hom.app (op U) ((memArrow A).hom.app (op U) x) =
      x.1.1 :=
  congrArg (fun k : memSheaf.{w} A ⟶ powerSheaf.{w} A => k.hom.app (op U) x) (prod.lift_fst _ _)

theorem memArrow_snd (U : Opens X) (x : (memSheaf.{w} A).obj.obj (op U)) :
    (prod.snd : powerSheaf.{w} A ⨯ A ⟶ _).hom.app (op U) ((memArrow A).hom.app (op U) x) =
      x.1.2 :=
  congrArg (fun k : memSheaf.{w} A ⟶ A => k.hom.app (op U) x) (prod.lift_snd _ _)

instance memArrow_mono : Mono (memArrow.{w} A) := by
  refine mono_of_injective _ fun U x y e => ?_
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · have := congrArg ((prod.fst : powerSheaf.{w} A ⨯ A ⟶ _).hom.app (op U)) e
    rwa [memArrow_fst, memArrow_fst] at this
  · have := congrArg ((prod.snd : powerSheaf.{w} A ⨯ A ⟶ _).hom.app (op U)) e
    rwa [memArrow_snd, memArrow_snd] at this

/-- A section of the product is a membership pair exactly when its member is in its family. -/
theorem memArrow_image_iff (U : Opens X) (y : (powerSheaf.{w} A ⨯ A).obj.obj (op U)) :
    (∃ x, (memArrow.{w} A).hom.app (op U) x = y) ↔
      (prod.snd : powerSheaf.{w} A ⨯ A ⟶ _).hom.app (op U) y ∈
        ((prod.fst : powerSheaf.{w} A ⨯ A ⟶ _).hom.app (op U) y : SmallSub.{w} A U).carrier U
          le_rfl := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [memArrow_fst, memArrow_snd]
    exact x.2
  · intro h
    refine ⟨⟨((prod.fst : powerSheaf.{w} A ⨯ A ⟶ _).hom.app (op U) y,
      (prod.snd : powerSheaf.{w} A ⨯ A ⟶ _).hom.app (op U) y), h⟩, ?_⟩
    exact prod_sections_ext _ _ (memArrow_fst A U _) (memArrow_snd A U _)

end Membership

/-! ## Classifying maps -/

section Classify

variable (A : SheafOn X) [Small.{w} (Opens X)] {I R : SheafOn X} (p : R ⟶ I) (q : R ⟶ A)

/-- Two maps out of `R` that together separate the sections of `R`. -/
def JointlyInjective : Prop :=
  ∀ (U : Opens X) (r r' : R.obj.obj (op U)), p.hom.app (op U) r = p.hom.app (op U) r' →
    q.hom.app (op U) r = q.hom.app (op U) r' → r = r'

variable (hp : sheafSmall.{w} p) (hpq : JointlyInjective A p q)

/-- The sections of `A` related to `i` through `R`. -/
abbrev related {U : Opens X} (i : I.obj.obj (op U)) (V : Opens X) (hV : V ≤ U)
    (a : A.obj.obj (op V)) : Prop :=
  ∃ r : R.obj.obj (op V), p.hom.app (op V) r = res I.obj hV i ∧ q.hom.app (op V) r = a

/-- **The family classifying `R` at `i`.** -/
noncomputable def relSub {U : Opens X} (i : I.obj.obj (op U)) : SmallSub.{w} A U where
  carrier V hV := {a | related A p q i V hV a}
  restrict V W hV hW := by
    rintro a ⟨r, hr, rfl⟩
    exact ⟨res R.obj hW r, by rw [res_nat, hr, res_res], res_nat _ _ _⟩
  isLocal V hV a hloc := by
    obtain ⟨r, hr⟩ := sheaf_glue R hloc
      (fun W hW hm => Classical.choose (show related A p q i W _ (res A.obj hW a) from hm))
      (fun W W' hW hW' hm hm' Z hZ hZ' => by
        have c := Classical.choose_spec (show related A p q i W _ (res A.obj hW a) from hm)
        have c' := Classical.choose_spec (show related A p q i W' _ (res A.obj hW' a) from hm')
        refine hpq Z _ _ ?_ ?_
        · calc p.hom.app (op Z) (res R.obj hZ (Classical.choose _))
                = res I.obj hZ (p.hom.app (op W) (Classical.choose _)) := res_nat _ _ _
            _ = res I.obj hZ (res I.obj (le_trans hW hV) i) := by rw [c.1]
            _ = res I.obj hZ' (res I.obj (le_trans hW' hV) i) :=
                (res_res _ _ _ _).trans (res_res _ _ _ _).symm
            _ = res I.obj hZ' (p.hom.app (op W') (Classical.choose _)) := by rw [c'.1]
            _ = p.hom.app (op Z) (res R.obj hZ' (Classical.choose _)) := (res_nat _ _ _).symm
        · calc q.hom.app (op Z) (res R.obj hZ (Classical.choose _))
                = res A.obj hZ (q.hom.app (op W) (Classical.choose _)) := res_nat _ _ _
            _ = res A.obj hZ (res A.obj hW a) := by rw [c.2]
            _ = res A.obj hZ' (res A.obj hW' a) :=
                (res_res _ _ _ _).trans (res_res _ _ _ _).symm
            _ = res A.obj hZ' (q.hom.app (op W') (Classical.choose _)) := by rw [c'.2]
            _ = q.hom.app (op Z) (res R.obj hZ' (Classical.choose _)) := (res_nat _ _ _).symm)
    refine ⟨r, ?_, ?_⟩
    · refine sheaf_eq_of_covered I (covered_mono (fun W hW hm => ?_) hloc)
      change res I.obj hW (p.hom.app (op V) r) = res I.obj hW (res I.obj hV i)
      rw [← res_nat, hr W hW hm,
        (Classical.choose_spec (show related A p q i W _ (res A.obj hW a) from hm)).1, res_res]
    · refine sheaf_eq_of_covered A (covered_mono (fun W hW hm => ?_) hloc)
      change res A.obj hW (q.hom.app (op V) r) = res A.obj hW a
      rw [← res_nat, hr W hW hm,
        (Classical.choose_spec (show related A p q i W _ (res A.obj hW a) from hm)).2]
  small V hV := by
    have := hp (op V) (res I.obj hV i)
    refine small_of_surjective
      (f := fun r : {r // p.hom.app (op V) r = res I.obj hV i} =>
        (⟨q.hom.app (op V) r.1, r.1, r.2, rfl⟩ : {a | related A p q i V hV a})) ?_
    rintro ⟨a, r, hr, rfl⟩
    exact ⟨⟨r, hr⟩, rfl⟩

/-- **The classifying map** `I ⟶ powerSheaf A`. -/
noncomputable def classifyMap : I ⟶ powerSheaf.{w} A :=
  ObjectProperty.homMk
    { app := fun U => TypeCat.ofHom fun i => relSub A p q hp hpq (U := unop U) i
      naturality := by
        intro U V k
        ext i
        refine SmallSub.ext' fun W hW => Set.ext fun a => ?_
        change related A p q (res I.obj (leOfHom k.unop) i) W hW a ↔
          related A p q i W (le_trans hW (leOfHom k.unop)) a
        unfold related
        rw [res_res] }

theorem classifyMap_app (U : Opens X) (i : I.obj.obj (op U)) :
    (classifyMap A p q hp hpq).hom.app (op U) i = relSub A p q hp hpq i :=
  rfl

/-- The graph of `R` in membership. -/
noncomputable def graphMap : R ⟶ memSheaf.{w} A :=
  ObjectProperty.homMk
    { app := fun U => TypeCat.ofHom fun r =>
        ⟨(relSub A p q hp hpq (U := unop U) (p.hom.app U r), q.hom.app U r),
          ⟨r, (res_self I.obj le_rfl _).symm, rfl⟩⟩
      naturality := by
        intro U V k
        ext r
        apply Subtype.ext
        refine Prod.ext ?_ ?_
        · change (classifyMap A p q hp hpq).hom.app V (p.hom.app V (R.obj.map k r)) =
            (powerSheaf.{w} A).obj.map k ((classifyMap A p q hp hpq).hom.app U (p.hom.app U r))
          rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
        · exact NatTrans.naturality_apply q.hom k r }

/-- **The square from `R` to membership is a pullback.** -/
theorem classify_isPullback :
    IsPullback (graphMap A p q hp hpq) p (memFst.{w} A) (classifyMap A p q hp hpq) := by
  refine isPullback_of_sections (by apply Sheaf.hom_ext; rfl) fun U => ?_
  refine (Types.isPullback_iff _ _ _ _).mpr ⟨?_, ?_, ?_⟩
  · ext r
    rfl
  · rintro r r' ⟨e, e'⟩
    refine hpq U r r' e' ?_
    exact congrArg (fun x : (memSheaf.{w} A).obj.obj (op U) => x.1.2) e
  · intro x i e
    have hx := x.2
    change x.1.2 ∈ x.1.1.carrier U le_rfl at hx
    have e' : x.1.1 = relSub A p q hp hpq i := e
    rw [e'] at hx
    obtain ⟨r, hr, hq⟩ := hx
    rw [res_self] at hr
    refine ⟨r, ?_, hr⟩
    apply Subtype.ext
    refine Prod.ext ?_ hq
    change relSub A p q hp hpq (p.hom.app (op U) r) = x.1.1
    rw [hr, e']

end Classify

/-! ## (P1) -/

section PowerClassAxiom

variable [Small.{w} (Opens X)]

omit [Small.{w} (Opens X)] in
/-- A small relation, read as a jointly injective pair. -/
theorem subobject_jointlyInjective {I A : SheafOn X} (R : Subobject (I ⨯ A)) :
    JointlyInjective A (R.arrow ≫ prod.fst) (R.arrow ≫ prod.snd) := by
  intro U r r' e e'
  exact injective_of_mono R.arrow U (prod_sections_ext I A e e')

omit [Small.{w} (Opens X)] in
/-- The image of a section of `I ⨯ A` under `prod.map χ (𝟙 A)`, read on its two components. -/
theorem prodMap_fst {I A B : SheafOn X} (χ : I ⟶ B) (U : Opens X) (s : (I ⨯ A).obj.obj (op U)) :
    (prod.fst : B ⨯ A ⟶ B).hom.app (op U) ((prod.map χ (𝟙 A)).hom.app (op U) s) =
      χ.hom.app (op U) ((prod.fst : I ⨯ A ⟶ I).hom.app (op U) s) :=
  congrArg (fun k : I ⨯ A ⟶ B => k.hom.app (op U) s) (prod.map_fst χ (𝟙 A))

omit [Small.{w} (Opens X)] in
theorem prodMap_snd {I A B : SheafOn X} (χ : I ⟶ B) (U : Opens X) (s : (I ⨯ A).obj.obj (op U)) :
    (prod.snd : B ⨯ A ⟶ A).hom.app (op U) ((prod.map χ (𝟙 A)).hom.app (op U) s) =
      (prod.snd : I ⨯ A ⟶ A).hom.app (op U) s :=
  congrArg (fun k : I ⨯ A ⟶ A => k.hom.app (op U) s) (prod.map_snd χ (𝟙 A))

/-- A section factors through the pullback of membership along `prod.map χ (𝟙 A)` exactly when its
member is in the family `χ` gives its index. -/
theorem pullback_mem_iff {I A : SheafOn X} (χ : I ⟶ powerSheaf.{w} A) (U : Opens X)
    (s : (I ⨯ A).obj.obj (op U)) :
    (∃ r, ((Subobject.pullback (prod.map χ (𝟙 A))).obj
        (Subobject.mk (memArrow.{w} A))).arrow.hom.app (op U) r = s) ↔
      (prod.snd : I ⨯ A ⟶ A).hom.app (op U) s ∈
        (χ.hom.app (op U) ((prod.fst : I ⨯ A ⟶ I).hom.app (op U) s) : SmallSub.{w} A U).carrier U
          le_rfl := by
  rw [pullback_arrow_sections, mk_arrow_sections, memArrow_image_iff, prodMap_fst, prodMap_snd]

/-- **The power class of a sheaf**, with membership as a subobject of `powerSheaf A ⨯ A`. -/
noncomputable def sheafPowerClass (A : SheafOn X) :
    PowerClass (sheafSmall.{w} : MorphismProperty (SheafOn X)) A where
  obj := powerSheaf.{w} A
  mem := Subobject.mk (memArrow.{w} A)
  mem_small := by
    unfold IsSmallRelation
    rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc]
    change sheafSmall.{w} (_ ≫ prod.lift (memFst.{w} A) (memSnd.{w} A) ≫ prod.fst)
    rw [prod.lift_fst]
    exact sheafSmall_comp _ _ (sheafSmall_monosSmall _ inferInstance) (memFst_small A)
  classify := by
    intro I R hR
    have hpq := subobject_jointlyInjective R
    -- membership in the classified family is membership in `R`
    have key : ∀ (χ : I ⟶ powerSheaf.{w} A),
        (Subobject.pullback (prod.map χ (𝟙 A))).obj (Subobject.mk (memArrow.{w} A)) = R →
        ∀ (U : Opens X) (s : (I ⨯ A).obj.obj (op U)),
          (prod.snd : I ⨯ A ⟶ A).hom.app (op U) s ∈
            (χ.hom.app (op U) ((prod.fst : I ⨯ A ⟶ I).hom.app (op U) s) : SmallSub.{w} A U).carrier
              U le_rfl ↔ ∃ r, R.arrow.hom.app (op U) r = s := by
      intro χ hχ U s
      rw [← pullback_mem_iff, hχ]
    let χ := classifyMap A (R.arrow ≫ prod.fst) (R.arrow ≫ prod.snd) hR hpq
    have hχ : (Subobject.pullback (prod.map χ (𝟙 A))).obj (Subobject.mk (memArrow.{w} A)) = R := by
      refine subobject_eq_of_sections fun U s => ?_
      rw [pullback_mem_iff]
      constructor
      · rintro ⟨r, hr, hq⟩
        rw [res_self] at hr
        exact ⟨r, prod_sections_ext I A hr hq⟩
      · rintro ⟨r, rfl⟩
        exact ⟨r, (res_self I.obj le_rfl _).symm, rfl⟩
    refine ⟨χ, hχ, fun χ' hχ' => ?_⟩
    apply Sheaf.hom_ext
    ext U i
    refine SmallSub.ext' fun V hV => Set.ext fun a => ?_
    obtain ⟨s, hs₁, hs₂⟩ := prod_sections_exists I A (res I.obj hV i) a
    have n' := (res_nat χ'.hom hV i).symm
    have n := (res_nat χ.hom hV i).symm
    have e' := key χ' hχ' V s
    have e := key χ hχ V s
    rw [hs₁, hs₂] at e' e
    change a ∈ (χ'.hom.app U i : SmallSub.{w} A (unop U)).carrier V hV ↔
      a ∈ (χ.hom.app U i : SmallSub.{w} A (unop U)).carrier V hV
    have c' : (χ'.hom.app U i : SmallSub.{w} A (unop U)).carrier V hV =
        (χ'.hom.app (op V) (res I.obj hV i) : SmallSub.{w} A V).carrier V le_rfl :=
      congrArg (fun T : SmallSub.{w} A V => T.carrier V le_rfl) n'
    have c : (χ.hom.app U i : SmallSub.{w} A (unop U)).carrier V hV =
        (χ.hom.app (op V) (res I.obj hV i) : SmallSub.{w} A V).carrier V le_rfl :=
      congrArg (fun T : SmallSub.{w} A V => T.carrier V le_rfl) n
    rw [c', c]
    exact e'.trans e.symm

/-- **(P1) Power classes exist in sheaves on a space whose open sets form a small type.** -/
theorem sheafSmall_powerClassAxiom :
    PowerClassAxiom (sheafSmall.{w} : MorphismProperty (SheafOn X)) :=
  fun A => ⟨sheafPowerClass A⟩

end PowerClassAxiom

end Mettapedia.SetTheory.CarveOuts.Sheaves
