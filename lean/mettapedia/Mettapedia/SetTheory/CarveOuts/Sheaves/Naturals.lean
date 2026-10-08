import Mettapedia.SetTheory.CarveOuts.Sheaves.Sections
import Mathlib.Topology.LocallyConstant.Basic

/-!
# The natural numbers object of sheaves on a space, and its smallness

**In any category** with binary products and a terminal object, a parametrised natural numbers
object (`ParamNNO`) is unique up to a unique isomorphism (`paramNNOIso`): maps out of it are
determined by where zero goes and how the successor acts (`paramNNO_hom_ext`). A map satisfying
the recursion equations is, on the `k`-th numeral, the `k`-th iterate of the step
(`recursion_on_numeral`).

**In sheaves on a space** `X`, the natural numbers object is the sheaf of locally constant
`ℕ`-valued functions (`natSheaf`): on an open set `U`, the functions `U → ℕ` whose fibres are open
(`OpenFibres`, equivalently `IsLocallyConstant`, `openFibres_iff_isLocallyConstant`). Zero and the
successor act pointwise.

* **Recursion** (`natNNO`). Given `f : P ⟶ Y` and `t : P ⨯ Y ⟶ Y`, the map `P ⨯ ℕ ⟶ Y` is glued
  from the iterates of `t` on the open sets where the natural number is constant. It is unique
  because every section of `natSheaf` is, on a cover, a numeral.
* **Smallness.** The sections of `natSheaf` on `U` are determined by their level sets, which are
  open sets of `X`; so they form a `w`-small set as soon as the open sets of `X` do
  (`natSheaf_sections_small`). Every parametrised natural numbers object of sheaves is isomorphic
  to `natSheaf`, so every one is small (`sheafSmall_naturalsSmall`): this is axiom (I).

The level sets are open sets of the space, and the gluing uses points of the space. Choice enters
through `Classical.choose` in the gluing and through Mathlib's limits and sheaf condition.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts.Sheaves

open CategoryTheory Limits TopologicalSpace Opposite
open Mettapedia.SetTheory.CarveOuts.Sites
open Mettapedia.SetTheory.CarveOuts.Sites.SmallMaps

universe w u v u'

/-! ## In any category -/

section Category

variable {E : Type u'} [Category.{v} E] [HasBinaryProducts E] [HasTerminal E]

omit [HasBinaryProducts E] in
theorem terminal_from_self : terminal.from (⊤_ E) = 𝟙 (⊤_ E) :=
  terminal.hom_ext _ _

/-- The numerals `zero ≫ succ ≫ ⋯ ≫ succ`. -/
noncomputable def numeral {N : E} (zero : ⊤_ E ⟶ N) (succ : N ⟶ N) : ℕ → (⊤_ E ⟶ N)
  | 0 => zero
  | k + 1 => numeral zero succ k ≫ succ

/-- The iterates of a step `t` with parameters, from a start `f`. -/
noncomputable def iterateStep {P Y : E} (f : P ⟶ Y) (t : P ⨯ Y ⟶ Y) : ℕ → (P ⟶ Y)
  | 0 => f
  | k + 1 => prod.lift (𝟙 P) (iterateStep f t k) ≫ t

/-- A map satisfying the recursion equations is the `k`-th iterate on the `k`-th numeral. -/
theorem recursion_on_numeral {P Y N : E} (zero : ⊤_ E ⟶ N) (succ : N ⟶ N) (f : P ⟶ Y)
    (t : P ⨯ Y ⟶ Y) (h : P ⨯ N ⟶ Y)
    (h₀ : prod.lift (𝟙 P) (terminal.from P ≫ zero) ≫ h = f)
    (hs : prod.map (𝟙 P) succ ≫ h = prod.lift prod.fst h ≫ t) (k : ℕ) :
    prod.lift (𝟙 P) (terminal.from P ≫ numeral zero succ k) ≫ h = iterateStep f t k := by
  induction k with
  | zero => exact h₀
  | succ k ih =>
    have e : prod.lift (𝟙 P) (terminal.from P ≫ numeral zero succ (k + 1)) =
        prod.lift (𝟙 P) (terminal.from P ≫ numeral zero succ k) ≫ prod.map (𝟙 P) succ := by
      rw [prod.lift_map, Category.comp_id, Category.assoc]
      rfl
    rw [e, Category.assoc, hs, ← Category.assoc, prod.comp_lift, prod.lift_fst, ih]
    rfl

/-- **Maps out of a natural numbers object are determined by zero and the successor.** -/
theorem paramNNO_hom_ext (n : ParamNNO E) {Y : E} (y₀ : ⊤_ E ⟶ Y) (s : Y ⟶ Y) {φ ψ : n.N ⟶ Y}
    (hφ₀ : n.zero ≫ φ = y₀) (hφ : n.succ ≫ φ = φ ≫ s)
    (hψ₀ : n.zero ≫ ψ = y₀) (hψ : n.succ ≫ ψ = ψ ≫ s) : φ = ψ := by
  obtain ⟨h, -, uniq⟩ := n.recursion (P := ⊤_ E) y₀ (prod.snd ≫ s)
  have key : ∀ χ : n.N ⟶ Y, n.zero ≫ χ = y₀ → n.succ ≫ χ = χ ≫ s →
      (prod.snd : (⊤_ E) ⨯ n.N ⟶ n.N) ≫ χ = h := by
    intro χ h₀ hs
    refine uniq _ ⟨?_, ?_⟩
    · rw [prod.lift_snd_assoc, terminal_from_self, Category.id_comp, h₀]
    · simp only [Category.assoc, prod.map_snd_assoc, prod.lift_snd_assoc, hs]
  have e : (prod.snd : (⊤_ E) ⨯ n.N ⟶ n.N) ≫ φ = prod.snd ≫ ψ :=
    (key φ hφ₀ hφ).trans (key ψ hψ₀ hψ).symm
  have := congrArg (fun k => prod.lift (terminal.from n.N) (𝟙 n.N) ≫ k) e
  simpa only [prod.lift_snd_assoc, Category.id_comp] using this

/-- The comparison map between two natural numbers objects, by recursion. -/
noncomputable def paramNNOMap (n m : ParamNNO E) : n.N ⟶ m.N :=
  prod.lift (terminal.from n.N) (𝟙 n.N) ≫
    (n.recursion (P := ⊤_ E) m.zero (prod.snd ≫ m.succ)).exists.choose

theorem paramNNOMap_zero (n m : ParamNNO E) : n.zero ≫ paramNNOMap n m = m.zero := by
  have hspec := (n.recursion (P := ⊤_ E) m.zero (prod.snd ≫ m.succ)).exists.choose_spec
  have e : n.zero ≫ prod.lift (terminal.from n.N) (𝟙 n.N) =
      prod.lift (𝟙 (⊤_ E)) (terminal.from (⊤_ E) ≫ n.zero) := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst]
      exact terminal.hom_ext _ _
    · simp only [Category.assoc, prod.lift_snd, Category.comp_id, terminal_from_self,
        Category.id_comp]
  rw [paramNNOMap, ← Category.assoc, e, hspec.1]

theorem paramNNOMap_succ (n m : ParamNNO E) :
    n.succ ≫ paramNNOMap n m = paramNNOMap n m ≫ m.succ := by
  have hspec := (n.recursion (P := ⊤_ E) m.zero (prod.snd ≫ m.succ)).exists.choose_spec
  have e : n.succ ≫ prod.lift (terminal.from n.N) (𝟙 n.N) =
      prod.lift (terminal.from n.N) (𝟙 n.N) ≫ prod.map (𝟙 (⊤_ E)) n.succ := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, prod.map_fst, Category.comp_id]
      exact terminal.hom_ext _ _
    · simp only [Category.assoc, prod.lift_snd, prod.map_snd, Category.comp_id, prod.lift_snd_assoc,
        Category.id_comp]
  rw [paramNNOMap, ← Category.assoc, e, Category.assoc, hspec.2]
  simp only [prod.lift_snd_assoc, Category.assoc]

/-- **A parametrised natural numbers object is unique up to isomorphism.** -/
noncomputable def paramNNOIso (n m : ParamNNO E) : n.N ≅ m.N where
  hom := paramNNOMap n m
  inv := paramNNOMap m n
  hom_inv_id := paramNNO_hom_ext n n.zero n.succ
    (by rw [← Category.assoc, paramNNOMap_zero, paramNNOMap_zero])
    (by rw [← Category.assoc, paramNNOMap_succ, Category.assoc, paramNNOMap_succ,
      Category.assoc])
    (Category.comp_id _) (by rw [Category.comp_id, Category.id_comp])
  inv_hom_id := paramNNO_hom_ext m m.zero m.succ
    (by rw [← Category.assoc, paramNNOMap_zero, paramNNOMap_zero])
    (by rw [← Category.assoc, paramNNOMap_succ, Category.assoc, paramNNOMap_succ,
      Category.assoc])
    (Category.comp_id _) (by rw [Category.comp_id, Category.id_comp])

end Category

/-! ## The sheaf of locally constant natural numbers -/

section NatSheaf

variable {X : Type u} [TopologicalSpace X]

/-- Membership along an inclusion of open sets. -/
theorem mem_of_le {U V : Opens X} (h : V ≤ U) {x : X} (hx : x ∈ V) : x ∈ U :=
  h hx

/-- A function on the points of an open set whose fibres are open sets of the space. -/
def OpenFibres {U : Opens X} (n : U → ℕ) : Prop :=
  ∀ S : Set ℕ, IsOpen {x : X | ∃ h : x ∈ U, n ⟨x, h⟩ ∈ S}

/-- Open fibres are local constancy. -/
theorem openFibres_iff_isLocallyConstant {U : Opens X} (n : U → ℕ) :
    OpenFibres n ↔ IsLocallyConstant n := by
  constructor
  · intro hn S
    have e : n ⁻¹' S = Subtype.val ⁻¹' {x : X | ∃ h : x ∈ U, n ⟨x, h⟩ ∈ S} := by
      ext x
      exact ⟨fun hx => ⟨x.2, hx⟩, fun ⟨_, hx⟩ => hx⟩
    rw [e]
    exact (hn S).preimage continuous_subtype_val
  · intro hn S
    have e : {x : X | ∃ h : x ∈ U, n ⟨x, h⟩ ∈ S} = Subtype.val '' (n ⁻¹' S) := by
      ext x
      exact ⟨fun ⟨h, hx⟩ => ⟨⟨x, h⟩, hx, rfl⟩, fun ⟨y, hy, hyx⟩ => hyx ▸ ⟨y.2, hy⟩⟩
    rw [e]
    exact U.isOpen.isOpenMap_subtype_val _ (hn S)

/-- The presheaf of locally constant `ℕ`-valued functions. -/
def natPresheaf : (Opens X)ᵒᵖ ⥤ Type u where
  obj U := {n : ↥(unop U) → ℕ // OpenFibres n}
  map {U V} k := TypeCat.ofHom fun n => ⟨fun x => n.1 ⟨x.1, leOfHom k.unop x.2⟩, fun S => by
    have h := (unop V).isOpen.inter (n.2 S)
    convert h using 1
    ext x
    exact ⟨fun ⟨hx, hS⟩ => ⟨hx, leOfHom k.unop hx, hS⟩, fun ⟨hx, _, hS⟩ => ⟨hx, hS⟩⟩⟩

theorem natPresheaf_isSheaf :
    Presieve.IsSheaf (Opens.grothendieckTopology X) (natPresheaf (X := X)) := by
  refine isSheaf_of_covered _ (fun U s t hst => ?_) (fun U P Pmono hP s compat => ?_)
  · apply Subtype.ext
    funext x
    obtain ⟨V, hV, e, hxV⟩ := covered_opens_iff.mp hst x.1 x.2
    exact congrArg (fun m : (natPresheaf (X := X)).obj (op V) => m.1 ⟨x.1, hxV⟩) e
  · have pick : ∀ x : (U : Opens X), ∃ (V : Opens X) (h : V ≤ U), P V h ∧ x.1 ∈ V :=
      fun x => covered_opens_iff.mp hP x.1 x.2
    have agree : ∀ (V V' : Opens X) (h : V ≤ U) (h' : V' ≤ U) (p : P V h) (p' : P V' h')
        (x : X) (hx : x ∈ V) (hx' : x ∈ V'), (s V h p).1 ⟨x, hx⟩ = (s V' h' p').1 ⟨x, hx'⟩ := by
      intro V V' h h' p p' x hx hx'
      have e₁ := compat V (V ⊓ V') h inf_le_left p (Pmono V _ h inf_le_left p)
      have e₂ := compat V' (V ⊓ V') h' inf_le_right p' (Pmono V' _ h' inf_le_right p')
      have hx₂ : x ∈ V ⊓ V' := ⟨hx, hx'⟩
      exact (congrArg (fun m : (natPresheaf (X := X)).obj (op (V ⊓ V')) => m.1 ⟨x, hx₂⟩) e₁).trans
        (congrArg (fun m : (natPresheaf (X := X)).obj (op (V ⊓ V')) => m.1 ⟨x, hx₂⟩) e₂).symm
    let t : ↥U → ℕ := fun x =>
      (s (pick x).choose (pick x).choose_spec.fst (pick x).choose_spec.snd.1).1
        ⟨x.1, (pick x).choose_spec.snd.2⟩
    have t_eq : ∀ (V : Opens X) (h : V ≤ U) (p : P V h) (x : X) (hx : x ∈ V),
        t ⟨x, h hx⟩ = (s V h p).1 ⟨x, hx⟩ := fun V h p x hx => agree _ _ _ _ _ _ _ _ _
    refine ⟨⟨t, fun S => ?_⟩, fun V h p => Subtype.ext (funext fun x => t_eq V h p x.1 x.2)⟩
    refine isOpen_iff_forall_mem_open.mpr fun x ⟨hx, hxS⟩ => ?_
    obtain ⟨V, h, p, hxV⟩ := pick ⟨x, hx⟩
    refine ⟨{y | ∃ hy : y ∈ V, (s V h p).1 ⟨y, hy⟩ ∈ S}, ?_, (s V h p).2 S, ⟨hxV, ?_⟩⟩
    · rintro y ⟨hy, hyS⟩
      exact ⟨h hy, by rw [t_eq V h p y hy]; exact hyS⟩
    · rw [← t_eq V h p x hxV]
      exact hxS

/-- **The sheaf of locally constant natural numbers.** -/
def natSheaf : SheafOn X :=
  ⟨natPresheaf, (isSheaf_iff_isSheaf_of_type _ _).mpr natPresheaf_isSheaf⟩

/-- The constant section. -/
def natConst (U : Opens X) (k : ℕ) : (natSheaf (X := X)).obj.obj (op U) :=
  ⟨fun _ => k, fun S => by
    convert U.isOpen.inter (isOpen_const (p := k ∈ S)) using 1
    ext x
    exact ⟨fun ⟨hx, hS⟩ => ⟨hx, hS⟩, fun ⟨hx, hS⟩ => ⟨hx, hS⟩⟩⟩

/-- Zero: the constant section `0`. -/
noncomputable def natZero : ⊤_ (SheafOn X) ⟶ natSheaf (X := X) :=
  ObjectProperty.homMk
    { app := fun U => TypeCat.ofHom fun _ => natConst (unop U) 0
      naturality := fun _ _ _ => by ext; rfl }

/-- The successor, pointwise. -/
def natSucc : natSheaf (X := X) ⟶ natSheaf :=
  ObjectProperty.homMk
    { app := fun _ => TypeCat.ofHom fun n => ⟨fun x => n.1 x + 1, fun S => n.2 ((· + 1) ⁻¹' S)⟩
      naturality := fun _ _ _ => by ext; rfl }

theorem numeral_app (k : ℕ) (V : Opens X) (x : (⊤_ SheafOn X).obj.obj (op V)) :
    (numeral (natZero (X := X)) natSucc k).hom.app (op V) x = natConst V k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (natSucc (X := X)).hom.app (op V)
      ((numeral (natZero (X := X)) natSucc k).hom.app (op V) x) = _
    rw [ih]
    rfl

/-- The open sets on which a section is constant cover. -/
theorem natLevels_covered {U : Opens X} (n : (natSheaf (X := X)).obj.obj (op U)) :
    Covered U fun V h => ∃ k : ℕ, ∀ (x : X) (hx : x ∈ V), n.1 ⟨x, mem_of_le h hx⟩ = k := by
  refine covered_opens_iff.mpr fun x hx => ?_
  refine ⟨⟨{y | ∃ hy : y ∈ U, n.1 ⟨y, hy⟩ ∈ ({n.1 ⟨x, hx⟩} : Set ℕ)}, n.2 _⟩,
    fun y ⟨hy, _⟩ => hy, ⟨n.1 ⟨x, hx⟩, fun y ⟨_, hyk⟩ => hyk⟩, ⟨hx, rfl⟩⟩

/-- A section that is constant on an open set is the constant section there. -/
theorem res_eq_natConst {U V : Opens X} (h : V ≤ U) (n : (natSheaf (X := X)).obj.obj (op U))
    {k : ℕ} (hk : ∀ (x : X) (hx : x ∈ V), n.1 ⟨x, mem_of_le h hx⟩ = k) :
    res (natSheaf (X := X)).obj h n = natConst V k :=
  Subtype.ext (funext fun x => hk x.1 x.2)

/-! ### Recursion -/

variable {P Y : SheafOn X} (f : P ⟶ Y) (t : P ⨯ Y ⟶ Y)

/-- On an open set, iterates indexed by two values of a function constant on it agree. -/
theorem iterate_level_congr {V : Opens X} (q : P.obj.obj (op V)) {k k' : ℕ} (m : V → ℕ)
    (hk : ∀ (x : X) (hx : x ∈ V), m ⟨x, hx⟩ = k) (hk' : ∀ (x : X) (hx : x ∈ V), m ⟨x, hx⟩ = k') :
    (iterateStep f t k).hom.app (op V) q = (iterateStep f t k').hom.app (op V) q := by
  by_cases hV : ∃ x, x ∈ V
  · obtain ⟨x, hx⟩ := hV
    rw [show k = k' from (hk x hx).symm.trans (hk' x hx)]
  · have := sheaf_sections_subsingleton_of_empty Y (W := V) fun x hx => hV ⟨x, hx⟩
    exact Subsingleton.elim _ _

/-- **The glued section**: on the open sets where the natural number is `k`, the `k`-th
iterate. -/
theorem recSection_exists (U : Opens X) (p : P.obj.obj (op U))
    (n : (natSheaf (X := X)).obj.obj (op U)) :
    ∃ y : Y.obj.obj (op U), ∀ (V : Opens X) (h : V ≤ U) (k : ℕ),
      (∀ (x : X) (hx : x ∈ V), n.1 ⟨x, mem_of_le h hx⟩ = k) →
        res Y.obj h y = (iterateStep f t k).hom.app (op V) (res P.obj h p) := by
  obtain ⟨y, hy⟩ := sheaf_glue Y (natLevels_covered n)
    (fun V h pf => (iterateStep f t pf.choose).hom.app (op V) (res P.obj h p))
    (fun V V' h h' pf pf' Z hZ hZ' => by
      rw [← res_nat, ← res_nat, res_res, res_res]
      exact iterate_level_congr f t _ (fun z : Z => n.1 ⟨z.1, h (hZ z.2)⟩)
        (fun z hz => pf.choose_spec z (hZ hz)) (fun z hz => pf'.choose_spec z (hZ' hz)))
  refine ⟨y, fun V h k hk => (hy V h ⟨k, hk⟩).trans ?_⟩
  exact iterate_level_congr f t _ (fun z : V => n.1 ⟨z.1, h z.2⟩)
    (fun z hz => (⟨k, hk⟩ : ∃ k : ℕ, ∀ (x : X) (hx : x ∈ V), n.1 ⟨x, mem_of_le h hx⟩ = k).choose_spec z hz)
    hk

/-- The recursive map, on sections. -/
noncomputable def recApp (U : Opens X) (s : (P ⨯ natSheaf (X := X)).obj.obj (op U)) :
    Y.obj.obj (op U) :=
  (recSection_exists f t U ((prod.fst : P ⨯ natSheaf ⟶ P).hom.app (op U) s)
    ((prod.snd : P ⨯ natSheaf ⟶ natSheaf).hom.app (op U) s)).choose

theorem recApp_spec (U : Opens X) (s : (P ⨯ natSheaf (X := X)).obj.obj (op U)) (V : Opens X)
    (h : V ≤ U) (k : ℕ)
    (hk : ∀ (x : X) (hx : x ∈ V),
      ((prod.snd : P ⨯ natSheaf ⟶ natSheaf).hom.app (op U) s).1 ⟨x, mem_of_le h hx⟩ = k) :
    res Y.obj h (recApp f t U s) =
      (iterateStep f t k).hom.app (op V)
        (res P.obj h ((prod.fst : P ⨯ natSheaf ⟶ P).hom.app (op U) s)) :=
  (recSection_exists f t U _ _).choose_spec V h k hk

/-- **The recursive map** `P ⨯ ℕ ⟶ Y`. -/
noncomputable def recMap : P ⨯ natSheaf (X := X) ⟶ Y :=
  ObjectProperty.homMk
    { app := fun U => TypeCat.ofHom (recApp f t (unop U))
      naturality := by
        intro U V k
        ext s
        change recApp f t (unop V) (res _ (leOfHom k.unop) s) =
          res Y.obj (leOfHom k.unop) (recApp f t (unop U) s)
        apply sheaf_eq_of_covered Y
        refine covered_mono (fun W hW ⟨j, hj⟩ => ?_)
          (natLevels_covered ((prod.snd : P ⨯ natSheaf ⟶ natSheaf).hom.app _
            (res _ (leOfHom k.unop) s)))
        change res Y.obj hW _ = res Y.obj hW _
        rw [recApp_spec f t _ _ W hW j hj, res_res,
          recApp_spec f t _ s W (le_trans hW (leOfHom k.unop)) j fun x hx => by
            have := hj x hx
            rw [res_nat] at this
            exact this,
          res_nat (prod.fst : P ⨯ natSheaf ⟶ P).hom (leOfHom k.unop) s, res_res] }

theorem recMap_app (U : Opens X) (s : (P ⨯ natSheaf (X := X)).obj.obj (op U)) :
    (recMap f t).hom.app (op U) s = recApp f t U s :=
  rfl

theorem recMap_zero :
    prod.lift (𝟙 P) (terminal.from P ≫ natZero (X := X)) ≫ recMap f t = f := by
  apply Sheaf.hom_ext
  ext U p
  change recApp f t (unop U) ((prod.lift (𝟙 P) (terminal.from P ≫ natZero)).hom.app U p) = _
  have hfst : (prod.fst : P ⨯ natSheaf ⟶ P).hom.app U
      ((prod.lift (𝟙 P) (terminal.from P ≫ natZero)).hom.app U p) = p :=
    congrArg (fun k : P ⟶ P => k.hom.app U p) (prod.lift_fst _ _)
  have hsnd : (prod.snd : P ⨯ natSheaf ⟶ natSheaf).hom.app U
      ((prod.lift (𝟙 P) (terminal.from P ≫ natZero)).hom.app U p) = natConst (unop U) 0 :=
    congrArg (fun k : P ⟶ natSheaf => k.hom.app U p) (prod.lift_snd _ _)
  have := recApp_spec f t (unop U) _ (unop U) le_rfl 0 fun x hx => by rw [hsnd]; rfl
  rw [res_self, res_self, hfst] at this
  exact this

theorem recMap_succ :
    prod.map (𝟙 P) (natSucc (X := X)) ≫ recMap f t = prod.lift prod.fst (recMap f t) ≫ t := by
  apply Sheaf.hom_ext
  ext U s
  change recApp f t (unop U) ((prod.map (𝟙 P) natSucc).hom.app U s) =
    t.hom.app U ((prod.lift prod.fst (recMap f t)).hom.app U s)
  apply sheaf_eq_of_covered Y
  refine covered_mono (fun W hW ⟨j, hj⟩ => ?_)
    (natLevels_covered ((prod.snd : P ⨯ natSheaf ⟶ natSheaf).hom.app _ s))
  have hfst : (prod.fst : P ⨯ natSheaf ⟶ P).hom.app U ((prod.map (𝟙 P) natSucc).hom.app U s) =
      (prod.fst : P ⨯ natSheaf ⟶ P).hom.app U s :=
    congrArg (fun k : P ⨯ natSheaf ⟶ P => k.hom.app U s) (prod.map_fst (𝟙 P) natSucc)
  have hsnd : (prod.snd : P ⨯ natSheaf ⟶ natSheaf).hom.app U
      ((prod.map (𝟙 P) natSucc).hom.app U s) =
      natSucc.hom.app U ((prod.snd : P ⨯ natSheaf ⟶ natSheaf).hom.app U s) :=
    congrArg (fun k : P ⨯ natSheaf ⟶ natSheaf => k.hom.app U s) (prod.map_snd (𝟙 P) natSucc)
  change res Y.obj hW _ = res Y.obj hW _
  rw [recApp_spec f t _ _ W hW (j + 1) (fun x hx => by rw [hsnd]; exact congrArg (· + 1) (hj x hx)),
    hfst]
  change t.hom.app (op W) ((prod.lift (𝟙 P) (iterateStep f t j)).hom.app (op W) _) = _
  rw [← res_nat t.hom hW]
  refine congrArg (t.hom.app (op W)) ?_
  refine prod_sections_ext P Y ?_ ?_
  · change (prod.lift (𝟙 P) (iterateStep f t j) ≫ prod.fst).hom.app (op W) _ = _
    rw [prod.lift_fst, res_nat (prod.fst : P ⨯ Y ⟶ P).hom hW]
    change _ = res P.obj hW ((prod.lift prod.fst (recMap f t) ≫ prod.fst).hom.app U s)
    rw [prod.lift_fst]
    rfl
  · change (prod.lift (𝟙 P) (iterateStep f t j) ≫ prod.snd).hom.app (op W) _ = _
    rw [prod.lift_snd, res_nat (prod.snd : P ⨯ Y ⟶ Y).hom hW]
    change _ = res Y.obj hW ((prod.lift prod.fst (recMap f t) ≫ prod.snd).hom.app U s)
    rw [prod.lift_snd]
    exact (recApp_spec f t _ s W hW j hj).symm

/-- Two maps that agree on every numeral agree. -/
theorem natRec_ext {h₁ h₂ : P ⨯ natSheaf (X := X) ⟶ Y}
    (e : ∀ k : ℕ, prod.lift (𝟙 P) (terminal.from P ≫ numeral natZero natSucc k) ≫ h₁ =
      prod.lift (𝟙 P) (terminal.from P ≫ numeral natZero natSucc k) ≫ h₂) : h₁ = h₂ := by
  apply Sheaf.hom_ext
  ext U s
  apply sheaf_eq_of_covered Y
  refine covered_mono (fun W hW ⟨j, hj⟩ => ?_)
    (natLevels_covered ((prod.snd : P ⨯ natSheaf ⟶ natSheaf).hom.app _ s))
  have hs : res _ hW s = (prod.lift (𝟙 P) (terminal.from P ≫ numeral natZero natSucc j)).hom.app
      (op W) (res P.obj hW ((prod.fst : P ⨯ natSheaf ⟶ P).hom.app _ s)) := by
    refine prod_sections_ext P natSheaf ?_ ?_
    · rw [res_nat]
      exact (congrArg (fun k : P ⟶ P => k.hom.app (op W) (res P.obj hW
        ((prod.fst : P ⨯ natSheaf ⟶ P).hom.app _ s)))
        (prod.lift_fst (𝟙 P) (terminal.from P ≫ numeral natZero natSucc j))).symm
    · rw [res_nat, res_eq_natConst hW _ hj]
      refine Eq.trans ?_ (congrArg (fun k : P ⟶ natSheaf => k.hom.app (op W) (res P.obj hW
        ((prod.fst : P ⨯ natSheaf ⟶ P).hom.app _ s)))
        (prod.lift_snd (𝟙 P) (terminal.from P ≫ numeral natZero natSucc j))).symm
      exact (numeral_app j W _).symm
  change res Y.obj hW (h₁.hom.app _ s) = res Y.obj hW (h₂.hom.app _ s)
  rw [← res_nat, ← res_nat, hs]
  exact congrArg (fun k : P ⟶ Y => k.hom.app (op W) (res P.obj hW
    ((prod.fst : P ⨯ natSheaf ⟶ P).hom.app _ s))) (e j)

/-- **The sheaf of locally constant natural numbers is a parametrised natural numbers object.** -/
noncomputable def natNNO : ParamNNO (SheafOn X) where
  N := natSheaf
  zero := natZero
  succ := natSucc
  recursion f t := ⟨recMap f t, ⟨recMap_zero f t, recMap_succ f t⟩, fun h ⟨h₀, hs⟩ =>
    natRec_ext fun k =>
      (recursion_on_numeral natZero natSucc f t h h₀ hs k).trans
        (recursion_on_numeral natZero natSucc f t (recMap f t) (recMap_zero f t)
          (recMap_succ f t) k).symm⟩

/-! ### Smallness -/

/-- **The locally constant natural numbers on an open set form a small set**, when the open sets
of the space do: a section is determined by its level sets. -/
theorem natSheaf_sections_small [Small.{w} (Opens X)] (U : Opens X) :
    Small.{w} ((natSheaf (X := X)).obj.obj (op U)) := by
  refine small_of_injective (β := ℕ → Opens X)
    (f := fun n k => ⟨{x | ∃ h : x ∈ U, n.1 ⟨x, h⟩ ∈ ({k} : Set ℕ)}, n.2 {k}⟩) ?_
  intro n n' e
  apply Subtype.ext
  funext x
  have e' : {y | ∃ h : y ∈ U, n.1 ⟨y, h⟩ ∈ ({n.1 x} : Set ℕ)} =
      {y | ∃ h : y ∈ U, n'.1 ⟨y, h⟩ ∈ ({n.1 x} : Set ℕ)} :=
    congrArg (fun O : Opens X => (O : Set X)) (congrFun e (n.1 x))
  obtain ⟨_, hk⟩ := (Set.ext_iff.mp e' x.1).mp ⟨x.2, rfl⟩
  exact hk.symm

/-- **The natural numbers object of sheaves is small.** -/
theorem natSheaf_small [Small.{w} (Opens X)] :
    sheafSmall.{w} (terminal.from (natSheaf (X := X))) := by
  intro U a
  have := natSheaf_sections_small.{w} (unop U)
  exact small_of_injective (f := fun y : {y // _} => y.1) fun _ _ => Subtype.ext

/-- **(I) Every parametrised natural numbers object of sheaves is small**: it is isomorphic to the
sheaf of locally constant natural numbers. -/
theorem sheafSmall_naturalsSmall [Small.{w} (Opens X)] :
    NaturalsSmallAxiom (sheafSmall.{w} : MorphismProperty (SheafOn X)) := by
  intro n U a
  have := natSheaf_sections_small.{w} (X := X) (unop U)
  let e := paramNNOIso n natNNO
  refine small_of_injective (β := (natSheaf (X := X)).obj.obj (op (unop U)))
    (f := fun y : {y // _} => e.hom.hom.app U y.1) fun y₁ y₂ same => ?_
  apply Subtype.ext
  have h₁ := congrArg (fun k => k.hom.app U y₁.1) e.hom_inv_id
  have h₂ := congrArg (fun k => k.hom.app U y₂.1) e.hom_inv_id
  change e.inv.hom.app U (e.hom.hom.app U y₁.1) = y₁.1 at h₁
  change e.inv.hom.app U (e.hom.hom.app U y₂.1) = y₂.1 at h₂
  rw [← h₁, ← h₂]
  exact congrArg (e.inv.hom.app U) same

end NatSheaf

end Mettapedia.SetTheory.CarveOuts.Sheaves
