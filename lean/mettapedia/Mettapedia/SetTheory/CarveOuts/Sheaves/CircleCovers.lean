import Mathlib.Algebra.Order.Field.Basic
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.LocallySurjective
import Mettapedia.GSLT.Core.NonFactorization

/-!
# The exponential covering: an epimorphism of sheaves that is not surjective on sections

`UnitAddCircle`, the quotient `ℝ ⧸ ℤ`, is the additive model of the circle, and the quotient
map `ℝ → UnitAddCircle` is the covering `t ↦ exp(2πit)`.

Let `R` be the sheaf of continuous real-valued functions on the circle and `C` the sheaf of
continuous circle-valued functions. Postcomposition with the quotient map is a morphism
`exp : R ⟶ C`.

* It is an epimorphism of sheaves: it is locally surjective. Around every value there is a
  chart of the covering, cut at the antipode of a chosen representative, on which a continuous
  logarithm exists.
* It is not surjective on global sections. The identity of the circle has no continuous
  logarithm: the straight-line lift of the standard loop and the lift through a logarithm
  would be two lifts of one loop with the same start and different ends.
* Reading a morphism by "surjective on every open set" does not determine "epimorphism of
  sheaves". The zero map `ℝ → UnitAddCircle` fails the first reading for the same reason the
  exponential does, and it is not an epimorphism. That pair is a `NonTrivialFiber`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.SetTheory.CarveOuts.Sheaves

open CategoryTheory Opposite TopologicalSpace TopologicalSpace.Opens Set
open CategoryTheory.Functor
open Mettapedia.GSLT.Core.NonFactorization

section Circle

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

abbrev circleSpace : TopCat := TopCat.of UnitAddCircle

abbrev lineSpace : TopCat := TopCat.of ℝ

/-- The quotient map `ℝ → ℝ ⧸ ℤ`, the exponential covering of the circle. -/
def circleArrow : lineSpace ⟶ circleSpace :=
  TopCat.ofHom ⟨((↑) : ℝ → UnitAddCircle), AddCircle.continuous_mk' (1 : ℝ)⟩

lemma circleArrow_apply (t : ℝ) : circleArrow t = (t : UnitAddCircle) := by
  simp [circleArrow]

/-- The constant map at `0`. -/
def zeroArrow : lineSpace ⟶ circleSpace :=
  TopCat.ofHom ⟨fun _ => 0, continuous_const⟩

lemma zeroArrow_apply (t : ℝ) : zeroArrow t = 0 := by
  simp [zeroArrow]

/-- The constant endomorphism of the circle at `0`. -/
def zeroEndArrow : circleSpace ⟶ circleSpace :=
  TopCat.ofHom ⟨fun _ => 0, continuous_const⟩

def realSheaf : TopCat.Sheaf (Type _) circleSpace :=
  TopCat.sheafToTop (X := circleSpace) lineSpace

def circleSheaf : TopCat.Sheaf (Type _) circleSpace :=
  TopCat.sheafToTop (X := circleSpace) circleSpace

/-- Postcomposition with the exponential covering. -/
def expNat : realSheaf.obj ⟶ circleSheaf.obj :=
  whiskerLeft (toTopCat circleSpace).op (yoneda.map circleArrow)

def expHom : realSheaf ⟶ circleSheaf :=
  ObjectProperty.homMk expNat

/-- Postcomposition with the constant map at `0`. -/
def zeroNat : realSheaf.obj ⟶ circleSheaf.obj :=
  whiskerLeft (toTopCat circleSpace).op (yoneda.map zeroArrow)

def zeroHom : realSheaf ⟶ circleSheaf :=
  ObjectProperty.homMk zeroNat

/-- Postcomposition with the constant endomorphism at `0`. -/
def zeroEndNat : circleSheaf.obj ⟶ circleSheaf.obj :=
  whiskerLeft (toTopCat circleSpace).op (yoneda.map zeroEndArrow)

def zeroEnd : circleSheaf ⟶ circleSheaf :=
  ObjectProperty.homMk zeroEndNat

/-- The identity section of the sheaf of circle-valued functions, over the whole circle. -/
def identitySection : (toTopCat circleSpace).obj ⊤ ⟶ circleSpace :=
  (inclusionTopIso circleSpace).hom

lemma exp_app {U : Opens circleSpace} (f : realSheaf.obj.obj (op U)) :
    expHom.hom.app (op U) f = f ≫ circleArrow :=
  rfl

lemma zero_app {U : Opens circleSpace} (f : realSheaf.obj.obj (op U)) :
    zeroHom.hom.app (op U) f = f ≫ zeroArrow :=
  rfl

lemma zeroEnd_app {U : Opens circleSpace} (f : circleSheaf.obj.obj (op U)) :
    zeroEnd.hom.app (op U) f = f ≫ zeroEndArrow :=
  rfl

lemma circle_restrict {T : TopCat} {V U : Opens circleSpace} (h : V ≤ U)
    (f : (toTopCat circleSpace).obj U ⟶ T) :
    (TopCat.presheafToTop circleSpace T).map (homOfLE h).op f =
      (toTopCat circleSpace).map (homOfLE h) ≫ f :=
  rfl

lemma circleSheaf_restrict {V U : Opens circleSpace} (h : V ≤ U)
    (f : circleSheaf.obj.obj (op U)) :
    circleSheaf.obj.map (homOfLE h).op f =
      (toTopCat circleSpace).map (homOfLE h) ≫ f :=
  rfl

lemma identitySection_apply (y : UnitAddCircle) :
    identitySection ⟨y, trivial⟩ = y := by
  unfold identitySection inclusionTopIso
  exact congrFun (coe_inclusion' (X := circleSpace) (U := ⊤)) ⟨y, trivial⟩

/-! ## A chart of the covering around every point -/

lemma half_pos : (0 : ℝ) < 2⁻¹ :=
  inv_pos.mpr zero_lt_two

/-- `1 / 2` is not an integer, so it is nonzero on the circle. -/
lemma half_ne_zero : ((2⁻¹ : ℝ) : UnitAddCircle) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).1 h
  rw [zsmul_one] at hn
  cases n with
  | ofNat k =>
    cases k with
    | zero =>
      rw [Int.ofNat_eq_natCast, Int.cast_natCast, Nat.cast_zero] at hn
      exact half_pos.ne' hn.symm
    | succ k =>
      rw [Int.ofNat_eq_natCast, Int.cast_natCast] at hn
      have hge : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
        rw [Nat.cast_add, Nat.cast_one]
        exact le_add_of_nonneg_left (Nat.cast_nonneg k)
      exact not_lt_of_ge hge (hn.symm ▸ two_inv_lt_one)
  | negSucc k =>
    have hneg : (Int.negSucc k : ℝ) < 0 := by
      rw [Int.cast_negSucc]
      exact neg_lt_zero.mpr (Nat.cast_pos.mpr (Nat.succ_pos k))
    exact not_lt_of_gt half_pos (hn ▸ hneg)

/-- The representative in `[0, 1)`. -/
def rep (y : UnitAddCircle) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0 y : ℝ)

lemma coe_rep (y : UnitAddCircle) : (rep y : UnitAddCircle) = y := by
  simp [rep]

/-- The cut of the chart: half a turn before the representative. -/
def anchor (y : UnitAddCircle) : ℝ :=
  rep y - 2⁻¹

lemma rep_sub_anchor (y : UnitAddCircle) : rep y - anchor y = 2⁻¹ := by
  unfold anchor
  exact sub_sub_cancel (rep y) (2⁻¹)

lemma anchor_add_sub_rep (y : UnitAddCircle) : anchor y + 1 - rep y = 1 - 2⁻¹ := by
  unfold anchor
  ring

lemma rep_mem_Ioo (y : UnitAddCircle) : rep y ∈ Ioo (anchor y) (anchor y + 1) :=
  ⟨sub_pos.mp (rep_sub_anchor y ▸ half_pos),
    sub_pos.mp (anchor_add_sub_rep y ▸ sub_pos.mpr two_inv_lt_one)⟩

lemma y_ne_anchor (y : UnitAddCircle) : y ≠ (anchor y : UnitAddCircle) := by
  intro h
  apply half_ne_zero
  rw [← rep_sub_anchor, AddCircle.coe_sub, coe_rep]
  exact sub_eq_zero.mpr h

/-- The covering chart on `(anchor, anchor + 1)`, with inverse the representative map. -/
def logChart (y : UnitAddCircle) : OpenPartialHomeomorph ℝ UnitAddCircle :=
  AddCircle.openPartialHomeomorphCoe (1 : ℝ) (anchor y)

lemma mem_chart_target (y : UnitAddCircle) : y ∈ (logChart y).target := by
  rw [logChart, AddCircle.openPartialHomeomorphCoe_target]
  exact y_ne_anchor y

lemma rep_mem_source (y : UnitAddCircle) : rep y ∈ (logChart y).source := by
  rw [logChart, AddCircle.openPartialHomeomorphCoe_source]
  exact rep_mem_Ioo y

/-! ## Local logarithms -/

/-- The open set of points of `U` whose value lies in the chart about `g x`. -/
def logNbhd {U : Opens circleSpace} (g : (toTopCat circleSpace).obj U ⟶ circleSpace)
    (x : (toTopCat circleSpace).obj U) : Opens circleSpace :=
  ⟨Subtype.val '' (⇑g.hom ⁻¹' (logChart (g x)).target),
    (U.2.isOpenEmbedding_subtypeVal).isOpenMap _
      ((logChart (g x)).open_target.preimage g.hom.continuous)⟩

lemma logNbhd_le {U : Opens circleSpace} (g : (toTopCat circleSpace).obj U ⟶ circleSpace)
    (x : (toTopCat circleSpace).obj U) : logNbhd g x ≤ U := by
  intro z hz
  dsimp [logNbhd] at hz
  obtain ⟨u, -, rfl⟩ := hz
  exact u.2

lemma logNbhd_mem {U : Opens circleSpace} (g : (toTopCat circleSpace).obj U ⟶ circleSpace)
    (x : ↑circleSpace) (hx : x ∈ U) : x ∈ logNbhd g ⟨x, hx⟩ := by
  dsimp [logNbhd]
  exact ⟨⟨x, hx⟩, mem_chart_target (g ⟨x, hx⟩), rfl⟩

lemma logLift_lands {U : Opens circleSpace} (g : (toTopCat circleSpace).obj U ⟶ circleSpace)
    (x : (toTopCat circleSpace).obj U) (z : (toTopCat circleSpace).obj (logNbhd g x)) :
    g ⟨z.1, logNbhd_le g x z.2⟩ ∈ (logChart (g x)).target := by
  have hz := z.2
  unfold logNbhd at hz
  rw [Opens.mem_mk, Set.mem_image] at hz
  obtain ⟨u, hu, huz⟩ := hz
  have hzu : (⟨z.1, logNbhd_le g x z.2⟩ : (toTopCat circleSpace).obj U) = u :=
    Subtype.ext huz.symm
  rw [hzu]
  exact hu

/-- The logarithm of `g` on `logNbhd g x`, through the chart about `g x`. -/
def logLift {U : Opens circleSpace} (g : (toTopCat circleSpace).obj U ⟶ circleSpace)
    (x : (toTopCat circleSpace).obj U) :
    (toTopCat circleSpace).obj (logNbhd g x) ⟶ lineSpace :=
  TopCat.ofHom ⟨fun z => (logChart (g x)).symm (g ⟨z.1, logNbhd_le g x z.2⟩), by
    have incl_cont : Continuous (fun z : (toTopCat circleSpace).obj (logNbhd g x) =>
        (⟨z.1, logNbhd_le g x z.2⟩ : (toTopCat circleSpace).obj U)) :=
      Continuous.subtype_mk continuous_subtype_val fun z => logNbhd_le g x z.2
    have gcont : Continuous (fun z : (toTopCat circleSpace).obj (logNbhd g x) =>
        g ⟨z.1, logNbhd_le g x z.2⟩) :=
      g.hom.continuous.comp incl_cont
    exact (logChart (g x)).continuousOn_symm.comp_continuous gcont fun z =>
      logLift_lands g x z⟩

lemma logLift_apply {U : Opens circleSpace} (g : (toTopCat circleSpace).obj U ⟶ circleSpace)
    (x : (toTopCat circleSpace).obj U) (z : (toTopCat circleSpace).obj (logNbhd g x)) :
    logLift g x z = (logChart (g x)).symm (g ⟨z.1, logNbhd_le g x z.2⟩) := by
  simp [logLift]

lemma logLift_spec {U : Opens circleSpace} (g : (toTopCat circleSpace).obj U ⟶ circleSpace)
    (x : (toTopCat circleSpace).obj U) :
    logLift g x ≫ circleArrow =
      circleSheaf.obj.map (homOfLE (logNbhd_le g x)).op g := by
  apply TopCat.ext
  intro z
  have hpoint : ((toTopCat circleSpace).map (homOfLE (logNbhd_le g x))) z =
      ⟨z.1, logNbhd_le g x z.2⟩ := by
    refine Subtype.ext ?_
    rw [show z = ⟨z.1, z.2⟩ from rfl, Opens.toTopCat_map]
  have hchart : circleArrow (logLift g x z) =
      g (((toTopCat circleSpace).map (homOfLE (logNbhd_le g x))) z) := by
    rw [logLift_apply, circleArrow_apply, hpoint]
    exact (logChart (g x)).right_inv (logLift_lands g x z)
  rw [circleSheaf_restrict, TopCat.comp_app, TopCat.comp_app]
  exact hchart

/-- Every circle-valued section is locally a value of the exponential. -/
theorem exp_isLocallySurjective :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology circleSpace) expHom.hom where
  imageSieve_mem {U} s := by
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    let xU : (toTopCat circleSpace).obj U := ⟨x, hx⟩
    refine ⟨logNbhd s xU, homOfLE (logNbhd_le s xU), ?_, logNbhd_mem s x hx⟩
    refine ⟨logLift s xU, ?_⟩
    rw [exp_app]
    exact logLift_spec s xU

/-- The exponential is an epimorphism of sheaves of sets. -/
theorem exp_epi : Epi expHom := by
  let _ : Sheaf.IsLocallySurjective expHom := exp_isLocallySurjective
  exact Sheaf.epi_of_isLocallySurjective' expHom

/-- The identity has a logarithm on a neighbourhood of every point. -/
theorem identity_has_local_logarithm (y : UnitAddCircle) :
    ∃ (V : Opens circleSpace) (_ : y ∈ V) (s : realSheaf.obj.obj (op V)),
      expHom.hom.app (op V) s =
        circleSheaf.obj.map (homOfLE (le_top : V ≤ ⊤)).op identitySection := by
  let x : (toTopCat circleSpace).obj ⊤ := ⟨y, trivial⟩
  refine ⟨logNbhd identitySection x, logNbhd_mem identitySection y trivial,
    logLift identitySection x, ?_⟩
  rw [exp_app]
  exact logLift_spec identitySection x

/-! ## No global logarithm -/

section Loop

open unitInterval

/-- The standard loop `t ↦ t`, from `0` back to `0` on the circle. -/
def standardLoop : C(I, UnitAddCircle) where
  toFun t := (t : ℝ)
  continuous_toFun := (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val

lemma standardLoop_zero : standardLoop 0 = 0 := by
  change (((0 : I) : ℝ) : UnitAddCircle) = 0
  rw [Set.Icc.coe_zero, AddCircle.coe_zero]

lemma standardLoop_one : standardLoop 1 = 0 := by
  change (((1 : I) : ℝ) : UnitAddCircle) = 0
  rw [Set.Icc.coe_one, AddCircle.coe_period]

/-- The identity `UnitAddCircle → UnitAddCircle` has no continuous logarithm. -/
theorem no_continuous_logarithm :
    ¬ ∃ t : realSheaf.obj.obj (op ⊤), expHom.hom.app (op ⊤) t = identitySection := by
  intro ⟨t, ht⟩
  let tHom : (toTopCat circleSpace).obj ⊤ ⟶ lineSpace := t
  have ht' : tHom ≫ circleArrow = identitySection := by
    rw [exp_app] at ht
    exact ht
  let logSection : C(UnitAddCircle, ℝ) :=
    ⟨fun y => tHom ((inclusionTopIso circleSpace).inv y),
      (map_continuous tHom.hom).comp
        (map_continuous (inclusionTopIso circleSpace).inv.hom)⟩
  have logSection_spec : ∀ y, ((logSection y : ℝ) : UnitAddCircle) = y := by
    intro y
    unfold logSection
    rw [ContinuousMap.coe_mk]
    have hcomp : (inclusionTopIso circleSpace).inv ≫ tHom ≫ circleArrow = 𝟙 circleSpace := by
      rw [ht', identitySection]
      exact (inclusionTopIso circleSpace).inv_hom_id
    have happ := ConcreteCategory.congr_hom hcomp y
    rw [TopCat.comp_app, TopCat.comp_app, TopCat.id_app, circleArrow_apply] at happ
    exact happ
  let e : ℝ := logSection 0
  have e_zero : (e : UnitAddCircle) = 0 := logSection_spec 0
  let cov : IsCoveringMap ((↑) : ℝ → UnitAddCircle) := AddCircle.isCoveringMap_coe (1 : ℝ)
  have hstart : standardLoop 0 = (e : UnitAddCircle) := by
    rw [standardLoop_zero, e_zero]
  let Γ : C(I, ℝ) :=
    ⟨fun s => e + (s : ℝ), continuous_const.add continuous_subtype_val⟩
  have Γ_lifts : ((↑) : ℝ → UnitAddCircle) ∘ (Γ : I → ℝ) = (standardLoop : I → UnitAddCircle) := by
    funext s
    rw [Function.comp_apply]
    unfold Γ standardLoop
    rw [ContinuousMap.coe_mk, ContinuousMap.coe_mk, AddCircle.coe_add, e_zero, zero_add]
  have Γ_zero : Γ 0 = e := by
    unfold Γ
    rw [ContinuousMap.coe_mk, Set.Icc.coe_zero, add_zero]
  have Γ_eq : Γ = cov.liftPath standardLoop e hstart :=
    (cov.eq_liftPath_iff' (γ := standardLoop) (e := e) hstart).mpr ⟨Γ_lifts, Γ_zero⟩
  let Λ : C(I, ℝ) :=
    ⟨fun s => logSection (standardLoop s),
      (map_continuous logSection).comp (map_continuous standardLoop)⟩
  have Λ_lifts : ((↑) : ℝ → UnitAddCircle) ∘ (Λ : I → ℝ) = (standardLoop : I → UnitAddCircle) := by
    funext s
    unfold Λ
    rw [ContinuousMap.coe_mk]
    exact logSection_spec (standardLoop s)
  have Λ_zero : Λ 0 = e := by
    unfold Λ
    rw [ContinuousMap.coe_mk, standardLoop_zero]
  have Λ_eq : Λ = cov.liftPath standardLoop e hstart :=
    (cov.eq_liftPath_iff' (γ := standardLoop) (e := e) hstart).mpr ⟨Λ_lifts, Λ_zero⟩
  have Λ_one : Λ 1 = e := by
    unfold Λ
    rw [ContinuousMap.coe_mk, standardLoop_one]
  have Γ_one : Γ 1 = e + 1 := by
    unfold Γ
    rw [ContinuousMap.coe_mk, Set.Icc.coe_one]
  have sameEnd : Λ 1 = Γ 1 := by
    rw [Λ_eq, Γ_eq]
  have ends : e = e + 1 := (Λ_one.symm.trans sameEnd).trans Γ_one
  have : e + 0 = e + 1 := by
    rw [add_zero]
    exact ends
  exact zero_ne_one (add_left_cancel this)

end Loop

/-- The exponential is not surjective on global sections. -/
theorem exp_not_sectionwise_at_top :
    ¬ Function.Surjective (expHom.hom.app (op ⊤)) := by
  intro h
  obtain ⟨t, ht⟩ := h identitySection
  exact no_continuous_logarithm ⟨t, ht⟩

/-! ## The zero map is not an epimorphism -/

lemma zeroArrow_comp_zeroEndArrow : zeroArrow ≫ zeroEndArrow = zeroArrow := by
  apply TopCat.ext
  intro y
  rw [TopCat.comp_app]
  rfl

lemma zeroNat_comp_zeroEndNat : zeroNat ≫ zeroEndNat = zeroNat := by
  unfold zeroNat zeroEndNat
  rw [← whiskerLeft_comp, ← Functor.map_comp, zeroArrow_comp_zeroEndArrow]

lemma zeroHom_comp_zeroEnd : zeroHom ≫ zeroEnd = zeroHom := by
  apply ObjectProperty.hom_ext
  rw [ObjectProperty.FullSubcategory.comp_hom]
  exact zeroNat_comp_zeroEndNat

lemma zeroEnd_ne_id : zeroEnd ≠ 𝟙 circleSheaf := by
  intro h
  have hhom : zeroEnd.hom = 𝟙 circleSheaf.obj := by
    have h1 : zeroEnd.hom = InducedCategory.Hom.hom (𝟙 circleSheaf) :=
      congrArg InducedCategory.Hom.hom h
    rw [ObjectProperty.FullSubcategory.id_hom] at h1
    exact h1
  have happ : zeroEnd.hom.app (op ⊤) identitySection = identitySection := by
    have h2 := congrArg
      (fun α : circleSheaf.obj ⟶ circleSheaf.obj => α.app (op ⊤) identitySection) hhom
    rw [NatTrans.id_app, CategoryTheory.id_apply] at h2
    exact h2
  have hL : zeroEnd.hom.app (op ⊤) identitySection = identitySection ≫ zeroEndArrow :=
    zeroEnd_app identitySection
  have hpt := ConcreteCategory.congr_hom (hL.symm.trans happ)
    ⟨((2⁻¹ : ℝ) : UnitAddCircle), trivial⟩
  rw [TopCat.comp_app, zeroEndArrow, TopCat.ofHom_apply, identitySection_apply] at hpt
  exact half_ne_zero hpt.symm

/-- The zero map is not an epimorphism: cancelling it would identify the identity of `C`
with the constant endomorphism at `0`. -/
theorem zero_not_epi : ¬ Epi zeroHom := by
  intro hEpi
  have hcomp : zeroHom ≫ zeroEnd = zeroHom ≫ 𝟙 circleSheaf := by
    rw [zeroHom_comp_zeroEnd, Category.comp_id]
  exact zeroEnd_ne_id (hEpi.left_cancellation zeroEnd (𝟙 circleSheaf) hcomp)

lemma zero_misses_identity {V : Opens circleSpace}
    (hV : ((2⁻¹ : ℝ) : UnitAddCircle) ∈ V) (s : realSheaf.obj.obj (op V)) :
    zeroHom.hom.app (op V) s ≠
      circleSheaf.obj.map (homOfLE (le_top : V ≤ ⊤)).op identitySection := by
  intro hs
  let sHom : (toTopCat circleSpace).obj V ⟶ lineSpace := s
  have hs' : sHom ≫ zeroArrow =
      (toTopCat circleSpace).map (homOfLE (le_top : V ≤ ⊤)) ≫ identitySection := by
    rw [← zero_app, ← circleSheaf_restrict]
    exact hs
  have hpt := ConcreteCategory.congr_hom hs' ⟨((2⁻¹ : ℝ) : UnitAddCircle), hV⟩
  rw [TopCat.comp_app, TopCat.comp_app, zeroArrow_apply, Opens.toTopCat_map,
    identitySection_apply] at hpt
  exact half_ne_zero hpt.symm

/-! ## The two readings do not factor -/

/-- Surjective on the sections over every open set. -/
def sectionwiseSurjective (f : realSheaf ⟶ circleSheaf) : Prop :=
  ∀ U : Opens circleSpace, Function.Surjective (f.hom.app (op U))

theorem exp_not_sectionwiseSurjective : ¬ sectionwiseSurjective expHom := by
  intro h
  exact exp_not_sectionwise_at_top (h ⊤)

theorem zero_not_sectionwiseSurjective : ¬ sectionwiseSurjective zeroHom := by
  intro h
  obtain ⟨s, hs⟩ := h ⊤ identitySection
  have hrest : circleSheaf.obj.map (homOfLE (le_top : (⊤ : Opens circleSpace) ≤ ⊤)).op
      identitySection = identitySection := by
    rw [circleSheaf_restrict]
    have : homOfLE (le_top : (⊤ : Opens circleSpace) ≤ ⊤) = 𝟙 _ := Subsingleton.elim _ _
    rw [this, CategoryTheory.Functor.map_id, Category.id_comp]
  exact zero_misses_identity (V := ⊤) trivial s (hs.trans hrest.symm)

/-- The exponential is an epimorphism and misses the identity on global sections. -/
theorem exp_epi_not_globalSection :
    Epi expHom ∧ ¬ ∃ t, expHom.hom.app (op ⊤) t = identitySection :=
  ⟨exp_epi, no_continuous_logarithm⟩

/-- An epimorphism of sheaves on the circle need not be surjective on every open set. -/
theorem epi_does_not_imply_sectionwiseSurjective :
    ∃ f : realSheaf ⟶ circleSheaf, Epi f ∧ ¬ sectionwiseSurjective f :=
  ⟨expHom, exp_epi, exp_not_sectionwiseSurjective⟩

/-- The sectionwise reading does not determine the epimorphism reading.
The exponential and the zero map fail to be surjective on every open set, and only the
exponential is an epimorphism. -/
def circleFiber : NonTrivialFiber sectionwiseSurjective (fun f => Epi f) :=
  NonTrivialFiber.ofProp
    (propext (iff_of_false exp_not_sectionwiseSurjective zero_not_sectionwiseSurjective))
    exp_epi zero_not_epi

/-- Surjectivity on every open set does not factor the property of being an epimorphism. -/
theorem pointwise_does_not_factor_epi :
    ¬ Factors sectionwiseSurjective (fun f : realSheaf ⟶ circleSheaf => Epi f) :=
  circleFiber.not_factors

end Circle

end Mettapedia.SetTheory.CarveOuts.Sheaves
