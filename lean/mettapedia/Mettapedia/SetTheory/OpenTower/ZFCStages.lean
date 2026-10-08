import Mettapedia.SetTheory.OpenTower.ExternalTower

/-!
# First-order set theory in the stages, and the union of the ω-tower

The second hosting instance uses an existing first-order derivation system: the Foundation
library's language of set theory `ℒₛₑₜ`, its theories `𝗭`, `𝗭𝗖`, `𝗭𝗙` and `𝗭𝗙𝗖`, its proof
calculus, and its soundness theorem (`consistent_of_model`).

**Closed sets containing `ω` are models of `𝗭𝗙𝗖`.** For a transitive set closed under pairing,
union and power set and containing `ω` (`ZClosed`), the structure of its members is a model of
Zermelo set theory with choice (`zclosed_models_zc`): every Zermelo axiom only needs witnesses
bounded by one member. A closed set containing `ω` is such a set, and replacement adds `𝗭𝗙`
(`closed_models_zfc`). Every stage of the ω-tower after the first is therefore a set model of
`𝗭𝗙𝗖` (`stage_models_zfc`), and so is the image of a whole level one level up
(`image_models_zfc`), hence the level itself (`zfset_models_zfc`, through the elementary
equivalence of `ExternalTower`).

**Consistency, relative to the host.** A set model gives consistency of the exact theory in
Foundation's calculus (`zfc_consistent_of_stage`). This is a host-level theorem about a
derivation system; it is not an arithmetized consistency statement evaluated inside a stage.

**The union of the ω-tower, for a declared fragment.** The union of the ω-tower is not closed
under replacement by host functions (`InternalTower.towerUnion_not_closed`), so it is not a
stage. It is closed under the Zermelo operations, because two members of the union lie in one
stage and each operation stays in the stage of its argument (`towerUnion_zclosed`). So the union
is a model of `𝗭𝗖` (`towerUnion_models_zc`). Whether it satisfies every first-order instance of
`𝗭𝗙` replacement is not settled here.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.OpenTower.ZFCStages

open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure ZFSetHenkinInterpretation ZFSetUniverseLift
open InternalTower ExternalTower
open LO LO.FirstOrder LO.FirstOrder.SetTheory

universe u

/-- The closure that Zermelo set theory with choice needs: no replacement. -/
structure ZClosed (W : ZFSet.{u}) : Prop where
  transitive : ZFSet.IsTransitive W
  pair_mem : ∀ {a b : ZFSet.{u}}, a ∈ W → b ∈ W → ({a, b} : ZFSet.{u}) ∈ W
  union_mem : ∀ {a : ZFSet.{u}}, a ∈ W → ZFSet.sUnion a ∈ W
  power_mem : ∀ {a : ZFSet.{u}}, a ∈ W → ZFSet.powerset a ∈ W
  omega_mem : ZFSet.omega ∈ W

namespace ZClosed

variable {W : ZFSet.{u}} (hW : ZClosed W)
include hW

theorem subset_mem {a b : ZFSet.{u}} (ha : a ∈ W) (hb : b ⊆ a) : b ∈ W :=
  hW.transitive _ (hW.power_mem ha) (ZFSet.mem_powerset.mpr hb)

theorem mem_of_mem {a b : ZFSet.{u}} (ha : a ∈ W) (hb : b ∈ a) : b ∈ W :=
  hW.transitive _ ha hb

theorem empty_mem : (∅ : ZFSet.{u}) ∈ W :=
  hW.subset_mem hW.omega_mem (ZFSet.empty_subset _)

theorem nonempty : Nonempty (Members W) := ⟨⟨∅, hW.empty_mem⟩⟩

theorem insert_mem {a b : ZFSet.{u}} (ha : a ∈ W) (hb : b ∈ W) : insert a b ∈ W := by
  have singleton : ({a} : ZFSet.{u}) ∈ W := by
    have member := hW.pair_mem ha ha
    rwa [ZFSet.pair_eq_singleton] at member
  have hunion := hW.union_mem (hW.pair_mem singleton hb)
  have heq : ZFSet.sUnion {{a}, b} = insert a b := by
    apply ZFSet.ext
    intro y
    rw [ZFSet.mem_sUnion, ZFSet.mem_insert_iff]
    constructor
    · rintro ⟨z, hz, hy⟩
      rcases ZFSet.mem_pair.mp hz with rfl | rfl
      · exact Or.inl (ZFSet.mem_singleton.mp hy)
      · exact Or.inr hy
    · rintro (rfl | hy)
      · exact ⟨{y}, ZFSet.mem_pair.mpr (Or.inl rfl), ZFSet.mem_singleton.mpr rfl⟩
      · exact ⟨b, ZFSet.mem_pair.mpr (Or.inr rfl), hy⟩
  rwa [heq] at hunion

end ZClosed

/-- A closed set containing `ω` has the Zermelo closure. -/
theorem zclosed_of_closed {U : ZFSet.{u}} (hU : Closed U) (hω : ZFSet.omega ∈ U) :
    ZClosed U where
  transitive := hU.transitive
  pair_mem ha hb := hU.unorderedPair_mem ha hb
  union_mem ha := hU.union_mem ha
  power_mem ha := hU.power_mem ha
  omega_mem := hω

/-! ## Zermelo set theory with choice -/

theorem members_eq_iff {W : ZFSet.{u}} {x y : Members W} : x = y ↔ x.1 = y.1 :=
  ⟨congrArg Subtype.val, Subtype.ext⟩

section Zermelo

variable {W : ZFSet.{u}} (hW : ZClosed W) [Nonempty (Members W)]
include hW

/-- The member of `W` given by a set in `W`. -/
abbrev member (x : ZFSet.{u}) (hx : x ∈ W) : Members W := ⟨x, hx⟩

theorem models_empty : Members W ⊧ₘ Axiom.empty := by
  simp [models_iff, Axiom.empty]
  exact ⟨member ∅ hW.empty_mem, fun y => ZFSet.notMem_empty _⟩

theorem models_extentionality : Members W ⊧ₘ Axiom.extentionality := by
  simp [models_iff, Axiom.extentionality]
  intro a b
  constructor
  · rintro rfl
    exact fun _ => Iff.rfl
  · intro h
    apply Subtype.ext
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      exact (h (member z (hW.mem_of_mem a.2 hz))).mp hz
    · intro hz
      exact (h (member z (hW.mem_of_mem b.2 hz))).mpr hz

theorem models_pairing : Members W ⊧ₘ Axiom.pairing := by
  simp [models_iff, Axiom.pairing]
  intro a b
  refine ⟨member {a.1, b.1} (hW.pair_mem a.2 b.2), fun z => ?_⟩
  change z.1 ∈ ({a.1, b.1} : ZFSet.{u}) ↔ z = a ∨ z = b
  rw [ZFSet.mem_pair, members_eq_iff, members_eq_iff]

theorem models_union : Members W ⊧ₘ Axiom.union := by
  simp [models_iff, Axiom.union]
  intro a
  refine ⟨member (ZFSet.sUnion a.1) (hW.union_mem a.2), fun z => ?_⟩
  change z.1 ∈ ZFSet.sUnion a.1 ↔ ∃ y : Members W, y.1 ∈ a.1 ∧ z.1 ∈ y.1
  rw [ZFSet.mem_sUnion]
  constructor
  · rintro ⟨y, hya, hzy⟩
    exact ⟨member y (hW.mem_of_mem a.2 hya), hya, hzy⟩
  · rintro ⟨y, hya, hzy⟩
    exact ⟨y.1, hya, hzy⟩

theorem models_power : Members W ⊧ₘ Axiom.power := by
  simp [models_iff, Axiom.power, SetTheory.subset_def]
  intro a
  refine ⟨member (ZFSet.powerset a.1) (hW.power_mem a.2), fun z => ?_⟩
  change z.1 ∈ ZFSet.powerset a.1 ↔ ∀ y : Members W, y.1 ∈ z.1 → y.1 ∈ a.1
  rw [ZFSet.mem_powerset]
  constructor
  · intro hza y hy
    exact hza hy
  · intro h y hy
    exact h (member y (hW.mem_of_mem z.2 hy)) hy

theorem models_infinity : Members W ⊧ₘ Axiom.infinity := by
  simp [models_iff, Axiom.infinity, val_isSucc_iff, SetTheory.IsEmpty]
  refine ⟨member ZFSet.omega hW.omega_mem, ?_, ?_⟩
  · intro e hempty
    change e.1 ∈ ZFSet.omega
    have : e.1 = ∅ := by
      apply ZFSet.ext
      intro z
      constructor
      · intro hz
        exact absurd hz (hempty (member z (hW.mem_of_mem e.2 hz)))
      · intro hz
        exact absurd hz (ZFSet.notMem_empty z)
    rw [this]
    exact ZFSet.omega_zero
  · intro x hxω y hsucc
    change x.1 ∈ ZFSet.omega at hxω
    change y.1 ∈ ZFSet.omega
    have : y.1 = insert x.1 x.1 := by
      apply ZFSet.ext
      intro z
      rw [ZFSet.mem_insert_iff]
      constructor
      · intro hz
        have := (hsucc (member z (hW.mem_of_mem y.2 hz))).mp hz
        rcases this with same | hz'
        · exact Or.inl (congrArg Subtype.val same)
        · exact Or.inr hz'
      · intro hz
        have hzW : z ∈ W := by
          rcases hz with rfl | hz
          · exact x.2
          · exact hW.mem_of_mem x.2 hz
        refine (hsucc (member z hzW)).mpr ?_
        rcases hz with rfl | hz
        · exact Or.inl rfl
        · exact Or.inr hz
    rw [this]
    exact ZFSet.omega_succ hxω

theorem models_foundation : Members W ⊧ₘ Axiom.foundation := by
  simp [models_iff, Axiom.foundation, isNonempty_def]
  intro a z hza
  obtain ⟨y, hy, hmin⟩ := ZFSet.mem_wf.has_min {w | w ∈ a.1} ⟨z.1, hza⟩
  exact ⟨member y (hW.mem_of_mem a.2 hy), hy, fun w hwa hwy => hmin w.1 hwa hwy⟩

theorem models_separation (φ : SyntacticSemiformula ℒₛₑₜ 1) :
    Members W ⊧ₘ Axiom.separationSchema φ := by
  let P (f : ℕ → Members W) (x : Members W) : Prop :=
    Semiformula.Eval (standardStructure (Members W)) ![x] f φ
  suffices ∀ (f : ℕ → Members W) (x : Members W), ∃ y : Members W,
      ∀ z : Members W, z ∈ y ↔ z ∈ x ∧ P f z by
    simpa [models_iff, Axiom.separationSchema, Matrix.constant_eq_singleton, P]
  intro f x
  refine ⟨member (ZFSet.sep (fun z => ∃ hz : z ∈ W, P f ⟨z, hz⟩) x.1)
    (hW.subset_mem x.2 ZFSet.sep_subset), fun z => ?_⟩
  change z.1 ∈ ZFSet.sep (fun z => ∃ hz : z ∈ W, P f ⟨z, hz⟩) x.1 ↔ z.1 ∈ x.1 ∧ P f z
  rw [ZFSet.mem_sep]
  constructor
  · rintro ⟨hzx, _, hp⟩
    exact ⟨hzx, hp⟩
  · rintro ⟨hzx, hp⟩
    exact ⟨hzx, z.2, hp⟩

theorem models_choice : Members W ⊧ₘ Axiom.choice := by
  classical
  simp [models_iff, Axiom.choice, isNonempty_def]
  intro 𝓧 nonempty disjoint
  let pick : ZFSet.{u} → ZFSet.{u} := fun X =>
    if hX : ∃ x, x ∈ X then Classical.choose hX else ∅
  have pick_mem : ∀ X : Members W, X.1 ∈ 𝓧.1 → pick X.1 ∈ X.1 := by
    intro X hX
    obtain ⟨x, hx⟩ := nonempty X hX
    have exists_member : ∃ x, x ∈ X.1 := ⟨x.1, hx⟩
    simp only [pick, dif_pos exists_member]
    exact Classical.choose_spec exists_member
  let C : ZFSet.{u} := ZFSet.sep (fun x => ∃ X : Members W, X.1 ∈ 𝓧.1 ∧ pick X.1 = x)
    (ZFSet.sUnion 𝓧.1)
  have hC : C ∈ W := hW.subset_mem (hW.union_mem 𝓧.2) ZFSet.sep_subset
  refine ⟨member C hC, fun X hX => ?_⟩
  refine ExistsUnique.intro (member (pick X.1) (hW.mem_of_mem X.2 (pick_mem X hX)))
    ⟨?_, pick_mem X hX⟩ ?_
  · change pick X.1 ∈ C
    exact ZFSet.mem_sep.mpr ⟨ZFSet.mem_sUnion.mpr ⟨X.1, hX, pick_mem X hX⟩, X, hX, rfl⟩
  · rintro y ⟨hyC, hyX⟩
    change y.1 ∈ C at hyC
    obtain ⟨_, Y, hY, hYy⟩ := ZFSet.mem_sep.mp hyC
    have same : Y = X := disjoint Y hY X hX y (hYy ▸ pick_mem Y hY) hyX
    apply Subtype.ext
    rw [← hYy, same]

/-- **Zermelo set theory holds in every Zermelo-closed set.** -/
theorem zclosed_models_z : Members W ⊧ₘ* 𝗭 where
  models_set φ hφ := by
    rcases hφ
    case axiom_of_equality h =>
      have : Members W ⊧ₘ* (𝗘𝗤 : Theory ℒₛₑₜ) := inferInstance
      exact modelsTheory_iff.mp this h
    case axiom_of_empty_set => exact models_empty hW
    case axiom_of_extentionality => exact models_extentionality hW
    case axiom_of_pairing => exact models_pairing hW
    case axiom_of_union => exact models_union hW
    case axiom_of_power_set => exact models_power hW
    case axiom_of_infinity => exact models_infinity hW
    case axiom_of_foundation => exact models_foundation hW
    case axiom_of_separation φ => exact models_separation hW φ

theorem zclosed_models_ac : Members W ⊧ₘ* 𝗔𝗖 where
  models_set φ hφ := by
    rcases hφ
    exact models_choice hW

/-- **Zermelo set theory with choice holds in every Zermelo-closed set.** -/
theorem zclosed_models_zc : Members W ⊧ₘ* 𝗭𝗖 := by
  have := zclosed_models_z hW
  have := zclosed_models_ac hW
  infer_instance

end Zermelo

/-! ## Replacement in closed sets -/

section Replacement

variable {U : ZFSet.{u}} (hU : Closed U) [Nonempty (Members U)]
include hU

theorem models_replacement (φ : SyntacticSemiformula ℒₛₑₜ 2) :
    Members U ⊧ₘ Axiom.replacementSchema φ := by
  classical
  let R (f : ℕ → Members U) (x y : Members U) : Prop :=
    Semiformula.Eval (standardStructure (Members U)) ![x, y] f φ
  suffices ∀ f : ℕ → Members U, (∀ x, ∃! y, R f x y) →
      ∀ X : Members U, ∃ Y : Members U, ∀ y, y ∈ Y ↔ ∃ x ∈ X, R f x y by
    simpa [models_iff, Axiom.replacementSchema, Matrix.constant_eq_singleton,
      Matrix.comp_vecCons', R]
  intro f h X
  choose F hF using fun x => (h x).exists
  have hFiff : ∀ x y, R f x y ↔ F x = y :=
    fun x y => ⟨fun hxy => (h x).unique (hF x) hxy, by rintro rfl; exact hF x⟩
  let G : ZFSet.{u} → ZFSet.{u} := fun z => if hz : z ∈ U then (F ⟨z, hz⟩).1 else ∅
  have hG : ∀ z (hz : z ∈ U), G z = (F ⟨z, hz⟩).1 := by
    intro z hz
    simp only [G, dif_pos hz]
  refine ⟨⟨replacement X.1 G, hU.replacement_mem X.2 G (fun z hz => by
    rw [hG z (hU.transitive _ X.2 hz)]
    exact (F _).2)⟩, fun y => ?_⟩
  change y.1 ∈ replacement X.1 G ↔ ∃ x : Members U, x.1 ∈ X.1 ∧ R f x y
  rw [mem_replacement]
  constructor
  · rintro ⟨z, hzX, hzy⟩
    have hz := hU.transitive _ X.2 hzX
    refine ⟨⟨z, hz⟩, hzX, (hFiff _ _).mpr (Subtype.ext ?_)⟩
    rw [← hzy, hG z hz]
  · rintro ⟨x, hxX, hxy⟩
    refine ⟨x.1, hxX, ?_⟩
    rw [hG x.1 x.2]
    exact congrArg Subtype.val ((hFiff _ _).mp hxy)

/-- **A closed set containing `ω` is a model of `𝗭𝗙`.** -/
theorem closed_models_zf (hω : ZFSet.omega ∈ U) : Members U ⊧ₘ* 𝗭𝗙 where
  models_set φ hφ := by
    have hW := zclosed_of_closed hU hω
    rcases hφ
    case axiom_of_equality h =>
      have : Members U ⊧ₘ* (𝗘𝗤 : Theory ℒₛₑₜ) := inferInstance
      exact modelsTheory_iff.mp this h
    case axiom_of_empty_set => exact models_empty hW
    case axiom_of_extentionality => exact models_extentionality hW
    case axiom_of_pairing => exact models_pairing hW
    case axiom_of_union => exact models_union hW
    case axiom_of_power_set => exact models_power hW
    case axiom_of_infinity => exact models_infinity hW
    case axiom_of_foundation => exact models_foundation hW
    case axiom_of_separation φ => exact models_separation hW φ
    case axiom_of_replacement φ => exact models_replacement hU φ

/-- **A closed set containing `ω` is a model of `𝗭𝗙𝗖`.** -/
theorem closed_models_zfc (hω : ZFSet.omega ∈ U) : Members U ⊧ₘ* 𝗭𝗙𝗖 := by
  have := closed_models_zf hU hω
  have := zclosed_models_ac (zclosed_of_closed hU hω)
  infer_instance

end Replacement

/-! ## The towers -/

instance stage_nonempty (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}) (n : ℕ) :
    Nonempty (Members (stage h N n)) :=
  ⟨⟨∅, empty_mem_stage h N n⟩⟩

/-- **Every stage of the ω-tower after the first is a set model of `𝗭𝗙𝗖`.** -/
theorem stage_models_zfc (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}) (n : ℕ) :
    Members (stage h N (n + 1)) ⊧ₘ* 𝗭𝗙𝗖 :=
  closed_models_zfc (stage_closed h N (n + 1)) (omega_mem_stage_succ h N n)

/-- Consistency of `𝗭𝗙𝗖` in Foundation's calculus, from a set model at a stage. -/
theorem zfc_consistent_of_stage (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}) (n : ℕ) :
    Entailment.Consistent (𝗭𝗙𝗖 : Theory ℒₛₑₜ) := by
  have := stage_models_zfc h N n
  exact consistent_of_model 𝗭𝗙𝗖 (Members (stage h N (n + 1)))

/-- **The image of a level, one level up, is a set model of `𝗭𝗙𝗖`**, with no hypothesis. -/
theorem image_models_zfc : Members carrierCode.{u} ⊧ₘ* 𝗭𝗙𝗖 :=
  closed_models_zfc carrierCode_closed omega_mem_image

/-- Hence the level itself is a model of `𝗭𝗙𝗖`, through the elementary equivalence. -/
theorem zfset_models_zfc : ZFSet.{u} ⊧ₘ* 𝗭𝗙𝗖 :=
  (modelsTheory_iff_image _).mpr image_models_zfc

/-- Consistency of `𝗭𝗙𝗖` from the set `carrierCode` of level one, the image of level zero,
with no hypothesis beyond Lean's own universe rules. -/
theorem zfc_consistent_of_image : Entailment.Consistent (𝗭𝗙𝗖 : Theory ℒₛₑₜ) := by
  have := image_models_zfc.{0}
  exact consistent_of_model 𝗭𝗙𝗖 (Members carrierCode.{0})

/-- **The union of the ω-tower has the Zermelo closure.** Two members of the union lie in one
stage, and every Zermelo operation stays in the stage of its arguments. -/
theorem towerUnion_zclosed (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}) :
    ZClosed (towerUnion h N) where
  transitive x hx y hy := by
    obtain ⟨n, hn⟩ := (mem_towerUnion h N).mp hx
    exact (mem_towerUnion h N).mpr ⟨n, (stage_closed h N n).transitive _ hn hy⟩
  pair_mem ha hb := by
    obtain ⟨m, hm⟩ := (mem_towerUnion h N).mp ha
    obtain ⟨n, hn⟩ := (mem_towerUnion h N).mp hb
    refine (mem_towerUnion h N).mpr ⟨max m n, (stage_closed h N (max m n)).unorderedPair_mem ?_ ?_⟩
    · exact stage_subset_of_le h N (le_max_left m n) hm
    · exact stage_subset_of_le h N (le_max_right m n) hn
  union_mem ha := by
    obtain ⟨n, hn⟩ := (mem_towerUnion h N).mp ha
    exact (mem_towerUnion h N).mpr ⟨n, (stage_closed h N n).union_mem hn⟩
  power_mem ha := by
    obtain ⟨n, hn⟩ := (mem_towerUnion h N).mp ha
    exact (mem_towerUnion h N).mpr ⟨n, (stage_closed h N n).power_mem hn⟩
  omega_mem := (mem_towerUnion h N).mpr ⟨1, omega_mem_stage_succ h N 0⟩

instance towerUnion_nonempty (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}) :
    Nonempty (Members (towerUnion h N)) :=
  (towerUnion_zclosed h N).nonempty

/-- **The union of the ω-tower is a model of `𝗭𝗖`**, although it is not closed under
replacement by host functions (`InternalTower.towerUnion_not_closed`). -/
theorem towerUnion_models_zc (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}) :
    Members (towerUnion h N) ⊧ₘ* 𝗭𝗖 :=
  zclosed_models_zc (towerUnion_zclosed h N)

#print axioms zclosed_models_zc
#print axioms closed_models_zfc
#print axioms stage_models_zfc
#print axioms zfc_consistent_of_stage
#print axioms image_models_zfc
#print axioms zfset_models_zfc
#print axioms zfc_consistent_of_image
#print axioms towerUnion_zclosed
#print axioms towerUnion_models_zc

end Mettapedia.SetTheory.OpenTower.ZFCStages
