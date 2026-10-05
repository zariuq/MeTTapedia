import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.MegalodonHOTG.SetLaws
import Mathlib.SetTheory.ZFC.Ordinal

/-!
# Russell, Kuratowski, Cantor and Burali-Forti in the set model

Closed sentences of the set signature, read by the same embedding as `powerIn` and
`universalSet`. They are consequences of the set model, not further laws of the package, so
they stay beside `MegalodonHOTG.SetLaws`. Signature `eq` on a set is identity, and Leibniz `same`
is identity (`same_iff_eq`), so substitution and the extensionality of `same` are valid here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace MegalodonHOTG
namespace Curriculum

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open ZFSetHenkinInterpretation
open ZFSetUniverseInterpretation (embed)
open ZFSetTraceProofDecoding (mem_truthCode)
open ZFSetUniverseClosure (CofinalInaccessibles)

universe u

/-! ## The carrier -/

/-- A set whose only member is `a`. -/
def IsSingleton (s a : ZFSet.{u}) : Prop := ∀ z, z ∈ s ↔ z = a

/-- A set whose members are exactly `a` and `b`. -/
def IsUPair (u a b : ZFSet.{u}) : Prop := ∀ z, z ∈ u ↔ z = a ∨ z = b

/-- A Kuratowski pair `{{a}, {a, b}}`, stated by membership. -/
def IsKPair (p a b : ZFSet.{u}) : Prop :=
  ∀ z, z ∈ p ↔ IsSingleton z a ∨ IsUPair z a b

/-- A transitive set whose members are transitive sets. -/
def CurriculumOrdinal (a : ZFSet.{u}) : Prop :=
  a.IsTransitive ∧ ∀ b ∈ a, b.IsTransitive

theorem isSingleton_iff {s a : ZFSet.{u}} : IsSingleton s a ↔ s = ({a} : ZFSet.{u}) := by
  constructor
  · intro h
    apply ZFSet.ext
    intro z
    rw [h z, ZFSet.mem_singleton]
  · rintro rfl z
    rw [ZFSet.mem_singleton]

theorem isUPair_iff {u a b : ZFSet.{u}} : IsUPair u a b ↔ u = ({a, b} : ZFSet.{u}) := by
  constructor
  · intro h
    apply ZFSet.ext
    intro z
    rw [h z, ZFSet.mem_pair]
  · rintro rfl z
    rw [ZFSet.mem_pair]

theorem isKPair_iff {p a b : ZFSet.{u}} : IsKPair p a b ↔ p = ZFSet.pair a b := by
  constructor
  · intro h
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      rcases (h z).mp hz with hs | hu
      · rw [ZFSet.pair]
        exact ZFSet.mem_pair.mpr (Or.inl ((isSingleton_iff (s := z) (a := a)).mp hs))
      · rw [ZFSet.pair]
        exact ZFSet.mem_pair.mpr (Or.inr ((isUPair_iff (u := z) (a := a) (b := b)).mp hu))
    · intro hz
      rw [ZFSet.pair, ZFSet.mem_pair] at hz
      rcases hz with hza | hzb
      · exact (h z).mpr (Or.inl ((isSingleton_iff (s := z) (a := a)).mpr hza))
      · exact (h z).mpr (Or.inr ((isUPair_iff (u := z) (a := a) (b := b)).mpr hzb))
  · rintro rfl z
    constructor
    · intro hz
      rw [ZFSet.pair, ZFSet.mem_pair] at hz
      rcases hz with hza | hzb
      · rw [hza]
        exact Or.inl ((isSingleton_iff (s := {a}) (a := a)).mpr rfl)
      · rw [hzb]
        exact Or.inr ((isUPair_iff (u := {a, b}) (a := a) (b := b)).mpr rfl)
    · intro hz
      rw [ZFSet.pair, ZFSet.mem_pair]
      rcases hz with hs | hu
      · exact Or.inl ((isSingleton_iff (s := z) (a := a)).mp hs)
      · exact Or.inr ((isUPair_iff (u := z) (a := a) (b := b)).mp hu)

/-- Equal Kuratowski pairs have equal components, and conversely. -/
theorem kuratowski_characteristic {a b c d : ZFSet.{u}} :
    ZFSet.pair a b = ZFSet.pair c d ↔ a = c ∧ b = d :=
  ZFSet.pair_inj

theorem mem_iff_isKPair {f x y : ZFSet.{u}} :
    ZFSet.pair x y ∈ f ↔ ∃ p, IsKPair p x y ∧ p ∈ f := by
  constructor
  · intro h
    exact ⟨ZFSet.pair x y, (isKPair_iff).mpr rfl, h⟩
  · rintro ⟨p, hp, hmem⟩
    rwa [(isKPair_iff).mp hp] at hmem

/-- Two pairs with the same members, in order, are characterized by the same sets. -/
theorem kuratowski_inj {p a b c d : ZFSet.{u}}
    (hab : IsKPair p a b) (hcd : IsKPair p c d) : a = c ∧ b = d :=
  kuratowski_characteristic.mp (((isKPair_iff).mp hab).symm.trans ((isKPair_iff).mp hcd))

theorem kuratowski_inj_first {p a b c d : ZFSet.{u}}
    (hab : IsKPair p a b) (hcd : IsKPair p c d) : a = c :=
  (kuratowski_inj hab hcd).1

theorem kuratowski_inj_second {p a b c d : ZFSet.{u}}
    (hab : IsKPair p a b) (hcd : IsKPair p c d) : b = d :=
  (kuratowski_inj hab hcd).2

theorem kuratowski_cong {p a b c d : ZFSet.{u}}
    (hab : IsKPair p a b) (hac : a = c) (hbd : b = d) : IsKPair p c d := by
  rw [← hac, ← hbd]
  exact hab

/-- Swapping the components of a Kuratowski pair changes the pair. -/
theorem kuratowski_not_commutative :
    ZFSet.pair (∅ : ZFSet.{u}) ({∅} : ZFSet.{u}) ≠
      ZFSet.pair ({∅} : ZFSet.{u}) (∅ : ZFSet.{u}) := by
  intro h
  exact empty_ne_singleton (kuratowski_characteristic.mp h).1

/-- A relation of pairs relates each member of its domain to one value. -/
def IsFunctional (f : ZFSet.{u}) : Prop :=
  ∀ x y z, ZFSet.pair x y ∈ f → ZFSet.pair x z ∈ f → y = z

/-- Every member of `B` is a value of `f` at a member of `A`. -/
def IsOnto (f A B : ZFSet.{u}) : Prop :=
  ∀ Y ∈ B, ∃ x ∈ A, ZFSet.pair x Y ∈ f

/-- `f` relates every member of `A` to some set. -/
def IsTotal (f A : ZFSet.{u}) : Prop :=
  ∀ x ∈ A, ∃ y, ZFSet.pair x y ∈ f

/-- `f` is a set of pairs from `A` and `B`. -/
def IsRelation (f A B : ZFSet.{u}) : Prop :=
  f ⊆ ZFSet.prod A B

/-- No functional relation maps a set onto its power set. -/
theorem cantor_core {A f : ZFSet.{u}} (functional : IsFunctional f)
    (onto : IsOnto f A (ZFSet.powerset A)) : False := by
  classical
  let D := ZFSet.sep (fun x => ∀ Y, ZFSet.pair x Y ∈ f → x ∉ Y) A
  have hD : D ∈ ZFSet.powerset A := ZFSet.mem_powerset.mpr ZFSet.sep_subset
  obtain ⟨a, haA, haPair⟩ := onto D hD
  have hnin : a ∉ D := fun hin => (ZFSet.mem_sep.mp hin).2 D haPair hin
  have hfail : ¬ ∀ Y, ZFSet.pair a Y ∈ f → a ∉ Y :=
    fun hall => hnin (ZFSet.mem_sep.mpr ⟨haA, hall⟩)
  obtain ⟨Y, hY⟩ := Classical.not_forall.mp hfail
  obtain ⟨hYf, hnot⟩ := Classical.not_imp.mp hY
  exact hnin ((functional a Y D hYf haPair) ▸ Classical.not_not.mp hnot)

/-- No surjection from a set onto its power set. The product bound and totality are the
curriculum's function; the contradiction is the diagonal of functionality and surjectivity. -/
theorem cantor {A f : ZFSet.{u}} (_rel : IsRelation f A (ZFSet.powerset A))
    (functional : IsFunctional f) (_total : IsTotal f A)
    (onto : IsOnto f A (ZFSet.powerset A)) : False :=
  cantor_core functional onto

/-- No function of sets maps a set onto its power set. -/
theorem cantor_fn {A : ZFSet.{u}} (F : ZFSet.{u} → ZFSet.{u}) :
    ¬ ∀ Y ∈ ZFSet.powerset A, ∃ x ∈ A, F x = Y := by
  intro surj
  let D := ZFSet.sep (fun x => x ∉ F x) A
  have hD : D ∈ ZFSet.powerset A := ZFSet.mem_powerset.mpr ZFSet.sep_subset
  obtain ⟨x, hxA, hx⟩ := surj D hD
  have hnin : x ∉ D := fun hin => (ZFSet.mem_sep.mp hin).2 (hx ▸ hin)
  exact hnin (ZFSet.mem_sep.mpr ⟨hxA, hx ▸ hnin⟩)

/-- The identity at a member of `A` is a member of `A` equal to it. -/
theorem identity_onto_self {A Y : ZFSet.{u}} (hY : Y ∈ A) : ∃ x ∈ A, x = Y :=
  ⟨Y, hY, rfl⟩

/-- The identity does not map a set onto its power set. -/
theorem identity_not_onto_power :
    ¬ ∀ (A Y : ZFSet.{u}), Y ∈ ZFSet.powerset A → ∃ x ∈ A, x = Y := by
  intro h
  obtain ⟨x, hx, _⟩ := h ∅ ∅
    (ZFSet.mem_powerset.mpr fun _ hm => (ZFSet.notMem_empty _ hm).elim)
  exact ZFSet.notMem_empty x hx

/-- The curriculum ordinal is Mathlib's ordinal. The two directions are the definition
`ZFSet.isOrdinal_iff_forall_mem_isTransitive`. -/
theorem curriculumOrdinal_iff_isOrdinal {a : ZFSet.{u}} :
    CurriculumOrdinal a ↔ a.IsOrdinal :=
  (ZFSet.isOrdinal_iff_forall_mem_isTransitive).symm

/-- An ordinal is well-ordered by membership. Well-foundedness is `ZFSet.mem_wf`. -/
theorem curriculumOrdinal_isWellOrder {a : ZFSet.{u}} (h : CurriculumOrdinal a) :
    IsWellOrder _ (Subrel (· ∈ ·) (· ∈ a)) :=
  ((curriculumOrdinal_iff_isOrdinal (a := a)).mp h).isWellOrder

/-- There is no set whose members are exactly the ordinals. Such a set would be an ordinal
and a member of itself, contradicting `ZFSet.mem_irrefl`. -/
theorem burali_forti : ¬ ∃ O : ZFSet.{u}, ∀ x, x ∈ O ↔ CurriculumOrdinal x := by
  rintro ⟨O, hO⟩
  have htrans : O.IsTransitive := by
    intro x hx y hy
    have hxOrd := (hO x).mp hx
    have hyOrd : CurriculumOrdinal y :=
      ⟨hxOrd.2 y hy, fun c hc => hxOrd.2 c ((hxOrd.1 y hy) hc)⟩
    exact (hO y).mpr hyOrd
  have hOord : CurriculumOrdinal O := ⟨htrans, fun b hb => ((hO b).mp hb).1⟩
  exact ZFSet.mem_irrefl O ((hO O).mpr hOord)

/-- Leibniz equality of sets is identity. -/
theorem same_iff_eq {x y : ZFSet.{u}} :
    (∀ P : ZFSet.{u} → ULift.{u + 1} Prop, (P x).down → (P y).down) ↔ x = y := by
  constructor
  · intro h
    exact (h (fun z => .up (z = x)) rfl).symm
  · rintro rfl _ hx
    exact hx

/-- Leibniz equality in a full domain, where the quantifier admits every predicate. -/
theorem same_adm_iff_eq {x y : ZFSet.{u}} :
    (∀ P : ZFSet.{u} → ULift.{u + 1} Prop, True → (P x).down → (P y).down) ↔ x = y := by
  rw [← same_iff_eq]
  constructor
  · intro h P hx
    exact h P trivial hx
  · intro h P _ hx
    exact h P hx

/-! ## The terms built from the choice operator

`pick`, `both`, `UPair`, `Sing`, `kpair`, `binunion`, `prod`, `dom`, `ran`,
`id-rel` and `succ` are the curriculum's terms. `same` is identity here
(`same_iff_eq`). `Sing` separates from a power set and does not use choice. -/

/-- `Sing a`, separated from the power set by identity. -/
noncomputable def singSet (a : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun w => w = a) (ZFSet.powerset a)

theorem sing_intro (a : ZFSet.{u}) : a ∈ singSet a := by
  refine ZFSet.mem_sep.mpr ⟨ZFSet.mem_powerset.mpr fun _ hz => hz, rfl⟩

theorem sing_elim {a z : ZFSet.{u}} (h : z ∈ singSet a) : z = a :=
  (ZFSet.mem_sep.mp h).2

theorem sing_inj {a c : ZFSet.{u}} (h : singSet a = singSet c) : a = c :=
  sing_elim (h ▸ sing_intro a)

theorem singSet_eq (a : ZFSet.{u}) : singSet a = ({a} : ZFSet.{u}) := by
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_singleton]
  constructor
  · intro hz
    exact sing_elim hz
  · intro hz
    rw [hz]
    exact sing_intro a

/-- `pick a b X`: `a` when the empty set belongs to `X`, and `b` otherwise. -/
noncomputable def pickSet (a b X : ZFSet.{u}) : ZFSet.{u} :=
  epsilonSet fun w => .up ((∅ ∈ X → w = a) ∧ (¬ ∅ ∈ X → w = b))

theorem pick_yes {a b X : ZFSet.{u}} (hX : (∅ : ZFSet.{u}) ∈ X) : pickSet a b X = a := by
  have hspec := epsilonSet_spec
    (fun w => .up ((∅ ∈ X → w = a) ∧ (¬ ∅ ∈ X → w = b))) (x := a)
    ⟨fun _ => rfl, fun hn => (hn hX).elim⟩
  exact hspec.1 hX

theorem pick_no {a b X : ZFSet.{u}} (hX : (∅ : ZFSet.{u}) ∉ X) : pickSet a b X = b := by
  have hspec := epsilonSet_spec
    (fun w => .up ((∅ ∈ X → w = a) ∧ (¬ ∅ ∈ X → w = b))) (x := b)
    ⟨fun h => (hX h).elim, fun _ => rfl⟩
  exact hspec.2 hX

/-- `both a b`, the replacement of `pick` over the power set of the power set of the empty set. -/
noncomputable def bothSet (a b : ZFSet.{u}) : ZFSet.{u} :=
  replacement (ZFSet.powerset (ZFSet.powerset ∅)) (pickSet a b)

theorem both_left (a b : ZFSet.{u}) : a ∈ bothSet a b := by
  refine mem_replacement.mpr ⟨ZFSet.powerset ∅, ?_, ?_⟩
  · exact ZFSet.mem_powerset.mpr fun _ hz => hz
  · exact pick_yes (ZFSet.mem_powerset.mpr (ZFSet.empty_subset _))

theorem both_right (a b : ZFSet.{u}) : b ∈ bothSet a b := by
  refine mem_replacement.mpr ⟨∅, ?_, pick_no (ZFSet.notMem_empty _)⟩
  exact ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)

/-- `UPair a b`, the members of `both a b` that are `a` or `b`. -/
noncomputable def upairSet (a b : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun w => w = a ∨ w = b) (bothSet a b)

theorem upair_left (a b : ZFSet.{u}) : a ∈ upairSet a b :=
  ZFSet.mem_sep.mpr ⟨both_left a b, Or.inl rfl⟩

theorem upair_right (a b : ZFSet.{u}) : b ∈ upairSet a b :=
  ZFSet.mem_sep.mpr ⟨both_right a b, Or.inr rfl⟩

theorem upair_elim {a b z : ZFSet.{u}} (h : z ∈ upairSet a b) : z = a ∨ z = b :=
  (ZFSet.mem_sep.mp h).2

theorem upairSet_eq (a b : ZFSet.{u}) : upairSet a b = ({a, b} : ZFSet.{u}) := by
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_pair]
  constructor
  · intro hz
    exact upair_elim hz
  · intro h
    rcases h with hza | hzb
    · rw [hza]
      exact upair_left a b
    · rw [hzb]
      exact upair_right a b

theorem upair_sing {a b c : ZFSet.{u}} (h : upairSet a b = singSet c) : a = c ∧ b = c :=
  ⟨sing_elim (h ▸ upair_left a b), sing_elim (h ▸ upair_right a b)⟩

theorem upair_second {a b c d : ZFSet.{u}} (hac : a = c) (h : upairSet a b = upairSet c d) :
    b = d := by
  have hb : b ∈ upairSet c d := h ▸ upair_right a b
  rcases upair_elim hb with hbc | hbd
  · have hd : d ∈ upairSet a b := h.symm ▸ upair_right c d
    rcases upair_elim hd with hda | hdb
    · exact hbc.trans (hac.symm.trans hda.symm)
    · exact hdb.symm
  · exact hbd

/-- Kuratowski's `kpair a b = UPair (Sing a) (UPair a b)`. -/
noncomputable def kpairSet (a b : ZFSet.{u}) : ZFSet.{u} :=
  upairSet (singSet a) (upairSet a b)

theorem kpairSet_eq (a b : ZFSet.{u}) : kpairSet a b = ZFSet.pair a b := by
  rw [kpairSet, upairSet_eq, singSet_eq, upairSet_eq]
  rfl

/-- `binunion X Y = Union (UPair X Y)`. -/
noncomputable def binunionSet (X Y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sUnion (upairSet X Y)

theorem binunionSet_eq (X Y : ZFSet.{u}) : binunionSet X Y = X ∪ Y := by
  rw [binunionSet, upairSet_eq, ZFSet.sUnion_pair]

theorem binunion_left {X Y x : ZFSet.{u}} (hx : x ∈ X) : x ∈ binunionSet X Y :=
  ZFSet.mem_sUnion.mpr ⟨X, upair_left X Y, hx⟩

theorem binunion_right {X Y x : ZFSet.{u}} (hx : x ∈ Y) : x ∈ binunionSet X Y :=
  ZFSet.mem_sUnion.mpr ⟨Y, upair_right X Y, hx⟩

theorem binunion_elim {X Y x : ZFSet.{u}} (hx : x ∈ binunionSet X Y) : x ∈ X ∨ x ∈ Y := by
  rcases ZFSet.mem_sUnion.mp hx with ⟨Z, hZ, hxZ⟩
  rcases upair_elim hZ with rfl | rfl
  · exact Or.inl hxZ
  · exact Or.inr hxZ

/-- A Kuratowski pair of members sits in the double power set of the union. -/
theorem pair_mem_double_powerset {A B x y : ZFSet.{u}} (hx : x ∈ A) (hy : y ∈ B) :
    ZFSet.pair x y ∈ ZFSet.powerset (ZFSet.powerset (A ∪ B)) := by
  refine ZFSet.mem_powerset.mpr ?_
  intro z hz
  rw [ZFSet.pair, ZFSet.mem_pair] at hz
  rcases hz with hz | hz
  · rw [hz]
    refine ZFSet.mem_powerset.mpr ?_
    intro w hw
    rw [ZFSet.mem_singleton] at hw
    rw [hw]
    exact ZFSet.mem_union.mpr (Or.inl hx)
  · rw [hz]
    refine ZFSet.mem_powerset.mpr ?_
    intro w hw
    rw [ZFSet.mem_pair] at hw
    rcases hw with hw | hw
    · rw [hw]
      exact ZFSet.mem_union.mpr (Or.inl hx)
    · rw [hw]
      exact ZFSet.mem_union.mpr (Or.inr hy)

/-- `prod A B`, separated from the power set of the power set of the binary union. -/
noncomputable def prodSet (A B : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ A, ∃ y ∈ B, z = kpairSet x y)
    (ZFSet.powerset (ZFSet.powerset (binunionSet A B)))

theorem prod_intro {A B x y : ZFSet.{u}} (hx : x ∈ A) (hy : y ∈ B) :
    kpairSet x y ∈ prodSet A B := by
  refine ZFSet.mem_sep.mpr ⟨?_, x, hx, y, hy, rfl⟩
  rw [kpairSet_eq, binunionSet_eq]
  exact pair_mem_double_powerset hx hy

theorem prod_elim {A B z : ZFSet.{u}} (hz : z ∈ prodSet A B) :
    ∃ x, x ∈ A ∧ ∃ y, y ∈ B ∧ z = kpairSet x y := by
  rcases (ZFSet.mem_sep.mp hz).2 with ⟨x, hx, y, hy, hzp⟩
  exact ⟨x, hx, y, hy, hzp⟩

theorem prod_relation {A B z : ZFSet.{u}} (hz : z ∈ prodSet A B) :
    ∃ x y, z = kpairSet x y := by
  rcases prod_elim hz with ⟨x, _, y, _, hzp⟩
  exact ⟨x, y, hzp⟩

theorem prodSet_eq (A B : ZFSet.{u}) : prodSet A B = ZFSet.prod A B := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    rcases prod_elim hz with ⟨x, hx, y, hy, hzp⟩
    exact ZFSet.mem_prod.mpr ⟨x, hx, y, hy, hzp.trans (kpairSet_eq x y)⟩
  · intro hz
    rcases ZFSet.mem_prod.mp hz with ⟨x, hx, y, hy, hzp⟩
    have hmem : ZFSet.pair x y ∈
        ZFSet.powerset (ZFSet.powerset (A ∪ B)) :=
      pair_mem_double_powerset hx hy
    refine ZFSet.mem_sep.mpr ⟨?_, x, hx, y, hy, ?_⟩
    · rw [binunionSet_eq, hzp]
      exact hmem
    · rw [kpairSet_eq]
      exact hzp

/-- The domain of a set of Kuratowski pairs. -/
noncomputable def domSet (R : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => ∃ y, kpairSet x y ∈ R) (ZFSet.sUnion (ZFSet.sUnion R))

/-- The range of a set of Kuratowski pairs. -/
noncomputable def ranSet (R : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun y => ∃ x, kpairSet x y ∈ R) (ZFSet.sUnion (ZFSet.sUnion R))

theorem dom_intro {R x y : ZFSet.{u}} (h : kpairSet x y ∈ R) : x ∈ domSet R := by
  refine ZFSet.mem_sep.mpr ⟨?_, y, h⟩
  refine ZFSet.mem_sUnion.mpr ⟨singSet x, ?_, sing_intro x⟩
  refine ZFSet.mem_sUnion.mpr ⟨kpairSet x y, h, ?_⟩
  rw [kpairSet]
  exact upair_left (singSet x) (upairSet x y)

theorem dom_elim {R x : ZFSet.{u}} (h : x ∈ domSet R) : ∃ y, kpairSet x y ∈ R :=
  (ZFSet.mem_sep.mp h).2

theorem ran_intro {R x y : ZFSet.{u}} (h : kpairSet x y ∈ R) : y ∈ ranSet R := by
  refine ZFSet.mem_sep.mpr ⟨?_, x, h⟩
  refine ZFSet.mem_sUnion.mpr ⟨upairSet x y, ?_, upair_right x y⟩
  refine ZFSet.mem_sUnion.mpr ⟨kpairSet x y, h, ?_⟩
  rw [kpairSet]
  exact upair_right (singSet x) (upairSet x y)

theorem ran_elim {R y : ZFSet.{u}} (h : y ∈ ranSet R) : ∃ x, kpairSet x y ∈ R :=
  (ZFSet.mem_sep.mp h).2

/-- `id-rel A`, the pairs of a member of `A` with itself, separated from the product. -/
noncomputable def idRelSet (A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x, z = kpairSet x x) (prodSet A A)

/-- The identity relation on `A` is a function from `A` to `A`. -/
theorem id_function (A : ZFSet.{u}) :
    idRelSet A ⊆ prodSet A A ∧
      (∀ x y z, kpairSet x y ∈ idRelSet A → kpairSet x z ∈ idRelSet A → y = z) ∧
      (∀ x, x ∈ A → ∃ y, kpairSet x y ∈ idRelSet A) := by
  refine ⟨ZFSet.sep_subset, ?_, ?_⟩
  · intro x y z hy hz
    rcases (ZFSet.mem_sep.mp hy).2 with ⟨u, hyu⟩
    rcases (ZFSet.mem_sep.mp hz).2 with ⟨v, hzv⟩
    have hy' : ZFSet.pair x y = ZFSet.pair u u := by
      rw [← kpairSet_eq, ← kpairSet_eq]
      exact hyu
    have hz' : ZFSet.pair x z = ZFSet.pair v v := by
      rw [← kpairSet_eq, ← kpairSet_eq]
      exact hzv
    rcases ZFSet.pair_inj.mp hy' with ⟨hxu, hyu'⟩
    rcases ZFSet.pair_inj.mp hz' with ⟨hxv, hzv'⟩
    exact hyu'.trans (hxu.symm.trans (hxv.trans hzv'.symm))
  · intro x hx
    exact ⟨x, ZFSet.mem_sep.mpr ⟨prod_intro hx hx, x, rfl⟩⟩

/-- `succ a = binunion a (Sing a)`. -/
noncomputable def succSet (a : ZFSet.{u}) : ZFSet.{u} :=
  binunionSet a (singSet a)

theorem succSet_eq (a : ZFSet.{u}) : succSet a = insert a a := by
  apply ZFSet.ext
  intro z
  rw [succSet, binunionSet_eq, singSet_eq, ZFSet.insert_eq, ZFSet.mem_union, ZFSet.mem_union,
    ZFSet.mem_singleton]
  constructor
  · intro h
    rcases h with hz | hz
    · exact Or.inr hz
    · exact Or.inl hz
  · intro h
    rcases h with hz | hz
    · exact Or.inr hz
    · exact Or.inl hz

theorem succ_self (a : ZFSet.{u}) : a ∈ succSet a := by
  rw [succSet_eq]
  exact ZFSet.mem_insert a a

theorem succ_mem {a x : ZFSet.{u}} (hx : x ∈ a) : x ∈ succSet a := by
  rw [succSet_eq]
  exact ZFSet.mem_insert_of_mem a hx

theorem succ_elim {a x : ZFSet.{u}} (hx : x ∈ succSet a) : x ∈ a ∨ x = a := by
  rw [succSet_eq] at hx
  rcases ZFSet.mem_insert_iff.mp hx with rfl | hx
  · exact Or.inr rfl
  · exact Or.inl hx

theorem succ_neq (a : ZFSet.{u}) : succSet a ≠ a := by
  intro h
  have ha : a ∈ succSet a := succ_self a
  rw [h] at ha
  exact ZFSet.mem_irrefl a ha

theorem succ_inj {a b : ZFSet.{u}} (h : succSet a = succSet b) : a = b := by
  have ha : a ∈ succSet b := h ▸ succ_self a
  have hb : b ∈ succSet a := h.symm ▸ succ_self b
  rcases succ_elim ha with hab | rfl
  · rcases succ_elim hb with hba | rfl
    · exact (ZFSet.mem_asymm hab hba).elim
    · rfl
  · rfl

theorem ordinal_succ {a : ZFSet.{u}} (ha : CurriculumOrdinal a) :
    CurriculumOrdinal (succSet a) := by
  rw [succSet_eq]
  exact (curriculumOrdinal_iff_isOrdinal).mpr
    (ZFSet.isOrdinal_succ ((curriculumOrdinal_iff_isOrdinal).mp ha))

theorem empty_ordinal : CurriculumOrdinal (∅ : ZFSet.{u}) :=
  ⟨ZFSet.isTransitive_empty, fun b hb => (ZFSet.notMem_empty b hb).elim⟩

theorem ordinal_hered {a b : ZFSet.{u}} (ha : CurriculumOrdinal a) (hb : b ∈ a) :
    CurriculumOrdinal b :=
  ⟨ha.2 b hb, fun c hc => ha.2 c (ha.1 b hb hc)⟩

theorem transset_power {A : ZFSet.{u}} (h : A.IsTransitive) : (ZFSet.powerset A).IsTransitive :=
  h.powerset

theorem transset_union {S : ZFSet.{u}} (h : ∀ X ∈ S, X.IsTransitive) :
    (ZFSet.sUnion S).IsTransitive :=
  ZFSet.IsTransitive.sUnion' h

theorem ordinal_union {S : ZFSet.{u}} (h : ∀ a ∈ S, CurriculumOrdinal a) :
    CurriculumOrdinal (ZFSet.sUnion S) :=
  ⟨ZFSet.IsTransitive.sUnion' fun a ha => (h a ha).1,
    fun b hb => by
      rcases ZFSet.mem_sUnion.mp hb with ⟨a, haS, hba⟩
      exact (h a haS).2 b hba⟩

/-- An unordered pair of members of `S` is included in `S`. -/
theorem upair_subq {x y S : ZFSet.{u}} (hx : x ∈ S) (hy : y ∈ S) : upairSet x y ⊆ S := by
  intro w hw
  rcases upair_elim hw with hw | hw
  · rw [hw]
    exact hx
  · rw [hw]
    exact hy

/-- A Kuratowski pair of members of `S` lies in the double power set of `S`. -/
theorem kpair_power {x y S : ZFSet.{u}} (hx : x ∈ S) (hy : y ∈ S) :
    kpairSet x y ∈ ZFSet.powerset (ZFSet.powerset S) := by
  rw [kpairSet_eq]
  have hSS : S ∪ S = S := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_union]
    constructor
    · intro h
      rcases h with hz | hz
      · exact hz
      · exact hz
    · intro hz
      exact Or.inl hz
  have hmem := pair_mem_double_powerset hx hy
  rw [hSS] at hmem
  exact hmem

/-- A subset of a set of Kuratowski pairs is a set of Kuratowski pairs. -/
theorem relation_subq {R S : ZFSet.{u}}
    (hR : ∀ z : ZFSet.{u}, z ∈ R → ∃ x y, z = kpairSet x y) (hS : S ⊆ R) :
    ∀ z : ZFSet.{u}, z ∈ S → ∃ x y, z = kpairSet x y :=
  fun z hz => hR z (hS hz)

/-- The domain of a product is included in the first factor. -/
theorem dom_prod (A B : ZFSet.{u}) : domSet (prodSet A B) ⊆ A := by
  intro x hx
  rcases dom_elim hx with ⟨y, hxy⟩
  rcases prod_elim hxy with ⟨u, hu, v, _, heq⟩
  have heq' : ZFSet.pair x y = ZFSet.pair u v := by
    rw [← kpairSet_eq, ← kpairSet_eq]
    exact heq
  have hxu : x = u := (ZFSet.pair_inj.mp heq').1
  rw [hxu]
  exact hu

/-- A function from `A` to `B` is defined on all of `A`. -/
theorem function_dom {f A B : ZFSet.{u}}
    (h : f ⊆ prodSet A B ∧
      (∀ x y z, kpairSet x y ∈ f → kpairSet x z ∈ f → y = z) ∧
      (∀ x, x ∈ A → ∃ y, kpairSet x y ∈ f)) :
    A ⊆ domSet f := by
  intro x hx
  rcases h.2.2 x hx with ⟨y, hy⟩
  exact dom_intro hy

/-! ## Sentences of the signature -/

/-- Leibniz equality, a quantifier over predicates. -/
def same {Γ : Ctx Unit} (x y : Expr Γ set) : Formula Symbol Γ :=
  .all (.imp (.app (.var .vz) (weaken x)) (.app (.var .vz) (weaken y)))

def isSingleton {Γ : Ctx Unit} (s a : Expr Γ set) : Formula Symbol Γ :=
  .all (iffFormula (member (.var .vz) (weaken s)) (.eq (.var .vz) (weaken a)))

def isUPair {Γ : Ctx Unit} (u a b : Expr Γ set) : Formula Symbol Γ :=
  .all (iffFormula (member (.var .vz) (weaken u))
    (.or (.eq (.var .vz) (weaken a)) (.eq (.var .vz) (weaken b))))

def isKPair {Γ : Ctx Unit} (p a b : Expr Γ set) : Formula Symbol Γ :=
  .all (iffFormula (member (.var .vz) (weaken p))
    (.or (isSingleton (.var .vz) (weaken a)) (isUPair (.var .vz) (weaken a) (weaken b))))

/-- A pair code of `x` and `y` is a member of `f`. -/
def pairIn {Γ : Ctx Unit} (x y f : Expr Γ set) : Formula Symbol Γ :=
  .ex (.and (isKPair (.var .vz) (weaken x) (weaken y)) (member (.var .vz) (weaken f)))

/-- `∀ x y z,` a pair of `x, y` in `f` and a pair of `x, z` in `f` give `same y z`. -/
def functionalFormula {Γ : Ctx Unit} (f : Expr Γ set) : Formula Symbol Γ :=
  .all (.all (.all (.imp
    (pairIn (.var (.vs (.vs .vz))) (.var (.vs .vz)) (weaken (weaken (weaken f))))
    (.imp
      (pairIn (.var (.vs (.vs .vz))) (.var .vz) (weaken (weaken (weaken f))))
      (same (.var (.vs .vz)) (.var .vz))))))

/-- Every member of `B` is the second component of a pair in `f` whose first component is in `A`. -/
def ontoFormula {Γ : Ctx Unit} (f A B : Expr Γ set) : Formula Symbol Γ :=
  .all (.imp (member (.var .vz) (weaken B))
    (.ex (.and (member (.var .vz) (weaken (weaken A)))
      (pairIn (.var .vz) (.var (.vs .vz)) (weaken (weaken f))))))

def subsetOf {Γ : Ctx Unit} (x y : Expr Γ set) : Formula Symbol Γ :=
  .all (.imp (member (.var .vz) (weaken x)) (member (.var .vz) (weaken y)))

def transSet {Γ : Ctx Unit} (x : Expr Γ set) : Formula Symbol Γ :=
  .all (.imp (member (.var .vz) (weaken x)) (subsetOf (.var .vz) (weaken x)))

/-- A transitive set whose members are transitive sets. -/
def ordinalFormula {Γ : Ctx Unit} (a : Expr Γ set) : Formula Symbol Γ :=
  .and (transSet a) (.all (.imp (member (.var .vz) (weaken a)) (transSet (.var .vz))))

/-! ## The closed sentences -/

/-- No set is a member of itself. -/
def inIrrefl : ClosedFormula Symbol :=
  .all (.not (member (.var .vz) (.var .vz)))

theorem inIrrefl_valid : model.{u}.models inIrrefl := by
  intro x _
  exact ZFSet.mem_irrefl x

/-- Membership is asymmetric. -/
def inAsym : ClosedFormula Symbol :=
  .all (.all (.imp (member (.var (.vs .vz)) (.var .vz))
    (.not (member (.var .vz) (.var (.vs .vz))))))

theorem inAsym_valid : model.{u}.models inAsym := by
  intro x _ y _ hxy hyx
  exact ZFSet.mem_asymm hxy hyx

/-- There is a set whose members are exactly the sets that are not members of themselves. -/
def russellExistence : ClosedFormula Symbol :=
  .ex (.all (iffFormula (member (.var .vz) (.var (.vs .vz)))
    (.not (member (.var .vz) (.var .vz)))))

theorem russell_false : ¬ model.{u}.models russellExistence := by
  rintro ⟨R, _, hR⟩
  have h := hR R trivial
  exact ZFSet.mem_irrefl R (h.2 fun hmem => h.1 hmem hmem)

/-- The class of sets that are not members of themselves. -/
def nonSelfMember : Formula Symbol [set] :=
  .not (member (.var .vz) (.var .vz))

/-- Separating the sets that are not members of themselves from any set yields a set
that is not a member of itself. -/
theorem separated_nonSelf_misses_the_class (a : ZFSet.{u}) :
    ∃ R : ZFSet.{u}, (∀ x, x ∈ R ↔ x ∈ a ∧ x ∉ x) ∧ R ∉ R := by
  refine ⟨ZFSet.sep (fun x => x ∉ x) a, fun x => ZFSet.mem_sep, ?_⟩
  intro h
  exact (ZFSet.mem_sep.mp h).2 h

/-- The identity reaches every member of its domain. -/
def identityOntoSelf : ClosedFormula Symbol :=
  .all (.all (.imp (member (.var .vz) (.var (.vs .vz)))
    (.ex (.and (member (.var .vz) (.var (.vs (.vs .vz))))
      (.eq (.var .vz) (.var (.vs .vz)))))))

theorem identity_onto_self_valid : model.{u}.models identityOntoSelf := by
  intro A _ Y _ hY
  exact ⟨Y, trivial, hY, rfl⟩

/-- The same shape, aimed at the power set, is false. -/
def identityOntoPower : ClosedFormula Symbol :=
  .all (.all (.imp (member (.var .vz) (.app (.const .power) (.var (.vs .vz))))
    (.ex (.and (member (.var .vz) (.var (.vs (.vs .vz))))
      (.eq (.var .vz) (.var (.vs .vz)))))))

/-- No function of the logic maps a set onto its power set. Equality of the value is Leibniz. -/
def cantorFn : ClosedFormula Symbol :=
  .all (.all (.not (.all (.imp
    (member (.var .vz) (.app (.const .power) (.var (.vs (.vs .vz)))))
    (.ex (.and (member (.var .vz) (.var (.vs (.vs (.vs .vz)))))
      (same (.app (.var (.vs (.vs .vz))) (.var .vz)) (.var (.vs .vz)))))))))

theorem cantor_fn_valid : model.{u}.models cantorFn := by
  intro A _ F _ surj
  change ZFSet.{u} at A
  change ZFSet.{u} → ZFSet.{u} at F
  let D := ZFSet.sep (fun x => x ∉ F x) A
  have hD : D ∈ ZFSet.powerset A := ZFSet.mem_powerset.mpr ZFSet.sep_subset
  obtain ⟨x, _, hxA, hsame⟩ := surj D trivial hD
  change ZFSet.{u} at x
  have hxEq : F x = D := by
    change ∀ P : ZFSet.{u} → ULift.{u + 1} Prop, True → (P (F x)).down → (P D).down at hsame
    exact (hsame (fun z => .up (z = F x)) trivial rfl).symm
  have hnin : x ∉ D := fun hin => (ZFSet.mem_sep.mp hin).2 (hxEq ▸ hin)
  exact hnin (ZFSet.mem_sep.mpr ⟨hxA, hxEq ▸ hnin⟩)

/-- A functional relation onto the power set is absurd. -/
def cantorCore : ClosedFormula Symbol :=
  .all (.all (.imp (functionalFormula (.var .vz))
    (.imp (ontoFormula (.var .vz) (.var (.vs .vz))
        (.app (.const .power) (.var (.vs .vz))))
      .bot)))

/-- A common Kuratowski code gives equal components. The components are compared by Leibniz
equality. The code is the membership characterization: the signature has no pairing constant. -/
def kuratowskiInj : ClosedFormula Symbol :=
  .all (.all (.all (.all (.imp
    (.ex (.and
      (isKPair (.var .vz) (.var (.vs (.vs (.vs (.vs .vz))))) (.var (.vs (.vs (.vs .vz)))))
      (isKPair (.var .vz) (.var (.vs (.vs .vz))) (.var (.vs .vz)))))
    (.and (same (.var (.vs (.vs (.vs .vz)))) (.var (.vs .vz)))
      (same (.var (.vs (.vs .vz))) (.var .vz)))))))

theorem kuratowski_inj_valid : model.{u}.models kuratowskiInj := by
  intro a _ b _ c _ d _ h
  change ZFSet.{u} at a
  change ZFSet.{u} at b
  change ZFSet.{u} at c
  change ZFSet.{u} at d
  obtain ⟨p, _, hpab, hpcd⟩ := h
  change ZFSet.{u} at p
  have hab : IsKPair p a b := by
    intro w
    have hw := hpab w trivial
    constructor
    · intro hmem
      rcases hw.1 hmem with hs | hu
      · exact Or.inl (fun t => ⟨(hs t trivial).1, (hs t trivial).2⟩)
      · exact Or.inr (fun t => ⟨(hu t trivial).1, (hu t trivial).2⟩)
    · intro hor
      exact hw.2 (hor.elim
        (fun hs => Or.inl (fun t _ => ⟨(hs t).1, (hs t).2⟩))
        (fun hu => Or.inr (fun t _ => ⟨(hu t).1, (hu t).2⟩)))
  have hcd : IsKPair p c d := by
    intro w
    have hw := hpcd w trivial
    constructor
    · intro hmem
      rcases hw.1 hmem with hs | hu
      · exact Or.inl (fun t => ⟨(hs t trivial).1, (hs t trivial).2⟩)
      · exact Or.inr (fun t => ⟨(hu t trivial).1, (hu t trivial).2⟩)
    · intro hor
      exact hw.2 (hor.elim
        (fun hs => Or.inl (fun t _ => ⟨(hs t).1, (hs t).2⟩))
        (fun hu => Or.inr (fun t _ => ⟨(hu t).1, (hu t).2⟩)))
  obtain ⟨hac, hbd⟩ := kuratowski_inj hab hcd
  constructor
  · intro P _ hP
    change ZFSet.{u} → ULift.{u + 1} Prop at P
    exact hac ▸ hP
  · intro P _ hP
    change ZFSet.{u} → ULift.{u + 1} Prop at P
    exact hbd ▸ hP

/-- Equal components give the same Kuratowski codes. -/
def kuratowskiCong : ClosedFormula Symbol :=
  .all (.all (.all (.all (.imp
    (same (.var (.vs (.vs (.vs .vz)))) (.var (.vs .vz)))
    (.imp (same (.var (.vs (.vs .vz))) (.var .vz))
      (.all (.imp
        (isKPair (.var .vz) (.var (.vs (.vs (.vs (.vs .vz)))))
          (.var (.vs (.vs (.vs .vz)))))
        (isKPair (.var .vz) (.var (.vs (.vs .vz))) (.var (.vs .vz))))))))))

theorem kuratowski_cong_valid : model.{u}.models kuratowskiCong := by
  intro a _ b _ c _ d _ hac hbd p _ hp
  change ZFSet.{u} at a
  change ZFSet.{u} at b
  change ZFSet.{u} at c
  change ZFSet.{u} at d
  have hac' : a = c := by
    change ∀ P : ZFSet.{u} → ULift.{u + 1} Prop, True → (P a).down → (P c).down at hac
    exact (hac (fun z => .up (z = a)) trivial rfl).symm
  have hbd' : b = d := by
    change ∀ P : ZFSet.{u} → ULift.{u + 1} Prop, True → (P b).down → (P d).down at hbd
    exact (hbd (fun z => .up (z = b)) trivial rfl).symm
  change ZFSet.{u} at p
  have hab : IsKPair p a b := by
    intro w
    have hw := hp w trivial
    constructor
    · intro hmem
      rcases hw.1 hmem with hs | hu
      · exact Or.inl (fun t => ⟨(hs t trivial).1, (hs t trivial).2⟩)
      · exact Or.inr (fun t => ⟨(hu t trivial).1, (hu t trivial).2⟩)
    · intro hor
      exact hw.2 (hor.elim
        (fun hs => Or.inl (fun t _ => ⟨(hs t).1, (hs t).2⟩))
        (fun hu => Or.inr (fun t _ => ⟨(hu t).1, (hu t).2⟩)))
  have hcd : IsKPair p c d := kuratowski_cong hab hac' hbd'
  intro w _
  constructor
  · intro hmem
    rcases (hcd w).1 hmem with hs | hu
    · exact Or.inl (fun t _ => ⟨(hs t).1, (hs t).2⟩)
    · exact Or.inr (fun t _ => ⟨(hu t).1, (hu t).2⟩)
  · intro hor
    exact (hcd w).2 (hor.elim
      (fun hs => Or.inl (fun t => ⟨(hs t trivial).1, (hs t trivial).2⟩))
      (fun hu => Or.inr (fun t => ⟨(hu t trivial).1, (hu t trivial).2⟩)))

/-- There is a set whose members are exactly the ordinals. -/
def buraliFortiExistence : ClosedFormula Symbol :=
  .ex (.all (iffFormula (member (.var .vz) (.var (.vs .vz))) (ordinalFormula (.var .vz))))

theorem buraliForti_false : ¬ model.{u}.models buraliFortiExistence := by
  rintro ⟨O, _, hO⟩
  change ZFSet.{u} at O
  apply burali_forti
  refine ⟨O, fun x => ?_⟩
  have hx := hO x trivial
  constructor
  · intro hxO
    have hord := hx.1 hxO
    refine ⟨fun y hy z hz => hord.1 y trivial hy z trivial hz,
      fun b hb y hy z hz => hord.2 b trivial hb y trivial hy z trivial hz⟩
  · intro hord
    apply hx.2
    refine ⟨fun y _ hy z _ hz => (hord.1 y hy) hz,
      fun b _ hb y _ hy z _ hz => (hord.2 b hb y hy) hz⟩

/-- `Sing a = Sep (Power a) (λ w. same w a)`. -/
def singTerm {Γ : Ctx Unit} (a : Expr Γ set) : Expr Γ set :=
  separate (.app (.const .power) a) (.lam (same (.var .vz) (weaken a)))

/-- `a` belongs to its singleton. -/
def singIntro : ClosedFormula Symbol :=
  .all (member (.var .vz) (singTerm (.var .vz)))

theorem sing_intro_valid : model.{u}.models singIntro := by
  intro a _
  change ZFSet.{u} at a
  change a ∈ ZFSet.sep (fun w =>
      ∀ P : ZFSet.{u} → ULift.{u + 1} Prop, True → (P w).down → (P a).down)
      (ZFSet.powerset a)
  refine ZFSet.mem_sep.mpr ⟨ZFSet.mem_powerset.mpr (fun _ hz => hz), ?_⟩
  intro P _ hP
  exact hP

/-- A member of a singleton is Leibniz-equal to its element. -/
def singElim : ClosedFormula Symbol :=
  .all (.all (.imp
    (member (.var .vz) (singTerm (.var (.vs .vz))))
    (same (.var .vz) (.var (.vs .vz)))))

theorem sing_elim_valid : model.{u}.models singElim := by
  intro a _ z _ hz
  change ZFSet.{u} at a
  change ZFSet.{u} at z
  have hzSep : z ∈ ZFSet.sep (fun w =>
      ∀ P : ZFSet.{u} → ULift.{u + 1} Prop, True → (P w).down → (P a).down)
      (ZFSet.powerset a) := hz
  change ∀ P : ZFSet.{u} → ULift.{u + 1} Prop, True → (P z).down → (P a).down
  exact (ZFSet.mem_sep.mp hzSep).2

/-- Sets with the same singleton are Leibniz-equal. -/
def singInj : ClosedFormula Symbol :=
  .all (.all (.imp
    (same (singTerm (.var (.vs .vz))) (singTerm (.var .vz)))
    (same (.var (.vs .vz)) (.var .vz))))

theorem sing_inj_valid : model.{u}.models singInj := by
  intro a _ c _ h
  change ZFSet.{u} at a
  change ZFSet.{u} at c
  have ha : a ∈ ZFSet.sep (fun w =>
      ∀ P : ZFSet.{u} → ULift.{u + 1} Prop, True → (P w).down → (P a).down)
      (ZFSet.powerset a) := by
    refine ZFSet.mem_sep.mpr ⟨ZFSet.mem_powerset.mpr (fun _ hz => hz), ?_⟩
    intro P _ hP
    exact hP
  have hsame : ∀ Q : ZFSet.{u} → ULift.{u + 1} Prop, True →
      (Q (ZFSet.sep (fun w =>
        ∀ P : ZFSet.{u} → ULift.{u + 1} Prop, True → (P w).down → (P a).down)
        (ZFSet.powerset a))).down →
      (Q (ZFSet.sep (fun w =>
        ∀ P : ZFSet.{u} → ULift.{u + 1} Prop, True → (P w).down → (P c).down)
        (ZFSet.powerset c))).down := by
    change _ at h
    exact h
  have hc : a ∈ ZFSet.sep (fun w =>
      ∀ P : ZFSet.{u} → ULift.{u + 1} Prop, True → (P w).down → (P c).down)
      (ZFSet.powerset c) :=
    (hsame (fun s => .up (a ∈ s)) trivial ha)
  change ∀ P : ZFSet.{u} → ULift.{u + 1} Prop, True → (P a).down → (P c).down
  exact (ZFSet.mem_sep.mp hc).2

/-- The empty set is an ordinal. -/
def emptyOrdinal : ClosedFormula Symbol :=
  ordinalFormula (.const .empty)

theorem empty_ordinal_valid : model.{u}.models emptyOrdinal := by
  constructor
  · intro x _ hx
    exact (ZFSet.notMem_empty x hx).elim
  · intro b _ hb
    exact (ZFSet.notMem_empty b hb).elim

/-- A member of an ordinal is an ordinal. -/
def ordinalHered : ClosedFormula Symbol :=
  .all (.all (.imp (ordinalFormula (.var (.vs .vz)))
    (.imp (member (.var .vz) (.var (.vs .vz))) (ordinalFormula (.var .vz)))))

theorem ordinal_hered_valid : model.{u}.models ordinalHered := by
  intro a _ b _ ha hb
  constructor
  · exact ha.2 b trivial hb
  · intro c _ hc
    exact ha.2 c trivial (ha.1 b trivial hb c trivial hc)

/-- The power set of a transitive set is transitive. -/
def transsetPower : ClosedFormula Symbol :=
  .all (.imp (transSet (.var .vz)) (transSet (.app (.const .power) (.var .vz))))

theorem transset_power_valid : model.{u}.models transsetPower := by
  intro A _ hA x _ hx y _ hy
  change ZFSet.{u} at A
  change ZFSet.{u} at x
  change ZFSet.{u} at y
  change y ∈ ZFSet.powerset A
  apply ZFSet.mem_powerset.mpr
  intro z hz
  exact hA y trivial (ZFSet.mem_powerset.mp hx hy) z trivial hz

/-- The union of a set of transitive sets is transitive. -/
def transsetUnion : ClosedFormula Symbol :=
  .all (.imp
    (.all (.imp (member (.var .vz) (.var (.vs .vz))) (transSet (.var .vz))))
    (transSet (.app (.const .union) (.var .vz))))

theorem transset_union_valid : model.{u}.models transsetUnion := by
  intro S _ hS x _ hx y _ hy
  change ZFSet.{u} at S
  change ZFSet.{u} at x
  change ZFSet.{u} at y
  change y ∈ ZFSet.sUnion S
  have hxU : x ∈ ZFSet.sUnion S := hx
  rcases ZFSet.mem_sUnion.mp hxU with ⟨X, hXS, hxX⟩
  have hyX : y ∈ X := hS X trivial hXS x trivial hxX y trivial hy
  exact ZFSet.mem_sUnion.mpr ⟨X, hXS, hyX⟩

/-- The union of a set of ordinals is an ordinal. -/
def ordinalUnion : ClosedFormula Symbol :=
  .all (.imp
    (.all (.imp (member (.var .vz) (.var (.vs .vz))) (ordinalFormula (.var .vz))))
    (ordinalFormula (.app (.const .union) (.var .vz))))

theorem ordinal_union_valid : model.{u}.models ordinalUnion := by
  intro S _ hS
  constructor
  · intro x _ hx y _ hy
    change ZFSet.{u} at S
    change ZFSet.{u} at x
    change ZFSet.{u} at y
    change y ∈ ZFSet.sUnion S
    have hxU : x ∈ ZFSet.sUnion S := hx
    rcases ZFSet.mem_sUnion.mp hxU with ⟨a, haS, hxa⟩
    have hord := hS a trivial haS
    exact ZFSet.mem_sUnion.mpr ⟨a, haS, hord.1 x trivial hxa y trivial hy⟩
  · intro b _ hb
    change ZFSet.{u} at S
    change ZFSet.{u} at b
    have hbU : b ∈ ZFSet.sUnion S := hb
    rcases ZFSet.mem_sUnion.mp hbU with ⟨a, haS, hba⟩
    exact (hS a trivial haS).2 b trivial hba

/-- Every set includes itself. -/
def subqRefl : ClosedFormula Symbol :=
  .all (subsetOf (.var .vz) (.var .vz))

theorem subq_refl_valid : model.{u}.models subqRefl := by
  intro X _ x _ hx
  exact hx

/-- Inclusion is transitive. -/
def subqTrans : ClosedFormula Symbol :=
  .all (.all (.all (.imp
    (subsetOf (.var (.vs (.vs .vz))) (.var (.vs .vz)))
    (.imp
      (subsetOf (.var (.vs .vz)) (.var .vz))
      (subsetOf (.var (.vs (.vs .vz))) (.var .vz))))))

theorem subq_trans_valid : model.{u}.models subqTrans := by
  intro X _ Y _ Z _ hXY hYZ x _ hx
  exact hYZ x trivial (hXY x trivial hx)

/-- A subset of a set belongs to its power set. -/
def powerIntro : ClosedFormula Symbol :=
  .all (.all (.imp
    (subsetOf (.var .vz) (.var (.vs .vz)))
    (member (.var .vz) (.app (.const .power) (.var (.vs .vz))))))

theorem power_intro_valid : model.{u}.models powerIntro := by
  intro a _ b _ h
  exact ZFSet.mem_powerset.mpr (fun x hx => h x trivial hx)

/-- A member of a power set is a subset. -/
def powerElim : ClosedFormula Symbol :=
  .all (.all (.imp
    (member (.var .vz) (.app (.const .power) (.var (.vs .vz))))
    (subsetOf (.var .vz) (.var (.vs .vz)))))

theorem power_elim_valid : model.{u}.models powerElim := by
  intro a _ b _ h x _ hx
  exact ZFSet.mem_powerset.mp h hx

/-- The empty set is included in every set. -/
def emptySubq : ClosedFormula Symbol :=
  .all (subsetOf (.const .empty) (.var .vz))

theorem empty_subq_valid : model.{u}.models emptySubq := by
  intro X _ x _ hx
  exact (ZFSet.notMem_empty x hx).elim

/-- A member of a set with the property belongs to the separated set. -/
def sepIntro : ClosedFormula Symbol :=
  .all (.all (.all (.imp
    (member (.var .vz) (.var (.vs (.vs .vz))))
    (.imp
      (.app (.var (.vs .vz)) (.var .vz))
      (member (.var .vz) (separate (.var (.vs (.vs .vz))) (.var (.vs .vz))))))))

theorem sep_intro_valid : model.{u}.models sepIntro := by
  intro a _ P _ x _ hx hP
  change ZFSet.{u} at a
  change ZFSet.{u} at x
  change ZFSet.{u} → ULift.{u + 1} Prop at P
  change x ∈ ZFSet.sep (fun y => (P y).down) a
  have hxIn : (x : ZFSet.{u}) ∈ a := hx
  have hProp : (P x).down := hP
  exact ZFSet.mem_sep.mpr ⟨hxIn, hProp⟩

/-- A member of a separated set belongs to the set. -/
def sepElimIn : ClosedFormula Symbol :=
  .all (.all (.all (.imp
    (member (.var .vz) (separate (.var (.vs (.vs .vz))) (.var (.vs .vz))))
    (member (.var .vz) (.var (.vs (.vs .vz)))))))

theorem sep_elim_in_valid : model.{u}.models sepElimIn := by
  intro a _ P _ x _ h
  change ZFSet.{u} at a
  change ZFSet.{u} at x
  change ZFSet.{u} → ULift.{u + 1} Prop at P
  have hSep : x ∈ ZFSet.sep (fun y => (P y).down) a := h
  change x ∈ a
  exact (ZFSet.mem_sep.mp hSep).1

/-- A member of a separated set has the property. -/
def sepElimProp : ClosedFormula Symbol :=
  .all (.all (.all (.imp
    (member (.var .vz) (separate (.var (.vs (.vs .vz))) (.var (.vs .vz))))
    (.app (.var (.vs .vz)) (.var .vz)))))

theorem sep_elim_prop_valid : model.{u}.models sepElimProp := by
  intro a _ P _ x _ h
  change ZFSet.{u} at a
  change ZFSet.{u} at x
  change ZFSet.{u} → ULift.{u + 1} Prop at P
  have hSep : x ∈ ZFSet.sep (fun y => (P y).down) a := h
  change (P x).down
  exact (ZFSet.mem_sep.mp hSep).2

/-- A separated set is included in the set. -/
def sepSubq : ClosedFormula Symbol :=
  .all (.all (subsetOf (separate (.var (.vs .vz)) (.var .vz)) (.var (.vs .vz))))

theorem sep_subq_valid : model.{u}.models sepSubq := by
  intro a _ P _ x _ hx
  change ZFSet.{u} at a
  change ZFSet.{u} at x
  change ZFSet.{u} → ULift.{u + 1} Prop at P
  have hxSep : x ∈ ZFSet.sep (fun y => (P y).down) a := hx
  change x ∈ a
  exact (ZFSet.mem_sep.mp hxSep).1

/-- A member of a member of a set belongs to the union. -/
def unionIntro : ClosedFormula Symbol :=
  .all (.all (.all (.imp
    (member (.var (.vs .vz)) (.var .vz))
    (.imp
      (member (.var .vz) (.var (.vs (.vs .vz))))
      (member (.var (.vs .vz)) (.app (.const .union) (.var (.vs (.vs .vz)))))))))

theorem union_intro_valid : model.{u}.models unionIntro := by
  intro a _ x _ y _ hxy hya
  exact ZFSet.mem_sUnion.mpr ⟨y, hya, hxy⟩

/-- Membership in a union is the impredicative existence of a member. -/
def unionElim : ClosedFormula Symbol :=
  .all (.all (.imp
    (member (.var .vz) (.app (.const .union) (.var (.vs .vz))))
    (.all (.imp
      (.all (.imp
        (member (.var .vz) (.var (.vs (.vs (.vs .vz)))))
        (.imp (member (.var (.vs (.vs .vz))) (.var .vz)) (.var (.vs .vz)))))
      (.var .vz)))))

theorem union_elim_valid : model.{u}.models unionElim := by
  intro a _ x _ hx p _ hyp
  rcases ZFSet.mem_sUnion.mp hx with ⟨y, hya, hxy⟩
  exact hyp y trivial hya hxy

/-- The value of a map at a member belongs to the replacement. The equation is signature `eq`. -/
def replIntro : ClosedFormula Symbol :=
  .all (.all (.all (.all (.imp
    (member (.var (.vs .vz)) (.var (.vs (.vs (.vs .vz)))))
    (.imp
      (.eq (.app (.var (.vs (.vs .vz))) (.var (.vs .vz))) (.var .vz))
      (member (.var .vz) (replace (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz))))))))))

theorem repl_intro_valid : model.{u}.models replIntro := by
  intro a _ F _ x _ y _ hx heq
  exact mem_replacement.mpr ⟨x, hx, heq⟩

/-- Signature `eq` of a set with itself. In this model that `eq` is identity. -/
def eqRefl : ClosedFormula Symbol :=
  .all (show Formula Symbol (set :: []) from .eq (.var .vz) (.var .vz))

theorem eq_refl_valid : model.{u}.models eqRefl := by
  intro x _
  rfl

/-- Two inclusions give signature `eq`. In this model that `eq` is identity. -/
def setExt : ClosedFormula Symbol :=
  .all (.all (.imp
    (subsetOf (.var (.vs .vz)) (.var .vz))
    (.imp
      (subsetOf (.var .vz) (.var (.vs .vz)))
      (.eq (.var (.vs .vz)) (.var .vz)))))

theorem set_ext_valid : model.{u}.models setExt := by
  intro X _ Y _ hXY hYX
  exact ZFSet.ext fun z => ⟨fun hz => hXY z trivial hz, fun hz => hYX z trivial hz⟩

/-- Leibniz `same` is reflexive. -/
def sameRefl : ClosedFormula Symbol :=
  .all (same (.var .vz) (.var .vz))

theorem same_refl_valid : model.{u}.models sameRefl := by
  intro x _ P _ hP
  exact hP

/-- Leibniz `same` is symmetric. -/
def sameSym : ClosedFormula Symbol :=
  .all (.all (.imp
    (same (.var (.vs .vz)) (.var .vz))
    (same (.var .vz) (.var (.vs .vz)))))

theorem same_sym_valid : model.{u}.models sameSym := by
  intro x _ y _ h
  change ZFSet.{u} at x
  change ZFSet.{u} at y
  change ∀ P : ZFSet.{u} → ULift.{u + 1} Prop, True → (P x).down → (P y).down at h
  have hxy : x = y := (same_adm_iff_eq).mp h
  subst hxy
  intro P _ hP
  exact hP

/-- Leibniz `same` is transitive. -/
def sameTrans : ClosedFormula Symbol :=
  .all (.all (.all (.imp
    (same (.var (.vs (.vs .vz))) (.var (.vs .vz)))
    (.imp
      (same (.var (.vs .vz)) (.var .vz))
      (same (.var (.vs (.vs .vz))) (.var .vz))))))

theorem same_trans_valid : model.{u}.models sameTrans := by
  intro x _ y _ z _ hxy hyz
  change ZFSet.{u} at x
  change ZFSet.{u} at y
  change ZFSet.{u} at z
  change ∀ P : ZFSet.{u} → ULift.{u + 1} Prop, True → (P x).down → (P y).down at hxy
  change ∀ P : ZFSet.{u} → ULift.{u + 1} Prop, True → (P y).down → (P z).down at hyz
  have hxz : x = z := ((same_adm_iff_eq).mp hxy).trans ((same_adm_iff_eq).mp hyz)
  subst hxz
  intro P _ hP
  exact hP

/-- Leibniz `same` implies signature `eq`. In this model that `eq` is identity. -/
def sameToEq : ClosedFormula Symbol :=
  .all (.all (.imp
    (same (.var (.vs .vz)) (.var .vz))
    (.eq (.var (.vs .vz)) (.var .vz))))

theorem same_to_eq_valid : model.{u}.models sameToEq := by
  intro x _ y _ h
  change ZFSet.{u} at x
  change ZFSet.{u} at y
  change ∀ P : ZFSet.{u} → ULift.{u + 1} Prop, True → (P x).down → (P y).down at h
  exact (same_adm_iff_eq).mp h

/-- Substitution of signature `eq` at `set`, with the sets outside the predicate.
`∀ a b. eq a b → ∀ P. P a → P b`. In this model that `eq` is identity. -/
def eqSubst : ClosedFormula Symbol :=
  .all (show Formula Symbol (set :: []) from
    .all (.imp
      (.eq (.var (.vs .vz)) (.var .vz))
      (.all (.imp
        (.app (.var .vz) (.var (.vs (.vs .vz))))
        (.app (.var .vz) (.var (.vs .vz)))))))

theorem eq_subst_valid : model.{u}.models eqSubst := by
  intro a _ b _ hab P _ hP
  have hab' : a = b := hab
  exact hab' ▸ hP

/-- The same sentence in every Henkin model of this signature. Base equality is identity,
so the set laws are not a hypothesis. -/
theorem eq_subst_valid_any_model (M : HenkinModel.{0, 0, u + 1} Unit Symbol) :
    M.models eqSubst := by
  intro a _ b _ hab P _ hP
  have hab' : a = b := hab
  exact hab' ▸ hP

/-- Substitution of signature `eq` at `set`, with the predicate outside the sets.
`∀ P a b. eq a b → P a → P b`. This is the per-carrier substitution axiom at `set`. -/
def substSet : ClosedFormula Symbol :=
  .all (show Formula Symbol (predicate :: []) from
    .all (.all (.imp
      (.eq (.var (.vs .vz)) (.var .vz))
      (.imp
        (.app (.var (.vs (.vs .vz))) (.var (.vs .vz)))
        (.app (.var (.vs (.vs .vz))) (.var .vz))))))

theorem subst_set_valid : model.{u}.models substSet := by
  intro P _ a _ b _ hab hP
  have hab' : a = b := hab
  exact hab' ▸ hP

/-- The two binder orders are the same validity. -/
theorem eq_subst_iff_subst_set :
    model.{u}.models eqSubst ↔ model.{u}.models substSet := by
  constructor
  · intro h P _ a _ b _ hab hP
    exact h a trivial b trivial hab P trivial hP
  · intro h a _ b _ hab P _ hP
    exact h P trivial a trivial b trivial hab hP

/-- Two inclusions give Leibniz `same`. `setExt` gives signature `eq` from the same inclusions. -/
def sameExt : ClosedFormula Symbol :=
  .all (.all (.imp
    (subsetOf (.var (.vs .vz)) (.var .vz))
    (.imp
      (subsetOf (.var .vz) (.var (.vs .vz)))
      (same (.var (.vs .vz)) (.var .vz)))))

theorem same_ext_valid : model.{u}.models sameExt := by
  intro X _ Y _ hXY hYX
  change ZFSet.{u} at X
  change ZFSet.{u} at Y
  have hXYY : X = Y :=
    ZFSet.ext fun z => ⟨fun hz => hXY z trivial hz, fun hz => hYX z trivial hz⟩
  subst hXYY
  intro P _ hP
  exact hP

/-- Signature `eq` implies Leibniz `same`. The converse sentence is `sameToEq`. -/
def eqToSame : ClosedFormula Symbol :=
  .all (.all (.imp
    (.eq (.var (.vs .vz)) (.var .vz))
    (same (.var (.vs .vz)) (.var .vz))))

theorem eq_to_same_valid : model.{u}.models eqToSame := by
  intro x _ y _ h
  change ZFSet.{u} at x
  change ZFSet.{u} at y
  have hxy : x = y := h
  subst hxy
  intro P _ hP
  exact hP

/-- Signature `eq` agrees with Leibniz `same`. On the carrier, `same_iff_eq` is `same`
if and only if identity. -/
def eqIffSame : ClosedFormula Symbol :=
  .all (.all (iffFormula
    (.eq (.var (.vs .vz)) (.var .vz))
    (same (.var (.vs .vz)) (.var .vz))))

theorem eq_iff_same_valid : model.{u}.models eqIffSame := by
  intro x _ y _
  constructor
  · intro h
    change ZFSet.{u} at x
    change ZFSet.{u} at y
    have hxy : x = y := h
    subst hxy
    intro P _ hP
    exact hP
  · intro h
    change ZFSet.{u} at x
    change ZFSet.{u} at y
    change ∀ P : ZFSet.{u} → ULift.{u + 1} Prop, True → (P x).down → (P y).down at h
    exact (same_adm_iff_eq).mp h

/-- A proposition equivalent to its negation is absurd. -/
def iffNotAbsurd : ClosedFormula Symbol :=
  .all (.not (iffFormula (.var .vz) (.not (.var .vz))))

theorem iff_not_absurd_valid : model.{u}.models iffNotAbsurd := by
  intro A _ h
  have hA : A.down := h.2 (fun a => h.1 a a)
  exact h.1 hA hA

/-- The singleton of a member is included in the set. -/
def singSubq : ClosedFormula Symbol :=
  .all (.all (.imp
    (member (.var (.vs .vz)) (.var .vz))
    (subsetOf (singTerm (.var (.vs .vz))) (.var .vz))))

theorem sing_subq_valid : model.{u}.models singSubq := by
  intro x _ S _ hx w _ hw
  change ZFSet.{u} at x
  change ZFSet.{u} at S
  change ZFSet.{u} at w
  have hwSep : w ∈ ZFSet.sep (fun t =>
      ∀ P : ZFSet.{u} → ULift.{u + 1} Prop, True → (P t).down → (P x).down)
      (ZFSet.powerset x) := hw
  have hwx : w = x := (same_adm_iff_eq).mp (ZFSet.mem_sep.mp hwSep).2
  rw [hwx]
  exact hx

/-- An ordinal is a transitive set. -/
def ordinalTransset : ClosedFormula Symbol :=
  .all (.imp (ordinalFormula (.var .vz)) (transSet (.var .vz)))

theorem ordinal_transset_valid : model.{u}.models ordinalTransset := by
  intro a _ h
  exact h.1

/-- A member of an ordinal is a transitive set. -/
def ordinalMemberTransset : ClosedFormula Symbol :=
  .all (.all (.imp
    (ordinalFormula (.var (.vs .vz)))
    (.imp (member (.var .vz) (.var (.vs .vz))) (transSet (.var .vz)))))

theorem ordinal_member_transset_valid : model.{u}.models ordinalMemberTransset := by
  intro a _ b _ ha hb
  exact ha.2 b trivial hb

/-- Induction along membership inside a transitive set. -/
def transsetInduction : ClosedFormula Symbol :=
  .all (.imp (transSet (.var .vz))
    (.all (.imp
      (.all (.imp
        (member (.var .vz) (.var (.vs (.vs .vz))))
        (.imp
          (.all (.imp
            (member (.var .vz) (.var (.vs .vz)))
            (.app (.var (.vs (.vs .vz))) (.var .vz))))
          (.app (.var (.vs .vz)) (.var .vz)))))
      (.all (.imp
        (member (.var .vz) (.var (.vs (.vs .vz))))
        (.app (.var (.vs .vz)) (.var .vz)))))))

theorem transset_induction_valid : model.{u}.models transsetInduction := by
  intro a _ ht P _ hstep x _ hx
  change ZFSet.{u} at a
  change ZFSet.{u} at x
  change ZFSet.{u} → ULift.{u + 1} Prop at P
  have hxIn : x ∈ a := hx
  have step : ∀ z : ZFSet.{u}, z ∈ a → (P z).down :=
    fun z => ZFSet.inductionOn (p := fun w => w ∈ a → (P w).down) z
      (fun b ih hb =>
        hstep b trivial hb (fun y _ hy => ih y hy (ht b trivial hb y trivial hy)))
  exact step x hxIn

/-- Membership is a strict order on an ordinal: irreflexive and transitive on its members. -/
def ordinalStrictOrder : ClosedFormula Symbol :=
  .all (.imp (ordinalFormula (.var .vz))
    (.and
      (.all (.imp (member (.var .vz) (.var (.vs .vz)))
        (.not (member (.var .vz) (.var .vz)))))
      (.all (.all (.all (.imp
        (member (.var (.vs (.vs .vz))) (.var (.vs (.vs (.vs .vz)))))
        (.imp (member (.var (.vs .vz)) (.var (.vs (.vs (.vs .vz)))))
          (.imp (member (.var .vz) (.var (.vs (.vs (.vs .vz)))))
            (.imp (member (.var (.vs (.vs .vz))) (.var (.vs .vz)))
              (.imp (member (.var (.vs .vz)) (.var .vz))
                (member (.var (.vs (.vs .vz))) (.var .vz))))))))))))

theorem ordinal_strict_order_valid : model.{u}.models ordinalStrictOrder := by
  intro a _ ha
  constructor
  · intro x _ _
    exact ZFSet.mem_irrefl x
  · intro x _ y _ z _ _ _ hz hxy hyz
    exact ha.2 z trivial hz y trivial hyz x trivial hxy

/-- A strict order is asymmetric. `R` is a relation of the logic. -/
def strictOrderAsym : ClosedFormula Symbol :=
  .all (.all (.imp
    (.and
      (.all (.imp
        (member (.var .vz) (.var (.vs .vz)))
        (.not (.app (.app (.var (.vs (.vs .vz))) (.var .vz)) (.var .vz)))))
      (.all (.all (.all (.imp
        (member (.var (.vs (.vs .vz))) (.var (.vs (.vs (.vs .vz)))))
        (.imp
          (member (.var (.vs .vz)) (.var (.vs (.vs (.vs .vz)))))
          (.imp
            (member (.var .vz) (.var (.vs (.vs (.vs .vz)))))
            (.imp
              (.app (.app (.var (.vs (.vs (.vs (.vs .vz))))) (.var (.vs (.vs .vz)))) (.var (.vs .vz)))
              (.imp
                (.app (.app (.var (.vs (.vs (.vs (.vs .vz))))) (.var (.vs .vz))) (.var .vz))
                (.app (.app (.var (.vs (.vs (.vs (.vs .vz))))) (.var (.vs (.vs .vz))))
                  (.var .vz)))))))))))
    (.all (.all (.imp
      (member (.var (.vs .vz)) (.var (.vs (.vs .vz))))
      (.imp
        (member (.var .vz) (.var (.vs (.vs .vz))))
        (.imp
          (.app (.app (.var (.vs (.vs (.vs .vz)))) (.var (.vs .vz))) (.var .vz))
          (.not
            (.app (.app (.var (.vs (.vs (.vs .vz)))) (.var .vz)) (.var (.vs .vz)))))))))))

theorem strict_order_asym_valid : model.{u}.models strictOrderAsym := by
  intro R _ A _ h x _ y _ hx hy hxy hyx
  exact h.1 x trivial hx
    (h.2 x trivial y trivial x trivial hx hy hx hxy hyx)

/-! ## The reading in the tower -/

section Ambient

variable {L : Type} [LevelOrder L]
variable (large : CofinalInaccessibles.{u + 1})
variable {ground : ZFSet.{u + 1}} {ν : Nat → Above L}

theorem holds_of_valid {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts)
    {φ : ClosedFormula Symbol} (valid : model.{u}.models φ) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed φ))) Fin.elim0 :=
  holds_embed_of_valid large reads valid

theorem false_in_model {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts)
    {φ : ClosedFormula Symbol} (false : ¬ model.{u}.models φ) (z : ZFSet.{u + 1}) :
    z ∉ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed φ))) Fin.elim0 := by
  intro inside
  rw [ev_holds_embed large reads] at inside
  exact false ((mem_truthCode _ _).mp inside).2

theorem inIrrefl_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed inIrrefl))) Fin.elim0 :=
  holds_of_valid large reads inIrrefl_valid

theorem inAsym_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed inAsym))) Fin.elim0 :=
  holds_of_valid large reads inAsym_valid

theorem russell_false_in_model {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) (z : ZFSet.{u + 1}) :
    z ∉ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed russellExistence))) Fin.elim0 :=
  false_in_model large reads russell_false z

theorem identity_onto_self_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed identityOntoSelf))) Fin.elim0 :=
  holds_of_valid large reads identity_onto_self_valid

theorem cantor_fn_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed cantorFn))) Fin.elim0 :=
  holds_of_valid large reads cantor_fn_valid

theorem kuratowski_inj_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed kuratowskiInj))) Fin.elim0 :=
  holds_of_valid large reads kuratowski_inj_valid

theorem kuratowski_cong_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed kuratowskiCong))) Fin.elim0 :=
  holds_of_valid large reads kuratowski_cong_valid

theorem buraliForti_false_in_model {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) (z : ZFSet.{u + 1}) :
    z ∉ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed buraliFortiExistence))) Fin.elim0 :=
  false_in_model large reads buraliForti_false z

theorem sing_intro_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed singIntro))) Fin.elim0 :=
  holds_of_valid large reads sing_intro_valid

theorem sing_elim_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed singElim))) Fin.elim0 :=
  holds_of_valid large reads sing_elim_valid

theorem sing_inj_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed singInj))) Fin.elim0 :=
  holds_of_valid large reads sing_inj_valid

theorem empty_ordinal_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed emptyOrdinal))) Fin.elim0 :=
  holds_of_valid large reads empty_ordinal_valid

theorem ordinal_hered_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed ordinalHered))) Fin.elim0 :=
  holds_of_valid large reads ordinal_hered_valid

theorem transset_power_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed transsetPower))) Fin.elim0 :=
  holds_of_valid large reads transset_power_valid

theorem transset_union_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed transsetUnion))) Fin.elim0 :=
  holds_of_valid large reads transset_union_valid

theorem ordinal_union_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed ordinalUnion))) Fin.elim0 :=
  holds_of_valid large reads ordinal_union_valid

theorem subq_refl_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed subqRefl))) Fin.elim0 :=
  holds_of_valid large reads subq_refl_valid

theorem subq_trans_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed subqTrans))) Fin.elim0 :=
  holds_of_valid large reads subq_trans_valid

theorem power_intro_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed powerIntro))) Fin.elim0 :=
  holds_of_valid large reads power_intro_valid

theorem power_elim_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed powerElim))) Fin.elim0 :=
  holds_of_valid large reads power_elim_valid

theorem empty_subq_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed emptySubq))) Fin.elim0 :=
  holds_of_valid large reads empty_subq_valid

theorem sep_intro_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed sepIntro))) Fin.elim0 :=
  holds_of_valid large reads sep_intro_valid

theorem sep_elim_in_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed sepElimIn))) Fin.elim0 :=
  holds_of_valid large reads sep_elim_in_valid

theorem sep_elim_prop_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed sepElimProp))) Fin.elim0 :=
  holds_of_valid large reads sep_elim_prop_valid

theorem sep_subq_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed sepSubq))) Fin.elim0 :=
  holds_of_valid large reads sep_subq_valid

theorem union_intro_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed unionIntro))) Fin.elim0 :=
  holds_of_valid large reads union_intro_valid

theorem union_elim_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed unionElim))) Fin.elim0 :=
  holds_of_valid large reads union_elim_valid

theorem repl_intro_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed replIntro))) Fin.elim0 :=
  holds_of_valid large reads repl_intro_valid

theorem eq_refl_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed eqRefl))) Fin.elim0 :=
  holds_of_valid large reads eq_refl_valid

theorem set_ext_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed setExt))) Fin.elim0 :=
  holds_of_valid large reads set_ext_valid

theorem same_refl_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed sameRefl))) Fin.elim0 :=
  holds_of_valid large reads same_refl_valid

theorem same_sym_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed sameSym))) Fin.elim0 :=
  holds_of_valid large reads same_sym_valid

theorem same_trans_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed sameTrans))) Fin.elim0 :=
  holds_of_valid large reads same_trans_valid

theorem same_to_eq_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed sameToEq))) Fin.elim0 :=
  holds_of_valid large reads same_to_eq_valid

theorem eq_subst_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed eqSubst))) Fin.elim0 :=
  holds_of_valid large reads eq_subst_valid

theorem subst_set_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed substSet))) Fin.elim0 :=
  holds_of_valid large reads subst_set_valid

theorem same_ext_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed sameExt))) Fin.elim0 :=
  holds_of_valid large reads same_ext_valid

theorem eq_to_same_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed eqToSame))) Fin.elim0 :=
  holds_of_valid large reads eq_to_same_valid

theorem eq_iff_same_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed eqIffSame))) Fin.elim0 :=
  holds_of_valid large reads eq_iff_same_valid

theorem iff_not_absurd_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed iffNotAbsurd))) Fin.elim0 :=
  holds_of_valid large reads iff_not_absurd_valid

theorem sing_subq_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed singSubq))) Fin.elim0 :=
  holds_of_valid large reads sing_subq_valid

theorem ordinal_transset_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed ordinalTransset))) Fin.elim0 :=
  holds_of_valid large reads ordinal_transset_valid

theorem ordinal_member_transset_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed ordinalMemberTransset))) Fin.elim0 :=
  holds_of_valid large reads ordinal_member_transset_valid

theorem transset_induction_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed transsetInduction))) Fin.elim0 :=
  holds_of_valid large reads transset_induction_valid

theorem ordinal_strict_order_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed ordinalStrictOrder))) Fin.elim0 :=
  holds_of_valid large reads ordinal_strict_order_valid

theorem strict_order_asym_holds {consts : DeclName → ZFSet.{u + 1}}
    {around : ZFSet.{u + 1} → ZFSet.{u + 1}}
    (reads : Reads L (stages (L := L) large (.above 0)) (stages (L := L) large (.above 1))
      around consts) :
    (∅ : ZFSet.{u + 1}) ∈ ev (lowerSetsHeads (L := L) large ground ν) consts
      (cHolds (trTerm (embed strictOrderAsym))) Fin.elim0 :=
  holds_of_valid large reads strict_order_asym_valid

end Ambient

end Curriculum
end MegalodonHOTG
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
