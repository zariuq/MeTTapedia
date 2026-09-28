import Mettapedia.TypeTheory.MaterialSets.Hypersets.MembershipEvidence

/-!
# Grothendieck universes of well-founded hypersets

A Grothendieck universe of well-founded sets (`IsGrothendieckUniverse`) is a transitive set
closed under union, power set, unordered pairs and dependent replacement. Pairing is a closure
law of its own: it is not obtained from the others by a case split on membership.

Closure under dependent replacement needs no presentation of hypersets by graphs: a family whose
values lie in the universe `U` has its image separated from `U` (`imageWithin`), and this is the
image of every presentation (`IsGrothendieckUniverse.dependentReplacement_mem`).

**The least universe.** The members of an enclosing universe `B ∋ N` that lie in every universe
containing `N` form a universe (`hull_isGrothendieckUniverse`), the least one containing `N`
(`hull_minimal`), independent of `B` (`hull_independent`). An operation `enclose` placing every
set in some universe (`UniverseEnclosure`) therefore yields `univOf`, with the four universe laws
(`UniverseEnclosure.isUniverseOperator`):

* `N ∈ univOf N`;
* `univOf N` is transitive;
* `univOf N` is closed under union, power set, pairing and dependent replacement;
* `univOf N` is contained in every universe that contains `N`.

The laws determine the operation (`IsUniverseOperator.unique`), so `univOf` does not depend on
the enclosure (`UniverseEnclosure.univOf_independent`). It is monotone
(`IsUniverseOperator.mono`).

No choice is used. Whether an enclosure exists is a large-cardinal question, settled in
`Hypersets.ZFSetUniverses` under an explicit hypothesis.

**Controls.**
* The empty set is a universe (`isGrothendieckUniverse_empty`); `{∅}` is not, since it lacks
  `𝒫 ∅ = {∅}` (`not_isGrothendieckUniverse_singleton_empty`).
* Membership of a set in its universe does not give closure: `N ↦ {N}` satisfies the first law
  (`mem_singleton_self`), yet the power-set step fails for it (`closure_needed`), so it is not a
  universe operation (`singleton_not_isUniverseOperator`).
* The operation moves strictly outward: `univOf N ≠ N` and `univOf (univOf N) ≠ univOf N`
  (`IsUniverseOperator.univOf_ne_self`, `IsUniverseOperator.univOf_univOf_ne`).

M. Artin, A. Grothendieck and J.-L. Verdier, *Théorie des topos et cohomologie étale des schémas*
(SGA 4), Exposé I, Appendice: Univers, Lecture Notes in Mathematics 269, 1972;
C. E. Brown, C. Kaliszyk and K. Pąk, *Higher-Order Tarski Grothendieck as a Foundation for Formal
Proof*, ITP 2019.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

universe u

namespace WellFoundedPart

open HSet

/-! ## Operations on the well-founded part -/

/-- The union of the members. -/
def sUnion (X : WellFoundedPart.{u}) : WellFoundedPart.{u} :=
  ⟨HSet.sUnion X.1, X.2.sUnion⟩

/-- The power set. -/
def powerset (X : WellFoundedPart.{u}) : WellFoundedPart.{u} :=
  ⟨HSet.powerset X.1, X.2.powerset⟩

/-- The unordered pair. -/
def upair (x y : WellFoundedPart.{u}) : WellFoundedPart.{u} :=
  ⟨{x.1, y.1}, x.2.pair y.2⟩

/-- The singleton. -/
def singleton (x : WellFoundedPart.{u}) : WellFoundedPart.{u} :=
  ⟨{x.1}, x.2.singleton⟩

/-- Separation. -/
def sep (P : HSet.{u} → Prop) (X : WellFoundedPart.{u}) : WellFoundedPart.{u} :=
  ⟨HSet.sep P X.1, X.2.sep P⟩

/-- The family on the members of `X.1` induced by a family on the members of `X`. -/
def toHSetFamily {X : WellFoundedPart.{u}} (F : El Mem X → WellFoundedPart.{u}) :
    El (· ∈ ·) X.1 → HSet.{u} :=
  fun a => (F ⟨⟨a.1, X.2.mem a.2⟩, a.2⟩).1

/-- Dependent replacement below a bound: the values of `F` that are members of `B`. -/
def imageWithin (B X : WellFoundedPart.{u}) (F : El Mem X → WellFoundedPart.{u}) :
    WellFoundedPart.{u} :=
  ⟨HSet.imageWithin B.1 X.1 (toHSetFamily F), B.2.sep _⟩

/-- A subset of the well-founded part. -/
def Subset (X Y : WellFoundedPart.{u}) : Prop :=
  ∀ ⦃z : HSet.{u}⦄, z ∈ X.1 → z ∈ Y.1

theorem subset_antisymm {X Y : WellFoundedPart.{u}} (hXY : Subset X Y) (hYX : Subset Y X) :
    X = Y :=
  Subtype.ext (HSet.ext fun _ => ⟨fun h => hXY h, fun h => hYX h⟩)

variable {x y X Y B C : WellFoundedPart.{u}} {z : HSet.{u}}

theorem mem_sUnion : z ∈ (sUnion X).1 ↔ ∃ W ∈ X.1, z ∈ W :=
  HSet.mem_sUnion

theorem mem_powerset : z ∈ (powerset X).1 ↔ z ⊆ X.1 :=
  HSet.mem_powerset

theorem mem_upair : z ∈ (upair x y).1 ↔ z = x.1 ∨ z = y.1 :=
  HSet.mem_pair

theorem mem_singleton : z ∈ (singleton x).1 ↔ z = x.1 :=
  HSet.mem_singleton

theorem mem_sep {P : HSet.{u} → Prop} : z ∈ (sep P X).1 ↔ z ∈ X.1 ∧ P z :=
  HSet.mem_sep

theorem mem_imageWithin {F : El Mem X → WellFoundedPart.{u}} (bound : ∀ a, Mem (F a) B) :
    Mem y (imageWithin B X F) ↔ ∃ a, F a = y := by
  change y.1 ∈ HSet.imageWithin B.1 X.1 (toHSetFamily F) ↔ _
  rw [HSet.mem_imageWithin (F := toHSetFamily F) fun a => bound ⟨⟨a.1, X.2.mem a.2⟩, a.2⟩]
  constructor
  · rintro ⟨a, e⟩
    exact ⟨_, Subtype.ext e⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a.1.1, a.2⟩, rfl⟩

/-- Below two bounds collecting its values, a family has the same image. -/
theorem imageWithin_eq {F : El Mem X → WellFoundedPart.{u}} (hB : ∀ a, Mem (F a) B)
    (hC : ∀ a, Mem (F a) C) : imageWithin B X F = imageWithin C X F := by
  refine subset_antisymm (fun w hw => ?_) (fun w hw => ?_)
  · have hwf : w.WF := (imageWithin B X F).2.mem hw
    exact (mem_imageWithin (y := ⟨w, hwf⟩) hC).mpr ((mem_imageWithin (y := ⟨w, hwf⟩) hB).mp hw)
  · have hwf : w.WF := (imageWithin C X F).2.mem hw
    exact (mem_imageWithin (y := ⟨w, hwf⟩) hB).mpr ((mem_imageWithin (y := ⟨w, hwf⟩) hC).mp hw)

/-- Below a bound collecting its values, a family has the image given by any presentation. -/
theorem dependentReplacement_image_eq (p : Presentation.{u}) {F : El Mem X → WellFoundedPart.{u}}
    (bound : ∀ a, Mem (F a) B) : (dependentReplacement p).image X F = imageWithin B X F :=
  Subtype.ext (HSet.image_eq_imageWithin p (F := toHSetFamily F)
    fun a => bound ⟨⟨a.1, X.2.mem a.2⟩, a.2⟩)

/-! ## Grothendieck universes -/

/-- A Grothendieck universe of well-founded sets: a transitive set closed under union, power
set, unordered pairs and dependent replacement. -/
structure IsGrothendieckUniverse (U : WellFoundedPart.{u}) : Prop where
  /-- Members of members are members. -/
  transitive : ∀ ⦃X : WellFoundedPart.{u}⦄ ⦃z : HSet.{u}⦄, Mem X U → z ∈ X.1 → z ∈ U.1
  /-- Closure under union. -/
  sUnion_mem : ∀ ⦃X⦄, Mem X U → Mem (sUnion X) U
  /-- Closure under power set. -/
  powerset_mem : ∀ ⦃X⦄, Mem X U → Mem (powerset X) U
  /-- Closure under unordered pairs. -/
  upair_mem : ∀ ⦃x y⦄, Mem x U → Mem y U → Mem (upair x y) U
  /-- Closure under dependent replacement. -/
  image_mem : ∀ ⦃X⦄, Mem X U → ∀ F : El Mem X → WellFoundedPart.{u},
    (∀ a, Mem (F a) U) → Mem (imageWithin U X F) U

namespace IsGrothendieckUniverse

variable {U : WellFoundedPart.{u}} (hU : IsGrothendieckUniverse U)
include hU

theorem subset_of_mem (hX : Mem X U) : Subset X U :=
  fun _ hz => hU.transitive hX hz

theorem singleton_mem (hx : Mem x U) : Mem (singleton x) U := by
  have same : upair x x = singleton x :=
    Subtype.ext (HSet.ext fun _ => mem_upair.trans (or_self_iff.trans mem_singleton.symm))
  exact same ▸ hU.upair_mem hx hx

theorem sep_mem (hX : Mem X U) (P : HSet.{u} → Prop) : Mem (sep P X) U :=
  hU.transitive (X := powerset X) (hU.powerset_mem hX)
    (mem_powerset.mpr fun _ hz => (mem_sep.mp hz).1)

/-- Closure under the dependent replacement of every presentation. -/
theorem dependentReplacement_mem (p : Presentation.{u}) (hX : Mem X U)
    (F : El Mem X → WellFoundedPart.{u}) (hF : ∀ a, Mem (F a) U) : Mem ((dependentReplacement p).image X F) U := by
  rw [dependentReplacement_image_eq p hF]
  exact hU.image_mem hX F hF

/-- Kuratowski pairs of members are members. -/
theorem kpair_mem (hx : Mem x U) (hy : Mem y U) : Mem (pairing.pair x y) U := by
  change kpair x.1 y.1 ∈ U.1
  exact hU.upair_mem (x := singleton x) (y := upair x y) (hU.singleton_mem hx)
    (hU.upair_mem hx hy)

end IsGrothendieckUniverse

/-- The empty set is a Grothendieck universe. -/
theorem isGrothendieckUniverse_empty : IsGrothendieckUniverse empty.{u} where
  transitive _ _ h _ := absurd h (notMem_empty _)
  sUnion_mem _ h := absurd h (notMem_empty _)
  powerset_mem _ h := absurd h (notMem_empty _)
  upair_mem _ _ h _ := absurd h (notMem_empty _)
  image_mem _ h _ _ := absurd h (notMem_empty _)

theorem powerset_empty : powerset empty.{u} = singleton empty :=
  Subtype.ext HSet.powerset_empty

/-- `{∅}` is not a universe: it does not contain `𝒫 ∅ = {∅}`. -/
theorem not_isGrothendieckUniverse_singleton_empty :
    ¬ IsGrothendieckUniverse (singleton empty.{u}) := fun hU => by
  have h := hU.powerset_mem (X := empty) (mem_singleton.mpr rfl)
  rw [powerset_empty] at h
  exact empty_ne_singleton_empty (mem_singleton.mp h).symm

/-! ## The least universe containing a set -/

/-- The members of `B` that lie in every universe containing `N`. -/
def hull (N B : WellFoundedPart.{u}) : WellFoundedPart.{u} :=
  sep (fun x => ∀ U : WellFoundedPart.{u}, Mem N U → IsGrothendieckUniverse U → x ∈ U.1) B

theorem mem_hull {N : WellFoundedPart.{u}} :
    z ∈ (hull N B).1 ↔
      z ∈ B.1 ∧ ∀ U : WellFoundedPart.{u}, Mem N U → IsGrothendieckUniverse U → z ∈ U.1 :=
  mem_sep

theorem mem_hull_self {N : WellFoundedPart.{u}} (hN : Mem N B) : Mem N (hull N B) :=
  mem_hull.mpr ⟨hN, fun _ h _ => h⟩

theorem hull_minimal {N U : WellFoundedPart.{u}} (hN : Mem N U) (hU : IsGrothendieckUniverse U) :
    Subset (hull N B) U :=
  fun _ hz => (mem_hull.mp hz).2 U hN hU

theorem hull_subset (N : WellFoundedPart.{u}) : Subset (hull N B) B :=
  fun _ hz => (mem_hull.mp hz).1

/-- Inside a universe, the least universe containing `N` is a universe. -/
theorem hull_isGrothendieckUniverse {N : WellFoundedPart.{u}} (hB : IsGrothendieckUniverse B) :
    IsGrothendieckUniverse (hull N B) where
  transitive X z hX hz := by
    obtain ⟨hXB, hXall⟩ := mem_hull.mp hX
    exact mem_hull.mpr ⟨hB.transitive hXB hz, fun U hN hU => hU.transitive (hXall U hN hU) hz⟩
  sUnion_mem X hX := by
    obtain ⟨hXB, hXall⟩ := mem_hull.mp hX
    exact mem_hull.mpr ⟨hB.sUnion_mem hXB, fun U hN hU => hU.sUnion_mem (hXall U hN hU)⟩
  powerset_mem X hX := by
    obtain ⟨hXB, hXall⟩ := mem_hull.mp hX
    exact mem_hull.mpr ⟨hB.powerset_mem hXB, fun U hN hU => hU.powerset_mem (hXall U hN hU)⟩
  upair_mem x y hx hy := by
    obtain ⟨hxB, hxall⟩ := mem_hull.mp hx
    obtain ⟨hyB, hyall⟩ := mem_hull.mp hy
    exact mem_hull.mpr ⟨hB.upair_mem hxB hyB,
      fun U hN hU => hU.upair_mem (hxall U hN hU) (hyall U hN hU)⟩
  image_mem X hX F hF := by
    obtain ⟨hXB, hXall⟩ := mem_hull.mp hX
    have inB : ∀ a, Mem (F a) B := fun a => (mem_hull.mp (hF a)).1
    refine mem_hull.mpr ⟨?_, fun U hN hU => ?_⟩
    · rw [imageWithin_eq hF inB]
      exact hB.image_mem hXB F inB
    · have inU : ∀ a, Mem (F a) U := fun a => (mem_hull.mp (hF a)).2 U hN hU
      rw [imageWithin_eq hF inU]
      exact hU.image_mem (hXall U hN hU) F inU

/-- The least universe containing `N` does not depend on the enclosing universe. -/
theorem hull_independent {N : WellFoundedPart.{u}} (hB : IsGrothendieckUniverse B) (hNB : Mem N B)
    (hC : IsGrothendieckUniverse C) (hNC : Mem N C) : hull N B = hull N C :=
  subset_antisymm
    (fun _ hz => hull_minimal (mem_hull_self hNC) (hull_isGrothendieckUniverse hC) hz)
    (fun _ hz => hull_minimal (mem_hull_self hNB) (hull_isGrothendieckUniverse hB) hz)

/-! ## Universe operations -/

/-- The four universe laws of an operation `univOf`, with closure including pairing. -/
structure IsUniverseOperator (univOf : WellFoundedPart.{u} → WellFoundedPart.{u}) : Prop where
  /-- `N ∈ univOf N`. -/
  mem_univOf : ∀ N, Mem N (univOf N)
  /-- `univOf N` is transitive and closed: a Grothendieck universe. -/
  isGrothendieckUniverse : ∀ N, IsGrothendieckUniverse (univOf N)
  /-- `univOf N` is contained in every universe containing `N`. -/
  minimal : ∀ ⦃N U⦄, Mem N U → IsGrothendieckUniverse U → Subset (univOf N) U

namespace IsUniverseOperator

variable {univOf univOf' : WellFoundedPart.{u} → WellFoundedPart.{u}}

/-- The universe laws determine the operation. -/
theorem unique (h : IsUniverseOperator univOf) (h' : IsUniverseOperator univOf') :
    univOf = univOf' :=
  funext fun N => subset_antisymm (h.minimal (h'.mem_univOf N) (h'.isGrothendieckUniverse N))
    (h'.minimal (h.mem_univOf N) (h.isGrothendieckUniverse N))

theorem powerset_mem (h : IsUniverseOperator univOf) {N X : WellFoundedPart.{u}}
    (hX : Mem X (univOf N)) : Mem (powerset X) (univOf N) :=
  (h.isGrothendieckUniverse N).powerset_mem hX

/-- The operation is monotone. -/
theorem mono (h : IsUniverseOperator univOf) {N M : WellFoundedPart.{u}} (hNM : Subset N M) :
    Subset (univOf N) (univOf M) := by
  have same : sep (· ∈ N.1) M = N :=
    subset_antisymm (fun _ hz => (mem_sep.mp hz).2) (fun _ hz => mem_sep.mpr ⟨hNM hz, hz⟩)
  have hN : Mem N (univOf M) :=
    same ▸ (h.isGrothendieckUniverse M).sep_mem (h.mem_univOf M) (· ∈ N.1)
  exact h.minimal hN (h.isGrothendieckUniverse M)

/-- The universe of `N` is not `N`: it contains `N`, and no well-founded set contains itself. -/
theorem univOf_ne_self (h : IsUniverseOperator univOf) (N : WellFoundedPart.{u}) :
    univOf N ≠ N := fun e => N.2.notMem_self (by
  have hN := h.mem_univOf N
  rwa [e] at hN)

theorem univOf_univOf_ne (h : IsUniverseOperator univOf) (N : WellFoundedPart.{u}) :
    univOf (univOf N) ≠ univOf N :=
  h.univOf_ne_self (univOf N)

end IsUniverseOperator

/-- An operation placing every well-founded set in a Grothendieck universe. -/
structure UniverseEnclosure : Type (u + 1) where
  /-- The enclosing universe. -/
  enclose : WellFoundedPart.{u} → WellFoundedPart.{u}
  /-- It contains its argument. -/
  mem_enclose : ∀ N, Mem N (enclose N)
  /-- It is a universe. -/
  isGrothendieckUniverse_enclose : ∀ N, IsGrothendieckUniverse (enclose N)

namespace UniverseEnclosure

variable (e e' : UniverseEnclosure.{u})

/-- The least universe containing `N`, separated from its enclosure. -/
def univOf (N : WellFoundedPart.{u}) : WellFoundedPart.{u} :=
  hull N (e.enclose N)

/-- An enclosure yields an operation with the four universe laws. -/
theorem isUniverseOperator : IsUniverseOperator e.univOf where
  mem_univOf N := mem_hull_self (e.mem_enclose N)
  isGrothendieckUniverse N := hull_isGrothendieckUniverse (e.isGrothendieckUniverse_enclose N)
  minimal _ _ hN hU := hull_minimal hN hU

/-- The operation does not depend on the enclosure. -/
theorem univOf_independent : e.univOf = e'.univOf :=
  e.isUniverseOperator.unique e'.isUniverseOperator

end UniverseEnclosure

/-! ## Membership in a universe does not give closure -/

theorem mem_singleton_self (N : WellFoundedPart.{u}) : Mem N (singleton N) :=
  mem_singleton.mpr rfl

/-- Without closure, membership of a set in its universe does not prove the power-set step:
for `univOf N = {N}`, the first law holds and the step fails at `∅`. -/
theorem closure_needed :
    ¬ ∀ N X : WellFoundedPart.{u}, Mem X (singleton N) → Mem (powerset X) (singleton N) :=
  fun h => by
    have step := h empty empty (mem_singleton_self empty)
    rw [powerset_empty] at step
    exact empty_ne_singleton_empty (mem_singleton.mp step).symm

theorem singleton_not_isUniverseOperator : ¬ IsUniverseOperator singleton.{u} :=
  fun h => closure_needed fun _ _ hX => h.powerset_mem hX

end WellFoundedPart

end Mettapedia.TypeTheory.MaterialSets.Hypersets
