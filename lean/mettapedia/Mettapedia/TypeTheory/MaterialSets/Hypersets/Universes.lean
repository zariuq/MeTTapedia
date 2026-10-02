import Mathlib.Data.Countable.Defs
import Mettapedia.TypeTheory.MaterialSets.Hypersets.MembershipEvidence
import Mettapedia.TypeTheory.UniverseLevel.Notation

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

**Towers over a level order.** The universe laws enclose one set; they do not collect a
family. A family of sets is collected (`IsCollected`) when some set has every value as a
member, and its values then form a set by separation. The family of all well-founded sets is
not collected (`not_isCollected_id`); a family presented by graphs is
(`isCollected_of_presented`).

A family of sets indexed by the levels of a level order satisfies the tower equation of an
operation `univOf` and a seed (`IsUniverseTower`) when the stage at every level is `univOf` of
the set of the seed and the earlier stages. That this set exists is a separate hypothesis,
`CollectsEarlierStages`: at every level the earlier stages are collected. It holds at the
least level and passes to successors (`isCollected_below_bot`, `isCollected_below_succ`), so
over a level order with predecessors it is an obligation at the limit levels only
(`collectsEarlierStages_of_isLimit`), and none over the natural numbers
(`collectsEarlierStages_nat`). At the first limit level `ω` of the ordinal notations it says
that the finite stages are members of one set (`isCollected_below_omega_iff`). Given a
presentation of the hypersets by graphs it holds for every family
(`collectsEarlierStages_of_presentation`), so it has content only without choice.

From the universe laws, the tower equation and the collection hypothesis: every stage is a
universe containing the seed (`IsUniverseTower.isGrothendieckUniverse`, `seed_mem`);
membership and inclusion of stages are the strict and the weak order of levels, so the tower
is injective (`mem_iff`, `subset_iff`, `injective`); the stage at the least level is the
universe of the seed, and the stage at a successor is the universe of the previous stage
(`stage_bot`, `stage_succ`); the set of the earlier stages and its union are members of the
stage and of no earlier one, the union is a stage exactly at a successor level, and the stage
at a limit level is the universe of no single stage; at a level with countably many lower
levels the stage is the least universe that has the seed and every earlier stage as members
(`subset_of_forall_mem`), and at a limit level the union of the earlier stages is then not a
universe; the same holds along a sequence of levels (`subset_of_sequence_mem`); the tower is
monotone in the seed (`seed_mono`). Two towers of one operation and seed have the same stages
(`unique`), and towers commute with initial embeddings of level orders (`map_eq`).

**Where the stages come from.** The laws above are about a given family of stages. Three
constructions give one without choice.

* Over the natural numbers the set of the seed and the earlier stages is built by insertion.
  A tower exists for every operation and seed (`natStage`, `isUniverseTower_natStage`), and
  its stages are the finite stages of every tower over every level order, with no collection
  hypothesis (`IsUniverseTower.stage_ofNat`). For a universe operation it is the iteration of
  the operation from the universe of the seed (`natStage_zero`, `natStage_succ`).
* When the operation is given on graphs (`Presents`), the stages are built as graphs by the
  recursion along the level order (`stageGraph`). Their pictures satisfy the tower equation
  and are collected by the set of their graphs (`isUniverseTower_stageGraph`,
  `collectsEarlierStages_stageGraph`). The singleton is given on graphs
  (`presents_singleton`); so is every operation once a presentation of the hypersets by
  graphs is given (`presents_ofPresentation`), and the least universe once an enclosure is
  given on graphs (`presents_hull`). The only presentation of every hyperset,
  `HSet.Presentation.choice`, is `Classical.choice`.
* Inside a universe closed under the operation, over a level order with countably many
  levels, the stages are built by the same recursion with the set of the seed and the earlier
  stages separated from that universe (`stageWithin`). They satisfy the tower equation and
  are collected by the universe, and every tower has these stages
  (`isUniverseTower_stageWithin`, `IsUniverseTower.collectsEarlierStages_of_closed`). A
  universe closed under the operation is a hypothesis beyond the universe laws.

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
* For a universe operation and a tower with collected earlier stages, every finite stage is
  a member of the stage at `ω` (`IsUniverseTower.stage_ofNat_mem_stage_omega`).
* Without closure the tower laws fail: for `N ↦ {N}` a tower with collected earlier stages
  exists over every level order, built as graphs, and none of its stages is a universe
  (`exists_singleton_tower`), in particular not the stage at the limit level `ω`
  (`exists_singleton_tower_omega`); the seed is a member of no stage
  (`IsUniverseTower.singleton_seed_notMem`).

M. Artin, A. Grothendieck and J.-L. Verdier, *Théorie des topos et cohomologie étale des schémas*
(SGA 4), Exposé I, Appendice: Univers, Lecture Notes in Mathematics 269, 1972;
C. E. Brown, C. Kaliszyk and K. Pąk, *Higher-Order Tarski Grothendieck as a Foundation for Formal
Proof*, ITP 2019.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

open Mettapedia.TypeTheory.UniverseLevel

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

/-- Every set is a subset of itself. -/
theorem Subset.refl (X : WellFoundedPart.{u}) : Subset X X :=
  fun _ hz => hz

/-- Inclusion is transitive. -/
theorem Subset.trans {X Y Z : WellFoundedPart.{u}} (hXY : Subset X Y) (hYZ : Subset Y Z) :
    Subset X Z :=
  fun _ hz => hYZ (hXY hz)

/-- Membership in the well-founded part is asymmetric. -/
theorem notMem_of_mem {x y : WellFoundedPart.{u}} (h : Mem y x) : ¬ Mem x y := by
  have asymmetric : ∀ a : HSet.{u}, a.WF → ∀ b : HSet.{u}, b ∈ a → a ∉ b := fun a ha => by
    induction ha with
    | intro a _ ih => exact fun b hba hab => ih b hba a hab hba
  exact asymmetric x.1 x.2 y.1 h

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

/-- A subset of a member of a universe is a member: it is separated from the member. -/
theorem subset_mem (hX : Mem X U) (hYX : Subset Y X) : Mem Y U := by
  have same : sep (· ∈ Y.1) X = Y :=
    subset_antisymm (fun _ hz => (mem_sep.mp hz).2) (fun _ hz => mem_sep.mpr ⟨hYX hz, hz⟩)
  exact same ▸ hU.sep_mem hX (· ∈ Y.1)

/-- A set whose members are all subsets of one member of a universe is a member of the
universe: it is a subset of a power set. -/
theorem mem_of_forall_subset (hX : Mem X U) (hY : ∀ z ∈ Y.1, z ⊆ X.1) : Mem Y U :=
  hU.subset_mem (hU.powerset_mem hX) fun z hz => mem_powerset.mpr (hY z hz)

/-- The empty set is a member of every universe that has a member. -/
theorem empty_mem (hX : Mem X U) : Mem empty U :=
  hU.subset_mem hX fun _ hz => absurd hz (notMem_empty _)

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

/-- A singleton `{N}` is not a universe: it would contain `𝒫 N`, which has `N` as a member
and so is not `N`. -/
theorem not_isGrothendieckUniverse_singleton (N : WellFoundedPart.{u}) :
    ¬ IsGrothendieckUniverse (singleton N) := fun hU => by
  have same : (powerset N).1 = N.1 := mem_singleton.mp (hU.powerset_mem (mem_singleton.mpr rfl))
  have self : N.1 ∈ (powerset N).1 := mem_powerset.mpr fun _ hz => hz
  rw [same] at self
  exact N.2.notMem_self self

/-- `{∅}` is not a universe: it does not contain `𝒫 ∅ = {∅}`. -/
theorem not_isGrothendieckUniverse_singleton_empty :
    ¬ IsGrothendieckUniverse (singleton empty.{u}) :=
  not_isGrothendieckUniverse_singleton empty

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
    Subset (univOf N) (univOf M) :=
  h.minimal ((h.isGrothendieckUniverse M).subset_mem (h.mem_univOf M) hNM)
    (h.isGrothendieckUniverse M)

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

/-! ## Collected families

The universe laws enclose one set. A family of sets is a set only when some set has every
value as a member; then its values are separated from that set. -/

/-- A family of well-founded sets is collected when some set has every value as a member. -/
def IsCollected {ι : Sort*} (F : ι → WellFoundedPart.{u}) : Prop :=
  ∃ B : WellFoundedPart.{u}, ∀ i, Mem (F i) B

/-- The family of all well-founded sets is not collected: a set with every well-founded set
as a member would be a member of itself. -/
theorem not_isCollected_id : ¬ IsCollected fun x : WellFoundedPart.{u} => x :=
  fun ⟨B, hB⟩ => B.2.notMem_self (hB B)

/-- A family presented by graphs is collected, by the set of its graphs. The index type is
lifted to the universe of the nodes. -/
theorem isCollected_of_presented {ι : Type} {F : ι → WellFoundedPart.{u}}
    (g : ι → AccessiblePointedGraph.{u}) (presents : ∀ i, HSet.mk (g i) = (F i).1) :
    IsCollected F :=
  ⟨⟨HSet.range fun i : ULift.{u} ι => g i.down,
      wf_range fun i => (presents i.down).symm ▸ (F i.down).2⟩,
    fun i => mem_range.mpr ⟨⟨i⟩, presents i⟩⟩

/-- A presentation of the hypersets by graphs collects every family indexed by a small type.
The only presentation of every hyperset, `HSet.Presentation.choice`, is `Classical.choice`. -/
theorem isCollected_of_presentation (p : Presentation.{u}) {ι : Type}
    (F : ι → WellFoundedPart.{u}) : IsCollected F :=
  isCollected_of_presented (fun i => p.graph (F i).1) fun i => p.mk_graph (F i).1

/-! ## The iterated power sets of the empty set -/

/-- The `n`-fold power set of the empty set. -/
def iteratedPowerset : Nat → WellFoundedPart.{u}
  | 0 => empty
  | n + 1 => powerset (iteratedPowerset n)

/-- Each iterated power set of the empty set is transitive. -/
theorem iteratedPowerset_transitive :
    ∀ (n : Nat) ⦃z : HSet.{u}⦄, z ∈ (iteratedPowerset n).1 → z ⊆ (iteratedPowerset n).1
  | 0, _, hz => absurd hz (notMem_empty _)
  | n + 1, _, hz => fun _ hw =>
    mem_powerset.mpr (iteratedPowerset_transitive n (mem_powerset.mp hz hw))

/-- Each iterated power set of the empty set is a member of the next. -/
theorem iteratedPowerset_mem_succ (n : Nat) :
    Mem (iteratedPowerset.{u} n) (iteratedPowerset (n + 1)) :=
  mem_powerset.mpr fun _ hz => hz

/-- An earlier iterated power set of the empty set is a member of every later one. -/
theorem iteratedPowerset_mem_of_lt :
    ∀ {m n : Nat}, m < n → Mem (iteratedPowerset.{u} m) (iteratedPowerset n)
  | m, n + 1, h =>
    (Nat.eq_or_lt_of_le (Nat.le_of_lt_succ h)).elim
      (fun e => e ▸ iteratedPowerset_mem_succ m)
      fun hlt => mem_powerset.mpr (iteratedPowerset_transitive n (iteratedPowerset_mem_of_lt hlt))

/-- Distinct numbers give distinct iterated power sets of the empty set. -/
theorem iteratedPowerset_injective {m n : Nat}
    (h : (iteratedPowerset.{u} m).1 = (iteratedPowerset n).1) : m = n := by
  rcases Nat.lt_trichotomy m n with hlt | heq | hgt
  · have hmem : (iteratedPowerset.{u} m).1 ∈ (iteratedPowerset n).1 :=
      iteratedPowerset_mem_of_lt hlt
    rw [h] at hmem
    exact absurd hmem (iteratedPowerset n).2.notMem_self
  · exact heq
  · have hmem : (iteratedPowerset.{u} n).1 ∈ (iteratedPowerset m).1 :=
      iteratedPowerset_mem_of_lt hgt
    rw [h] at hmem
    exact absurd hmem (iteratedPowerset n).2.notMem_self

/-- The iterated power sets of the empty set are members of every universe that has a
member. -/
theorem IsGrothendieckUniverse.iteratedPowerset_mem {U X : WellFoundedPart.{u}}
    (hU : IsGrothendieckUniverse U) (hX : Mem X U) : ∀ n : Nat, Mem (iteratedPowerset n) U
  | 0 => hU.empty_mem hX
  | n + 1 => hU.powerset_mem (hU.iteratedPowerset_mem hX n)

/-- Replacement along natural-number codes. In a universe `U`, the values of a family form a
member of `U` when every value is a member of `U`, the indices have injective codes in the
natural numbers, and some member of `U` has every iterated power set of the empty set as a
member. The iterated power sets of the codes are separated from that member, and each is
replaced by the value it codes. No graph of a value is chosen. -/
theorem IsGrothendieckUniverse.exists_range_mem {U W : WellFoundedPart.{u}}
    (hU : IsGrothendieckUniverse U) (hW : Mem W U) (hWn : ∀ n, Mem (iteratedPowerset n) W)
    {ι : Sort*} (code : ι → Nat) (injective : Function.Injective code)
    (F : ι → WellFoundedPart.{u}) (hF : ∀ i, Mem (F i) U) :
    ∃ E : WellFoundedPart.{u}, Mem E U ∧ ∀ z : HSet.{u}, z ∈ E.1 ↔ ∃ i, (F i).1 = z := by
  have hX : Mem (sep (fun y => ∃ i, (iteratedPowerset (code i)).1 = y) W) U :=
    hU.sep_mem hW _
  have value : ∀ (i : ι) (x : HSet.{u}), (iteratedPowerset (code i)).1 = x →
      sUnion (sep (fun y => ∃ j, (iteratedPowerset (code j)).1 = x ∧ (F j).1 = y) U) = F i :=
    fun i x hx => subset_antisymm
      (fun z hz => by
        obtain ⟨V, hV, hzV⟩ := WellFoundedPart.mem_sUnion.mp hz
        obtain ⟨-, j, hj, rfl⟩ := mem_sep.mp hV
        rw [injective (iteratedPowerset_injective (hx.trans hj.symm))]
        exact hzV)
      fun z hz => WellFoundedPart.mem_sUnion.mpr
        ⟨(F i).1, mem_sep.mpr ⟨hF i, i, hx, rfl⟩, hz⟩
  have values : ∀ a : El Mem (sep (fun y => ∃ i, (iteratedPowerset (code i)).1 = y) W),
      Mem (sUnion (sep (fun y => ∃ j, (iteratedPowerset (code j)).1 = a.1.1 ∧ (F j).1 = y) U))
        U := fun a => by
    obtain ⟨i, hi⟩ := (mem_sep.mp a.2).2
    rw [value i a.1.1 hi]
    exact hF i
  obtain ⟨E, hE, image⟩ : ∃ E : WellFoundedPart.{u}, Mem E U ∧
      ∀ y : WellFoundedPart.{u}, Mem y E ↔ ∃ i, F i = y :=
    ⟨_, hU.image_mem hX _ values, fun y => (mem_imageWithin values).trans
      ⟨fun ⟨a, ha⟩ => let ⟨i, hi⟩ := (mem_sep.mp a.2).2
        ⟨i, (value i a.1.1 hi).symm.trans ha⟩,
      fun ⟨i, hi⟩ => ⟨⟨iteratedPowerset (code i), mem_sep.mpr ⟨hWn _, i, rfl⟩⟩,
        (value i _ rfl).trans hi⟩⟩⟩
  exact ⟨E, hE, fun z =>
    ⟨fun hz => let ⟨i, hi⟩ := (image ⟨z, E.2.mem hz⟩).mp hz
      ⟨i, congrArg Subtype.val hi⟩,
    fun ⟨i, hi⟩ => hi ▸ (image (F i)).mpr ⟨i, rfl⟩⟩⟩

/-! ## Towers of universes over a level order -/

section Tower

open LevelOrder

variable {L : Type} [LevelOrder L]

/-- `N` is the set of the seed and the stages below the level `α`. -/
def IsGeneratingSet (seed : WellFoundedPart.{u}) (stage : L → WellFoundedPart.{u}) (α : L)
    (N : WellFoundedPart.{u}) : Prop :=
  ∀ z : HSet.{u}, z ∈ N.1 ↔ z = seed.1 ∨ ∃ β, β < α ∧ (stage β).1 = z

/-- `E` is the set of the stages below the level `α`. -/
def IsEarlierStages (stage : L → WellFoundedPart.{u}) (α : L) (E : WellFoundedPart.{u}) : Prop :=
  ∀ z : HSet.{u}, z ∈ E.1 ↔ ∃ β, β < α ∧ (stage β).1 = z

/-- The collection hypothesis of a tower: at every level, the earlier stages are collected.
The universe laws do not provide it. -/
def CollectsEarlierStages (stage : L → WellFoundedPart.{u}) : Prop :=
  ∀ α : L, IsCollected fun β : {β : L // β < α} => stage β.1

/-- The equation of a tower of universes over a level order, for an operation `univOf` and
a seed: the stage at a level is `univOf` of the set of the seed and the earlier stages. That
this set exists is not part of the equation; it is `CollectsEarlierStages`. -/
def IsUniverseTower (univOf : WellFoundedPart.{u} → WellFoundedPart.{u})
    (seed : WellFoundedPart.{u}) (stage : L → WellFoundedPart.{u}) : Prop :=
  ∀ (α : L) (N : WellFoundedPart.{u}), IsGeneratingSet seed stage α N → stage α = univOf N

variable {univOf : WellFoundedPart.{u} → WellFoundedPart.{u}} {seed : WellFoundedPart.{u}}
  {stage : L → WellFoundedPart.{u}}

/-! ### Where the collection hypothesis has content -/

/-- Below the least level there is nothing to collect. -/
theorem isCollected_below_bot (stage : L → WellFoundedPart.{u}) :
    IsCollected fun β : {β : L // β < bot} => stage β.1 :=
  ⟨empty, fun β => absurd β.2 (not_lt_of_ge (bot_le β.1))⟩

/-- Below a successor level the stages are collected when they are below its predecessor:
the previous stage is inserted. -/
theorem isCollected_below_succ {l : L}
    (h : IsCollected fun β : {β : L // β < l} => stage β.1) :
    IsCollected fun β : {β : L // β < succ l} => stage β.1 :=
  let ⟨B, hB⟩ := h
  ⟨⟨insert (stage l).1 B.1, (stage l).2.insert B.2⟩, fun β =>
    HSet.mem_insert_iff.mpr ((Decidable.eq_or_lt_of_le (le_of_lt_succ β.2)).imp
      (fun e => congrArg (fun γ => (stage γ).1) e) fun hlt => hB ⟨β.1, hlt⟩)⟩

/-- The earlier stages of a tower are collected exactly when their set exists. -/
theorem isCollected_iff_exists_isEarlierStages {α : L} :
    (IsCollected fun β : {β : L // β < α} => stage β.1) ↔ ∃ E, IsEarlierStages stage α E :=
  ⟨fun ⟨B, hB⟩ => ⟨sep (fun y => ∃ β, β < α ∧ (stage β).1 = y) B,
      fun _ => mem_sep.trans ⟨And.right, fun ⟨β, hβ, e⟩ => ⟨e ▸ hB ⟨β, hβ⟩, β, hβ, e⟩⟩⟩,
    fun ⟨E, hE⟩ => ⟨E, fun β => (hE _).mpr ⟨β.1, β.2, rfl⟩⟩⟩

/-- When the earlier stages are collected, the set of the seed and the earlier stages
exists: the seed is inserted into their set. -/
theorem CollectsEarlierStages.exists_isGeneratingSet (collected : CollectsEarlierStages stage)
    (seed : WellFoundedPart.{u}) (α : L) : ∃ N, IsGeneratingSet seed stage α N :=
  let ⟨E, hE⟩ := isCollected_iff_exists_isEarlierStages.mp (collected α)
  ⟨⟨insert seed.1 E.1, seed.2.insert E.2⟩,
    fun z => HSet.mem_insert_iff.trans (or_congr Iff.rfl (hE z))⟩

/-- The collection hypothesis restricts along an order-preserving map of levels. -/
theorem CollectsEarlierStages.comp {L' : Type} [LevelOrder L'] {stage' : L' → WellFoundedPart.{u}}
    (collected : CollectsEarlierStages stage') (f : Embedding L L') :
    CollectsEarlierStages fun α => stage' (f α) := fun α =>
  let ⟨B, hB⟩ := collected (f α)
  ⟨B, fun β => hB ⟨f β.1, f.lt_iff.mpr β.2⟩⟩

/-- A presentation of the hypersets by graphs collects the earlier stages of every family
over every level order. With `HSet.Presentation.choice` the collection hypothesis therefore
always holds: it has content only without choice. -/
theorem collectsEarlierStages_of_presentation (p : Presentation.{u})
    (stage : L → WellFoundedPart.{u}) : CollectsEarlierStages stage :=
  fun _ => isCollected_of_presentation p _

/-- Inside a universe that has the seed and the stages below a level as members, the set of
the seed and those stages is a member, when the lower levels have injective codes in the
natural numbers and some member of the universe has every iterated power set of the empty
set as a member. -/
theorem IsGrothendieckUniverse.exists_isGeneratingSet_mem {B W : WellFoundedPart.{u}}
    (hB : IsGrothendieckUniverse B) (hW : Mem W B) (hWn : ∀ n, Mem (iteratedPowerset n) W)
    (hseed : Mem seed B) {α : L} (code : {β : L // β < α} → Nat)
    (injective : Function.Injective code) (below : ∀ β, β < α → Mem (stage β) B) :
    ∃ N, Mem N B ∧ IsGeneratingSet seed stage α N := by
  obtain ⟨E, hEB, hE⟩ := hB.exists_range_mem hW hWn code injective (fun β => stage β.1)
    fun β => below β.1 β.2
  refine ⟨sUnion (upair (singleton seed) E),
    hB.sUnion_mem (hB.upair_mem (hB.singleton_mem hseed) hEB), fun z => ?_⟩
  rw [WellFoundedPart.mem_sUnion]
  constructor
  · rintro ⟨V, hV, hz⟩
    rcases mem_upair.mp hV with rfl | rfl
    · exact Or.inl (mem_singleton.mp hz)
    · obtain ⟨β, e⟩ := (hE z).mp hz
      exact Or.inr ⟨β.1, β.2, e⟩
  · rintro (rfl | ⟨β, hβ, rfl⟩)
    · exact ⟨(singleton seed).1, mem_upair.mpr (Or.inl rfl), mem_singleton.mpr rfl⟩
    · exact ⟨E.1, mem_upair.mpr (Or.inr rfl), (hE _).mpr ⟨⟨β, hβ⟩, rfl⟩⟩

namespace IsGeneratingSet

variable {α : L} {N : WellFoundedPart.{u}}

/-- The set of the seed and the earlier stages is determined by its members. -/
theorem unique {N' : WellFoundedPart.{u}} (hN : IsGeneratingSet seed stage α N)
    (hN' : IsGeneratingSet seed stage α N') : N = N' :=
  Subtype.ext (HSet.ext fun z => (hN z).trans (hN' z).symm)

end IsGeneratingSet

namespace IsEarlierStages

variable {α : L} {E : WellFoundedPart.{u}}

/-- The set of the earlier stages is a member of no earlier stage. -/
theorem notMem_of_lt (hE : IsEarlierStages stage α E) {β : L} (hβα : β < α) :
    ¬ Mem E (stage β) :=
  notMem_of_mem ((hE _).mpr ⟨β, hβα, rfl⟩)

/-- The members of the union of the earlier stages are the members of the stages at the
lower levels. -/
theorem mem_sUnion (hE : IsEarlierStages stage α E) {z : HSet.{u}} :
    z ∈ (sUnion E).1 ↔ ∃ β, β < α ∧ z ∈ (stage β).1 := by
  rw [WellFoundedPart.mem_sUnion]
  constructor
  · rintro ⟨W, hW, hz⟩
    obtain ⟨β, hβ, rfl⟩ := (hE W).mp hW
    exact ⟨β, hβ, hz⟩
  · rintro ⟨β, hβ, hz⟩
    exact ⟨(stage β).1, (hE _).mpr ⟨β, hβ, rfl⟩, hz⟩

/-- The set of the earlier stages is not a member of their union. -/
theorem notMem_sUnion (hE : IsEarlierStages stage α E) : ¬ Mem E (sUnion E) := fun hmem =>
  let ⟨_, hβ, hz⟩ := hE.mem_sUnion.mp hmem
  hE.notMem_of_lt hβ hz

end IsEarlierStages

namespace IsUniverseTower

/-! ### The stage equation and the comparison of towers -/

/-- The stage equation: with the earlier stages collected, the stage at a level is `univOf`
of the set of the seed and the earlier stages. -/
theorem stage_eq (t : IsUniverseTower univOf seed stage)
    (collected : CollectsEarlierStages stage) (α : L) :
    ∃ N, IsGeneratingSet seed stage α N ∧ stage α = univOf N :=
  let ⟨N, hN⟩ := collected.exists_isGeneratingSet seed α
  ⟨N, hN, t α N hN⟩

/-- Two towers for one operation and seed have the same stages, when the earlier stages of
one of them are collected. No law of the operation is used. -/
theorem unique {stage' : L → WellFoundedPart.{u}} (t : IsUniverseTower univOf seed stage)
    (collected : CollectsEarlierStages stage) (t' : IsUniverseTower univOf seed stage') :
    stage = stage' := by
  funext α
  induction α using LevelOrder.induction with
  | step α ih =>
    obtain ⟨N, hN, hα⟩ := t.stage_eq collected α
    rw [hα]
    refine (t' α N fun z => (hN z).trans (or_congr Iff.rfl
      (exists_congr fun β => and_congr_right fun hβ => ?_))).symm
    rw [ih β hβ]

/-- The tower equation restricts along an initial embedding of level orders. -/
theorem comp_initial {L' : Type} [LevelOrder L'] {stage' : L' → WellFoundedPart.{u}}
    (t' : IsUniverseTower univOf seed stage') (f : Embedding L L') (initial : f.Initial) :
    IsUniverseTower univOf seed fun α => stage' (f α) := fun α N hN =>
  t' (f α) N fun z => (hN z).trans (or_congr Iff.rfl
    ⟨fun ⟨β, hβ, e⟩ => ⟨f β, f.lt_iff.mpr hβ, e⟩, by
      rintro ⟨β', hβ', rfl⟩
      obtain ⟨β, rfl⟩ := initial α β' hβ'
      exact ⟨β, f.lt_iff.mp hβ', rfl⟩⟩)

/-- Towers commute with initial embeddings of level orders: the stage at the image of a
level is the stage at that level. -/
theorem map_eq {L' : Type} [LevelOrder L'] {stage' : L' → WellFoundedPart.{u}}
    (t : IsUniverseTower univOf seed stage) (collected : CollectsEarlierStages stage)
    (t' : IsUniverseTower univOf seed stage') (f : Embedding L L') (initial : f.Initial)
    (α : L) : stage' (f α) = stage α :=
  (congrFun (t.unique collected (t'.comp_initial f initial)) α).symm

/-! ### Stages along the order -/

section Laws

variable (op : IsUniverseOperator univOf) (t : IsUniverseTower univOf seed stage)
  (collected : CollectsEarlierStages stage)
include op t collected

/-- Every stage is a universe. -/
theorem isGrothendieckUniverse (α : L) : IsGrothendieckUniverse (stage α) := by
  obtain ⟨N, -, hα⟩ := t.stage_eq collected α
  rw [hα]
  exact op.isGrothendieckUniverse N

omit collected in
/-- The set of the seed and the earlier stages is a member of the stage. -/
theorem generatingSet_mem {α : L} {N : WellFoundedPart.{u}}
    (hN : IsGeneratingSet seed stage α N) : Mem N (stage α) := by
  rw [t α N hN]
  exact op.mem_univOf N

/-- The seed is a member of every stage. -/
theorem seed_mem (α : L) : Mem seed (stage α) := by
  obtain ⟨N, hN, -⟩ := t.stage_eq collected α
  exact (t.isGrothendieckUniverse op collected α).transitive
    (t.generatingSet_mem op hN) ((hN seed.1).mpr (Or.inl rfl))

/-- An earlier stage is a member of every later stage. -/
theorem mem_of_lt {α β : L} (hβα : β < α) : Mem (stage β) (stage α) := by
  obtain ⟨N, hN, -⟩ := t.stage_eq collected α
  exact (t.isGrothendieckUniverse op collected α).transitive
    (t.generatingSet_mem op hN) ((hN (stage β).1).mpr (Or.inr ⟨β, hβα, rfl⟩))

/-- The tower is monotone: a stage is a subset of every stage at a level above. -/
theorem subset_of_le {α β : L} (hβα : β ≤ α) : Subset (stage β) (stage α) := by
  rcases Decidable.eq_or_lt_of_le hβα with rfl | hlt
  · exact Subset.refl _
  · exact (t.isGrothendieckUniverse op collected α).subset_of_mem (t.mem_of_lt op collected hlt)

/-- Membership of stages is the strict order of levels. -/
theorem mem_iff {α β : L} : Mem (stage β) (stage α) ↔ β < α :=
  ⟨fun hmem => lt_of_not_ge fun hαβ =>
    (stage β).2.notMem_self (t.subset_of_le op collected hαβ hmem), t.mem_of_lt op collected⟩

/-- Inclusion of stages is the order of levels. -/
theorem subset_iff {α β : L} : Subset (stage β) (stage α) ↔ β ≤ α :=
  ⟨fun hsub => le_of_not_gt fun hαβ =>
    (stage α).2.notMem_self (hsub (t.mem_of_lt op collected hαβ)), t.subset_of_le op collected⟩

/-- The tower is injective: distinct levels have distinct stages. -/
theorem injective : Function.Injective stage := fun _ _ heq =>
  le_antisymm ((t.subset_iff op collected).mp (heq ▸ Subset.refl _))
    ((t.subset_iff op collected).mp (heq ▸ Subset.refl _))

/-- An earlier stage differs from every later stage. -/
theorem ne_of_lt {α β : L} (hβα : β < α) : stage β ≠ stage α := fun heq =>
  _root_.ne_of_lt hβα (t.injective op collected heq)

/-! ### The least level and successor levels -/

/-- A stage is the universe of any of its members that includes the seed and every earlier
stage. -/
theorem eq_univOf {α : L} {M : WellFoundedPart.{u}} (hM : Mem M (stage α))
    (hseed : Subset seed M) (hstages : ∀ β, β < α → Subset (stage β) M) :
    stage α = univOf M := by
  obtain ⟨N, hN, hα⟩ := t.stage_eq collected α
  refine subset_antisymm ?_ (op.minimal hM (t.isGrothendieckUniverse op collected α))
  rw [hα]
  refine op.minimal ((op.isGrothendieckUniverse M).mem_of_forall_subset (op.mem_univOf M)
    fun z hz => ?_) (op.isGrothendieckUniverse M)
  rcases (hN z).mp hz with rfl | ⟨β, hβ, rfl⟩
  · exact hseed
  · exact hstages β hβ

/-- The stage at the least level is the universe of the seed. -/
theorem stage_bot : stage (bot : L) = univOf seed :=
  t.eq_univOf op collected (t.seed_mem op collected bot) (Subset.refl seed)
    fun β hβ => absurd hβ (not_lt_of_ge (bot_le β))

/-- The stage at a successor level is the universe of the previous stage. -/
theorem stage_succ (l : L) : stage (succ l) = univOf (stage l) :=
  t.eq_univOf op collected (t.mem_of_lt op collected (lt_succ l))
    ((t.isGrothendieckUniverse op collected l).subset_of_mem (t.seed_mem op collected l))
    fun _ hβ => t.subset_of_le op collected (le_of_lt_succ hβ)

/-- A stage is the universe of another stage exactly when its level is the successor of
the other's. -/
theorem eq_univOf_stage_iff {α β : L} : stage α = univOf (stage β) ↔ α = succ β := by
  rw [← t.stage_succ op collected]
  exact (t.injective op collected).eq_iff

/-! ### Every stage encloses the earlier ones -/

variable {α : L} {E : WellFoundedPart.{u}}

/-- The set of the earlier stages is a member of the stage. -/
theorem earlierStages_mem (hE : IsEarlierStages stage α E) : Mem E (stage α) := by
  obtain ⟨N, hN, -⟩ := t.stage_eq collected α
  exact (t.isGrothendieckUniverse op collected α).subset_mem
    (t.generatingSet_mem op hN) fun z hz => (hN z).mpr (Or.inr ((hE z).mp hz))

/-- The union of the earlier stages is a member of the stage: the stage encloses it. -/
theorem sUnion_earlierStages_mem (hE : IsEarlierStages stage α E) : Mem (sUnion E) (stage α) :=
  (t.isGrothendieckUniverse op collected α).sUnion_mem (t.earlierStages_mem op collected hE)

/-- The union of the earlier stages is a subset of the stage. -/
theorem sUnion_earlierStages_subset (hE : IsEarlierStages stage α E) :
    Subset (sUnion E) (stage α) :=
  (t.isGrothendieckUniverse op collected α).subset_of_mem
    (t.sUnion_earlierStages_mem op collected hE)

/-- The stage is not a subset of the union of the earlier stages: the union is a proper
subset. -/
theorem not_subset_sUnion_earlierStages (hE : IsEarlierStages stage α E) :
    ¬ Subset (stage α) (sUnion E) := fun hsub =>
  hE.notMem_sUnion (hsub (t.earlierStages_mem op collected hE))

/-- At a positive level the stage is the universe of the union of the earlier stages. -/
theorem eq_univOf_sUnion (hE : IsEarlierStages stage α E) (hα : bot < α) :
    stage α = univOf (sUnion E) :=
  t.eq_univOf op collected (t.sUnion_earlierStages_mem op collected hE)
    (fun _ hz => hE.mem_sUnion.mpr ⟨bot, hα,
      (t.isGrothendieckUniverse op collected bot).transitive (t.seed_mem op collected bot) hz⟩)
    fun β hβ _ hz => hE.mem_sUnion.mpr ⟨β, hβ, hz⟩

/-- At a successor level the union of the earlier stages is the previous stage. -/
theorem sUnion_earlierStages_succ {l : L} (hE : IsEarlierStages stage (succ l) E) :
    sUnion E = stage l :=
  subset_antisymm
    (fun _ hz => let ⟨_, hβ, hzβ⟩ := hE.mem_sUnion.mp hz
      t.subset_of_le op collected (le_of_lt_succ hβ) hzβ)
    fun _ hz => hE.mem_sUnion.mpr ⟨l, lt_succ l, hz⟩

/-- The union of the earlier stages is a stage exactly at a successor level, where it is
the previous stage. -/
theorem sUnion_earlierStages_eq_stage_iff (hE : IsEarlierStages stage α E) {β : L} :
    sUnion E = stage β ↔ α = succ β := by
  constructor
  · intro heq
    have hβα : β < α := lt_of_not_ge fun hαβ => by
      have hmem : (sUnion E).1 ∈ (stage β).1 :=
        t.subset_of_le op collected hαβ (t.sUnion_earlierStages_mem op collected hE)
      rw [heq] at hmem
      exact (stage β).2.notMem_self hmem
    refine le_antisymm (le_of_not_gt fun hlt => ?_) (succ_le_of_lt hβα)
    have hmem : (stage β).1 ∈ (sUnion E).1 :=
      hE.mem_sUnion.mpr ⟨succ β, hlt, t.mem_of_lt op collected (lt_succ β)⟩
    rw [heq] at hmem
    exact (stage β).2.notMem_self hmem
  · rintro rfl
    exact t.sUnion_earlierStages_succ op collected hE

/-! ### Limit levels -/

/-- Below a limit level the union of the stages is not a stage. -/
theorem sUnion_earlierStages_ne_stage_of_isLimit (hE : IsEarlierStages stage α E)
    (hα : IsLimit α) (β : L) : sUnion E ≠ stage β := fun heq =>
  hα.2 β ((t.sUnion_earlierStages_eq_stage_iff op collected hE).mp heq).symm

/-- The stage at a limit level is not the universe of any single stage. -/
theorem ne_univOf_stage_of_isLimit (hα : IsLimit α) (β : L) :
    stage α ≠ univOf (stage β) := fun heq =>
  hα.2 β ((t.eq_univOf_stage_iff op collected).mp heq).symm

/-- A universe that has the stages along a sequence of levels as members includes the stage
at every level whose lower levels all lie at or below members of the sequence. The stages
along the sequence form a member of the universe, by replacement along the numbers, and
every member of the seed or of an earlier stage is a member of its union. -/
theorem subset_of_sequence_mem (c : Nat → L) (hcof : ∀ β, β < α → ∃ n, β ≤ c n)
    {V : WellFoundedPart.{u}} (hV : ∀ n, Mem (stage (c n)) V)
    (closed : IsGrothendieckUniverse V) : Subset (stage α) V := by
  obtain ⟨N, hN, hα⟩ := t.stage_eq collected α
  have first := t.isGrothendieckUniverse op collected (c 0)
  obtain ⟨S, hSV, hS⟩ := closed.exists_range_mem (hV 0)
    (first.iteratedPowerset_mem (t.seed_mem op collected (c 0))) id Function.injective_id
    (fun n => stage (c n)) hV
  rw [hα]
  refine op.minimal (closed.mem_of_forall_subset (closed.sUnion_mem hSV) fun z hz => ?_) closed
  rcases (hN z).mp hz with rfl | ⟨β, hβ, rfl⟩
  · exact fun _ hw => WellFoundedPart.mem_sUnion.mpr
      ⟨(stage (c 0)).1, (hS _).mpr ⟨0, rfl⟩, first.transitive (t.seed_mem op collected (c 0)) hw⟩
  · obtain ⟨n, hn⟩ := hcof β hβ
    exact fun _ hw => WellFoundedPart.mem_sUnion.mpr
      ⟨(stage (c n)).1, (hS _).mpr ⟨n, rfl⟩, t.subset_of_le op collected hn hw⟩

/-- When every level below a level lies strictly below some member of a sequence of lower
levels, the union of the earlier stages is not a universe: it has the stages along the
sequence as members, so if it were a universe it would include the stage itself. -/
theorem sUnion_earlierStages_not_isGrothendieckUniverse_of_sequence
    (hE : IsEarlierStages stage α E) (c : Nat → L) (hc : ∀ n, c n < α)
    (hcof : ∀ β, β < α → ∃ n, β < c n) : ¬ IsGrothendieckUniverse (sUnion E) := fun closed =>
  t.not_subset_sUnion_earlierStages op collected hE
    (t.subset_of_sequence_mem op collected c (fun β hβ => (hcof β hβ).imp fun _ => le_of_lt)
      (fun n => let ⟨m, hm⟩ := hcof (c n) (hc n)
        hE.mem_sUnion.mpr ⟨c m, hc m, t.mem_of_lt op collected hm⟩) closed)

/-- At a level with countably many lower levels, the stage is the least universe that has
the seed and every earlier stage as members: it is included in every universe with these
members. The set of the seed and the earlier stages is formed inside such a universe, by
replacement along the codes of the lower levels. -/
theorem subset_of_forall_mem [Countable {β : L // β < α}] {V : WellFoundedPart.{u}}
    (hseed : Mem seed V) (hV : ∀ β, β < α → Mem (stage β) V)
    (closed : IsGrothendieckUniverse V) : Subset (stage α) V := by
  obtain ⟨N, hN, hα⟩ := t.stage_eq collected α
  obtain ⟨code, injective⟩ := Countable.exists_injective_nat {β : L // β < α}
  rw [hα]
  refine op.minimal ?_ closed
  rcases Decidable.eq_or_lt_of_le (bot_le α) with rfl | hpos
  · exact closed.subset_mem (closed.singleton_mem hseed) fun z hz => mem_singleton.mpr
      (((hN z).mp hz).resolve_right fun ⟨β, hβ, _⟩ => not_lt_of_ge (bot_le β) hβ)
  · obtain ⟨M, hMV, hM⟩ := closed.exists_isGeneratingSet_mem (hV bot hpos)
      ((t.isGrothendieckUniverse op collected bot).iteratedPowerset_mem
        (t.seed_mem op collected bot)) hseed code injective hV
    rw [hN.unique hM]
    exact hMV

/-- At a limit level with countably many lower levels, the union of the earlier stages is
not a universe: it has the seed and every earlier stage as members, so if it were a universe
it would include the stage itself. -/
theorem sUnion_earlierStages_not_isGrothendieckUniverse [Countable {β : L // β < α}]
    (hE : IsEarlierStages stage α E) (hα : IsLimit α) :
    ¬ IsGrothendieckUniverse (sUnion E) := fun closed =>
  t.not_subset_sUnion_earlierStages op collected hE
    (t.subset_of_forall_mem op collected
      (hE.mem_sUnion.mpr ⟨bot, hα.1, t.seed_mem op collected bot⟩)
      (fun β hβ => hE.mem_sUnion.mpr
        ⟨succ β, hα.succ_lt hβ, t.mem_of_lt op collected (lt_succ β)⟩) closed)

end Laws

/-! ### The seed -/

/-- Towers are monotone in the seed. -/
theorem seed_mono (op : IsUniverseOperator univOf) {small large : WellFoundedPart.{u}}
    {stageSmall stageLarge : L → WellFoundedPart.{u}}
    (tSmall : IsUniverseTower univOf small stageSmall)
    (collectedSmall : CollectsEarlierStages stageSmall)
    (tLarge : IsUniverseTower univOf large stageLarge)
    (collectedLarge : CollectsEarlierStages stageLarge) (below : Subset small large) (α : L) :
    Subset (stageSmall α) (stageLarge α) := by
  induction α using LevelOrder.induction with
  | step α ih =>
    obtain ⟨N, hN, hα⟩ := tSmall.stage_eq collectedSmall α
    obtain ⟨M, hM, -⟩ := tLarge.stage_eq collectedLarge α
    have closed := tLarge.isGrothendieckUniverse op collectedLarge α
    rw [hα]
    refine op.minimal (closed.mem_of_forall_subset
      (closed.sUnion_mem (tLarge.generatingSet_mem op hM)) fun z hz => ?_) closed
    rcases (hN z).mp hz with rfl | ⟨β, hβ, rfl⟩
    · exact fun _ hw => WellFoundedPart.mem_sUnion.mpr
        ⟨large.1, (hM _).mpr (Or.inl rfl), below hw⟩
    · exact fun _ hw => WellFoundedPart.mem_sUnion.mpr
        ⟨(stageLarge β).1, (hM _).mpr (Or.inr ⟨β, hβ, rfl⟩), ih β hβ hw⟩

end IsUniverseTower

/-! ### Stages inside a universe closed under the operation

A universe closed under the operation is a bound for every stage. Inside it the stages are
built by the recursion along the level order, the set of the seed and the earlier stages
being separated from the bound: no graph of a stage is chosen and none is given. -/

/-- The stages inside a bound `B`: at every level the operation is applied to the set of the
seed and those members of `B` that are earlier stages. -/
noncomputable def stageWithin (univOf : WellFoundedPart.{u} → WellFoundedPart.{u})
    (seed B : WellFoundedPart.{u}) : L → WellFoundedPart.{u} :=
  LevelOrder.wf.fix fun α earlier =>
    univOf ⟨insert seed.1 (sep (fun y => ∃ β, ∃ h : β < α, (earlier β h).1 = y) B).1,
      seed.2.insert (sep _ B).2⟩

/-- The recursion equation of the stages inside a bound. -/
theorem stageWithin_eq (B : WellFoundedPart.{u}) (α : L) :
    stageWithin univOf seed B α =
      univOf ⟨insert seed.1
        (sep (fun y => ∃ β, ∃ _ : β < α, (stageWithin univOf seed B β).1 = y) B).1,
        seed.2.insert (sep _ B).2⟩ :=
  LevelOrder.wf.fix_eq _ α

/-- Where the earlier stages are members of the bound, the stage inside the bound is the
operation applied to the set of the seed and the earlier stages. -/
theorem stageWithin_eq_univOf {B : WellFoundedPart.{u}} {α : L}
    (below : ∀ β, β < α → Mem (stageWithin univOf seed B β) B) {N : WellFoundedPart.{u}}
    (hN : IsGeneratingSet seed (stageWithin univOf seed B) α N) :
    stageWithin univOf seed B α = univOf N :=
  (stageWithin_eq B α).trans (congrArg univOf (Subtype.ext (HSet.ext fun z =>
    HSet.mem_insert_iff.trans ((or_congr Iff.rfl (mem_sep.trans
      ⟨fun ⟨_, β, hβ, e⟩ => ⟨β, hβ, e⟩, fun ⟨β, hβ, e⟩ => ⟨e ▸ below β hβ, β, hβ, e⟩⟩)).trans
        (hN z).symm))))

section Closed

variable [Countable L] (op : IsUniverseOperator univOf) {B : WellFoundedPart.{u}}
  (hB : IsGrothendieckUniverse B) (hseed : Mem seed B)
  (closed : ∀ N, Mem N B → Mem (univOf N) B)
include op hB hseed closed

/-- Inside a universe closed under the operation that has the seed as a member, every stage
inside the bound is a member, over a level order with countably many levels. The set of the
seed and the earlier stages is formed inside the universe, by replacement along the codes of
the levels. -/
theorem stageWithin_mem (α : L) : Mem (stageWithin univOf seed B α) B := by
  obtain ⟨code, injective⟩ := Countable.exists_injective_nat L
  induction α using LevelOrder.induction with
  | step α ih =>
    obtain ⟨N, hNB, hN⟩ := hB.exists_isGeneratingSet_mem (closed seed hseed)
      ((op.isGrothendieckUniverse seed).iteratedPowerset_mem (op.mem_univOf seed)) hseed
      (fun β : {β : L // β < α} => code β.1) (fun _ _ e => Subtype.ext (injective e)) ih
    rw [stageWithin_eq_univOf ih hN]
    exact closed N hNB

/-- The stages inside a universe closed under the operation satisfy the tower equation. -/
theorem isUniverseTower_stageWithin :
    IsUniverseTower univOf seed (stageWithin univOf seed B : L → WellFoundedPart.{u}) :=
  fun _ _ hN => stageWithin_eq_univOf (fun β _ => stageWithin_mem op hB hseed closed β) hN

/-- The stages inside a universe closed under the operation are collected at every level,
by that universe. -/
theorem collectsEarlierStages_stageWithin :
    CollectsEarlierStages (stageWithin univOf seed B : L → WellFoundedPart.{u}) :=
  fun _ => ⟨B, fun β => stageWithin_mem op hB hseed closed β.1⟩

/-- A universe closed under the operation that has the seed as a member has every stage of
every tower as a member: the tower has the stages built inside the universe. -/
theorem IsUniverseTower.mem_of_closed (t : IsUniverseTower univOf seed stage) (α : L) :
    Mem (stage α) B := by
  rw [← (isUniverseTower_stageWithin op hB hseed closed).unique
    (collectsEarlierStages_stageWithin op hB hseed closed) t]
  exact stageWithin_mem op hB hseed closed α

/-- A universe closed under the operation that has the seed as a member collects the earlier
stages of every tower, at every level. Neither a graph of a stage nor a choice of one is
used; the hypothesis is a universe of universes, which the universe laws do not provide. -/
theorem IsUniverseTower.collectsEarlierStages_of_closed
    (t : IsUniverseTower univOf seed stage) : CollectsEarlierStages stage :=
  fun _ => ⟨B, fun β => t.mem_of_closed op hB hseed closed β.1⟩

end Closed

end Tower

/-! ### The collection hypothesis is an obligation at limit levels -/

/-- Over a level order with predecessors, the earlier stages are collected at every level
when they are collected at the limit levels: nothing is collected at the least level, and at
a successor the previous stage is inserted. -/
theorem collectsEarlierStages_of_isLimit {L : Type} [PredLevelOrder L]
    {stage : L → WellFoundedPart.{u}}
    (limits : ∀ α : L, LevelOrder.IsLimit α → IsCollected fun β : {β : L // β < α} => stage β.1) :
    CollectsEarlierStages stage := by
  intro α
  induction α using LevelOrder.induction with
  | step α ih =>
    cases hp : PredLevelOrder.pred? α with
    | some p =>
      obtain rfl := PredLevelOrder.pred?_eq_some.mp hp
      exact isCollected_below_succ (ih p (LevelOrder.lt_succ p))
    | none =>
      by_cases hα : LevelOrder.bot < α
      · exact limits α (PredLevelOrder.isLimit_of_pred?_eq_none hα hp)
      · obtain rfl : α = LevelOrder.bot :=
          le_antisymm (le_of_not_gt hα) (LevelOrder.bot_le α)
        exact isCollected_below_bot stage

/-- Over the natural numbers the earlier stages of every family are collected: there is no
limit level. -/
theorem collectsEarlierStages_nat (stage : Nat → WellFoundedPart.{u}) :
    CollectsEarlierStages stage :=
  collectsEarlierStages_of_isLimit fun α hα => absurd hα (nat_not_isLimit α)

/-! ### Over the natural numbers

Below a finite level there are finitely many stages, and the set of the seed and the earlier
stages is built by insertion. A tower therefore exists over the natural numbers for every
operation and seed, and its stages are the finite stages of every tower. -/

/-- The set of the seed and the first `n` stages over the natural numbers: the stage at `n`
is inserted to pass to `n + 1`. -/
def natGeneratingSet (univOf : WellFoundedPart.{u} → WellFoundedPart.{u})
    (seed : WellFoundedPart.{u}) : Nat → WellFoundedPart.{u}
  | 0 => singleton seed
  | n + 1 =>
    ⟨insert (univOf (natGeneratingSet univOf seed n)).1 (natGeneratingSet univOf seed n).1,
      (univOf (natGeneratingSet univOf seed n)).2.insert (natGeneratingSet univOf seed n).2⟩

/-- The stages over the natural numbers: the operation applied to the set of the seed and
the earlier stages. -/
def natStage (univOf : WellFoundedPart.{u} → WellFoundedPart.{u}) (seed : WellFoundedPart.{u})
    (n : Nat) : WellFoundedPart.{u} :=
  univOf (natGeneratingSet univOf seed n)

/-- The set built by insertion is the set of the seed and the earlier stages. -/
theorem isGeneratingSet_natGeneratingSet (univOf : WellFoundedPart.{u} → WellFoundedPart.{u})
    (seed : WellFoundedPart.{u}) (n : Nat) :
    IsGeneratingSet seed (natStage univOf seed) n (natGeneratingSet univOf seed n) := by
  induction n with
  | zero =>
    exact fun z => mem_singleton.trans
      ⟨Or.inl, fun h => h.resolve_right fun ⟨β, hβ, _⟩ => Nat.not_lt_zero β hβ⟩
  | succ n ih =>
    intro z
    change z ∈ insert (natStage univOf seed n).1 (natGeneratingSet univOf seed n).1 ↔ _
    refine HSet.mem_insert_iff.trans ⟨?_, ?_⟩
    · rintro (e | h)
      · exact Or.inr ⟨n, Nat.lt_succ_self n, e.symm⟩
      · exact ((ih z).mp h).imp id fun ⟨β, hβ, e⟩ => ⟨β, Nat.lt_succ_of_lt hβ, e⟩
    · rintro (e | ⟨β, hβ, e⟩)
      · exact Or.inr ((ih z).mpr (Or.inl e))
      · rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hβ) with rfl | hlt
        · exact Or.inl e.symm
        · exact Or.inr ((ih z).mpr (Or.inr ⟨β, hlt, e⟩))

/-- The stages over the natural numbers satisfy the tower equation, for every operation and
seed. Their earlier stages are collected (`collectsEarlierStages_nat`). -/
theorem isUniverseTower_natStage (univOf : WellFoundedPart.{u} → WellFoundedPart.{u})
    (seed : WellFoundedPart.{u}) : IsUniverseTower univOf seed (natStage univOf seed) :=
  fun n _ hN => congrArg univOf ((isGeneratingSet_natGeneratingSet univOf seed n).unique hN)

/-- For a universe operation, the stage at zero is the universe of the seed. -/
theorem natStage_zero {univOf : WellFoundedPart.{u} → WellFoundedPart.{u}}
    (op : IsUniverseOperator univOf) (seed : WellFoundedPart.{u}) :
    natStage univOf seed 0 = univOf seed :=
  (isUniverseTower_natStage univOf seed).stage_bot op (collectsEarlierStages_nat _)

/-- For a universe operation, the stage at `n + 1` is the universe of the stage at `n`: over
the natural numbers the tower is the iteration of the operation. -/
theorem natStage_succ {univOf : WellFoundedPart.{u} → WellFoundedPart.{u}}
    (op : IsUniverseOperator univOf) (seed : WellFoundedPart.{u}) (n : Nat) :
    natStage univOf seed (n + 1) = univOf (natStage univOf seed n) :=
  (isUniverseTower_natStage univOf seed).stage_succ op (collectsEarlierStages_nat _) n

/-- The finite stages of every tower are the stages over the natural numbers. No collection
hypothesis is used: below a finite level the earlier stages are collected by insertion. -/
theorem IsUniverseTower.stage_ofNat {L : Type} [LevelOrder L]
    {univOf : WellFoundedPart.{u} → WellFoundedPart.{u}} {seed : WellFoundedPart.{u}}
    {stage : L → WellFoundedPart.{u}} (t : IsUniverseTower univOf seed stage) (n : Nat) :
    stage (LevelOrder.ofNat n) = natStage univOf seed n :=
  (isUniverseTower_natStage univOf seed).map_eq (collectsEarlierStages_nat _) t
    (LevelOrder.Embedding.ofNat L) (LevelOrder.Embedding.ofNat_initial L) n

/-! ### Stages built as graphs

An operation given on graphs builds the stages as graphs, by the same recursion along the
level order. The tower equation holds for their pictures, and the earlier stages are
collected by the set of their graphs, without choice. -/

/-- A graph whose picture is a well-founded set. -/
abbrev Graph : Type (u + 1) :=
  {G : AccessiblePointedGraph.{u} // (HSet.mk G).WF}

/-- The well-founded set that a graph pictures. -/
def Graph.picture (G : Graph.{u}) : WellFoundedPart.{u} :=
  ⟨HSet.mk G.1, G.2⟩

/-- An operation on graphs presents an operation on well-founded sets when the picture of
its value is the value of the operation at the picture. -/
def Presents (univOfGraph : Graph.{u} → Graph.{u})
    (univOf : WellFoundedPart.{u} → WellFoundedPart.{u}) : Prop :=
  ∀ G, (univOfGraph G).picture = univOf G.picture

section Presented

open LevelOrder AccessiblePointedGraph

variable {L : Type} [LevelOrder L]

/-- The graph of the seed and the graphs of a family indexed by the levels below `α`, under
one new point. The index type is lifted to the universe of the nodes. -/
def generatingGraph (S : Graph.{u}) (α : L)
    (earlier : {β : L // β < α} → Graph.{u}) : Graph.{u} :=
  ⟨sup fun o : Option (ULift.{u} {β : L // β < α}) => o.elim S.1 fun β => (earlier β.down).1,
    wf_range fun o => by
      cases o with
      | none => exact S.2
      | some β => exact (earlier β.down).2⟩

/-- The children of the new point picture the seed and the given family. -/
theorem mem_picture_generatingGraph {S : Graph.{u}} {α : L}
    {earlier : {β : L // β < α} → Graph.{u}} {z : HSet.{u}} :
    z ∈ (generatingGraph S α earlier).picture.1 ↔
      z = S.picture.1 ∨ ∃ β, (earlier β).picture.1 = z := by
  change z ∈ HSet.range _ ↔ _
  rw [mem_range]
  constructor
  · rintro ⟨_ | β, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨β.down, rfl⟩
  · rintro (rfl | ⟨β, rfl⟩)
    · exact ⟨none, rfl⟩
    · exact ⟨some ⟨β⟩, rfl⟩

/-- The graphs of the stages, for an operation given on graphs: at every level the
operation is applied to the graph of the seed and the graphs of the earlier stages under one
new point. -/
noncomputable def stageGraph (univOfGraph : Graph.{u} → Graph.{u})
    (S : Graph.{u}) : L → Graph.{u} :=
  LevelOrder.wf.fix fun α earlier => univOfGraph (generatingGraph S α fun β => earlier β.1 β.2)

variable (univOfGraph : Graph.{u} → Graph.{u}) (S : Graph.{u})

/-- The recursion equation of the stages built as graphs. -/
theorem stageGraph_eq (α : L) :
    stageGraph univOfGraph S α =
      univOfGraph (generatingGraph S α fun β => stageGraph univOfGraph S β.1) :=
  LevelOrder.wf.fix_eq _ α

/-- The graph of the seed and of the earlier stages pictures the set of the seed and the
earlier stages. -/
theorem isGeneratingSet_generatingGraph (α : L) :
    IsGeneratingSet S.picture (fun β : L => (stageGraph univOfGraph S β).picture) α
      (generatingGraph S α fun β => stageGraph univOfGraph S β.1).picture :=
  fun _ => mem_picture_generatingGraph.trans (or_congr Iff.rfl
    ⟨fun ⟨β, e⟩ => ⟨β.1, β.2, e⟩, fun ⟨β, hβ, e⟩ => ⟨⟨β, hβ⟩, e⟩⟩)

/-- The pictures of the stages built as graphs are collected at every level, by the set of
their graphs. -/
theorem collectsEarlierStages_stageGraph :
    CollectsEarlierStages fun α : L => (stageGraph univOfGraph S α).picture :=
  fun _ => isCollected_of_presented (fun β => (stageGraph univOfGraph S β.1).1) fun _ => rfl

variable {univOfGraph} {univOf : WellFoundedPart.{u} → WellFoundedPart.{u}}

/-- The pictures of the stages built as graphs satisfy the tower equation of the presented
operation. -/
theorem isUniverseTower_stageGraph (presents : Presents univOfGraph univOf) :
    IsUniverseTower univOf S.picture fun α : L => (stageGraph univOfGraph S α).picture :=
  fun α N hN => by
    rw [hN.unique (isGeneratingSet_generatingGraph univOfGraph S α), ← presents]
    exact congrArg Graph.picture (stageGraph_eq univOfGraph S α)

end Presented

/-! ### Operations given on graphs -/

/-- One edge to the point of `G` pictures the singleton of the set that `G` pictures. -/
theorem mk_oneChild (G : AccessiblePointedGraph.{u}) :
    HSet.mk (AccessiblePointedGraph.oneChild G) = ({HSet.mk G} : HSet.{u}) :=
  HSet.ext fun _ => (mem_range (g := fun _ : PUnit.{u + 1} => G)).trans
    ⟨fun ⟨_, e⟩ => HSet.mem_singleton.mpr e.symm,
      fun h => ⟨PUnit.unit, (HSet.mem_singleton.mp h).symm⟩⟩

/-- The singleton, on graphs: one edge to the point. -/
def Graph.singleton (G : Graph.{u}) : Graph.{u} :=
  ⟨AccessiblePointedGraph.oneChild G.1, (mk_oneChild G.1).symm ▸ G.2.singleton⟩

/-- The singleton operation is given on graphs. -/
theorem presents_singleton : Presents Graph.singleton.{u} singleton :=
  fun G => Subtype.ext (mk_oneChild G.1)

/-- A presentation of the hypersets by graphs gives every operation on graphs: the graph of
the value. -/
def Graph.ofPresentation (p : Presentation.{u})
    (univOf : WellFoundedPart.{u} → WellFoundedPart.{u}) (G : Graph.{u}) :
    Graph.{u} :=
  ⟨p.graph (univOf G.picture).1, (p.mk_graph _).symm ▸ (univOf G.picture).2⟩

/-- The operation on graphs obtained from a presentation presents the operation. -/
theorem presents_ofPresentation (p : Presentation.{u})
    (univOf : WellFoundedPart.{u} → WellFoundedPart.{u}) :
    Presents (Graph.ofPresentation p univOf) univOf :=
  fun _ => Subtype.ext (p.mk_graph _)

/-- The least universe, on graphs, inside an enclosing universe given by a graph: the
children of its point that lie in every universe containing the set. -/
def Graph.hull (G E : Graph.{u}) : Graph.{u} :=
  ⟨AccessiblePointedGraph.sup fun c : {c // E.1.edge E.1.point c ∧
      ∀ U : WellFoundedPart.{u}, Mem G.picture U → IsGrothendieckUniverse U →
        decorate E.1.edge c ∈ U.1} => E.1.repoint c.1,
    (WellFoundedPart.hull G.picture E.picture).2⟩

/-- The graph of the least universe pictures the least universe. -/
theorem picture_hull (G E : Graph.{u}) :
    (Graph.hull G E).picture = WellFoundedPart.hull G.picture E.picture :=
  rfl

/-- An enclosure given on graphs gives the least-universe operation on graphs. What the
tree does not have is an enclosure given on graphs. -/
theorem presents_hull (e : UniverseEnclosure.{u})
    {encloseGraph : Graph.{u} → Graph.{u}}
    (presents : Presents encloseGraph e.enclose) :
    Presents (fun G => Graph.hull G (encloseGraph G)) e.univOf := fun G => by
  rw [picture_hull, presents]
  rfl

/-- Given a presentation of the hypersets by graphs, a tower with collected earlier stages
exists over every level order, for every operation and seed, without further choice. -/
theorem exists_isUniverseTower_of_presentation (p : Presentation.{u}) (L : Type) [LevelOrder L]
    (univOf : WellFoundedPart.{u} → WellFoundedPart.{u}) (seed : WellFoundedPart.{u}) :
    ∃ stage : L → WellFoundedPart.{u},
      IsUniverseTower univOf seed stage ∧ CollectsEarlierStages stage := by
  have same : Graph.picture ⟨p.graph seed.1, (p.mk_graph _).symm ▸ seed.2⟩ = seed :=
    Subtype.ext (p.mk_graph _)
  exact ⟨_, same ▸ isUniverseTower_stageGraph _ (presents_ofPresentation p univOf),
    collectsEarlierStages_stageGraph _ _⟩

/-! ### Without closure the tower laws fail -/

section Singleton

variable {L : Type} [LevelOrder L] {seed : WellFoundedPart.{u}} {stage : L → WellFoundedPart.{u}}

/-- For `univOf N = {N}`, no stage of a tower with collected earlier stages is a universe. -/
theorem IsUniverseTower.singleton_not_isGrothendieckUniverse
    (t : IsUniverseTower singleton seed stage) (collected : CollectsEarlierStages stage)
    (α : L) : ¬ IsGrothendieckUniverse (stage α) := by
  obtain ⟨N, -, hα⟩ := t.stage_eq collected α
  rw [hα]
  exact not_isGrothendieckUniverse_singleton N

/-- For `univOf N = {N}`, the seed is a member of no stage of a tower with collected earlier
stages. -/
theorem IsUniverseTower.singleton_seed_notMem (t : IsUniverseTower singleton seed stage)
    (collected : CollectsEarlierStages stage) (α : L) : ¬ Mem seed (stage α) := by
  obtain ⟨N, hN, hα⟩ := t.stage_eq collected α
  rw [hα]
  intro hmem
  have self : seed.1 ∈ N.1 := (hN seed.1).mpr (Or.inl rfl)
  rw [mem_singleton.mp hmem] at self
  exact N.2.notMem_self self

/-- Over every level order there is a tower for `univOf N = {N}` with collected earlier
stages, built as graphs without choice; none of its stages is a universe, at limit levels
as at the others. -/
theorem exists_singleton_tower (L : Type) [LevelOrder L] (S : Graph.{u}) :
    ∃ stage : L → WellFoundedPart.{u}, IsUniverseTower singleton S.picture stage ∧
      CollectsEarlierStages stage ∧ ∀ α, ¬ IsGrothendieckUniverse (stage α) :=
  ⟨_, isUniverseTower_stageGraph S presents_singleton, collectsEarlierStages_stageGraph _ S,
    fun α => (isUniverseTower_stageGraph S presents_singleton).singleton_not_isGrothendieckUniverse
      (collectsEarlierStages_stageGraph _ S) α⟩

end Singleton

/-! ### The first limit level

Over the ordinal notations below ε₀ the first limit level is `ω`. There the collection
hypothesis says that the finite stages are members of one set. -/

section Omega

variable {univOf : WellFoundedPart.{u} → WellFoundedPart.{u}} {seed : WellFoundedPart.{u}}
  {stage : Level → WellFoundedPart.{u}}

/-- Below `ω` the earlier stages are collected exactly when some set has every finite stage
as a member. -/
theorem isCollected_below_omega_iff :
    (IsCollected fun β : {β : Level // β < Level.omega} => stage β.1) ↔
      ∃ B : WellFoundedPart.{u}, ∀ n : Nat, Mem (stage (Level.ofNat n)) B := by
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨B, fun n => hB ⟨Level.ofNat n, Level.ofNat_lt_omega n⟩⟩
  · rintro ⟨B, hB⟩
    refine ⟨B, fun β => ?_⟩
    obtain ⟨n, hn⟩ := Level.exists_lt_ofNat_of_lt_omega β.2
    rw [← Level.levelOrder_ofNat] at hn
    obtain ⟨j, -, hj⟩ := LevelOrder.exists_ofNat_eq_of_lt hn
    change Mem (stage β.1) B
    rw [← hj, Level.levelOrder_ofNat]
    exact hB j

/-- For a universe operation and a tower with collected earlier stages, every finite stage
is a member of the stage at `ω`. -/
theorem IsUniverseTower.stage_ofNat_mem_stage_omega (op : IsUniverseOperator univOf)
    (t : IsUniverseTower univOf seed stage) (collected : CollectsEarlierStages stage)
    (n : Nat) : Mem (stage (Level.ofNat n)) (stage Level.omega) :=
  t.mem_of_lt op collected (Level.ofNat_lt_omega n)

/-- For `univOf N = {N}` there is a tower over the ordinal notations with collected earlier
stages whose stage at the limit level `ω` is not a universe. -/
theorem exists_singleton_tower_omega (S : Graph.{u}) :
    ∃ stage : Level → WellFoundedPart.{u}, IsUniverseTower singleton S.picture stage ∧
      CollectsEarlierStages stage ∧ ¬ IsGrothendieckUniverse (stage Level.omega) :=
  let ⟨stage, t, collected, h⟩ := exists_singleton_tower Level S
  ⟨stage, t, collected, h Level.omega⟩

end Omega

end WellFoundedPart

end Mettapedia.TypeTheory.MaterialSets.Hypersets
