import Mettapedia.TypeTheory.MaterialSets.Hypersets.Universes
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ZFSetModel
import Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure

/-!
# Universes of the well-founded part through `ZFSet`

The equivalence `wellFoundedPartEquivZFSet` between the well-founded hypersets and `ZFSet`
carries Grothendieck universes to the closed universes of
`Logic.HOL.Embedding.ZFSetUniverseClosure` and back (`isGrothendieckUniverse_iff_closed`). A
closed `ZFSet` universe has no pairing law, yet it is closed under pairs
(`closed_pair_mem`): `{a, b}` is the image of `𝒫 𝒫 ∅` under `z ↦ if ∅ ∈ z then b else a`. That
case split is excluded middle; the intuitionistic universe laws state pairing directly.

The least universe is carried as well (`equiv_hull`). Under the explicit large-cardinal
hypothesis `CofinalInaccessibles.{u}` (cofinally many inaccessible cardinals at level `u`), the
least-universe operation of `ZFSet`, carried to the well-founded part (`univOf`,
`equiv_univOf`), satisfies the four universe laws (`isUniverseOperator_univOf`). It is therefore
the operation of every universe enclosure (`UniverseEnclosure.univOf_eq_univOf`), and every
well-founded set lies in a universe (`exists_isGrothendieckUniverse`). The hypothesis is a
parameter of each statement, never an axiom.

Without any hypothesis, Lean's universe levels supply one universe at level `u + 1`: the
carried image of `V_κ` for the inaccessible `κ = Cardinal.univ.{u}` (`smallUniverse`,
`isGrothendieckUniverse_smallUniverse`), and so the least universe containing `∅` at that level
(`leastEmptyUniverse`, `equiv_leastEmptyUniverse`).

`ZFSetUniverseClosure` defines replacement through `Classical.allZFSetDefinable` and chooses
enclosures and inaccessible cardinals with `Classical.choice`; every statement here that
mentions a closed `ZFSet` universe inherits that dependency.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

open HSet Mettapedia.Logic.HOL.Embedding

universe u

/-! ## Pairs in a closed `ZFSet` universe -/

section Closed

open ZFSetUniverseClosure ZFSetHenkinInterpretation

theorem closed_empty_mem {U a : ZFSet.{u}} (hU : Closed U) (ha : a ∈ U) : (∅ : ZFSet.{u}) ∈ U :=
  hU.transitive _ (hU.power_mem ha) (ZFSet.mem_powerset.mpr (ZFSet.empty_subset a))

/-- A closed `ZFSet` universe is closed under pairs. The proof separates `𝒫 𝒫 ∅` by the case
split `∅ ∈ z`, which is excluded middle. -/
theorem closed_pair_mem {U a b : ZFSet.{u}} (hU : Closed U) (ha : a ∈ U) (hb : b ∈ U) :
    ({a, b} : ZFSet.{u}) ∈ U := by
  classical
  have hP : ZFSet.powerset (ZFSet.powerset (∅ : ZFSet.{u})) ∈ U :=
    hU.power_mem (hU.power_mem (closed_empty_mem hU ha))
  let f : ZFSet.{u} → ZFSet.{u} := fun z => if (∅ : ZFSet.{u}) ∈ z then b else a
  have values : ∀ z ∈ ZFSet.powerset (ZFSet.powerset (∅ : ZFSet.{u})), f z ∈ U := by
    intro z _
    by_cases h : (∅ : ZFSet.{u}) ∈ z
    · simp only [f, if_pos h]
      exact hb
    · simp only [f, if_neg h]
      exact ha
  have same : replacement (ZFSet.powerset (ZFSet.powerset (∅ : ZFSet.{u}))) f = {a, b} := by
    ext y
    rw [mem_replacement, ZFSet.mem_insert_iff, ZFSet.mem_singleton]
    constructor
    · rintro ⟨z, _, rfl⟩
      by_cases h : (∅ : ZFSet.{u}) ∈ z
      · right
        simp [f, h]
      · left
        simp [f, h]
    · rintro (rfl | rfl)
      · refine ⟨∅, ZFSet.mem_powerset.mpr (ZFSet.empty_subset _), ?_⟩
        simp only [f, if_neg (ZFSet.notMem_empty ∅)]
      · refine ⟨{∅}, ZFSet.mem_powerset.mpr fun w hw => ?_, ?_⟩
        · rw [ZFSet.mem_singleton.mp hw]
          exact ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)
        · simp only [f, if_pos (ZFSet.mem_singleton.mpr rfl)]
  rw [← same]
  exact hU.replacement_mem hP f values

end Closed

namespace WellFoundedPart

open ZFSetUniverseClosure ZFSetHenkinInterpretation

/-- The equivalence of the well-founded part with `ZFSet`. -/
local notation "toZF" => wellFoundedPartEquivZFSet

/-- Its inverse. -/
local notation "ofZF" => wellFoundedPartEquivZFSet.symm

/-! ## The operations through the equivalence -/

theorem mem_iff_equiv_mem {x X : WellFoundedPart.{u}} : Mem x X ↔ toZF x ∈ toZF X :=
  wellFoundedPartEquivZFSet_mem_iff.symm

theorem mem_equiv_iff {z : ZFSet.{u}} {X : WellFoundedPart.{u}} :
    z ∈ toZF X ↔ Mem (ofZF z) X := by
  rw [mem_iff_equiv_mem, Equiv.apply_symm_apply]

theorem subset_iff_equiv {X Y : WellFoundedPart.{u}} : Subset X Y ↔ toZF X ⊆ toZF Y := by
  constructor
  · intro h z hz
    exact mem_equiv_iff.mpr (h (mem_equiv_iff.mp hz))
  · intro h z hz
    have hwf : z.WF := X.2.mem hz
    exact mem_iff_equiv_mem.mpr (h ((mem_iff_equiv_mem (x := ⟨z, hwf⟩) (X := X)).mp hz))

theorem equiv_sUnion (X : WellFoundedPart.{u}) : toZF (sUnion X) = ZFSet.sUnion (toZF X) :=
  equiv_union X

theorem equiv_powerset (X : WellFoundedPart.{u}) :
    toZF (powerset X) = ZFSet.powerset (toZF X) := by
  apply ofZFSet_injective
  rw [ofZFSet_equiv, ofZFSet_powerset, ofZFSet_equiv]
  rfl

theorem equiv_upair (x y : WellFoundedPart.{u}) : toZF (upair x y) = {toZF x, toZF y} := by
  apply ofZFSet_injective
  rw [ofZFSet_equiv, ofZFSet_pair, ofZFSet_equiv, ofZFSet_equiv]
  rfl

/-- The image of a family below a bound, through the equivalence. -/
theorem mem_equiv_imageWithin {B X : WellFoundedPart.{u}} {F : El Mem X → WellFoundedPart.{u}}
    (bound : ∀ a, Mem (F a) B) {z : ZFSet.{u}} :
    z ∈ toZF (imageWithin B X F) ↔ ∃ a, toZF (F a) = z := by
  rw [mem_equiv_iff, mem_imageWithin bound]
  exact exists_congr fun _ => ⟨fun e => by rw [e, Equiv.apply_symm_apply],
    fun e => by rw [← e, Equiv.symm_apply_apply]⟩

/-! ## Universes through the equivalence -/

/-- A well-founded set is a Grothendieck universe exactly when its `ZFSet` is a closed
universe. -/
theorem isGrothendieckUniverse_iff_closed (U : WellFoundedPart.{u}) :
    IsGrothendieckUniverse U ↔ Closed (toZF U) := by
  constructor
  · intro hU
    refine ⟨fun a ha y hy => ?_, fun {a} ha => ?_, fun {a} ha => ?_, fun {a} ha f hf => ?_⟩
    · have hA := mem_equiv_iff.mp ha
      have hy' : Mem (ofZF y) (ofZF a) :=
        mem_iff_equiv_mem.mpr (by rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply])
      exact mem_equiv_iff.mpr (hU.transitive hA hy')
    · have h := mem_iff_equiv_mem.mp (hU.sUnion_mem (mem_equiv_iff.mp ha))
      rwa [equiv_sUnion, Equiv.apply_symm_apply] at h
    · have h := mem_iff_equiv_mem.mp (hU.powerset_mem (mem_equiv_iff.mp ha))
      rwa [equiv_powerset, Equiv.apply_symm_apply] at h
    · let F : El Mem (ofZF a) → WellFoundedPart.{u} := fun b => ofZF (f (toZF b.1))
      have hb : ∀ b : El Mem (ofZF a), toZF b.1 ∈ a := fun b => by
        have h := mem_iff_equiv_mem.mp b.2
        rwa [Equiv.apply_symm_apply] at h
      have hF : ∀ b, Mem (F b) U := fun b => mem_equiv_iff.mp (hf _ (hb b))
      have same : toZF (imageWithin U (ofZF a) F) = replacement a f := by
        ext z
        rw [mem_equiv_imageWithin hF, mem_replacement]
        constructor
        · rintro ⟨b, rfl⟩
          exact ⟨toZF b.1, hb b, (Equiv.apply_symm_apply _ _).symm⟩
        · rintro ⟨x, hx, rfl⟩
          refine ⟨⟨ofZF x, mem_equiv_iff.mp (by rwa [Equiv.apply_symm_apply])⟩, ?_⟩
          change toZF (ofZF (f (toZF (ofZF x)))) = f x
          rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      rw [← same]
      exact mem_iff_equiv_mem.mp (hU.image_mem (mem_equiv_iff.mp ha) F hF)
  · intro hU
    refine ⟨fun X z hX hz => ?_, fun X hX => ?_, fun X hX => ?_, fun x y hx hy => ?_,
      fun X hX F hF => ?_⟩
    · have hwf : z.WF := X.2.mem hz
      exact mem_iff_equiv_mem.mpr (hU.transitive _ (mem_iff_equiv_mem.mp hX)
        ((mem_iff_equiv_mem (x := ⟨z, hwf⟩) (X := X)).mp hz))
    · rw [mem_iff_equiv_mem, equiv_sUnion]
      exact hU.union_mem (mem_iff_equiv_mem.mp hX)
    · rw [mem_iff_equiv_mem, equiv_powerset]
      exact hU.power_mem (mem_iff_equiv_mem.mp hX)
    · rw [mem_iff_equiv_mem, equiv_upair]
      exact closed_pair_mem hU (mem_iff_equiv_mem.mp hx) (mem_iff_equiv_mem.mp hy)
    · classical
      have hX' : ∀ {x : ZFSet.{u}}, x ∈ toZF X → Mem (ofZF x) X := fun h => mem_equiv_iff.mp h
      let f : ZFSet.{u} → ZFSet.{u} := fun x => if h : x ∈ toZF X then toZF (F ⟨_, hX' h⟩) else ∅
      have hf : ∀ b : El Mem X, f (toZF b.1) = toZF (F b) := fun b => by
        have hb : toZF b.1 ∈ toZF X := mem_iff_equiv_mem.mp b.2
        simp only [f, dif_pos hb]
        exact congrArg (fun c => toZF (F c)) (El.ext propositional (Equiv.symm_apply_apply _ _))
      have values : ∀ x ∈ toZF X, f x ∈ toZF U := fun x hx => by
        have e := hf ⟨ofZF x, hX' hx⟩
        rw [Equiv.apply_symm_apply] at e
        rw [e]
        exact mem_iff_equiv_mem.mp (hF _)
      have same : toZF (imageWithin U X F) = replacement (toZF X) f := by
        ext z
        rw [mem_equiv_imageWithin hF, mem_replacement]
        constructor
        · rintro ⟨b, rfl⟩
          exact ⟨toZF b.1, mem_iff_equiv_mem.mp b.2, hf b⟩
        · rintro ⟨x, hx, rfl⟩
          have e := hf ⟨ofZF x, hX' hx⟩
          rw [Equiv.apply_symm_apply] at e
          exact ⟨_, e.symm⟩
      rw [mem_iff_equiv_mem, same]
      exact hU.replacement_mem (mem_iff_equiv_mem.mp hX) f values

/-- The least universe is carried to the least closed universe. -/
theorem equiv_hull (N B : WellFoundedPart.{u}) :
    toZF (hull N B) = ZFSetUniverseClosure.hull (toZF N) (toZF B) := by
  ext z
  rw [mem_equiv_iff, ZFSetUniverseClosure.mem_hull]
  change (ofZF z).1 ∈ (hull N B).1 ↔ _
  rw [mem_hull]
  refine and_congr (mem_equiv_iff.symm) ⟨fun h V hN hV => ?_, fun h U hN hU => ?_⟩
  · have hU : IsGrothendieckUniverse (ofZF V) :=
      (isGrothendieckUniverse_iff_closed _).mpr (by rwa [Equiv.apply_symm_apply])
    have hN' : Mem N (ofZF V) := by
      rw [mem_iff_equiv_mem, Equiv.apply_symm_apply]
      exact hN
    have hz := mem_equiv_iff.mpr (h _ hN' hU)
    rwa [Equiv.apply_symm_apply] at hz
  · exact mem_equiv_iff.mp
      (h _ (mem_iff_equiv_mem.mp hN) ((isGrothendieckUniverse_iff_closed U).mp hU))

/-! ## The least-universe operation under cofinally many inaccessibles -/

/-- The least-universe operation of `ZFSet`, carried to the well-founded part. -/
noncomputable def univOf (h : CofinalInaccessibles.{u}) (N : WellFoundedPart.{u}) :
    WellFoundedPart.{u} :=
  ofZF (ZFSetUniverseClosure.univOf h (toZF N))

theorem equiv_univOf (h : CofinalInaccessibles.{u}) (N : WellFoundedPart.{u}) :
    toZF (univOf h N) = ZFSetUniverseClosure.univOf h (toZF N) :=
  Equiv.apply_symm_apply _ _

/-- Under cofinally many inaccessibles, the carried operation satisfies the four universe
laws. -/
theorem isUniverseOperator_univOf (h : CofinalInaccessibles.{u}) :
    IsUniverseOperator (univOf h) where
  mem_univOf N := by
    rw [mem_iff_equiv_mem, equiv_univOf]
    exact ZFSetUniverseClosure.mem_univOf h _
  isGrothendieckUniverse N := by
    rw [isGrothendieckUniverse_iff_closed, equiv_univOf]
    exact ZFSetUniverseClosure.univOf_closed h _
  minimal N U hN hU := by
    rw [subset_iff_equiv, equiv_univOf]
    exact ZFSetUniverseClosure.univOf_minimal h (mem_iff_equiv_mem.mp hN)
      ((isGrothendieckUniverse_iff_closed U).mp hU)

/-- The universe enclosure given by cofinally many inaccessibles. -/
noncomputable def enclosure (h : CofinalInaccessibles.{u}) : UniverseEnclosure.{u} where
  enclose := univOf h
  mem_enclose := (isUniverseOperator_univOf h).mem_univOf
  isGrothendieckUniverse_enclose := (isUniverseOperator_univOf h).isGrothendieckUniverse

/-- Every universe enclosure yields the carried operation. -/
theorem UniverseEnclosure.univOf_eq_univOf (e : UniverseEnclosure.{u})
    (h : CofinalInaccessibles.{u}) : e.univOf = WellFoundedPart.univOf h :=
  e.isUniverseOperator.unique (isUniverseOperator_univOf h)

/-- Under cofinally many inaccessibles, every well-founded set lies in a universe. -/
theorem exists_isGrothendieckUniverse (h : CofinalInaccessibles.{u}) (N : WellFoundedPart.{u}) :
    ∃ U, Mem N U ∧ IsGrothendieckUniverse U :=
  ⟨univOf h N, (isUniverseOperator_univOf h).mem_univOf N,
    (isUniverseOperator_univOf h).isGrothendieckUniverse N⟩

/-! ## A universe from Lean's universe levels, without hypothesis -/

/-- The universe `V_κ` at level `u + 1`, for the inaccessible `κ = Cardinal.univ.{u}`. -/
noncomputable def smallUniverse : WellFoundedPart.{u + 1} :=
  ofZF ZFSetUniverseClosure.smallUniverse.{u}

theorem isGrothendieckUniverse_smallUniverse : IsGrothendieckUniverse smallUniverse.{u} := by
  rw [isGrothendieckUniverse_iff_closed, smallUniverse, Equiv.apply_symm_apply]
  exact smallUniverse_closed

theorem empty_mem_smallUniverse : Mem empty smallUniverse.{u} := by
  rw [mem_iff_equiv_mem, smallUniverse, Equiv.apply_symm_apply]
  have h : toZF empty.{u + 1} = ∅ := by
    apply ofZFSet_injective
    rw [ofZFSet_equiv, ofZFSet_empty]
    rfl
  rw [h]
  exact ZFSetUniverseClosure.empty_mem_smallUniverse

/-- The least universe containing `∅` at level `u + 1`, without any hypothesis. -/
noncomputable def leastEmptyUniverse : WellFoundedPart.{u + 1} :=
  hull empty smallUniverse.{u}

theorem isGrothendieckUniverse_leastEmptyUniverse :
    IsGrothendieckUniverse leastEmptyUniverse.{u} :=
  hull_isGrothendieckUniverse isGrothendieckUniverse_smallUniverse

theorem empty_mem_leastEmptyUniverse : Mem empty leastEmptyUniverse.{u} :=
  mem_hull_self empty_mem_smallUniverse

theorem equiv_leastEmptyUniverse :
    toZF leastEmptyUniverse.{u} = ZFSetUniverseClosure.leastEmptyUniverse.{u} := by
  rw [leastEmptyUniverse, equiv_hull, smallUniverse, Equiv.apply_symm_apply]
  have h : toZF empty.{u + 1} = ∅ := by
    apply ofZFSet_injective
    rw [ofZFSet_equiv, ofZFSet_empty]
    rfl
  rw [h]
  rfl

end WellFoundedPart

end Mettapedia.TypeTheory.MaterialSets.Hypersets
