import Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure
import Mettapedia.SetTheory.Profiles.Principles
import Mathlib.SetTheory.ZFC.VonNeumann

/-!
# Universes are not a consequence of the bubble's laws

The well-founded bubble satisfies seven set principles (`BubbleLaws`): extensionality, the
empty set, union, power set, separation, replacement and membership induction. HOTG adds a
closed universe around every set. The universe is an independent commitment:

* the hereditarily finite sets `V_ω` satisfy the seven principles
  (`hereditarilyFinite_bubbleLaws`), and contain no closed universe holding the empty set
  (`no_closed_universe_in_hereditarilyFinite`): a closed universe holding `∅` holds every
  iterated power set of `∅`, so its rank is at least `ω`;
* all of `ZFSet` satisfies the same principles (`zfSet_bubbleLaws`) and contains such a
  universe, `V_ω` itself (`vonNeumann_omega_closed`).

Both statements are about classes of `ZFSet` closed under the set operations
(`TransitiveClass`), and the seven principles are proved once for any such class
(`TransitiveClass.bubbleLaws`). Replacement on a class picks the unique image of each member
with `Classical.choose`.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts

open Mettapedia.SetTheory.Profiles
open Mettapedia.Logic.HOL.Embedding
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (mem_replacement)
open Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure (Closed)
open scoped ZFSet Cardinal Ordinal

universe u

/-- The bubble's seven set principles: the Megalodon principles without the choice operator. -/
structure BubbleLaws {S : Type u} (mem : Mem S) : Prop where
  extensional : Extensional mem
  empty : HasEmpty mem
  union : HasUnion mem
  power : HasPower mem
  separation : HasSeparation mem
  replacement : HasReplacement mem
  induction : HasMemInduction mem

/-- A class of sets that is transitive, holds the empty set, and is closed under union,
power set and replacement images. -/
structure TransitiveClass (M : ZFSet.{u} → Prop) : Prop where
  transitive : ∀ {x y : ZFSet.{u}}, M x → y ∈ x → M y
  empty : M ∅
  union : ∀ {a : ZFSet.{u}}, M a → M (ZFSet.sUnion a)
  power : ∀ {a : ZFSet.{u}}, M a → M (ZFSet.powerset a)
  replacement : ∀ {a : ZFSet.{u}} (f : ZFSet.{u} → ZFSet.{u}), M a → (∀ x ∈ a, M (f x)) →
    M (ZFSetHenkinInterpretation.replacement a f)

namespace TransitiveClass

variable {M : ZFSet.{u} → Prop} (hM : TransitiveClass M)
include hM

/-- **The seven principles hold on every transitive class.** -/
theorem bubbleLaws : BubbleLaws (fun x y : {x : ZFSet.{u} // M x} => x.1 ∈ y.1) where
  extensional x y h := Subtype.ext (ZFSet.ext fun z => ⟨fun hz =>
      (h ⟨z, hM.transitive x.2 hz⟩).mp hz,
    fun hz => (h ⟨z, hM.transitive y.2 hz⟩).mpr hz⟩)
  empty := ⟨⟨∅, hM.empty⟩, fun z hz => ZFSet.notMem_empty _ hz⟩
  union a := ⟨⟨ZFSet.sUnion a.1, hM.union a.2⟩, fun z => by
    show z.1 ∈ ZFSet.sUnion a.1 ↔ _
    rw [ZFSet.mem_sUnion]
    constructor
    · rintro ⟨y, hya, hzy⟩
      exact ⟨⟨y, hM.transitive a.2 hya⟩, hya, hzy⟩
    · rintro ⟨y, hya, hzy⟩
      exact ⟨y.1, hya, hzy⟩⟩
  power a := ⟨⟨ZFSet.powerset a.1, hM.power a.2⟩, fun z => by
    show z.1 ∈ ZFSet.powerset a.1 ↔ _
    rw [ZFSet.mem_powerset]
    constructor
    · intro h w hw
      exact h hw
    · intro h w hw
      exact h ⟨w, hM.transitive z.2 hw⟩ hw⟩
  separation a P := by
    refine ⟨⟨ZFSet.sep (fun z => ∃ hz : M z, P ⟨z, hz⟩) a.1,
      hM.transitive (hM.power a.2) (ZFSet.mem_powerset.mpr ZFSet.sep_subset)⟩, fun z => ?_⟩
    show z.1 ∈ ZFSet.sep (fun w => ∃ hw : M w, P ⟨w, hw⟩) a.1 ↔ z.1 ∈ a.1 ∧ P z
    rw [ZFSet.mem_sep]
    exact ⟨fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, z.2, h2⟩⟩
  replacement a R hR := by
    classical
    let g : ZFSet.{u} → ZFSet.{u} := fun z =>
      if h : ∃ hz : M z, z ∈ a.1 then (Classical.choose (hR ⟨z, h.1⟩ h.2)).1 else ∅
    have hg : ∀ (x : {x // M x}) (hx : x.1 ∈ a.1), g x.1 = (Classical.choose (hR x hx)).1 := by
      intro x hx
      simp only [g, dif_pos (⟨x.2, hx⟩ : ∃ hz : M x.1, x.1 ∈ a.1)]
    have gM : ∀ z ∈ a.1, M (g z) := fun z hz => by
      rw [hg ⟨z, hM.transitive a.2 hz⟩ hz]
      exact (Classical.choose (hR ⟨z, hM.transitive a.2 hz⟩ hz)).2
    refine ⟨⟨ZFSetHenkinInterpretation.replacement a.1 g, hM.replacement g a.2 gM⟩, fun y => ?_⟩
    show y.1 ∈ ZFSetHenkinInterpretation.replacement a.1 g ↔ _
    rw [mem_replacement]
    constructor
    · rintro ⟨z, hz, hzy⟩
      let x : {x // M x} := ⟨z, hM.transitive a.2 hz⟩
      refine ⟨x, hz, ?_⟩
      have hy : y = Classical.choose (hR x hz) := Subtype.ext (by rw [← hzy, hg x hz])
      rw [hy]
      exact (Classical.choose_spec (hR x hz)).1
    · rintro ⟨x, hx, hxy⟩
      refine ⟨x.1, hx, ?_⟩
      rw [hg x hx]
      exact congrArg Subtype.val ((Classical.choose_spec (hR x hx)).2 y hxy).symm
  induction P step x := by
    rcases x with ⟨x, hx⟩
    induction x using ZFSet.inductionOn with
    | h x ih =>
      exact step ⟨x, hx⟩ fun y hy => ih y.1 hy y.2

end TransitiveClass

/-! ## The hereditarily finite sets -/

theorem card_lt_aleph0_of_mem_omega {a : ZFSet.{u}} (ha : a ∈ V_ ω) : a.card < ℵ₀ := by
  calc a.card ≤ (V_ a.rank).card := ZFSet.card_mono (ZFSet.subset_vonNeumann_self a)
    _ = Cardinal.preBeth a.rank := ZFSet.card_vonNeumann _
    _ < Cardinal.preBeth ω := Cardinal.preBeth_strictMono (ZFSet.mem_vonNeumann.mp ha)
    _ = ℵ₀ := Cardinal.preBeth_omega

theorem replacement_eq_range' (a : ZFSet.{u}) (f : ZFSet.{u} → ZFSet.{u}) :
    ZFSetHenkinInterpretation.replacement a f = ZFSet.range (fun i : Shrink a => f ((equivShrink a).symm i).1) := by
  apply ZFSet.ext
  intro y
  rw [mem_replacement, ZFSet.mem_range]
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨equivShrink a ⟨x, hx⟩, by simpa using hxy⟩
  · rintro ⟨i, hiy⟩
    exact ⟨((equivShrink a).symm i).1, ((equivShrink a).symm i).2, hiy⟩

/-- **`V_ω` is a closed universe**: transitive and closed under union, power set and
higher-order replacement. -/
theorem vonNeumann_omega_closed : Closed (V_ ω : ZFSet.{u}) where
  transitive := ZFSet.isTransitive_vonNeumann _
  union_mem ha := ZFSet.mem_vonNeumann.mpr
    ((ZFSet.rank_sUnion_le _).trans_lt (ZFSet.mem_vonNeumann.mp ha))
  power_mem ha := by
    rw [ZFSet.mem_vonNeumann, ZFSet.rank_powerset]
    exact Ordinal.isSuccLimit_omega0.succ_lt (ZFSet.mem_vonNeumann.mp ha)
  replacement_mem ha f hf := by
    rw [ZFSet.mem_vonNeumann, replacement_eq_range', ZFSet.rank_range]
    apply Ordinal.iSup_lt_of_lt_cof
    · rw [Ordinal.cof_omega0]
      exact card_lt_aleph0_of_mem_omega ha
    · intro i
      exact Ordinal.isSuccLimit_omega0.succ_lt
        (ZFSet.mem_vonNeumann.mp (hf _ ((equivShrink _).symm i).2))

theorem empty_mem_vonNeumann_omega : (∅ : ZFSet.{u}) ∈ V_ ω := by
  rw [ZFSet.mem_vonNeumann, ZFSet.rank_empty]
  exact Ordinal.omega0_pos

/-- The hereditarily finite sets form a transitive class. -/
theorem hereditarilyFinite_transitiveClass : TransitiveClass (fun x : ZFSet.{u} => x ∈ V_ ω) where
  transitive hx hy := ZFSet.isTransitive_vonNeumann _ _ hx hy
  empty := empty_mem_vonNeumann_omega
  union := vonNeumann_omega_closed.union_mem
  power := vonNeumann_omega_closed.power_mem
  replacement f ha hf := vonNeumann_omega_closed.replacement_mem ha f hf

/-- **The hereditarily finite sets satisfy the bubble's seven principles.** -/
theorem hereditarilyFinite_bubbleLaws :
    BubbleLaws (fun x y : {x : ZFSet.{u} // x ∈ V_ ω} => x.1 ∈ y.1) :=
  hereditarilyFinite_transitiveClass.bubbleLaws

/-- All of `ZFSet` is a transitive class. -/
theorem zfSet_transitiveClass : TransitiveClass (fun _ : ZFSet.{u} => True) where
  transitive _ _ := trivial
  empty := trivial
  union _ := trivial
  power _ := trivial
  replacement _ _ _ := trivial

theorem zfSet_bubbleLaws : BubbleLaws (fun x y : {_x : ZFSet.{u} // True} => x.1 ∈ y.1) :=
  zfSet_transitiveClass.bubbleLaws

theorem rank_powerset_iterate (n : ℕ) :
    ZFSet.rank (ZFSet.powerset^[n] (∅ : ZFSet.{u})) = n := by
  induction n with
  | zero => exact ZFSet.rank_empty
  | succ n ih =>
    rw [Function.iterate_succ_apply', ZFSet.rank_powerset, ih, Order.succ_eq_add_one]
    push_cast
    rfl

theorem powerset_iterate_mem {U : ZFSet.{u}} (hU : Closed U) (h : (∅ : ZFSet.{u}) ∈ U) :
    ∀ n : ℕ, ZFSet.powerset^[n] (∅ : ZFSet.{u}) ∈ U
  | 0 => h
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    exact hU.power_mem (powerset_iterate_mem hU h n)

/-- **No closed universe holding the empty set is hereditarily finite.** -/
theorem no_closed_universe_in_hereditarilyFinite :
    ¬ ∃ U : ZFSet.{u}, U ∈ V_ ω ∧ (∅ : ZFSet.{u}) ∈ U ∧ Closed U := by
  rintro ⟨U, hUω, h0, hU⟩
  obtain ⟨m, hm⟩ := Ordinal.lt_omega0.mp (ZFSet.mem_vonNeumann.mp hUω)
  have := ZFSet.rank_lt_of_mem (powerset_iterate_mem hU h0 m)
  rw [rank_powerset_iterate, hm] at this
  exact lt_irrefl _ this

/-- **`ZFSet` has a closed universe holding the empty set.** -/
theorem exists_closed_universe : ∃ U : ZFSet.{u}, (∅ : ZFSet.{u}) ∈ U ∧ Closed U :=
  ⟨V_ ω, empty_mem_vonNeumann_omega, vonNeumann_omega_closed⟩

end Mettapedia.SetTheory.CarveOuts
