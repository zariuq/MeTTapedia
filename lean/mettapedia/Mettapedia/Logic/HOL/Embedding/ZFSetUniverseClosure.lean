import Mathlib.SetTheory.ZFC.VonNeumann
import Mathlib.SetTheory.Cardinal.Regular
import Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation

/-!
# Internal closed universes for the actual higher-order set interpretation

An inaccessible rank segment is closed under union, powerset and higher-order
replacement. A least closed universe containing a set is then constructed by
separation inside any enclosing closed universe. Its minimality is proved,
not supplied as a model field.

The total enclosing-universe operation constructed below at a fixed `ZFSet`
level is relative to a large-cardinal assumption. External Lean levels do not
silently provide cofinally many internal inaccessible cardinals at that level.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure

open ZFSetHenkinInterpretation
open scoped ZFSet Cardinal

universe u

/-- Exactly the transitivity and closure conditions used by the HOTG
universe operations, over the already constructed higher-order replacement. -/
structure Closed (U : ZFSet.{u}) : Prop where
  transitive : ZFSet.IsTransitive U
  union_mem : ∀ {a : ZFSet.{u}}, a ∈ U → ZFSet.sUnion a ∈ U
  power_mem : ∀ {a : ZFSet.{u}}, a ∈ U → ZFSet.powerset a ∈ U
  replacement_mem : ∀ {a : ZFSet.{u}}, a ∈ U →
    ∀ f : ZFSet.{u} → ZFSet.{u},
      (∀ x ∈ a, f x ∈ U) → replacement a f ∈ U

/-- Any subset of a member is again a member: use powerset and transitivity.
This is what places bounded HOL refinements inside the same universe. -/
theorem Closed.subset_mem {U a b : ZFSet.{u}} (hU : Closed U)
    (ha : a ∈ U) (hba : b ⊆ a) : b ∈ U :=
  hU.transitive _ (hU.power_mem ha) (ZFSet.mem_powerset.mpr hba)

theorem Closed.separation_mem {U a : ZFSet.{u}} (hU : Closed U)
    (ha : a ∈ U) (p : ZFSet.{u} → Prop) : ZFSet.sep p a ∈ U :=
  hU.subset_mem ha ZFSet.sep_subset

theorem Closed.predicateSet_mem {U : ZFSet.{u}} (hU : Closed U)
    {Γ : Ctx Unit} (bound : Expr Γ set) (φ : Formula Symbol (set :: Γ))
    (valuation : HenkinDependentFamilyInterpretation.AdmissibleContext model.{u} Γ)
    (hbound : model.denote bound valuation.1 ∈ U) :
    predicateSet bound φ valuation ∈ U :=
  hU.separation_mem hbound _

/-! ## Inaccessible rank segments supply actual closed sets -/

theorem card_lt_of_mem_inaccessible {κ : Cardinal.{u}} (hκ : κ.IsInaccessible)
    {a : ZFSet.{u}} (ha : a ∈ V_ κ.ord) : a.card < κ := by
  calc
    a.card ≤ (V_ a.rank).card := ZFSet.card_mono (ZFSet.subset_vonNeumann_self a)
    _ = Cardinal.preBeth a.rank := ZFSet.card_vonNeumann _
    _ < Cardinal.preBeth κ.ord := Cardinal.preBeth_strictMono (ZFSet.mem_vonNeumann.mp ha)
    _ = κ := hκ.preBeth_ord

private theorem replacement_eq_range (a : ZFSet.{u}) (f : ZFSet.{u} → ZFSet.{u}) :
    replacement a f = ZFSet.range
      (fun i : Shrink a => f ((equivShrink a).symm i).1) := by
  apply ZFSet.ext
  intro y
  rw [mem_replacement, ZFSet.mem_range]
  constructor
  · rintro ⟨x, hx, hxy⟩
    refine ⟨equivShrink a ⟨x, hx⟩, ?_⟩
    simpa using hxy
  · rintro ⟨i, hiy⟩
    exact ⟨((equivShrink a).symm i).1, ((equivShrink a).symm i).2, hiy⟩

theorem inaccessible_closed {κ : Cardinal.{u}} (hκ : κ.IsInaccessible) :
    Closed (V_ κ.ord) where
  transitive := ZFSet.isTransitive_vonNeumann _
  union_mem ha := ZFSet.mem_vonNeumann.mpr
    ((ZFSet.rank_sUnion_le _).trans_lt (ZFSet.mem_vonNeumann.mp ha))
  power_mem ha := by
    rw [ZFSet.mem_vonNeumann, ZFSet.rank_powerset]
    exact (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le).succ_lt
      (ZFSet.mem_vonNeumann.mp ha)
  replacement_mem ha f hf := by
    rw [ZFSet.mem_vonNeumann, replacement_eq_range, ZFSet.rank_range]
    apply Ordinal.iSup_lt_of_lt_cof
    · rw [hκ.isRegular.cof_ord]
      exact card_lt_of_mem_inaccessible hκ ha
    · intro i
      exact (Cardinal.isSuccLimit_ord hκ.aleph0_lt.le).succ_lt
        (ZFSet.mem_vonNeumann.mp (hf _ ((equivShrink _).symm i).2))

/-! ## Least closure, rather than a chosen arbitrary enclosure -/

/-- Intersect all closed universes containing `N`, using one known enclosure
as the separation bound. No set of all closed universes is required. -/
noncomputable def hull (N bound : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => ∀ U : ZFSet.{u}, N ∈ U → Closed U → x ∈ U) bound

theorem mem_hull {N bound x : ZFSet.{u}} : x ∈ hull N bound ↔
    x ∈ bound ∧ ∀ U : ZFSet.{u}, N ∈ U → Closed U → x ∈ U :=
  ZFSet.mem_sep

theorem contains_hull {N bound : ZFSet.{u}} (hN : N ∈ bound) : N ∈ hull N bound :=
  mem_hull.mpr ⟨hN, fun _ h _ => h⟩

theorem hull_minimal {N bound U : ZFSet.{u}} (hN : N ∈ U) (hU : Closed U) :
    hull N bound ⊆ U := fun _ hx => (mem_hull.mp hx).2 U hN hU

theorem hull_closed {N bound : ZFSet.{u}} (hbound : Closed bound) :
    Closed (hull N bound) where
  transitive y hy x hxy := by
    obtain ⟨hyb, hyall⟩ := mem_hull.mp hy
    exact mem_hull.mpr ⟨hbound.transitive y hyb hxy,
      fun U hNU hU => hU.transitive y (hyall U hNU hU) hxy⟩
  union_mem ha := by
    obtain ⟨hab, haall⟩ := mem_hull.mp ha
    exact mem_hull.mpr ⟨hbound.union_mem hab,
      fun U hNU hU => hU.union_mem (haall U hNU hU)⟩
  power_mem ha := by
    obtain ⟨hab, haall⟩ := mem_hull.mp ha
    exact mem_hull.mpr ⟨hbound.power_mem hab,
      fun U hNU hU => hU.power_mem (haall U hNU hU)⟩
  replacement_mem ha f hf := by
    obtain ⟨hab, haall⟩ := mem_hull.mp ha
    exact mem_hull.mpr
      ⟨hbound.replacement_mem hab f (fun x hx => (mem_hull.mp (hf x hx)).1),
       fun U hNU hU => hU.replacement_mem (haall U hNU hU) f
         (fun x hx => (mem_hull.mp (hf x hx)).2 U hNU hU)⟩

theorem hull_independent {N left right : ZFSet.{u}}
    (hleft : Closed left) (hNleft : N ∈ left)
    (hright : Closed right) (hNright : N ∈ right) :
    hull N left = hull N right :=
  ZFSet.ext fun _ =>
    ⟨fun h => hull_minimal (contains_hull hNright) (hull_closed hright) h,
      fun h => hull_minimal (contains_hull hNleft) (hull_closed hleft) h⟩

/-! ## A total operation under a precise relative cardinal assumption -/

/-- A sufficient relative model assumption for an enclosing universe around
every set at this fixed `ZFSet` level. This is a property of cardinals,
not an assumption that the desired semantic interpretation is correct. -/
def CofinalInaccessibles : Prop :=
  ∀ α : Ordinal.{u}, ∃ κ : Cardinal.{u}, κ.IsInaccessible ∧ α < κ.ord

theorem exists_closed_enclosure (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}) :
    ∃ U : ZFSet.{u}, N ∈ U ∧ Closed U := by
  obtain ⟨κ, hκ, hrank⟩ := h N.rank
  exact ⟨V_ κ.ord, ZFSet.mem_vonNeumann.mpr hrank, inaccessible_closed hκ⟩

/-- Least closed universe containing `N`, obtained by separation inside
an inaccessible-rank enclosure. Its value is independent of that enclosure. -/
noncomputable def univOf (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}) : ZFSet.{u} :=
  hull N (Classical.choose (exists_closed_enclosure h N))

theorem mem_univOf (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}) :
    N ∈ univOf h N :=
  contains_hull (Classical.choose_spec (exists_closed_enclosure h N)).1

theorem univOf_closed (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}) :
    Closed (univOf h N) :=
  hull_closed (Classical.choose_spec (exists_closed_enclosure h N)).2

theorem univOf_minimal (h : CofinalInaccessibles.{u})
    {N U : ZFSet.{u}} (hN : N ∈ U) (hU : Closed U) : univOf h N ⊆ U :=
  hull_minimal hN hU

/-- Least-universe formation respects inclusion of input sets. -/
theorem univOf_mono (h : CofinalInaccessibles.{u})
    {N M : ZFSet.{u}} (hNM : N ⊆ M) : univOf h N ⊆ univOf h M :=
  univOf_minimal h ((univOf_closed h M).subset_mem (mem_univOf h M) hNM)
    (univOf_closed h M)

/-- The assumption's proof supplies no observable choice of enclosure. -/
theorem univOf_independent (h k : CofinalInaccessibles.{u}) (N : ZFSet.{u}) :
    univOf h N = univOf k N :=
  ZFSet.ext fun _ =>
    ⟨fun hx => univOf_minimal h (mem_univOf k N) (univOf_closed k N) hx,
      fun hx => univOf_minimal k (mem_univOf h N) (univOf_closed h N) hx⟩

/-- A HOL-generated bounded refinement stays inside any enclosing closed
universe containing its interpreted bound, including the least enclosure. -/
theorem predicateSet_mem_univOf (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} (bound : Expr Γ set) (φ : Formula Symbol (set :: Γ))
    (valuation : HenkinDependentFamilyInterpretation.AdmissibleContext model.{u} Γ) :
    predicateSet bound φ valuation ∈ univOf h (model.denote bound valuation.1) :=
  (univOf_closed h _).predicateSet_mem bound φ valuation (mem_univOf h _)

/-! ## Concrete and negative controls -/

/-- Lean's lower universe gives one particular inaccessible at a higher
set level. This does not establish cofinally many inaccessibles there. -/
noncomputable def smallUniverse : ZFSet.{u + 1} :=
  V_ (Cardinal.univ.{u, 0}).ord

theorem smallUniverse_closed : Closed smallUniverse.{u} :=
  inaccessible_closed Cardinal.IsInaccessible.univ

theorem empty_mem_smallUniverse : (∅ : ZFSet.{u + 1}) ∈ smallUniverse.{u} := by
  rw [smallUniverse, ZFSet.mem_vonNeumann, ZFSet.rank_empty]
  exact Cardinal.ord_pos.mpr Cardinal.IsInaccessible.univ.pos

/-- The least-universe construction already has a concrete argument without
assuming the global relative cardinal condition. -/
noncomputable def leastEmptyUniverse : ZFSet.{u + 1} :=
  hull ∅ smallUniverse.{u}

theorem leastEmptyUniverse_closed : Closed leastEmptyUniverse.{u} :=
  hull_closed smallUniverse_closed

theorem empty_mem_leastEmptyUniverse : (∅ : ZFSet.{u + 1}) ∈ leastEmptyUniverse.{u} :=
  contains_hull empty_mem_smallUniverse

/-- Taking the enclosing universe again must genuinely go outward.
An idempotent "universe of" cannot satisfy the required membership law. -/
theorem univOf_ne_self (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}) :
    univOf h N ≠ N := by
  intro heq
  have hmem := mem_univOf h N
  rw [heq] at hmem
  exact ZFSet.mem_irrefl N hmem

theorem univOf_not_idempotent (h : CofinalInaccessibles.{u}) (N : ZFSet.{u}) :
    univOf h (univOf h N) ≠ univOf h N :=
  univOf_ne_self h (univOf h N)

/-- The small concrete enclosure is not a set containing every set of its
ambient model. In particular it does not contain itself. -/
theorem smallUniverse_not_member_self : smallUniverse.{u} ∉ smallUniverse.{u} :=
  ZFSet.mem_irrefl _

#print axioms inaccessible_closed
#print axioms hull_closed
#print axioms hull_independent
#print axioms mem_univOf
#print axioms univOf_closed
#print axioms univOf_minimal
#print axioms univOf_mono
#print axioms predicateSet_mem_univOf
#print axioms leastEmptyUniverse_closed
#print axioms empty_mem_leastEmptyUniverse
#print axioms univOf_not_idempotent

end Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure
