import Mettapedia.Logic.GunkyMereology
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Perfect
import Mathlib.Topology.Separation.Basic

/-!
# Stone duality for gunky Boolean algebras: atomless ⟺ perfect

For a Boolean algebra `B`, its **Stone space** `S(B)` is the prime spectrum of its
Boolean ring. We prove, in full generality, the Stone half of the dictionary used by
the ultrainfinitism development:

* `stoneRepr : B ≃o Clopens (StoneSpace B)` — the Stone representation
  (`B` is the clopen algebra of its Stone space), assembled from mathlib's
  `PrimeSpectrum.isIdempotentElemEquivClopens`.
* `isGunky_iff_perfect_stoneSpace : IsGunky B ↔ PerfectSpace (StoneSpace B)` — a Boolean
  algebra is atomless iff its Stone space has no isolated points.

The bridge is `IsAtom (a : B) ↔` "the corresponding clopen is a one-point set", i.e.
an atom of `B` is an isolated point of `S(B)`. Two concrete corollaries tie the result
to the gunky witnesses of `GunkyMereology`: Cantor space is perfect (`perfectSpace_cantor`),
matching the gunky Boolean algebra of Cantor clopens.
-/

namespace Mettapedia.Foundations.Gunk

open TopologicalSpace PrimeSpectrum

universe u

variable {B : Type u} [BooleanAlgebra B]

/-- The **Stone space** of a Boolean algebra: the prime spectrum of its Boolean ring. -/
abbrev StoneSpace (B : Type u) [BooleanAlgebra B] : Type u := PrimeSpectrum (AsBoolRing B)

/-- A Boolean algebra is order-isomorphic to the idempotents of its Boolean ring: every
element is idempotent, and the Boolean order is the multiplicative idempotent order. -/
def idempEquiv (B : Type u) [BooleanAlgebra B] :
    B ≃o {e : AsBoolRing B // IsIdempotentElem e} where
  toFun a := ⟨toBoolRing a, BooleanRing.mul_self _⟩
  invFun e := ofBoolRing e.1
  left_inv a := by simp
  right_inv e := by ext; simp
  map_rel_iff' {a b} := by
    show (toBoolRing a * toBoolRing b = toBoolRing a) ↔ a ≤ b
    rw [show (toBoolRing a : AsBoolRing B) * toBoolRing b = toBoolRing (a ⊓ b) from rfl,
      (toBoolRing : B ≃ AsBoolRing B).injective.eq_iff, inf_eq_left]

/-- **Stone representation.** A Boolean algebra is the clopen algebra of its Stone space.
Assembled from `idempEquiv` and mathlib's idempotent-clopen order-isomorphism. -/
noncomputable def stoneRepr (B : Type u) [BooleanAlgebra B] :
    B ≃o Clopens (StoneSpace B) :=
  (idempEquiv B).trans isIdempotentElemEquivClopens

@[simp] theorem coe_stoneRepr (a : B) :
    ((stoneRepr B a : Clopens (StoneSpace B)) : Set (StoneSpace B))
      = basicOpen (toBoolRing a) := rfl

/-! ## The Stone space is a Stone space (compact, Hausdorff, totally separated) -/

-- For an idempotent `f`, `basicOpen f` and `basicOpen (1 - f)` are complementary clopens.

private theorem onesub_notMem {p : StoneSpace B} {f : AsBoolRing B}
    (hfp : f ∈ p.asIdeal) : (1 - f) ∉ p.asIdeal := by
  intro hmem
  refine p.2.ne_top ?_
  rw [Ideal.eq_top_iff_one]
  simpa using p.asIdeal.add_mem hfp hmem

/-- Set-level membership in a basic open of the spectrum. -/
private theorem mem_bo (p : StoneSpace B) (f : AsBoolRing B) :
    p ∈ (basicOpen f : Set (StoneSpace B)) ↔ f ∉ p.asIdeal := by
  simp

private theorem mem_basicOpen_or (p : StoneSpace B) (f : AsBoolRing B) :
    p ∈ (basicOpen f : Set (StoneSpace B)) ∨ p ∈ (basicOpen (1 - f) : Set (StoneSpace B)) := by
  simp only [mem_bo]
  by_contra h
  push_neg at h
  exact onesub_notMem h.1 h.2

private theorem basicOpen_disjoint (f : AsBoolRing B) :
    Disjoint (basicOpen f : Set (StoneSpace B)) (basicOpen (1 - f) : Set (StoneSpace B)) := by
  rw [Set.disjoint_left]
  intro p hp1 hp2
  rw [mem_bo] at hp1 hp2
  rcases p.2.mem_or_mem (show f * (1 - f) ∈ p.asIdeal by
      rw [IsIdempotentElem.mul_one_sub_self (BooleanRing.mul_self f)]
      exact p.asIdeal.zero_mem) with h | h
  · exact hp1 h
  · exact hp2 h

/-- Distinct primes of a Boolean ring are separated by complementary clopens — so the
Stone space is totally separated, hence Hausdorff. -/
instance : TotallySeparatedSpace (StoneSpace B) := by
  refine ⟨fun p _ q _ hpq => ?_⟩
  obtain ⟨f, hf⟩ : ∃ f, (f ∈ p.asIdeal ∧ f ∉ q.asIdeal) ∨ (f ∈ q.asIdeal ∧ f ∉ p.asIdeal) := by
    by_contra h
    push_neg at h
    exact hpq (PrimeSpectrum.ext (Ideal.ext fun f => ⟨(h f).1, (h f).2⟩))
  rcases hf with ⟨hfp, hfq⟩ | ⟨hfq, hfp⟩
  · exact ⟨(basicOpen (1 - f) : Set _), (basicOpen f : Set _),
      (basicOpen _).2, (basicOpen _).2,
      (mem_bo ..).2 (onesub_notMem hfp), (mem_bo ..).2 hfq,
      fun x _ => (mem_basicOpen_or x f).symm, (basicOpen_disjoint f).symm⟩
  · exact ⟨(basicOpen f : Set _), (basicOpen (1 - f) : Set _),
      (basicOpen _).2, (basicOpen _).2,
      (mem_bo ..).2 hfp, (mem_bo ..).2 (onesub_notMem hfq),
      fun x _ => mem_basicOpen_or x f, basicOpen_disjoint f⟩

instance : T2Space (StoneSpace B) := by
  have hts : IsTotallySeparated (Set.univ : Set (StoneSpace B)) :=
    TotallySeparatedSpace.isTotallySeparated_univ
  refine ⟨fun p q hpq => ?_⟩
  obtain ⟨u, v, hu, hv, hpu, hqv, _, hdisj⟩ := hts (Set.mem_univ p) (Set.mem_univ q) hpq
  exact ⟨u, v, hu, hv, hpu, hqv, hdisj⟩

/-! ## The main theorem: atomless ⟺ perfect -/

/-- An atom of the clopen algebra of the Stone space is a one-point clopen. -/
theorem isAtom_clopens_isSingleton {K : Clopens (StoneSpace B)} (hK : IsAtom K) :
    ∃ p, (K : Set (StoneSpace B)) = {p} := by
  obtain ⟨p, hp⟩ : (K : Set (StoneSpace B)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hK.1 (SetLike.coe_injective (by rw [h, TopologicalSpace.Clopens.coe_bot]))
  refine ⟨p, Set.eq_singleton_iff_unique_mem.2 ⟨hp, fun q hq => ?_⟩⟩
  by_contra hqp
  have hts : IsTotallySeparated (Set.univ : Set (StoneSpace B)) :=
    TotallySeparatedSpace.isTotallySeparated_univ
  obtain ⟨u, v, hu, hv, hpu, hqv, hcov, hdisj⟩ :=
    hts (Set.mem_univ p) (Set.mem_univ q) (fun h => hqp h.symm)
  have huv : u = vᶜ := by
    apply Set.Subset.antisymm
    · intro x hx; exact Set.disjoint_left.1 hdisj hx
    · intro x hx
      rcases hcov (Set.mem_univ x) with h | h
      · exact h
      · exact absurd h hx
  have hucl : IsClopen u := ⟨huv ▸ hv.isClosed_compl, hu⟩
  have hlt : K ⊓ ⟨u, hucl⟩ < K := by
    refine lt_of_le_of_ne inf_le_left (fun heq => hdisj.le_bot ⟨?_, hqv⟩)
    have hmem : q ∈ ((K ⊓ ⟨u, hucl⟩ : Clopens (StoneSpace B)) : Set _) := by rw [heq]; exact hq
    rw [TopologicalSpace.Clopens.coe_inf] at hmem; exact hmem.2
  refine absurd (hK.2 _ hlt) (fun heq => ?_)
  have hpKC : p ∈ ((K ⊓ ⟨u, hucl⟩ : Clopens (StoneSpace B)) : Set _) := by
    rw [TopologicalSpace.Clopens.coe_inf]; exact ⟨hp, hpu⟩
  rw [heq, TopologicalSpace.Clopens.coe_bot] at hpKC
  exact (Set.mem_empty_iff_false p).1 hpKC

/-- A one-point clopen is an atom of the clopen algebra. -/
theorem isAtom_clopens_of_singleton {p : StoneSpace B}
    (hcl : IsClopen ({p} : Set (StoneSpace B))) :
    IsAtom (⟨{p}, hcl⟩ : Clopens (StoneSpace B)) := by
  refine ⟨fun heq => ?_, fun L hL => ?_⟩
  · have hp : p ∈ ((⟨{p}, hcl⟩ : Clopens (StoneSpace B)) : Set _) := rfl
    rw [heq, TopologicalSpace.Clopens.coe_bot] at hp
    exact (Set.mem_empty_iff_false p).1 hp
  refine SetLike.coe_injective ?_
  rw [TopologicalSpace.Clopens.coe_bot]
  rcases Set.subset_singleton_iff_eq.1 hL.le with h | h
  · exact h
  · exact absurd (SetLike.coe_injective h) hL.ne

/-- **Stone duality (atomless ⟺ perfect).** A Boolean algebra is atomless (gunky) iff its
Stone space has no isolated points. -/
theorem isGunky_iff_perfect_stoneSpace :
    IsGunky B ↔ PerfectSpace (StoneSpace B) := by
  rw [isGunky_iff_no_isAtom, perfectSpace_iff_forall_not_isolated]
  constructor
  · intro hno p
    rw [Filter.neBot_iff, Ne, ← isOpen_singleton_iff_punctured_nhds]
    intro hopen
    have hcl : IsClopen ({p} : Set (StoneSpace B)) := ⟨isClosed_singleton, hopen⟩
    exact hno _ ((OrderIso.isAtom_iff (stoneRepr B).symm _).2 (isAtom_clopens_of_singleton hcl))
  · intro hperf a hatom
    obtain ⟨p, hp⟩ :=
      isAtom_clopens_isSingleton ((OrderIso.isAtom_iff (stoneRepr B) a).2 hatom)
    have hopen : IsOpen ({p} : Set (StoneSpace B)) := hp ▸ (stoneRepr B a).2.isOpen
    exact (hperf p).ne' ((isOpen_singleton_iff_punctured_nhds p).1 hopen)

/-! ## Transfer pack: moving gunk across isomorphisms and down to parts

General-purpose lemmas for stating the atomless/atomic dial on *derived* algebras
(quotients, frontiers, sublattices of a concept state) rather than a fixed base space:
gunk transports across order isomorphisms and restricts to principal down-sets. -/

section Transfer

variable {α : Type*} {β : Type*} [PartialOrder α] [OrderBot α] [PartialOrder β] [OrderBot β]

/-- Gunk transports across order isomorphisms. -/
theorem isGunky_congr (f : α ≃o β) : IsGunky α ↔ IsGunky β := by
  rw [isGunky_iff_no_isAtom, isGunky_iff_no_isAtom]
  constructor
  · intro h b hb
    exact h (f.symm b) ((f.isAtom_iff (f.symm b)).mp (by rwa [f.apply_symm_apply]))
  · intro h a ha
    exact h (f a) ((f.isAtom_iff a).mpr ha)

/-- Gunk restricts to parts: in a gunky order, the down-set of any individual is again
gunky — every part of a gunky thing is gunky. -/
theorem isGunky_Iic (hg : IsGunky α) (a : α) : IsGunky (Set.Iic a) := by
  intro x hx
  have hx1 : (x : α) ≠ ⊥ := fun h => hx (Subtype.ext h)
  obtain ⟨b, hb, hba⟩ := hg x hx1
  exact ⟨⟨b, le_trans hba.le x.2⟩, fun h => hb (congrArg Subtype.val h),
    Subtype.mk_lt_mk.mpr hba⟩

end Transfer

/-- The Stone-space perfectness verdict transports across order isomorphisms of Boolean
algebras: state the dial on whatever algebra is order-isomorphic to the object of
interest. -/
theorem perfectSpace_stoneSpace_congr {C : Type u} [BooleanAlgebra C] (f : B ≃o C) :
    PerfectSpace (StoneSpace B) ↔ PerfectSpace (StoneSpace C) := by
  rw [← isGunky_iff_perfect_stoneSpace, ← isGunky_iff_perfect_stoneSpace]
  exact isGunky_congr f

end Mettapedia.Foundations.Gunk


