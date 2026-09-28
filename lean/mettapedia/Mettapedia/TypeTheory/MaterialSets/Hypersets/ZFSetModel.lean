import Mettapedia.TypeTheory.MaterialSets.Hypersets.MembershipEvidence
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ZFSet
import Mettapedia.TypeTheory.MaterialSets.Instances.ZFSet

/-!
# The well-founded part and the `ZFSet` model of the membership interface

`HSet.wellFoundedPartEquivZFSet` is an isomorphism between two models of the membership
interface, the well-founded hypersets and `Instances.ZFSetModel`:

* it preserves membership (`mem_iff_zfSetModel`);
* it carries union to union (`equiv_union`) and Kuratowski pairs to pairs (`equiv_pair`), and
  on pairs the derived projections to those of the `ZFSet` model (`equiv_fst_of_pair`,
  `equiv_snd_of_pair`);
* it carries dependent replacement to dependent replacement, for every presentation
  (`equiv_image`).

Dependent replacement in the `ZFSet` model is defined through `Classical.allZFSetDefinable`, so
`equiv_image` depends on `Classical.choice`. The other statements do not.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

open Instances HSet

universe u

namespace WellFoundedPart

theorem ofZFSet_equiv (x : WellFoundedPart.{u}) : ofZFSet (wellFoundedPartEquivZFSet x) = x.1 :=
  ofZFSet_toZFSet_of_wf x.2

/-- The equivalence preserves membership. -/
theorem mem_iff_zfSetModel {x X : WellFoundedPart.{u}} :
    Mem x X ↔ ZFSetModel.Mem (wellFoundedPartEquivZFSet x) (wellFoundedPartEquivZFSet X) :=
  wellFoundedPartEquivZFSet_mem_iff.symm

theorem mem_symm_of_mem {X : WellFoundedPart.{u}} {z : ZFSet.{u}}
    (h : ZFSetModel.Mem z (wellFoundedPartEquivZFSet X)) :
    Mem (wellFoundedPartEquivZFSet.symm z) X :=
  wellFoundedPartEquivZFSet_mem_iff.mp (by rwa [Equiv.apply_symm_apply])

/-- Union is carried to union. -/
theorem equiv_union (X : WellFoundedPart.{u}) :
    wellFoundedPartEquivZFSet (union.union X) =
      ZFSetModel.union.union (wellFoundedPartEquivZFSet X) := by
  apply ofZFSet_injective
  rw [ofZFSet_equiv]
  change sUnion X.1 = ofZFSet (ZFSet.sUnion (wellFoundedPartEquivZFSet X))
  rw [ofZFSet_sUnion, ofZFSet_equiv]

/-- Kuratowski pairs are carried to Kuratowski pairs. -/
theorem equiv_pair (x y : WellFoundedPart.{u}) :
    wellFoundedPartEquivZFSet (pairing.pair x y) =
      ZFSetModel.pairing.pair (wellFoundedPartEquivZFSet x) (wellFoundedPartEquivZFSet y) := by
  apply ofZFSet_injective
  rw [ofZFSet_equiv]
  change kpair x.1 y.1 =
    ofZFSet (ZFSet.pair (wellFoundedPartEquivZFSet x) (wellFoundedPartEquivZFSet y))
  rw [ofZFSet_kpair, ofZFSet_equiv, ofZFSet_equiv]

theorem equiv_fst_of_pair {z : WellFoundedPart.{u}} (hz : ∃ x y, pairing.pair x y = z) :
    wellFoundedPartEquivZFSet (pairing.fst z) =
      ZFSetModel.pairing.fst (wellFoundedPartEquivZFSet z) := by
  obtain ⟨x, y, rfl⟩ := hz
  rw [pairing.fst_pair, equiv_pair, ZFSetModel.pairing.fst_pair]

theorem equiv_snd_of_pair {z : WellFoundedPart.{u}} (hz : ∃ x y, pairing.pair x y = z) :
    wellFoundedPartEquivZFSet (pairing.snd z) =
      ZFSetModel.pairing.snd (wellFoundedPartEquivZFSet z) := by
  obtain ⟨x, y, rfl⟩ := hz
  rw [pairing.snd_pair, equiv_pair, ZFSetModel.pairing.snd_pair]

/-- Dependent replacement is carried to the dependent replacement of the `ZFSet` model, for
every presentation. -/
theorem equiv_image (p : Presentation.{u}) (X : WellFoundedPart.{u})
    (F : El Mem X → WellFoundedPart.{u}) :
    wellFoundedPartEquivZFSet ((dependentReplacement p).image X F) =
      ZFSetModel.dependentReplacement.image (wellFoundedPartEquivZFSet X)
        fun b => wellFoundedPartEquivZFSet (F ⟨wellFoundedPartEquivZFSet.symm b.1,
          mem_symm_of_mem b.2⟩) := by
  have target : ∀ {Y : ZFSet.{u}} {G : El ZFSetModel.Mem Y → ZFSet.{u}} {z : ZFSet.{u}},
      z ∈ ZFSetModel.dependentReplacement.image Y G ↔ ∃ b, G b = z := fun {_ _ _} =>
    nonempty_iff_of_prop.symm.trans ZFSetModel.dependentReplacement.nonempty_mem_image_iff
  have source : ∀ {Y : WellFoundedPart.{u}} {G : El Mem Y → WellFoundedPart.{u}}
      {z : WellFoundedPart.{u}}, Mem z ((dependentReplacement p).image Y G) ↔ ∃ a, G a = z :=
    fun {_ _ _} =>
      nonempty_iff_of_prop.symm.trans (dependentReplacement p).nonempty_mem_image_iff
  ext z
  rw [target, ← Equiv.apply_symm_apply wellFoundedPartEquivZFSet z,
    wellFoundedPartEquivZFSet_mem_iff, Equiv.apply_symm_apply]
  refine (source (z := wellFoundedPartEquivZFSet.symm z)).trans ⟨?_, ?_⟩
  · rintro ⟨a, ha⟩
    refine ⟨⟨wellFoundedPartEquivZFSet a.1, wellFoundedPartEquivZFSet_mem_iff.mpr a.2⟩, ?_⟩
    calc wellFoundedPartEquivZFSet (F ⟨wellFoundedPartEquivZFSet.symm
            (wellFoundedPartEquivZFSet a.1), _⟩)
        = wellFoundedPartEquivZFSet (F a) :=
          congrArg (fun c => wellFoundedPartEquivZFSet (F c))
            (El.ext propositional (Equiv.symm_apply_apply _ _))
      _ = z := by rw [ha, Equiv.apply_symm_apply]
  · rintro ⟨b, hb⟩
    exact ⟨_, by rw [← hb, Equiv.symm_apply_apply]⟩

end WellFoundedPart

end Mettapedia.TypeTheory.MaterialSets.Hypersets
