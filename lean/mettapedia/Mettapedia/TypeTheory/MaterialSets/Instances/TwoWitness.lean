import Mettapedia.TypeTheory.MaterialSets.Instances.ZFSet
import Mathlib.Data.Fintype.Prod

/-!
# Two witnesses for every membership

The interface over Mathlib's `ZFSet`, with evidence `{_t : Bool // x ∈ X}`: every
membership has exactly two witnesses. Dependent replacement, union, pairing,
extensionality and evidence recovery hold as in the `ZFSet` model. Only
`PropositionalMembership` fails, and each of its consequences fails with it,
over `one = {∅}`:

* `tagFamily`, which reads the tag, factors through no function of the members
  (`tagFamily_not_factors`), and its image is the replacement of no function on
  sets (`image_ne_repl`);
* the value of the image at one witness is not the value at the other
  (`image_members_fails`);
* transport along equality of sets is not reindexing (`transport_ne_reindex`) and
  does not determine a family by its members (`transportFamily_fails`), and
  reindexing along evidence maps between coextensional sets changes an image
  (`image_reindex_fails`);
* the set of pairs forgets which witness was paired (`pairMember_not_faithful`).
  Over the constant fibre `{∅}` its members number two and the dependent sum
  has four elements, so the two are not equivalent (`no_sigmaSetEquiv`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Instances.TwoWitness

open Mettapedia.Logic.HOL.Embedding

universe u

/-- Evidence of membership: a Boolean tag together with the membership. -/
abbrev Mem (x X : ZFSet.{u}) : Type := {_t : Bool // x ∈ X}

theorem nonempty_mem_iff {x X : ZFSet.{u}} : Nonempty (Mem x X) ↔ x ∈ X :=
  ⟨fun ⟨p⟩ => p.2, fun h => ⟨⟨true, h⟩⟩⟩

def recovery : EvidenceRecovery Mem.{u} := ⟨fun h => ⟨true, h.elim fun p => p.2⟩⟩

theorem extensional : Extensional Mem.{u} := fun coext =>
  ZFSet.ext fun z => nonempty_mem_iff.symm.trans ((coext z).trans nonempty_mem_iff)

/-- The index of an image: a member of `X` with a tag. -/
def toEl {X : ZFSet.{u}} (i : X × Bool) : El Mem X := ⟨i.1.1, ⟨i.2, i.1.2⟩⟩

noncomputable def dependentReplacement : DependentReplacement Mem.{u} where
  image X F := ZFSet.range fun i : X × Bool => F (toEl i)
  mem_image F a := ⟨true, ZFSet.mem_range.mpr ⟨(⟨a.1, a.2.2⟩, a.2.1), rfl⟩⟩
  exists_of_mem_image m := by
    obtain ⟨i, e⟩ := ZFSet.mem_range.mp m.2
    exact ⟨toEl i, e⟩

def union : UnionOperation Mem.{u} where
  union := ZFSet.sUnion
  mem_union hx hW := ⟨true, ZFSet.mem_sUnion_of_mem hx.2 hW.2⟩
  exists_of_mem_union m := by
    obtain ⟨W, hW, hx⟩ := ZFSet.mem_sUnion.mp m.2
    exact ⟨W, ⟨⟨true, hx⟩⟩, ⟨⟨true, hW⟩⟩⟩

/-! ## Two witnesses -/

theorem witnesses_distinct {x X : ZFSet.{u}} (h : x ∈ X) :
    (⟨true, h⟩ : Mem x X) ≠ ⟨false, h⟩ :=
  fun e => by
    have tags : true = false := congrArg Subtype.val e
    exact absurd tags (by decide)

/-- `one = {∅}`. -/
abbrev one : ZFSet.{u} := {∅}

theorem empty_mem_one : (∅ : ZFSet.{u}) ∈ one := ZFSet.mem_singleton.mpr rfl

theorem eq_empty_of_mem_one {x : ZFSet.{u}} (h : x ∈ one) : x = ∅ := ZFSet.mem_singleton.mp h

theorem not_propositional : ¬ PropositionalMembership Mem.{u} :=
  not_propositional_of_witnesses (witnesses_distinct empty_mem_one)

/-! ## Descent and `Image` fail -/

/-- The family that reads the tag: `{∅}` at `true`, `∅` at `false`. -/
def tagFamily {X : ZFSet.{u}} (a : El Mem X) : ZFSet.{u} := bif a.2.1 then {∅} else ∅

theorem tagFamily_distinguishes :
    tagFamily (X := one.{u}) ⟨∅, ⟨true, empty_mem_one⟩⟩ ≠ tagFamily ⟨∅, ⟨false, empty_mem_one⟩⟩ :=
  ZFSetHenkinInterpretation.empty_ne_singleton.symm

theorem tagFamily_not_factors :
    ¬ ∃ f : Members Mem one.{u} → ZFSet.{u}, ∀ a, f (forget a) = tagFamily a :=
  not_factors_of_distinguishes tagFamily tagFamily_distinguishes

/-- The image of `tagFamily` is the replacement of no function on sets. -/
theorem image_ne_repl (f : ZFSet.{u} → ZFSet.{u}) :
    dependentReplacement.image one tagFamily ≠ dependentReplacement.repl one f := by
  intro same
  have hTrue : ({∅} : ZFSet.{u}) ∈ dependentReplacement.image one tagFamily :=
    (dependentReplacement.mem_image tagFamily ⟨∅, ⟨true, empty_mem_one⟩⟩).2
  have hFalse : (∅ : ZFSet.{u}) ∈ dependentReplacement.image one tagFamily :=
    (dependentReplacement.mem_image tagFamily ⟨∅, ⟨false, empty_mem_one⟩⟩).2
  rw [same] at hTrue hFalse
  obtain ⟨a, ea⟩ := dependentReplacement.exists_of_mem_image
    (F := fun a : El Mem one => f a.1) (⟨true, hTrue⟩ : Mem _ _)
  obtain ⟨b, eb⟩ := dependentReplacement.exists_of_mem_image
    (F := fun a : El Mem one => f a.1) (⟨true, hFalse⟩ : Mem _ _)
  apply ZFSetHenkinInterpretation.empty_ne_singleton
  calc (∅ : ZFSet.{u}) = f b.1 := eb.symm
    _ = f a.1 := by rw [eq_empty_of_mem_one a.2.2, eq_empty_of_mem_one b.2.2]
    _ = {∅} := ea

/-- A value of the image at one witness need not be the value at the other:
`image_members` fails. -/
theorem image_members_fails :
    ({∅} : ZFSet.{u}) ∈ dependentReplacement.image one tagFamily ∧
      ¬ ∀ p : Mem ∅ one, tagFamily ⟨∅, p⟩ = ({∅} : ZFSet.{u}) :=
  ⟨(dependentReplacement.mem_image tagFamily ⟨∅, ⟨true, empty_mem_one⟩⟩).2,
    fun all => ZFSetHenkinInterpretation.empty_ne_singleton (all ⟨false, empty_mem_one⟩)⟩

/-! ## Transport and reindexing disagree -/

/-- Swap the tag of each witness. -/
def swap (z X : ZFSet.{u}) (p : Mem z X) : Mem z X := ⟨!p.1, p.2⟩

theorem transport_ne_reindex :
    transport (rfl : one.{u} = one) (⟨∅, ⟨true, empty_mem_one⟩⟩ : El Mem one) ≠
      reindex (fun z => swap z one) ⟨∅, ⟨true, empty_mem_one⟩⟩ := by
  intro same
  have tags : true = false := congrArg (fun a : El Mem one => a.2.1) same
  exact absurd tags (by decide)

/-- Transport of a family along equality of sets is not determined by the
member: `transportFamily_eq_of_fst_eq` fails. -/
theorem transportFamily_fails :
    DependentReplacement.transportFamily (rfl : one.{u} = one) tagFamily
        ⟨∅, ⟨true, empty_mem_one⟩⟩ ≠ tagFamily ⟨∅, ⟨false, empty_mem_one⟩⟩ :=
  tagFamily_distinguishes

/-- Retag each witness `true`. -/
def retag (z X : ZFSet.{u}) (p : Mem z X) : Mem z X := ⟨true, p.2⟩

/-- Reindexing along the evidence maps `retag` between `one` and itself changes
the image of `tagFamily`. -/
theorem image_reindex_fails :
    dependentReplacement.image one (fun a => tagFamily (reindex (fun z => retag z one) a)) ≠
      dependentReplacement.image one.{u} tagFamily := by
  intro same
  have hFalse : (∅ : ZFSet.{u}) ∈ dependentReplacement.image one tagFamily :=
    (dependentReplacement.mem_image tagFamily ⟨∅, ⟨false, empty_mem_one⟩⟩).2
  rw [← same] at hFalse
  obtain ⟨a, ea⟩ := dependentReplacement.exists_of_mem_image
    (F := fun a : El Mem one => tagFamily (reindex (fun z => retag z one) a))
    (⟨true, hFalse⟩ : Mem _ _)
  exact ZFSetHenkinInterpretation.empty_ne_singleton ea.symm

/-! ## The set of pairs is not the dependent sum -/

/-- The constant fibre `{∅}`. -/
def constFibre (_ : El Mem one.{u}) : ZFSet.{u} := one

/-- The set of pairs over `one` with constant fibre `one`. -/
noncomputable abbrev pairs : ZFSet.{u} :=
  sigmaSet dependentReplacement union ZFSetModel.pairing one constFibre

theorem eq_of_mem_pairs {z : ZFSet.{u}} (m : Mem z pairs) : z = ZFSet.pair ∅ ∅ := by
  obtain ⟨a, b, rfl⟩ := exists_of_mem_sigmaSet dependentReplacement union ZFSetModel.pairing m
  exact congrArg₂ ZFSet.pair (eq_empty_of_mem_one a.2.2) (eq_empty_of_mem_one b.2.2)

/-- The set of pairs forgets which witness was paired. -/
theorem pairMember_not_faithful :
    ¬ Function.Injective (fun ab : Σ' a : El Mem one.{u}, El Mem (constFibre a) =>
      (pairMember dependentReplacement union ZFSetModel.pairing ab).1) :=
  pairMember_fst_not_injective dependentReplacement union ZFSetModel.pairing
    (witnesses_distinct empty_mem_one) ⟨∅, ⟨true, empty_mem_one⟩⟩ ⟨∅, ⟨true, empty_mem_one⟩⟩ rfl

/-- The one pair of `pairs`, with its two witnesses. -/
noncomputable def pairsEquivBool : El Mem (pairs.{u}) ≃ Bool where
  toFun c := c.2.1
  invFun t := ⟨ZFSet.pair ∅ ∅, ⟨t, (pairMember dependentReplacement union ZFSetModel.pairing
    (B := constFibre) ⟨⟨∅, ⟨true, empty_mem_one⟩⟩, ⟨∅, ⟨true, empty_mem_one⟩⟩⟩).2.2⟩⟩
  left_inv c := by
    obtain ⟨z, t, h⟩ := c
    obtain rfl := eq_of_mem_pairs ⟨t, h⟩
    rfl
  right_inv _ := rfl

/-- The dependent sum: a tag for the member of `one` and a tag for its fibre member. -/
def sumEquivBoolBool : (Σ' a : El Mem one.{u}, El Mem (constFibre a)) ≃ Bool × Bool where
  toFun ab := (ab.1.2.1, ab.2.2.1)
  invFun t := ⟨⟨∅, ⟨t.1, empty_mem_one⟩⟩, ⟨∅, ⟨t.2, empty_mem_one⟩⟩⟩
  left_inv ab := by
    obtain ⟨⟨x, t, hx⟩, ⟨y, t', hy⟩⟩ := ab
    obtain rfl := eq_empty_of_mem_one hx
    obtain rfl := eq_empty_of_mem_one hy
    rfl
  right_inv _ := rfl

/-- With two-witness membership, the members of the set of pairs are not
equivalent to the dependent sum of member types. -/
theorem no_sigmaSetEquiv :
    IsEmpty (El Mem (pairs.{u}) ≃ Σ' a : El Mem one.{u}, El Mem (constFibre a)) :=
  ⟨fun e => by
    have cards := Fintype.card_congr ((pairsEquivBool.symm.trans e).trans sumEquivBoolBool)
    rw [Fintype.card_prod, Fintype.card_bool] at cards
    exact absurd cards (by decide)⟩

end Mettapedia.TypeTheory.MaterialSets.Instances.TwoWitness
