import Mettapedia.TypeTheory.MaterialSets.DependentSum
import Mettapedia.Logic.HOL.Embedding.ZFSetDependentProducts
import Mettapedia.SetTheory.ZFSet.OrderedPair

/-!
# The `ZFSet` model, where membership is a proposition

Mathlib's `ZFSet` with evidence `x ∈ X : Prop` is a model of the interface.
Membership is propositional by proof irrelevance, and recovery is the identity.

* `Image` is the replacement of the HOL set model,
  `ZFSetHenkinInterpretation.replacement`, applied to the family extended by
  `∅` outside `X`;
* `Union` is `⋃₀`; pairs are Kuratowski pairs with the projections of
  `ZFSetOrderedPair`;
* extensionality is `ZFSet.ext`.

Comparisons with the HOL and contextual set models:

* `repl_eq_replacement`: the restriction `Repl` is the HOL model's replacement;
* `sigmaSet_eq_dependentProducts`: on a family that depends only on the member,
  the set of pairs is `ZFSetDependentProducts.sigmaSet`, the dependent sum of
  the contextual set model.

`ZFSetHenkinInterpretation.replacement` is defined through
`Classical.allZFSetDefinable`, and the extension by `∅` decides membership
classically, so `dependentReplacement` and the results about `Image` here use
`Classical.choice`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Instances.ZFSetModel

open Mettapedia.Logic.HOL.Embedding
open Mettapedia.SetTheory

universe u

/-- Evidence of membership in `ZFSet` is a Lean proof. -/
abbrev Mem (x X : ZFSet.{u}) : Prop := x ∈ X

theorem propositional : PropositionalMembership Mem.{u} := fun _ _ => inferInstance

def recovery : EvidenceRecovery Mem.{u} := ⟨fun h => h.elim id⟩

theorem extensional : Extensional Mem.{u} := fun coext =>
  ZFSet.ext fun z => nonempty_prop.symm.trans ((coext z).trans nonempty_prop)

/-- A family on the members of `X`, extended by `∅` outside `X`. -/
noncomputable def extend {X : ZFSet.{u}} (F : El Mem X → ZFSet.{u}) (x : ZFSet.{u}) :
    ZFSet.{u} := by
  classical
  exact if hx : x ∈ X then F ⟨x, hx⟩ else ∅

theorem extend_el {X : ZFSet.{u}} (F : El Mem X → ZFSet.{u}) (a : El Mem X) :
    extend F a.1 = F a := by
  unfold extend
  rw [dif_pos a.2]

noncomputable def dependentReplacement : DependentReplacement Mem.{u} where
  image X F := ZFSetHenkinInterpretation.replacement X (extend F)
  mem_image F a := ZFSetHenkinInterpretation.mem_replacement.mpr ⟨a.1, a.2, extend_el F a⟩
  exists_of_mem_image := fun {_ F _} m => by
    obtain ⟨x, hx, e⟩ := ZFSetHenkinInterpretation.mem_replacement.mp m
    exact ⟨⟨x, hx⟩, (extend_el F ⟨x, hx⟩).symm.trans e⟩

def union : UnionOperation Mem.{u} where
  union := ZFSet.sUnion
  mem_union hx hW := ZFSet.mem_sUnion_of_mem hx hW
  exists_of_mem_union m := by
    obtain ⟨W, hW, hx⟩ := ZFSet.mem_sUnion.mp m
    exact ⟨W, ⟨hx⟩, ⟨hW⟩⟩

noncomputable def pairing : Pairing ZFSet.{u} where
  pair := ZFSet.pair
  fst := ZFSetOrderedPair.first
  snd := ZFSetOrderedPair.second
  fst_pair := ZFSetOrderedPair.first_pair
  snd_pair := ZFSetOrderedPair.second_pair

/-! ## The interface's consequences in this model -/

/-- The members of `Image X F` are the values of `F` at members of `X`. -/
theorem mem_image_iff {X y : ZFSet.{u}} {F : El Mem X → ZFSet.{u}} :
    y ∈ dependentReplacement.image X F ↔ ∃ x, x ∈ X ∧ ∀ p : x ∈ X, F ⟨x, p⟩ = y := by
  have members := dependentReplacement.image_members propositional (X := X) (y := y) (F := F)
  simpa only [nonempty_prop] using members

/-- The set of pairs and the dependent sum of member types, in the `ZFSet`
model. -/
noncomputable def sigmaSetEquiv (X : ZFSet.{u}) (B : El Mem X → ZFSet.{u}) :
    El Mem (sigmaSet dependentReplacement union pairing X B) ≃ Σ' a : El Mem X, El Mem (B a) :=
  MaterialSets.sigmaSetEquiv dependentReplacement union pairing propositional recovery X B

/-- No member of the empty set, with or without evidence. -/
instance el_empty_isEmpty : IsEmpty (El Mem (∅ : ZFSet.{u})) :=
  ⟨fun a => ZFSet.notMem_empty a.1 a.2⟩

/-! ## Comparison with the existing set model -/

/-- The restriction of `Image` to `set → set` is the HOL model's replacement. -/
theorem repl_eq_replacement (X : ZFSet.{u}) (f : ZFSet.{u} → ZFSet.{u}) :
    dependentReplacement.repl X f = ZFSetHenkinInterpretation.replacement X f := by
  ext y
  change y ∈ ZFSetHenkinInterpretation.replacement X (extend fun a : El Mem X => f a.1) ↔ _
  rw [ZFSetHenkinInterpretation.mem_replacement, ZFSetHenkinInterpretation.mem_replacement]
  constructor
  · rintro ⟨x, hx, e⟩
    exact ⟨x, hx, (extend_el (fun a : El Mem X => f a.1) ⟨x, hx⟩).symm.trans e⟩
  · rintro ⟨x, hx, e⟩
    exact ⟨x, hx, (extend_el (fun a : El Mem X => f a.1) ⟨x, hx⟩).trans e⟩

/-- On a family that depends only on the member, the set of pairs is the
dependent sum of the contextual set model. -/
theorem sigmaSet_eq_dependentProducts (X : ZFSet.{u}) (b : ZFSet.{u} → ZFSet.{u}) :
    sigmaSet dependentReplacement union pairing X (fun a => b a.1) =
      ZFSetDependentProducts.sigmaSet X b := by
  ext z
  rw [ZFSetDependentProducts.mem_sigmaSet]
  constructor
  · intro m
    obtain ⟨a, c, rfl⟩ := exists_of_mem_sigmaSet dependentReplacement union pairing m
    exact ⟨a.1, a.2, c.1, c.2, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact (pairMember dependentReplacement union pairing (B := fun a => b a.1)
      ⟨⟨x, hx⟩, ⟨y, hy⟩⟩).2

end Mettapedia.TypeTheory.MaterialSets.Instances.ZFSetModel
