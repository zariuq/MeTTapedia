import Mettapedia.TypeTheory.MaterialSets.Hypersets.KuratowskiPair
import Mathlib.SetTheory.ZFC.Basic

/-!
# The well-founded hypersets are Mathlib's `ZFSet`

A pre-set is a well-founded tree, so it pictures a hyperset: `graphOfPSet p` is a new point
over the graphs of its members. Equivalent pre-sets picture the same hyperset, and
conversely (`ofPSet_eq_ofPSet_iff`), so `ofZFSet : ZFSet → HSet` is injective, preserves and
reflects membership (`ofZFSet_mem_ofZFSet_iff`), and takes well-founded values (`wf_ofZFSet`).

In the other direction, `unfold` unwinds a graph below an accessible node into a pre-set, and
`toZFSet x` unwinds the well-founded members of `x`. Its composite with `ofZFSet` keeps the
well-founded members (`ofZFSet_toZFSet`); on the well-founded part it is the identity.
Hence the well-founded part is `ZFSet`, with membership preserved in both directions
(`wellFoundedPartEquivZFSet`, `wellFoundedPartEquivZFSet_mem_iff`,
`mem_wellFoundedPartEquivZFSet_symm_iff`).

`ofZFSet` carries Mathlib's set operations to those of hypersets: the empty set, `insert`,
pairs, Kuratowski pairs, separation, union and power set (`ofZFSet_insert`, `ofZFSet_kpair`,
`ofZFSet_sep`, `ofZFSet_sUnion`, `ofZFSet_powerset`).

The comparison uses Mathlib's pre-sets and the quotient `ZFSet`, not its choice-based
operations, and depends on no axiom beyond `propext` and `Quot.sound`.

**Controls.** `ofZFSet ∅ = ∅` (`ofZFSet_empty`); `Ω` is not in the range of `ofZFSet`
(`ofZFSet_ne_quineAtom`), and `toZFSet Ω = ∅` (`toZFSet_quineAtom`), so `toZFSet` is not
injective outside the well-founded part.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

open AccessiblePointedGraph

universe u

namespace HSet

/-! ## From pre-sets to hypersets -/

/-- The graph of a pre-set: a new point over the graphs of its members. -/
def graphOfPSet : PSet.{u} → AccessiblePointedGraph.{u}
  | ⟨_, A⟩ => sup fun a => graphOfPSet (A a)

/-- The hyperset pictured by a pre-set. -/
def ofPSet (p : PSet.{u}) : HSet.{u} :=
  mk (graphOfPSet p)

theorem mem_ofPSet_mk {α : Type u} {A : α → PSet.{u}} {y : HSet.{u}} :
    y ∈ ofPSet ⟨α, A⟩ ↔ ∃ a, ofPSet (A a) = y :=
  mem_range

theorem ofPSet_eq_ofPSet_iff {p q : PSet.{u}} : ofPSet p = ofPSet q ↔ PSet.Equiv p q := by
  induction p generalizing q with
  | mk α A ih =>
    obtain ⟨β, B⟩ := q
    rw [PSet.equiv_iff]
    constructor
    · intro h
      refine ⟨fun a => ?_, fun b => ?_⟩
      · have ha : ofPSet (A a) ∈ ofPSet ⟨β, B⟩ := h ▸ mem_ofPSet_mk.mpr ⟨a, rfl⟩
        obtain ⟨b, hb⟩ := mem_ofPSet_mk.mp ha
        exact ⟨b, (ih a).mp hb.symm⟩
      · have hb : ofPSet (B b) ∈ ofPSet ⟨α, A⟩ := h.symm ▸ mem_ofPSet_mk.mpr ⟨b, rfl⟩
        obtain ⟨a, ha⟩ := mem_ofPSet_mk.mp hb
        exact ⟨a, (ih a).mp ha⟩
    · rintro ⟨forth, back⟩
      ext y
      rw [mem_ofPSet_mk, mem_ofPSet_mk]
      constructor
      · rintro ⟨a, rfl⟩
        obtain ⟨b, hb⟩ := forth a
        exact ⟨b, ((ih a).mpr hb).symm⟩
      · rintro ⟨b, rfl⟩
        obtain ⟨a, ha⟩ := back b
        exact ⟨a, (ih a).mpr ha⟩

theorem wf_ofPSet (p : PSet.{u}) : (ofPSet p).WF := by
  induction p with
  | mk α A ih =>
    exact wf_of_forall_mem fun y hy => by
      obtain ⟨a, rfl⟩ := mem_ofPSet_mk.mp hy
      exact ih a

/-- The hyperset of a `ZFSet`. -/
def ofZFSet : ZFSet.{u} → HSet.{u} :=
  Quotient.lift ofPSet fun _ _ h => ofPSet_eq_ofPSet_iff.mpr h

theorem ofZFSet_mk (p : PSet.{u}) : ofZFSet (ZFSet.mk p) = ofPSet p :=
  rfl

theorem ofZFSet_injective : Function.Injective ofZFSet.{u} := by
  intro x y h
  induction x using Quotient.inductionOn with | h p => ?_
  induction y using Quotient.inductionOn with | h q => ?_
  exact Quotient.sound (ofPSet_eq_ofPSet_iff.mp h)

theorem ofZFSet_mem_ofZFSet_iff {x y : ZFSet.{u}} : ofZFSet x ∈ ofZFSet y ↔ x ∈ y := by
  induction x using Quotient.inductionOn with | h p => ?_
  induction y using Quotient.inductionOn with | h q => ?_
  obtain ⟨β, B⟩ := q
  change ofPSet p ∈ ofPSet ⟨β, B⟩ ↔ ZFSet.mk p ∈ ZFSet.mk ⟨β, B⟩
  rw [ZFSet.mk_mem_iff, PSet.mem_def, mem_ofPSet_mk]
  exact exists_congr fun _ => ofPSet_eq_ofPSet_iff.trans ⟨PSet.Equiv.symm, PSet.Equiv.symm⟩

theorem wf_ofZFSet (x : ZFSet.{u}) : (ofZFSet x).WF := by
  induction x using Quotient.inductionOn with | h p => ?_
  exact wf_ofPSet p

/-! ## From well-founded hypersets to pre-sets -/

/-- The tree unfolding of the graph `r` below a node accessible along reversed edges. -/
def unfold {α : Type u} (r : α → α → Prop) {a : α} (h : Acc (flip r) a) : PSet.{u} :=
  Acc.rec (motive := fun _ _ => PSet.{u}) (fun a _ ih => ⟨{b // r a b}, fun b => ih b.1 b.2⟩) h

theorem unfold_eq {α : Type u} (r : α → α → Prop) {a : α} (h : Acc (flip r) a) :
    unfold r h = ⟨{b // r a b}, fun b => unfold r (h.inv b.2)⟩ := by
  cases h
  rfl

theorem ofPSet_unfold {α : Type u} {r : α → α → Prop} {a : α} (h : Acc (flip r) a) :
    ofPSet (unfold r h) = decorate r a := by
  induction h with
  | intro a h ih =>
    rw [unfold_eq]
    ext y
    rw [mem_ofPSet_mk, mem_decorate]
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b.1, b.2, (ih b.1 b.2).symm⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, ih b hb⟩

/-- The pre-set of the well-founded members of the hyperset of `G`: the tree unfoldings of
the accessible children of its point. -/
def wfPSet (G : AccessiblePointedGraph.{u}) : PSet.{u} :=
  ⟨{c // G.edge G.point c ∧ Acc (flip G.edge) c}, fun c => unfold G.edge c.2.2⟩

theorem ofPSet_wfPSet (G : AccessiblePointedGraph.{u}) :
    ofPSet (wfPSet G) = HSet.sep WF (mk G) := by
  ext y
  rw [wfPSet, mem_ofPSet_mk, mem_sep, mem_mk]
  constructor
  · rintro ⟨⟨c, hc, hacc⟩, rfl⟩
    rw [ofPSet_unfold]
    exact ⟨⟨c, hc, rfl⟩, wf_decorate_iff.mpr hacc⟩
  · rintro ⟨⟨c, hc, rfl⟩, hwf⟩
    exact ⟨⟨c, hc, wf_decorate_iff.mp hwf⟩, ofPSet_unfold _⟩

/-- The `ZFSet` of the well-founded members of a hyperset, unwound recursively. -/
def toZFSet : HSet.{u} → ZFSet.{u} :=
  Quotient.lift (fun G => ZFSet.mk (wfPSet G)) fun _ _ h =>
    Quotient.sound (ofPSet_eq_ofPSet_iff.mp (by rw [ofPSet_wfPSet, ofPSet_wfPSet, sound h]))

/-- `ofZFSet ∘ toZFSet` keeps the well-founded members. -/
theorem ofZFSet_toZFSet (x : HSet.{u}) : ofZFSet (toZFSet x) = HSet.sep WF x := by
  induction x using HSet.ind with | mk G => ?_
  exact ofPSet_wfPSet G

theorem sep_wf_of_wf {x : HSet.{u}} (hx : x.WF) : HSet.sep WF x = x :=
  ext fun _ => ⟨fun h => (mem_sep.mp h).1, fun h => mem_sep.mpr ⟨h, hx.mem h⟩⟩

theorem ofZFSet_toZFSet_of_wf {x : HSet.{u}} (hx : x.WF) : ofZFSet (toZFSet x) = x :=
  (ofZFSet_toZFSet x).trans (sep_wf_of_wf hx)

theorem toZFSet_ofZFSet (x : ZFSet.{u}) : toZFSet (ofZFSet x) = x :=
  ofZFSet_injective (ofZFSet_toZFSet_of_wf (wf_ofZFSet x))

/-! ## The equivalence -/

/-- The well-founded hypersets are the `ZFSet`s. -/
def wellFoundedPartEquivZFSet : WellFoundedPart.{u} ≃ ZFSet.{u} where
  toFun x := toZFSet x.1
  invFun x := ⟨ofZFSet x, wf_ofZFSet x⟩
  left_inv x := Subtype.ext (ofZFSet_toZFSet_of_wf x.2)
  right_inv := toZFSet_ofZFSet

theorem wellFoundedPartEquivZFSet_mem_iff {x y : WellFoundedPart.{u}} :
    wellFoundedPartEquivZFSet x ∈ wellFoundedPartEquivZFSet y ↔ x.1 ∈ y.1 := by
  rw [← ofZFSet_mem_ofZFSet_iff]
  change ofZFSet (toZFSet x.1) ∈ ofZFSet (toZFSet y.1) ↔ _
  rw [ofZFSet_toZFSet_of_wf x.2, ofZFSet_toZFSet_of_wf y.2]

theorem mem_wellFoundedPartEquivZFSet_symm_iff {x y : ZFSet.{u}} :
    (wellFoundedPartEquivZFSet.symm x).1 ∈ (wellFoundedPartEquivZFSet.symm y).1 ↔ x ∈ y :=
  ofZFSet_mem_ofZFSet_iff

/-! ## `ofZFSet` preserves the set operations -/

/-- The members of the hyperset of a `ZFSet` are the hypersets of its members. -/
theorem mem_ofZFSet_iff {x : ZFSet.{u}} {y : HSet.{u}} :
    y ∈ ofZFSet x ↔ ∃ z ∈ x, ofZFSet z = y := by
  constructor
  · intro h
    have hy : y.WF := (wf_ofZFSet x).mem h
    refine ⟨toZFSet y, ?_, ofZFSet_toZFSet_of_wf hy⟩
    rw [← ofZFSet_mem_ofZFSet_iff, ofZFSet_toZFSet_of_wf hy]
    exact h
  · rintro ⟨z, hz, rfl⟩
    exact ofZFSet_mem_ofZFSet_iff.mpr hz

theorem ofZFSet_empty : ofZFSet (∅ : ZFSet.{u}) = ∅ :=
  eq_empty_iff.mpr fun _ h => by
    obtain ⟨a, _⟩ := mem_ofPSet_mk.mp h
    exact a.elim

theorem ofZFSet_insert (x y : ZFSet.{u}) :
    ofZFSet (insert x y) = insert (ofZFSet x) (ofZFSet y) := by
  ext z
  rw [mem_ofZFSet_iff, mem_insert_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases ZFSet.mem_insert_iff.mp hw with rfl | hw
    · exact Or.inl rfl
    · exact Or.inr (ofZFSet_mem_ofZFSet_iff.mpr hw)
  · rintro (rfl | hz)
    · exact ⟨x, ZFSet.mem_insert x y, rfl⟩
    · obtain ⟨w, hw, rfl⟩ := mem_ofZFSet_iff.mp hz
      exact ⟨w, ZFSet.mem_insert_of_mem x hw, rfl⟩

theorem ofZFSet_singleton (x : ZFSet.{u}) : ofZFSet {x} = {ofZFSet x} := by
  change ofZFSet (insert x ∅) = insert (ofZFSet x) ∅
  rw [ofZFSet_insert, ofZFSet_empty]

theorem ofZFSet_pair (x y : ZFSet.{u}) : ofZFSet {x, y} = {ofZFSet x, ofZFSet y} := by
  rw [ofZFSet_insert, ofZFSet_singleton]

/-- Mathlib's Kuratowski pair is carried to the Kuratowski pair of hypersets. -/
theorem ofZFSet_kpair (x y : ZFSet.{u}) :
    ofZFSet (ZFSet.pair x y) = kpair (ofZFSet x) (ofZFSet y) := by
  rw [ZFSet.pair, ofZFSet_pair, ofZFSet_singleton, ofZFSet_pair, kpair]

theorem ofZFSet_sep (P : ZFSet.{u} → Prop) (x : ZFSet.{u}) :
    ofZFSet (ZFSet.sep P x) = HSet.sep (fun y => P (toZFSet y)) (ofZFSet x) := by
  ext y
  rw [mem_ofZFSet_iff, mem_sep, mem_ofZFSet_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hzx, hP⟩ := ZFSet.mem_sep.mp hz
    exact ⟨⟨z, hzx, rfl⟩, (toZFSet_ofZFSet z).symm ▸ hP⟩
  · rintro ⟨⟨z, hz, rfl⟩, hP⟩
    exact ⟨z, ZFSet.mem_sep.mpr ⟨hz, toZFSet_ofZFSet z ▸ hP⟩, rfl⟩

theorem ofZFSet_sUnion (x : ZFSet.{u}) : ofZFSet (ZFSet.sUnion x) = sUnion (ofZFSet x) := by
  ext y
  rw [mem_ofZFSet_iff, mem_sUnion]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hzw⟩ := ZFSet.mem_sUnion.mp hz
    exact ⟨ofZFSet w, ofZFSet_mem_ofZFSet_iff.mpr hw, ofZFSet_mem_ofZFSet_iff.mpr hzw⟩
  · rintro ⟨w', hw', hy⟩
    obtain ⟨w, hw, rfl⟩ := mem_ofZFSet_iff.mp hw'
    obtain ⟨z, hz, rfl⟩ := mem_ofZFSet_iff.mp hy
    exact ⟨z, ZFSet.mem_sUnion.mpr ⟨w, hw, hz⟩, rfl⟩

theorem ofZFSet_powerset (x : ZFSet.{u}) :
    ofZFSet (ZFSet.powerset x) = powerset (ofZFSet x) := by
  ext y
  rw [mem_ofZFSet_iff, mem_powerset]
  constructor
  · rintro ⟨z, hz, rfl⟩ w hw
    obtain ⟨v, hv, rfl⟩ := mem_ofZFSet_iff.mp hw
    exact ofZFSet_mem_ofZFSet_iff.mpr (ZFSet.mem_powerset.mp hz hv)
  · intro hy
    have hwf : y.WF := wf_of_forall_mem fun _ hw => (wf_ofZFSet x).mem (hy hw)
    refine ⟨toZFSet y, ZFSet.mem_powerset.mpr fun v hv => ?_, ofZFSet_toZFSet_of_wf hwf⟩
    rw [← ofZFSet_mem_ofZFSet_iff] at hv ⊢
    rw [ofZFSet_toZFSet_of_wf hwf] at hv
    exact hy hv

/-! ## Examples -/

/-- `Ω` is not the hyperset of any `ZFSet`. -/
theorem ofZFSet_ne_quineAtom (x : ZFSet.{u}) : ofZFSet x ≠ quineAtom :=
  fun h => not_wf_quineAtom (h ▸ wf_ofZFSet x)

/-- `Ω` has no well-founded member, so `toZFSet` sends it to `∅`. -/
theorem toZFSet_quineAtom : toZFSet quineAtom.{u} = ∅ := by
  apply ofZFSet_injective
  rw [ofZFSet_toZFSet, ofZFSet_empty, eq_empty_iff]
  intro z hz
  obtain ⟨hz, hwf⟩ := mem_sep.mp hz
  exact not_wf_quineAtom (mem_quineAtom.mp hz ▸ hwf)

end HSet

end Mettapedia.TypeTheory.MaterialSets.Hypersets
