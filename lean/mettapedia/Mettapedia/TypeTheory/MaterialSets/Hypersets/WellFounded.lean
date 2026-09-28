import Mettapedia.TypeTheory.MaterialSets.Hypersets.AntiFoundation

/-!
# The well-founded part of the hypersets

A hyperset is well-founded (`HSet.WF`) when membership below it is well-founded: it is in the
accessible part of `∈`. On a graph, the hyperset at a node is well-founded exactly when every
path of edges from the node is finite (`wf_decorate_iff`).

* A self-member is not well-founded (`not_wf_of_mem_self`), from the fact that a node related
  to itself is not accessible (`not_acc_of_rel_self`); so `Ω` is not well-founded
  (`not_wf_quineAtom`).
* The well-founded part is closed under the empty set, `insert`, pairs, union, separation,
  power sets, the hyperset of a family of graphs (`wf_range`) and dependent replacement
  (`wf_image`).

`WellFoundedPart` is the type of well-founded hypersets.

**Controls.** `∅` and `{∅}` are well-founded (`wf_empty`, `wf_singleton_empty`); `Ω` and
`{∅, Ω}` are not (`not_wf_quineAtom`, `not_wf_pair_empty_quineAtom`), so `Ω` is outside the
well-founded part (`WellFoundedPart.ne_quineAtom`); no node of the two-node cycle is accessible
(`not_acc_twoCycle`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets

universe u

/-- A node related to itself is not in the accessible part of the relation. -/
theorem not_acc_of_rel_self {α : Sort*} {r : α → α → Prop} {a : α} (self : r a a) :
    ¬ Acc r a := by
  have irreflexive : ∀ b, Acc r b → ¬ r b b := by
    intro b hb
    induction hb with
    | intro b _ ih => exact fun loop => ih b loop loop
  exact fun h => irreflexive a h self

namespace Hypersets

namespace HSet

/-- A hyperset is well-founded when membership below it is well-founded. -/
def WF (x : HSet.{u}) : Prop :=
  Acc (· ∈ ·) x

variable {x y : HSet.{u}}

theorem WF.mem (hx : x.WF) (hy : y ∈ x) : y.WF :=
  Acc.inv hx hy

theorem wf_of_forall_mem (h : ∀ y ∈ x, y.WF) : x.WF :=
  Acc.intro x h

theorem wf_iff : x.WF ↔ ∀ y ∈ x, y.WF :=
  ⟨fun hx _ hy => hx.mem hy, wf_of_forall_mem⟩

/-- A self-member is not well-founded. -/
theorem not_wf_of_mem_self (h : x ∈ x) : ¬ x.WF :=
  not_acc_of_rel_self h

theorem WF.notMem_self (hx : x.WF) : x ∉ x :=
  fun h => not_wf_of_mem_self h hx

theorem not_wf_of_mem (hy : y ∈ x) (h : ¬ y.WF) : ¬ x.WF :=
  fun hx => h (hx.mem hy)

/-- On a graph: the hyperset at a node is well-founded exactly when the node is accessible
along reversed edges, that is, every path of edges from it is finite. -/
theorem wf_decorate_iff {α : Type u} {r : α → α → Prop} {a : α} :
    (decorate r a).WF ↔ Acc (flip r) a := by
  constructor
  · intro h
    suffices ∀ z : HSet.{u}, z.WF → ∀ b, decorate r b = z → Acc (flip r) b from this _ h a rfl
    intro z hz
    induction hz with
    | intro z _ ih =>
      rintro b rfl
      exact Acc.intro b fun c hc => ih _ (decorate_mem_decorate hc) c rfl
  · intro h
    induction h with
    | intro b _ ih =>
      exact wf_of_forall_mem fun y hy => by
        obtain ⟨c, hc, rfl⟩ := mem_decorate.mp hy
        exact ih c hc

theorem wf_mk_iff {G : AccessiblePointedGraph.{u}} : (mk G).WF ↔ Acc (flip G.edge) G.point := by
  rw [mk_eq_decorate, wf_decorate_iff]

/-! ## Closure of the well-founded part -/

theorem wf_empty : (∅ : HSet.{u}).WF :=
  wf_of_forall_mem fun y hy => absurd hy (notMem_empty y)

theorem WF.insert (hx : x.WF) (hy : y.WF) : (insert x y).WF :=
  wf_of_forall_mem fun _ hz => (mem_insert_iff.mp hz).elim (fun e => e ▸ hx) hy.mem

theorem WF.singleton (hx : x.WF) : ({x} : HSet.{u}).WF :=
  hx.insert wf_empty

theorem WF.pair (hx : x.WF) (hy : y.WF) : ({x, y} : HSet.{u}).WF :=
  hx.insert hy.singleton

theorem WF.sUnion (hx : x.WF) : (sUnion x).WF :=
  wf_of_forall_mem fun _ hy =>
    let ⟨_, hz, hyz⟩ := mem_sUnion.mp hy
    (hx.mem hz).mem hyz

theorem WF.sep (hx : x.WF) (P : HSet.{u} → Prop) : (HSet.sep P x).WF :=
  wf_of_forall_mem fun _ hy => hx.mem (mem_sep.mp hy).1

theorem WF.powerset (hx : x.WF) : (powerset x).WF :=
  wf_of_forall_mem fun _ hy => wf_of_forall_mem fun _ hz => hx.mem (mem_powerset.mp hy hz)

/-- The hyperset of a family of graphs is well-founded when each graph pictures a
well-founded hyperset. -/
theorem wf_range {ι : Type u} {g : ι → AccessiblePointedGraph.{u}} (h : ∀ i, (mk (g i)).WF) :
    (range g).WF :=
  wf_of_forall_mem fun _ hy =>
    let ⟨i, e⟩ := mem_range.mp hy
    e ▸ h i

/-- Dependent replacement preserves well-foundedness. -/
theorem wf_image {p : Presentation.{u}} {F : El (· ∈ ·) x → HSet.{u}} (h : ∀ a, (F a).WF) :
    (image p x F).WF :=
  wf_of_forall_mem fun _ hy =>
    let ⟨a, e⟩ := mem_image.mp hy
    e ▸ h a

/-! ## Examples -/

/-- `Ω` is not well-founded. -/
theorem not_wf_quineAtom : ¬ quineAtom.{u}.WF :=
  not_wf_of_mem_self quineAtom_mem_self

theorem not_wf_pair_empty_quineAtom : ¬ ({∅, quineAtom} : HSet.{u}).WF :=
  not_wf_of_mem (mem_pair.mpr (Or.inr rfl)) not_wf_quineAtom

theorem wf_singleton_empty : ({∅} : HSet.{u}).WF :=
  wf_empty.singleton

/-- No node of the two-node cycle is accessible. -/
theorem not_acc_twoCycle (a : twoCycle.{u}.Node) : ¬ Acc (flip twoCycle.edge) a := fun h =>
  not_wf_quineAtom ((decorate_twoCycle a) ▸ wf_decorate_iff.mpr h)

end HSet

/-- The well-founded hypersets. -/
abbrev WellFoundedPart : Type (u + 1) :=
  {x : HSet.{u} // x.WF}

namespace WellFoundedPart

/-- Membership in the well-founded part. -/
abbrev Mem (x X : WellFoundedPart.{u}) : Prop :=
  x.1 ∈ X.1

/-- The empty set is in the well-founded part. -/
def empty : WellFoundedPart.{u} :=
  ⟨∅, HSet.wf_empty⟩

/-- `Ω` is not in the well-founded part. -/
theorem ne_quineAtom (x : WellFoundedPart.{u}) : x.1 ≠ HSet.quineAtom :=
  fun h => HSet.not_wf_quineAtom (h ▸ x.2)

end WellFoundedPart

end Hypersets

end Mettapedia.TypeTheory.MaterialSets
