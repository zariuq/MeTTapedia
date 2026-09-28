import Mettapedia.TypeTheory.MaterialSets.MembershipEvidence
import Mettapedia.TypeTheory.MaterialSets.Hypersets.Hyperset

/-!
# Set operations on hypersets

Each operation is pictured by `sup` of a small family of graphs built from graphs of its
arguments. Its members depend only on the members of its arguments, so by extensionality it
does not depend on the graphs chosen.

* `range g`: the hyperset whose members are pictured by a small family of graphs;
* `∅`, `insert`, `{x}` and `{x, y}`;
* separation `HSet.sep P x`, for any proposition `P`;
* union `sUnion`;
* power set `powerset`: its members are the subsets of `x`, one for each proposition-valued
  subset of the children of the point of a graph of `x`.

None of these uses choice.

**Dependent replacement.** `image p x F`, for a family `F : El (· ∈ ·) x → HSet` on the
members of `x` with their evidence, needs a graph for each value of `F`. A `Presentation`
supplies a graph for every hyperset, a section of `mk`; the image does not depend on the
presentation (`image_eq_image`). `Presentation.choice` takes `Quotient.out`, and so depends on
`Classical.choice`. Two cases need no presentation:

* a family already given by graphs, over the children of a graph of `x`: its image is `range`
  (`image_eq_range`);
* a family whose values lie in a given hyperset `B`: its image is separated from `B`
  (`imageWithin`, `image_eq_imageWithin`).

So replacement is collection followed by separation, and only collection asks for graphs: a
family of hypersets has an image, necessarily unique, exactly when some hyperset collects its
values (`existsUnique_image_iff_exists_bound`), and a family presented by graphs is collected
(`exists_bound_of_presented`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

open AccessiblePointedGraph

universe u

namespace HSet

/-! ## The hyperset of a family of graphs -/

/-- The hyperset whose members are pictured by the graphs of a small family. -/
def range {ι : Type u} (g : ι → AccessiblePointedGraph.{u}) : HSet.{u} :=
  mk (sup g)

theorem mem_range {ι : Type u} {g : ι → AccessiblePointedGraph.{u}} {y : HSet.{u}} :
    y ∈ range g ↔ ∃ i, mk (g i) = y := by
  rw [range, mem_mk]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨i, rfl⟩ := supEdge_none_iff.mp hc
    exact ⟨i, (sound (repoint_sup_equiv i)).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, SupEdge.point i, sound (repoint_sup_equiv i)⟩

theorem mk_mem_range {ι : Type u} (g : ι → AccessiblePointedGraph.{u}) (i : ι) :
    mk (g i) ∈ range g :=
  mem_range.mpr ⟨i, rfl⟩

/-! ## The empty hyperset, insertion and pairs -/

instance : EmptyCollection HSet.{u} :=
  ⟨range (PEmpty.elim : PEmpty.{u + 1} → AccessiblePointedGraph.{u})⟩

theorem notMem_empty (x : HSet.{u}) : x ∉ (∅ : HSet.{u}) := fun h => by
  obtain ⟨i, _⟩ := mem_range.mp h
  exact i.elim

theorem mk_empty : mk AccessiblePointedGraph.empty.{u} = (∅ : HSet.{u}) :=
  rfl

theorem eq_empty_iff {x : HSet.{u}} : x = ∅ ↔ ∀ z, z ∉ x :=
  ⟨fun h z hz => notMem_empty z (h ▸ hz),
    fun h => ext fun z => ⟨fun hz => (h z hz).elim, fun hz => (notMem_empty z hz).elim⟩⟩

private theorem mem_insert_aux {G H : AccessiblePointedGraph.{u}} {z : HSet.{u}} :
    z ∈ range (fun o : Option {c // H.edge H.point c} => o.elim G fun c => H.repoint c.1) ↔
      z = mk G ∨ z ∈ mk H := by
  rw [mem_range, mem_mk]
  constructor
  · rintro ⟨_ | c, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨c.1, c.2, rfl⟩
  · rintro (rfl | ⟨c, hc, rfl⟩)
    · exact ⟨none, rfl⟩
    · exact ⟨some ⟨c, hc⟩, rfl⟩

/-- `insert x y`: the members of `y`, and `x`. -/
protected def insert (x y : HSet.{u}) : HSet.{u} :=
  Quotient.liftOn₂ x y
    (fun G H => range fun o : Option {c // H.edge H.point c} => o.elim G fun c => H.repoint c.1)
    fun _ _ _ _ hG hH => ext fun _ => by rw [mem_insert_aux, mem_insert_aux, sound hG, sound hH]

instance : Insert HSet.{u} HSet.{u} :=
  ⟨HSet.insert⟩

instance : Singleton HSet.{u} HSet.{u} :=
  ⟨fun x => insert x ∅⟩

instance : LawfulSingleton HSet.{u} HSet.{u} :=
  ⟨fun _ => rfl⟩

theorem mem_insert_iff {x y z : HSet.{u}} : z ∈ insert x y ↔ z = x ∨ z ∈ y := by
  induction x using HSet.ind with | mk G => ?_
  induction y using HSet.ind with | mk H => ?_
  exact mem_insert_aux

theorem mem_singleton {x z : HSet.{u}} : z ∈ ({x} : HSet.{u}) ↔ z = x :=
  mem_insert_iff.trans (or_iff_left (notMem_empty z))

theorem mem_singleton_self (x : HSet.{u}) : x ∈ ({x} : HSet.{u}) :=
  mem_singleton.mpr rfl

theorem mem_pair {x y z : HSet.{u}} : z ∈ ({x, y} : HSet.{u}) ↔ z = x ∨ z = y :=
  mem_insert_iff.trans (or_congr_right mem_singleton)

theorem singleton_inj {x y : HSet.{u}} : ({x} : HSet.{u}) = {y} ↔ x = y :=
  ⟨fun h => mem_singleton.mp (h ▸ mem_singleton_self x), fun h => h ▸ rfl⟩

/-! ## Separation -/

private theorem mem_sep_aux {P : HSet.{u} → Prop} {G : AccessiblePointedGraph.{u}} {y : HSet.{u}} :
    y ∈ range (fun c : {c // G.edge G.point c ∧ P (decorate G.edge c)} => G.repoint c.1) ↔
      y ∈ mk G ∧ P y := by
  rw [mem_range, mem_mk]
  constructor
  · rintro ⟨⟨c, hc, hP⟩, rfl⟩
    exact ⟨⟨c, hc, rfl⟩, hP⟩
  · rintro ⟨⟨c, hc, rfl⟩, hP⟩
    exact ⟨⟨c, hc, hP⟩, rfl⟩

/-- Separation: the members of `x` satisfying `P`. -/
protected def sep (P : HSet.{u} → Prop) (x : HSet.{u}) : HSet.{u} :=
  Quotient.liftOn x
    (fun G => range fun c : {c // G.edge G.point c ∧ P (decorate G.edge c)} => G.repoint c.1)
    fun _ _ h => ext fun _ => by rw [mem_sep_aux, mem_sep_aux, sound h]

instance : Sep HSet.{u} HSet.{u} :=
  ⟨HSet.sep⟩

theorem mem_sep {P : HSet.{u} → Prop} {x y : HSet.{u}} : y ∈ HSet.sep P x ↔ y ∈ x ∧ P y := by
  induction x using HSet.ind with | mk G => ?_
  exact mem_sep_aux

/-! ## Union -/

private theorem mem_sUnion_aux {G : AccessiblePointedGraph.{u}} {y : HSet.{u}} :
    y ∈ range (fun p : {p : G.Node × G.Node // G.edge G.point p.1 ∧ G.edge p.1 p.2} =>
        G.repoint p.1.2) ↔ ∃ z ∈ mk G, y ∈ z := by
  rw [mem_range]
  constructor
  · rintro ⟨⟨⟨c, m⟩, hc, hm⟩, rfl⟩
    exact ⟨decorate G.edge c, ⟨c, hc, rfl⟩, decorate_mem_decorate hm⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, hy⟩
    obtain ⟨m, hm, rfl⟩ := mem_decorate.mp hy
    exact ⟨⟨(c, m), hc, hm⟩, rfl⟩

/-- The union of the members of `x`. -/
def sUnion (x : HSet.{u}) : HSet.{u} :=
  Quotient.liftOn x
    (fun G => range fun p : {p : G.Node × G.Node // G.edge G.point p.1 ∧ G.edge p.1 p.2} =>
      G.repoint p.1.2)
    fun _ _ h => ext fun _ => by rw [mem_sUnion_aux, mem_sUnion_aux, sound h]

theorem mem_sUnion {x y : HSet.{u}} : y ∈ sUnion x ↔ ∃ z ∈ x, y ∈ z := by
  induction x using HSet.ind with | mk G => ?_
  exact mem_sUnion_aux

/-! ## Power set -/

instance : HasSubset HSet.{u} :=
  ⟨fun x y => ∀ ⦃z⦄, z ∈ x → z ∈ y⟩

theorem subset_iff {x y : HSet.{u}} : x ⊆ y ↔ ∀ ⦃z⦄, z ∈ x → z ∈ y :=
  Iff.rfl

private theorem mem_powerset_aux {G : AccessiblePointedGraph.{u}} {y : HSet.{u}} :
    y ∈ range (fun S : Set {c // G.edge G.point c} =>
        sup fun c : {c // c ∈ S} => G.repoint c.1.1) ↔ y ⊆ mk G := by
  rw [mem_range]
  constructor
  · rintro ⟨S, rfl⟩ z hz
    obtain ⟨c, rfl⟩ := mem_range.mp hz
    exact ⟨c.1.1, c.1.2, rfl⟩
  · intro hy
    refine ⟨{c | decorate G.edge c.1 ∈ y}, ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
    · obtain ⟨c, rfl⟩ := mem_range.mp hz
      exact c.2
    · obtain ⟨c, hc, rfl⟩ := hy hz
      exact mem_range.mpr ⟨⟨⟨c, hc⟩, hz⟩, rfl⟩

/-- The power set: the hyperset of the subsets of `x`. A subset is given by a
proposition-valued subset of the children of the point of a graph of `x`. -/
def powerset (x : HSet.{u}) : HSet.{u} :=
  Quotient.liftOn x
    (fun G => range fun S : Set {c // G.edge G.point c} =>
      sup fun c : {c // c ∈ S} => G.repoint c.1.1)
    fun _ _ h => ext fun _ => by rw [mem_powerset_aux, mem_powerset_aux, sound h]

theorem mem_powerset {x y : HSet.{u}} : y ∈ powerset x ↔ y ⊆ x := by
  induction x using HSet.ind with | mk G => ?_
  exact mem_powerset_aux

/-! ## Dependent replacement -/

/-- A presentation of every hyperset by a graph: a section of `mk`. -/
structure Presentation : Type (u + 1) where
  /-- The graph presenting a hyperset. -/
  graph : HSet.{u} → AccessiblePointedGraph.{u}
  /-- The graph of `x` pictures `x`. -/
  mk_graph : ∀ x, mk (graph x) = x

theorem Presentation.decorate_mem (p : Presentation.{u}) (x : HSet.{u})
    {c : (p.graph x).Node} (hc : (p.graph x).edge (p.graph x).point c) :
    decorate (p.graph x).edge c ∈ x := by
  have h : decorate (p.graph x).edge c ∈ HSet.mk (p.graph x) := mem_mk.mpr ⟨c, hc, rfl⟩
  rwa [p.mk_graph x] at h

/-- Dependent replacement: the hyperset of the values of a family on the members of `x`,
with their evidence. The presentation supplies a graph of `x`, over whose children the values
are indexed, and a graph for each value. -/
def image (p : Presentation.{u}) (x : HSet.{u}) (F : El (· ∈ ·) x → HSet.{u}) : HSet.{u} :=
  range fun c : {c // (p.graph x).edge (p.graph x).point c} =>
    p.graph (F ⟨decorate (p.graph x).edge c.1, p.decorate_mem x c.2⟩)

theorem mem_image {p : Presentation.{u}} {x : HSet.{u}} {F : El (· ∈ ·) x → HSet.{u}}
    {y : HSet.{u}} : y ∈ image p x F ↔ ∃ a, F a = y := by
  rw [image, mem_range]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨_, (p.mk_graph _).symm⟩
  · rintro ⟨⟨z, hz⟩, rfl⟩
    have hz' : z ∈ mk (p.graph x) := (p.mk_graph x).symm ▸ hz
    obtain ⟨c, hc, rfl⟩ := mem_mk.mp hz'
    exact ⟨⟨c, hc⟩, p.mk_graph _⟩

/-- The image does not depend on the presentation. -/
theorem image_eq_image (p q : Presentation.{u}) (x : HSet.{u}) (F : El (· ∈ ·) x → HSet.{u}) :
    image p x F = image q x F :=
  ext fun _ => mem_image.trans mem_image.symm

/-- Dependent replacement below a bound: the values of `F` that are members of `B`, separated
from `B`. When `B` collects every value of `F`, this is the image of `F`, with no
presentation. -/
def imageWithin (B x : HSet.{u}) (F : El (· ∈ ·) x → HSet.{u}) : HSet.{u} :=
  HSet.sep (fun y => ∃ a, F a = y) B

theorem mem_imageWithin {B x y : HSet.{u}} {F : El (· ∈ ·) x → HSet.{u}}
    (bound : ∀ a, F a ∈ B) : y ∈ imageWithin B x F ↔ ∃ a, F a = y :=
  mem_sep.trans ⟨And.right, fun ⟨a, e⟩ => ⟨e ▸ bound a, a, e⟩⟩

theorem image_eq_imageWithin (p : Presentation.{u}) {B x : HSet.{u}}
    {F : El (· ∈ ·) x → HSet.{u}} (bound : ∀ a, F a ∈ B) : image p x F = imageWithin B x F :=
  ext fun _ => mem_image.trans (mem_imageWithin bound).symm

/-- A family has an image exactly when some hyperset collects its values; the image is then
unique. -/
theorem existsUnique_image_iff_exists_bound {ι : Sort*} {F : ι → HSet.{u}} :
    (∃! z : HSet.{u}, ∀ y, y ∈ z ↔ ∃ i, F i = y) ↔ ∃ B : HSet.{u}, ∀ i, F i ∈ B := by
  constructor
  · rintro ⟨z, hz, -⟩
    exact ⟨z, fun i => (hz (F i)).mpr ⟨i, rfl⟩⟩
  · rintro ⟨B, hB⟩
    have members : ∀ y, y ∈ HSet.sep (fun y => ∃ i, F i = y) B ↔ ∃ i, F i = y := fun _ =>
      mem_sep.trans ⟨And.right, fun ⟨i, e⟩ => ⟨e ▸ hB i, i, e⟩⟩
    exact ⟨_, members, fun z hz => ext fun y => (hz y).trans (members y).symm⟩

/-- A family presented by graphs is collected by the hyperset of its graphs. -/
theorem exists_bound_of_presented {ι : Type u} {F : ι → HSet.{u}}
    (h : ∃ g : ι → AccessiblePointedGraph.{u}, ∀ i, mk (g i) = F i) :
    ∃ B : HSet.{u}, ∀ i, F i ∈ B :=
  let ⟨g, hg⟩ := h
  ⟨range g, fun i => hg i ▸ mk_mem_range g i⟩

/-- Over a family presented by graphs on the children of the point of `G`, dependent
replacement is `range`. -/
theorem image_eq_range (p : Presentation.{u}) {G : AccessiblePointedGraph.{u}}
    {F : El (· ∈ ·) (mk G) → HSet.{u}} (g : {c // G.edge G.point c} → AccessiblePointedGraph.{u})
    (presents : ∀ c, mk (g c) = F ⟨decorate G.edge c.1, mem_mk.mpr ⟨c.1, c.2, rfl⟩⟩) :
    image p (mk G) F = range g := by
  ext y
  rw [mem_image, mem_range]
  constructor
  · rintro ⟨⟨z, hz⟩, rfl⟩
    obtain ⟨c, hc, rfl⟩ := mem_mk.mp hz
    exact ⟨⟨c, hc⟩, presents ⟨c, hc⟩⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, (presents c).symm⟩

/-- `Classical.choice`, through `Quotient.out`, presents every hyperset by a graph. -/
noncomputable def Presentation.choice : Presentation.{u} :=
  ⟨Quotient.out, Quotient.out_eq⟩

/-! ## Examples -/

theorem empty_ne_singleton_empty : (∅ : HSet.{u}) ≠ {∅} := by
  intro h
  have self := mem_singleton_self (∅ : HSet.{u})
  rw [← h] at self
  exact notMem_empty _ self

/-- A constant map to graphs is not a presentation: the empty graph pictures only `∅`. -/
theorem not_forall_mk_empty_eq : ¬ ∀ x : HSet.{u}, mk AccessiblePointedGraph.empty = x :=
  fun h => empty_ne_singleton_empty (mk_empty.symm.trans (h {∅}))

/-- Two edges to childless nodes picture `{∅}`: the second edge is forgotten. -/
theorem range_bool_empty :
    range (fun _ : ULift.{u} Bool => AccessiblePointedGraph.empty.{u}) = {∅} :=
  ext fun _ => mem_range.trans
    ⟨fun ⟨_, h⟩ => mem_singleton.mpr (h.symm.trans mk_empty), fun h => ⟨⟨true⟩,
      (mk_empty.trans (mem_singleton.mp h).symm)⟩⟩

theorem sep_false (x : HSet.{u}) : HSet.sep (fun _ => False) x = ∅ :=
  eq_empty_iff.mpr fun _ h => (mem_sep.mp h).2

theorem sep_true (x : HSet.{u}) : HSet.sep (fun _ => True) x = x :=
  ext fun _ => mem_sep.trans (and_iff_left trivial)

theorem powerset_empty : powerset (∅ : HSet.{u}) = {∅} :=
  ext fun y => by
    rw [mem_powerset, mem_singleton, eq_empty_iff]
    exact ⟨fun h z hz => notMem_empty z (h hz), fun h z hz => (h z hz).elim⟩

theorem sUnion_singleton (x : HSet.{u}) : sUnion {x} = x :=
  ext fun _ => mem_sUnion.trans
    ⟨fun ⟨_, hw, hz⟩ => mem_singleton.mp hw ▸ hz, fun hz => ⟨x, mem_singleton_self x, hz⟩⟩

theorem sUnion_empty : sUnion (∅ : HSet.{u}) = ∅ :=
  eq_empty_iff.mpr fun _ h =>
    let ⟨w, hw, _⟩ := mem_sUnion.mp h
    notMem_empty w hw

/-- The constant family `∅` on `{∅}` has image `{∅}`, for every presentation. -/
theorem image_const_empty (p : Presentation.{u}) :
    image p {∅} (fun _ => ∅) = ({∅} : HSet.{u}) :=
  ext fun _ => mem_image.trans
    ⟨fun ⟨_, e⟩ => mem_singleton.mpr e.symm,
      fun h => ⟨⟨∅, mem_singleton_self ∅⟩, (mem_singleton.mp h).symm⟩⟩

theorem imageWithin_empty (x : HSet.{u}) (F : El (· ∈ ·) x → HSet.{u}) :
    imageWithin ∅ x F = ∅ :=
  eq_empty_iff.mpr fun _ h => notMem_empty _ (mem_sep.mp h).1

/-- Separated from a bound that misses its values, a family loses its image: the constant family
`∅` on `{∅}` has image `{∅}`, but separated from `∅` it gives `∅`. -/
theorem imageWithin_empty_ne_image (p : Presentation.{u}) :
    imageWithin ∅ {∅} (fun _ => ∅) ≠ image p {∅} (fun _ => (∅ : HSet.{u})) := by
  rw [imageWithin_empty, image_const_empty]
  exact empty_ne_singleton_empty

end HSet

end Mettapedia.TypeTheory.MaterialSets.Hypersets
