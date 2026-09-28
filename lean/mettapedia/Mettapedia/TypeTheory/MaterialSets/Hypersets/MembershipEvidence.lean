import Mettapedia.TypeTheory.MaterialSets.DependentSum
import Mettapedia.TypeTheory.MaterialSets.Hypersets.KuratowskiPair

/-!
# Membership evidence of hypersets

Membership is carried by two layers.

**The graph layer.** Evidence that `G` is a member of `H` is an edge from the point of `H` to
a child whose re-pointed graph is bisimilar to `G` (`AccessiblePointedGraph.MemEvidence`). It
is proof-relevant. The graph `twoChildren`, a point with two edges to childless nodes, has two
pieces of evidence for one member (`twoChildrenWitness_ne`); forgetting evidence is then not
injective (`fst_not_injective`, from `fst_injective_iff`), membership is not propositional
(`not_propositional`), and the family that reads the edge factors through no function of the
members (`edgeFamily_not_factors`, from `not_factors_of_distinguishes`). Over a point with one
edge, forgetting is injective (`oneChild_fst_injective`). Recovering an edge from the bare fact
of membership would choose among the edges, so no evidence recovery is given in this layer.
Re-pointing at a child changes the pictured hyperset (`not_repoint_twoChildren_equiv`).

**The quotient layer.** Membership of hypersets is a proposition (`HSet.propositional`),
recovered from its bare fact (`HSet.recovery`) and extensional (`HSet.extensional`). The
quotient forgets which edge was taken: `twoChildren` pictures `{∅}` (`mk_twoChildren`). The set
of dependent pairs is the dependent sum of member types (`HSet.sigmaSetEquiv`).

**The well-founded part** satisfies the same laws. It is closed under union, Kuratowski
pairing with its derived projections, and dependent replacement, and its equality is the
restriction of equality of hypersets: bisimilarity of graphs (`WellFoundedPart.mk_eq_mk_iff`)
and strong extensionality (`WellFoundedPart.eq_of_isBisimulation`). The set of dependent pairs
is then the dependent sum of member types (`WellFoundedPart.sigmaSetEquiv`).

Dependent replacement over an arbitrary family takes a `Presentation` of the hypersets by
graphs; `Presentation.choice` supplies one through `Classical.choice`. Everything else here is
choice-free.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

open AccessiblePointedGraph

universe u

theorem nonempty_iff_of_prop {p : Prop} : Nonempty p ↔ p :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

/-! ## The quotient layer -/

namespace HSet

/-- Membership of hypersets is a proposition. -/
theorem propositional : PropositionalMembership fun x X : HSet.{u} => x ∈ X :=
  fun _ _ => inferInstance

/-- Evidence of membership is its bare fact. -/
def recovery : EvidenceRecovery fun x X : HSet.{u} => x ∈ X :=
  ⟨fun h => h.elim id⟩

theorem extensional : Extensional fun x X : HSet.{u} => x ∈ X := fun coext =>
  ext fun z => nonempty_iff_of_prop.symm.trans ((coext z).trans nonempty_iff_of_prop)

def union : UnionOperation fun x X : HSet.{u} => x ∈ X where
  union := sUnion
  mem_union hx hW := mem_sUnion.mpr ⟨_, hW, hx⟩
  exists_of_mem_union h :=
    let ⟨W, hW, hx⟩ := mem_sUnion.mp h
    ⟨W, ⟨hx⟩, ⟨hW⟩⟩

/-- Dependent replacement, through a presentation of the hypersets by graphs. -/
def dependentReplacement (p : Presentation.{u}) :
    DependentReplacement fun x X : HSet.{u} => x ∈ X where
  image := image p
  mem_image _ a := mem_image.mpr ⟨a, rfl⟩
  exists_of_mem_image h := mem_image.mp h

/-- Kuratowski pairs with their derived projections. -/
def kuratowski : Pairing HSet.{u} where
  pair := kpair
  fst := fst
  snd := snd
  fst_pair := fst_kpair
  snd_pair := snd_kpair

/-- The members of the set of dependent pairs are the dependent sum of member types. -/
def sigmaSetEquiv (p : Presentation.{u}) (X : HSet.{u}) (B : El (· ∈ ·) X → HSet.{u}) :
    El (· ∈ ·) (sigmaSet (dependentReplacement p) union kuratowski X B) ≃
      Σ' a : El (· ∈ ·) X, El (· ∈ ·) (B a) :=
  MaterialSets.sigmaSetEquiv (dependentReplacement p) union kuratowski propositional recovery X B

end HSet

/-! ## The graph layer -/

namespace AccessiblePointedGraph

/-- Evidence that `G` is a member of `H` in the graph layer: an edge from the point of `H` to
a child whose re-pointed graph is bisimilar to `G`. -/
def MemEvidence (G H : AccessiblePointedGraph.{u}) : Type u :=
  {c : H.Node // H.edge H.point c ∧ G ≈ H.repoint c}

/-- Evidence exists exactly when the pictured hypersets are members. -/
theorem nonempty_memEvidence_iff {G H : AccessiblePointedGraph.{u}} :
    Nonempty (MemEvidence G H) ↔ HSet.mk G ∈ HSet.mk H :=
  ⟨fun ⟨c⟩ => HSet.mk_mem_mk_iff.mpr ⟨c.1, c.2⟩,
    fun h => let ⟨c, hc⟩ := HSet.mk_mem_mk_iff.mp h; ⟨⟨c, hc⟩⟩⟩

/-- A point with two edges to childless nodes. -/
def twoChildren : AccessiblePointedGraph.{u} :=
  sup fun _ : ULift.{u} Bool => empty

/-- The evidence given by the edge to the child tagged `b`. -/
def twoChildrenWitness (b : Bool) : MemEvidence empty twoChildren.{u} :=
  ⟨some ⟨⟨b⟩, empty.point⟩, SupEdge.point (g := fun _ : ULift.{u} Bool => empty) ⟨b⟩,
    Setoid.symm (repoint_sup_equiv (g := fun _ : ULift.{u} Bool => empty) ⟨b⟩)⟩

/-- The two edges are two pieces of evidence for one member. -/
theorem twoChildrenWitness_ne : twoChildrenWitness.{u} true ≠ twoChildrenWitness false :=
  fun h => absurd (congrArg (fun x : Option (Σ _ : ULift.{u} Bool, empty.{u}.Node) =>
    Option.elim x false fun p => p.1.down) (congrArg Subtype.val h)) Bool.noConfusion

theorem not_subsingleton_memEvidence : ¬ Subsingleton (MemEvidence empty twoChildren.{u}) :=
  fun _ => twoChildrenWitness_ne (Subsingleton.elim _ _)

/-- Forgetting evidence is not injective in the graph layer. -/
theorem fst_not_injective :
    ¬ Function.Injective
      (PSigma.fst : El MemEvidence twoChildren.{u} → AccessiblePointedGraph.{u}) :=
  fun h => not_subsingleton_memEvidence (fst_injective_iff.mp h empty)

/-- Membership in the graph layer is not propositional. -/
theorem not_propositional : ¬ PropositionalMembership MemEvidence.{u} :=
  not_propositional_of_witnesses twoChildrenWitness_ne

/-- The family that reads which edge a piece of evidence takes. -/
def edgeFamily (a : El MemEvidence twoChildren.{u}) : twoChildren.{u}.Node :=
  a.2.1

theorem edgeFamily_distinguishes :
    edgeFamily ⟨empty, twoChildrenWitness.{u} true⟩ ≠
      edgeFamily ⟨empty, twoChildrenWitness false⟩ :=
  fun h => twoChildrenWitness_ne (Subtype.ext h)

/-- The family that reads the edge factors through no function of the members. -/
theorem edgeFamily_not_factors :
    ¬ ∃ f : Members MemEvidence twoChildren.{u} → twoChildren.{u}.Node,
      ∀ a, f (forget a) = edgeFamily a :=
  not_factors_of_distinguishes edgeFamily edgeFamily_distinguishes

/-- The quotient forgets which edge was taken: `twoChildren` pictures `{∅}`. -/
theorem mk_twoChildren : HSet.mk twoChildren.{u} = {∅} :=
  HSet.range_bool_empty

/-- Re-pointing at a child changes the pictured hyperset: `twoChildren` pictures `{∅}`, its
re-pointed child `∅`. -/
theorem not_repoint_twoChildren_equiv :
    ¬ twoChildren.{u}.repoint (twoChildrenWitness true).1 ≈ twoChildren := fun h =>
  HSet.empty_ne_singleton_empty <|
    calc (∅ : HSet.{u}) = HSet.mk empty := HSet.mk_empty.symm
      _ = HSet.mk ((sup fun _ : ULift.{u} Bool => empty).repoint (some ⟨⟨true⟩, empty.point⟩)) :=
        (HSet.sound (repoint_sup_equiv (g := fun _ : ULift.{u} Bool => empty) ⟨true⟩)).symm
      _ = HSet.mk twoChildren := HSet.sound h
      _ = {∅} := mk_twoChildren

/-- A point with one edge, to the point of `G`. -/
def oneChild (G : AccessiblePointedGraph.{u}) : AccessiblePointedGraph.{u} :=
  sup fun _ : PUnit.{u + 1} => G

instance (G H : AccessiblePointedGraph.{u}) : Subsingleton (MemEvidence G (oneChild H)) :=
  ⟨fun a b => Subtype.ext <| by
    obtain ⟨_, ha⟩ := supEdge_none_iff.mp a.2.1
    obtain ⟨_, hb⟩ := supEdge_none_iff.mp b.2.1
    exact ha.trans hb.symm⟩

/-- Over a point with one edge, forgetting evidence is injective. -/
theorem oneChild_fst_injective (H : AccessiblePointedGraph.{u}) :
    Function.Injective (PSigma.fst : El MemEvidence (oneChild H) → AccessiblePointedGraph.{u}) :=
  fst_injective_iff.mpr fun _ => inferInstance

end AccessiblePointedGraph

/-! ## The well-founded part -/

namespace WellFoundedPart

open HSet

theorem propositional : PropositionalMembership Mem.{u} :=
  fun _ _ => inferInstance

def recovery : EvidenceRecovery Mem.{u} :=
  ⟨fun h => h.elim id⟩

theorem extensional : Extensional Mem.{u} := fun {X Y} coext =>
  Subtype.ext <| HSet.ext fun z =>
    ⟨fun hz => nonempty_iff_of_prop.mp ((coext ⟨z, X.2.mem hz⟩).mp ⟨hz⟩),
      fun hz => nonempty_iff_of_prop.mp ((coext ⟨z, Y.2.mem hz⟩).mpr ⟨hz⟩)⟩

def union : UnionOperation Mem.{u} where
  union X := ⟨sUnion X.1, X.2.sUnion⟩
  mem_union hx hW := mem_sUnion.mpr ⟨_, hW, hx⟩
  exists_of_mem_union := fun {_ Y} h =>
    let ⟨W, hW, hx⟩ := mem_sUnion.mp h
    ⟨⟨W, Y.2.mem hW⟩, ⟨hx⟩, ⟨hW⟩⟩

/-- Kuratowski pairs of well-founded hypersets, with their derived projections. -/
def pairing : Pairing WellFoundedPart.{u} where
  pair x y := ⟨kpair x.1 y.1, x.2.kpair y.2⟩
  fst z := ⟨HSet.fst z.1, z.2.fst⟩
  snd z := ⟨HSet.snd z.1, z.2.snd⟩
  fst_pair x y := Subtype.ext (fst_kpair x.1 y.1)
  snd_pair x y := Subtype.ext (snd_kpair x.1 y.1)

/-- Dependent replacement in the well-founded part, through a presentation of the hypersets by
graphs. -/
def dependentReplacement (p : Presentation.{u}) : DependentReplacement Mem.{u} where
  image X F := ⟨image p X.1 fun a => (F ⟨⟨a.1, X.2.mem a.2⟩, a.2⟩).1, wf_image fun _ => (F _).2⟩
  mem_image := fun {X} F a => by
    change (F a).1 ∈ image p X.1 fun b => (F ⟨⟨b.1, X.2.mem b.2⟩, b.2⟩).1
    exact mem_image.mpr ⟨⟨a.1.1, a.2⟩, rfl⟩
  exists_of_mem_image := fun {X F y} h => by
    change y.1 ∈ image p X.1 (fun b => (F ⟨⟨b.1, X.2.mem b.2⟩, b.2⟩).1) at h
    obtain ⟨a, e⟩ := mem_image.mp h
    exact ⟨⟨⟨a.1, X.2.mem a.2⟩, a.2⟩, Subtype.ext e⟩

/-- The members of the set of dependent pairs are the dependent sum of member types. -/
def sigmaSetEquiv (p : Presentation.{u}) (X : WellFoundedPart.{u})
    (B : El Mem X → WellFoundedPart.{u}) :
    El Mem (sigmaSet (dependentReplacement p) union pairing X B) ≃ Σ' a : El Mem X, El Mem (B a) :=
  MaterialSets.sigmaSetEquiv (dependentReplacement p) union pairing propositional recovery X B

/-- Equality of well-founded hypersets is bisimilarity of their graphs. -/
theorem mk_eq_mk_iff {G H : AccessiblePointedGraph.{u}} {hG : (HSet.mk G).WF}
    {hH : (HSet.mk H).WF} :
    (⟨HSet.mk G, hG⟩ : WellFoundedPart.{u}) = ⟨HSet.mk H, hH⟩ ↔ G ≈ H :=
  Subtype.ext_iff.trans HSet.mk_eq_mk_iff

/-- Strong extensionality of the well-founded part: a bisimulation of its membership graph
relates only equal sets. -/
theorem eq_of_isBisimulation {R : WellFoundedPart.{u} → WellFoundedPart.{u} → Prop}
    (hR : IsBisimulation (fun x y : WellFoundedPart.{u} => Mem y x) (fun x y => Mem y x) R)
    {x y : WellFoundedPart.{u}} (h : R x y) : x = y := by
  refine Subtype.ext (HSet.eq_of_isBisimulation
    (R := fun a b => ∃ x y : WellFoundedPart.{u}, x.1 = a ∧ y.1 = b ∧ R x y) ?_ ⟨x, y, rfl, rfl, h⟩)
  rintro _ _ ⟨x, y, rfl, rfl, hxy⟩
  refine ⟨fun a' ha => ?_, fun b' hb => ?_⟩
  · obtain ⟨y', hy', hR'⟩ := (hR hxy).1 ⟨a', x.2.mem ha⟩ ha
    exact ⟨y'.1, hy', ⟨a', x.2.mem ha⟩, y', rfl, rfl, hR'⟩
  · obtain ⟨x', hx', hR'⟩ := (hR hxy).2 ⟨b', y.2.mem hb⟩ hb
    exact ⟨x'.1, hx', x', ⟨b', y.2.mem hb⟩, rfl, rfl, hR'⟩

end WellFoundedPart

end Mettapedia.TypeTheory.MaterialSets.Hypersets
