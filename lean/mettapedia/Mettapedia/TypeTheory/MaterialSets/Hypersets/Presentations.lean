import Mettapedia.TypeTheory.MaterialSets.Hypersets.Finality
import Mettapedia.TypeTheory.MaterialSets.Hypersets.MembershipEvidence
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ZFSet
import Mettapedia.GSLT.Core.NonFactorization
import Mathlib.SetTheory.Cardinal.Defs

/-!
# Presentations and their pictures

An accessible pointed graph is a *presentation* of a hyperset, a process that keeps its
provenance: which edges were taken, how often, and in what shape. Its *picture* is the
decoration of its point (`picture`), and every hyperset is a picture (`picture_surjective`).

* A morphism of presentations is a bounded morphism of graphs that keeps the point (`Hom`).
  Morphisms preserve pictures (`Hom.picture_eq`). They carry occurrences onto occurrences
  (`Hom.mapOccurrence_surjective`), keeping the member each pictures
  (`Hom.picture_mapOccurrence`), and may merge them (`collapse_mapOccurrence_not_injective`).
* Two presentations have the same picture exactly when they are bisimilar
  (`picture_eq_picture_iff`), exactly when a span of morphisms joins them
  (`equiv_iff_exists_span`): the span is carried by the bisimilar pairs of nodes reachable from
  the pair of points (`span`).

Provenance lives on presentations. An *occurrence* of a member is an edge out of the point
(`Occurrence`), and membership evidence is an occurrence whose re-pointed graph is bisimilar to
the member (`AccessiblePointedGraph.MemEvidence`). Neither descends to pictures in general:

* two distinct occurrences of `twoChildren` picture the same member
  (`occurrence_picture_not_injective`);
* the observer that counts the edges out of the point (`occurrenceCount`) takes two values on
  presentations of `{∅}` (`occurrenceCount_twoChildren_ne`), so it does not factor through the
  picture (`occurrenceCount_not_factors`); the morphism `collapse` that merges the two edges of
  `twoChildren` changes the count (`occurrenceCount_not_morphismInvariant`);
* likewise the number of pieces of evidence that `∅` is a member (`emptyEvidenceCount_not_factors`).

**Descent.** An observer of presentations factors through the picture exactly when it is
invariant under bisimilarity (`factors_picture_iff`), exactly when it is invariant under
morphisms of presentations (`factors_picture_iff_morphismInvariant`). The readout on pictures is
then unique (`readout_unique`). Well-foundedness of the point is such an observer
(`wellFoundedPoint_factors`); the presence of a loop at the point is not
(`hasLoop_not_factors`: the loop and the two-node cycle both picture `Ω`).

The comparison of presentations with their pictures uses no choice.

**Labelled systems.** A labelled graph `r : α → β → α → Prop` has one decoration
(`decorateLabelled`). The members at a node are the Kuratowski pairs of a label and the
decoration of a child (`mem_decorateLabelled`). Existence and uniqueness reduce to the
unlabelled theorem on the graph whose nodes are the original nodes, the Kuratowski pairs, and
the nodes of a graph of each label (`IsLabelledDecoration.eq_decorateLabelled`). The label
graphs are chosen by `Presentation.choice`. A stream that repeats one label is the unique
solution of `x = {kpair b x}` (`repeatStream`, `repeatStream_unique`). It is the image of no
set (`repeatStream_ne_ofZFSet`), and it equals `Ω` exactly when the label does
(`repeatStream_eq_quineAtom_iff`): then `kpair Ω Ω = Ω`. Two alternating labels stay two
hypersets when the labels differ (`alternating_ne_of_ne`) and become one when they agree
(`alternating_eq_of_eq`).

P. Aczel, *Non-well-founded Sets*, CSLI Lecture Notes 14, 1988; J. J. M. M. Rutten, *Universal
coalgebra: a theory of systems*, Theoretical Computer Science 249, 2000.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

open Relation Mettapedia.GSLT.Core.NonFactorization

universe u

namespace AccessiblePointedGraph

/-! ## Pictures -/

/-- The picture of a presentation: the decoration of its point. -/
def picture (G : AccessiblePointedGraph.{u}) : HSet.{u} :=
  HSet.decorate G.edge G.point

theorem picture_eq_mk (G : AccessiblePointedGraph.{u}) : picture G = HSet.mk G :=
  (HSet.mk_eq_decorate G).symm

/-- Every hyperset is the picture of a presentation. -/
theorem picture_surjective : Function.Surjective picture.{u} := fun x =>
  let ⟨G, hG⟩ := HSet.exists_mk x
  ⟨G, (picture_eq_mk G).trans hG⟩

/-- Two presentations have the same picture exactly when they are bisimilar. -/
theorem picture_eq_picture_iff {G H : AccessiblePointedGraph.{u}} :
    picture G = picture H ↔ G ≈ H :=
  HSet.decorate_eq_decorate_iff

theorem mem_picture {G : AccessiblePointedGraph.{u}} {y : HSet.{u}} :
    y ∈ picture G ↔ ∃ c, G.edge G.point c ∧ HSet.decorate G.edge c = y :=
  HSet.mem_decorate

/-! ## Morphisms of presentations -/

/-- A morphism of presentations: a bounded morphism of the graphs that keeps the point. -/
structure Hom (G H : AccessiblePointedGraph.{u}) where
  /-- The map on nodes. -/
  toFun : G.Node → H.Node
  /-- It preserves and reflects edges. -/
  isBoundedMorphism : IsBoundedMorphism G.edge H.edge toFun
  /-- It keeps the point. -/
  map_point : toFun G.point = H.point

namespace Hom

variable {G H K : AccessiblePointedGraph.{u}}

/-- The identity morphism. -/
protected def id (G : AccessiblePointedGraph.{u}) : Hom G G :=
  ⟨id, IsBoundedMorphism.id, rfl⟩

/-- The composite of two morphisms. -/
def comp (ψ : Hom H K) (φ : Hom G H) : Hom G K :=
  ⟨ψ.toFun ∘ φ.toFun, ψ.isBoundedMorphism.comp φ.isBoundedMorphism,
    (congrArg ψ.toFun φ.map_point).trans ψ.map_point⟩

/-- Morphisms of presentations preserve pictures. -/
theorem picture_eq (φ : Hom G H) : picture H = picture G := by
  rw [picture, picture, ← φ.map_point]
  exact φ.isBoundedMorphism.decorate_apply G.point

theorem equiv (φ : Hom G H) : G ≈ H :=
  picture_eq_picture_iff.mp φ.picture_eq.symm

end Hom

/-! ## Spans of morphisms -/

section Span

variable (G H : AccessiblePointedGraph.{u})

/-- A step between pairs of nodes: an edge on each side, landing on a bisimilar pair. -/
def pairStep (p q : G.Node × H.Node) : Prop :=
  G.edge p.1 q.1 ∧ H.edge p.2 q.2 ∧ Bisimilar G.edge H.edge q.1 q.2

/-- The apex of the span of two bisimilar presentations: the pairs of nodes reachable from the
pair of points by steps between bisimilar pairs. -/
def span : AccessiblePointedGraph.{u} :=
  generated (pairStep G H) (G.point, H.point)

variable {G H}

theorem bisimilar_of_reachable (h : G ≈ H) {p : G.Node × H.Node}
    (hp : ReflTransGen (pairStep G H) (G.point, H.point) p) :
    Bisimilar G.edge H.edge p.1 p.2 := by
  induction hp with
  | refl => exact h
  | tail _ step _ => exact step.2.2

/-- The first leg of the span. -/
def spanFst (h : G ≈ H) : Hom (span G H) G where
  toFun p := p.1.1
  isBoundedMorphism :=
    ⟨fun _ _ step => step.1, fun p g' edge => by
      obtain ⟨h', hh', bis⟩ := (bisimilar_of_reachable h p.2).exists_child_left edge
      exact ⟨⟨(g', h'), p.2.tail ⟨edge, hh', bis⟩⟩, ⟨edge, hh', bis⟩, rfl⟩⟩
  map_point := rfl

/-- The second leg of the span. -/
def spanSnd (h : G ≈ H) : Hom (span G H) H where
  toFun p := p.1.2
  isBoundedMorphism :=
    ⟨fun _ _ step => step.2.1, fun p h' edge => by
      obtain ⟨g', hg', bis⟩ := (bisimilar_of_reachable h p.2).exists_child_right edge
      exact ⟨⟨(g', h'), p.2.tail ⟨hg', edge, bis⟩⟩, ⟨hg', edge, bis⟩, rfl⟩⟩
  map_point := rfl

/-- Two presentations are bisimilar exactly when a span of morphisms joins them. -/
theorem equiv_iff_exists_span :
    G ≈ H ↔ ∃ K : AccessiblePointedGraph.{u}, Nonempty (Hom K G) ∧ Nonempty (Hom K H) :=
  ⟨fun h => ⟨span G H, ⟨spanFst h⟩, ⟨spanSnd h⟩⟩,
    fun ⟨_, ⟨φ⟩, ⟨ψ⟩⟩ => Setoid.trans (Setoid.symm φ.equiv) ψ.equiv⟩

end Span

/-! ## Observers of presentations -/

section Observer

variable {Z : Sort*}

/-- An observer of presentations is invariant under bisimilarity. -/
def BisimulationInvariant (O : AccessiblePointedGraph.{u} → Z) : Prop :=
  ∀ G H, G ≈ H → O G = O H

/-- An observer of presentations is invariant under morphisms of presentations. -/
def MorphismInvariant (O : AccessiblePointedGraph.{u} → Z) : Prop :=
  ∀ G H, Hom G H → O G = O H

/-- The readout on pictures of a bisimulation-invariant observer. -/
def readout (O : AccessiblePointedGraph.{u} → Z) (inv : BisimulationInvariant O) :
    HSet.{u} → Z :=
  Quotient.lift O inv

theorem readout_picture (O : AccessiblePointedGraph.{u} → Z) (inv : BisimulationInvariant O)
    (G : AccessiblePointedGraph.{u}) : readout O inv (picture G) = O G := by
  rw [picture_eq_mk]
  rfl

/-- **Descent.** An observer of presentations factors through the picture exactly when it is
invariant under bisimilarity. -/
theorem factors_picture_iff (O : AccessiblePointedGraph.{u} → Z) :
    Factors picture O ↔ BisimulationInvariant O :=
  ⟨fun h G H e => h.constantOnFibers G H (picture_eq_picture_iff.mpr e),
    fun inv => ⟨readout O inv, readout_picture O inv⟩⟩

/-- Factoring through the picture is factoring through the quotient by bisimilarity. -/
theorem factors_picture_iff_factors_mk (O : AccessiblePointedGraph.{u} → Z) :
    Factors picture O ↔ Factors HSet.mk O := by
  have same : picture = HSet.mk.{u} := funext picture_eq_mk
  rw [same]

/-- The readout is unique: pictures are all hypersets. -/
theorem readout_unique (O : AccessiblePointedGraph.{u} → Z) (inv : BisimulationInvariant O)
    (f : HSet.{u} → Z) (factors : ∀ G, f (picture G) = O G) : f = readout O inv :=
  funext fun x =>
    let ⟨G, hG⟩ := picture_surjective x
    hG ▸ (factors G).trans (readout_picture O inv G).symm

theorem bisimulationInvariant_iff_morphismInvariant (O : AccessiblePointedGraph.{u} → Z) :
    BisimulationInvariant O ↔ MorphismInvariant O :=
  ⟨fun inv G H φ => inv G H φ.equiv, fun inv G H e =>
    let ⟨_, ⟨φ⟩, ⟨ψ⟩⟩ := equiv_iff_exists_span.mp e
    (inv _ G φ).symm.trans (inv _ H ψ)⟩

/-- An observer of presentations factors through the picture exactly when it is invariant
under morphisms of presentations. -/
theorem factors_picture_iff_morphismInvariant (O : AccessiblePointedGraph.{u} → Z) :
    Factors picture O ↔ MorphismInvariant O :=
  (factors_picture_iff O).trans (bisimulationInvariant_iff_morphismInvariant O)

end Observer

/-! ## Occurrences -/

/-- An occurrence of a member in a presentation: an edge out of the point. -/
def Occurrence (G : AccessiblePointedGraph.{u}) : Type u :=
  {c : G.Node // G.edge G.point c}

/-- The member an occurrence pictures. -/
def Occurrence.picture {G : AccessiblePointedGraph.{u}} (o : Occurrence G) : HSet.{u} :=
  HSet.decorate G.edge o.1

theorem mem_picture_iff_occurrence {G : AccessiblePointedGraph.{u}} {y : HSet.{u}} :
    y ∈ picture G ↔ ∃ o : Occurrence G, o.picture = y :=
  mem_picture.trans ⟨fun ⟨c, hc, e⟩ => ⟨⟨c, hc⟩, e⟩, fun ⟨o, e⟩ => ⟨o.1, o.2, e⟩⟩

namespace Hom

variable {G H : AccessiblePointedGraph.{u}}

/-- A morphism of presentations carries occurrences to occurrences. -/
def mapOccurrence (φ : Hom G H) (o : Occurrence G) : Occurrence H :=
  ⟨φ.toFun o.1, by
    rw [← φ.map_point]
    exact φ.isBoundedMorphism.map o.2⟩

/-- A morphism keeps the member an occurrence pictures. -/
theorem picture_mapOccurrence (φ : Hom G H) (o : Occurrence G) :
    (φ.mapOccurrence o).picture = o.picture :=
  φ.isBoundedMorphism.decorate_apply o.1

/-- Every occurrence in the target comes from an occurrence in the source. -/
theorem mapOccurrence_surjective (φ : Hom G H) : Function.Surjective φ.mapOccurrence := by
  intro o
  have edge : H.edge (φ.toFun G.point) o.1 := by
    rw [φ.map_point]
    exact o.2
  obtain ⟨c, hc, e⟩ := φ.isBoundedMorphism.lift edge
  exact ⟨⟨c, hc⟩, Subtype.ext e⟩

end Hom

/-- Membership evidence is an occurrence whose re-pointed graph presents the member. -/
def memEvidenceEquiv (G H : AccessiblePointedGraph.{u}) :
    MemEvidence G H ≃ {o : Occurrence H // G ≈ H.repoint o.1} where
  toFun e := ⟨⟨e.1, e.2.1⟩, e.2.2⟩
  invFun o := ⟨o.1.1, o.1.2, o.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The number of edges out of the point. -/
def occurrenceCount (G : AccessiblePointedGraph.{u}) : Cardinal.{u} :=
  Cardinal.mk (Occurrence G)

/-- The occurrence of `twoChildren` along the edge tagged `b`. -/
def twoChildrenOccurrence (b : Bool) : Occurrence twoChildren.{u} :=
  ⟨(twoChildrenWitness b).1, (twoChildrenWitness b).2.1⟩

theorem twoChildrenOccurrence_ne :
    twoChildrenOccurrence.{u} true ≠ twoChildrenOccurrence false := fun h =>
  twoChildrenWitness_ne (Subtype.ext (congrArg (fun o : Occurrence twoChildren.{u} => o.1) h))

theorem twoChildrenOccurrence_picture (b : Bool) :
    (twoChildrenOccurrence.{u} b).picture = ∅ :=
  calc HSet.decorate twoChildren.edge (twoChildrenWitness b).1
      = HSet.mk (twoChildren.repoint (twoChildrenWitness b).1) := (HSet.mk_repoint _ _).symm
    _ = HSet.mk empty := HSet.sound (Setoid.symm (twoChildrenWitness b).2.2)
    _ = ∅ := HSet.mk_empty

/-- Occurrence identity does not descend: two distinct occurrences picture the same member. -/
theorem occurrence_picture_not_injective :
    ¬ Function.Injective (Occurrence.picture (G := twoChildren.{u})) := fun h =>
  twoChildrenOccurrence_ne (h ((twoChildrenOccurrence_picture true).trans
    (twoChildrenOccurrence_picture false).symm))

instance (G : AccessiblePointedGraph.{u}) : Subsingleton (Occurrence (oneChild G)) :=
  ⟨fun a b => Subtype.ext <| by
    obtain ⟨_, ha⟩ := supEdge_none_iff.mp a.2
    obtain ⟨_, hb⟩ := supEdge_none_iff.mp b.2
    exact ha.trans hb.symm⟩

theorem picture_oneChild_empty : picture (oneChild empty.{u}) = {∅} :=
  (picture_eq_mk _).trans <| HSet.ext fun y => by
    rw [HSet.mem_mk, HSet.mem_singleton]
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨_, rfl⟩ := supEdge_none_iff.mp hc
      exact (HSet.sound (repoint_sup_equiv (g := fun _ : PUnit.{u + 1} => empty) _)).trans
        HSet.mk_empty
    · rintro rfl
      exact ⟨_, SupEdge.point (g := fun _ : PUnit.{u + 1} => empty) PUnit.unit,
        (HSet.sound (repoint_sup_equiv (g := fun _ : PUnit.{u + 1} => empty) _)).trans
          HSet.mk_empty⟩

theorem picture_twoChildren : picture twoChildren.{u} = {∅} :=
  (picture_eq_mk _).trans mk_twoChildren

/-- `twoChildren` and `oneChild empty` both present `{∅}`, with two edges and with one. -/
theorem occurrenceCount_twoChildren_ne :
    occurrenceCount twoChildren.{u} ≠ occurrenceCount (oneChild empty.{u}) := fun h => by
  obtain ⟨e⟩ := Cardinal.eq.mp h
  exact twoChildrenOccurrence_ne (e.injective (Subsingleton.elim _ _))

/-- The edge-counting observer takes two values on one picture. -/
def occurrenceCountFiber : NonTrivialFiber picture occurrenceCount.{u} where
  left := twoChildren
  right := oneChild empty
  sameShadow := picture_twoChildren.trans picture_oneChild_empty.symm
  differentValue := occurrenceCount_twoChildren_ne

/-- Counting edges does not descend to pictures. -/
theorem occurrenceCount_not_factors : ¬ Factors picture occurrenceCount.{u} :=
  occurrenceCountFiber.not_factors

/-- The number of pieces of evidence that `∅` is a member. -/
def emptyEvidenceCount (G : AccessiblePointedGraph.{u}) : Cardinal.{u} :=
  Cardinal.mk (MemEvidence empty G)

theorem emptyEvidenceCount_twoChildren_ne :
    emptyEvidenceCount twoChildren.{u} ≠ emptyEvidenceCount (oneChild empty.{u}) := fun h => by
  obtain ⟨e⟩ := Cardinal.eq.mp h
  exact twoChildrenWitness_ne (e.injective (Subsingleton.elim _ _))

/-- Membership evidence does not descend to pictures: `twoChildren` has two pieces of evidence
that `∅` is a member, `oneChild empty` one, and both picture `{∅}`. -/
theorem emptyEvidenceCount_not_factors : ¬ Factors picture emptyEvidenceCount.{u} :=
  NonTrivialFiber.not_factors
    { left := twoChildren
      right := oneChild empty
      sameShadow := picture_twoChildren.trans picture_oneChild_empty.symm
      differentValue := emptyEvidenceCount_twoChildren_ne }

/-- Reindexing a family along a surjection is a morphism of presentations. -/
def supReindex {ι κ : Type u} (g : ι → AccessiblePointedGraph.{u}) (f : κ → ι)
    (hf : Function.Surjective f) : Hom (sup (g ∘ f)) (sup g) where
  toFun
    | none => none
    | some ⟨k, n⟩ => some ⟨f k, n⟩
  isBoundedMorphism := by
    refine ⟨?_, ?_⟩
    · rintro _ _ (⟨k⟩ | ⟨k, h⟩)
      · exact SupEdge.point (f k)
      · exact SupEdge.edge (f k) h
    · rintro (_ | ⟨k, n⟩) y h
      · obtain ⟨i, rfl⟩ := supEdge_none_iff.mp h
        obtain ⟨k, rfl⟩ := hf i
        exact ⟨_, SupEdge.point k, rfl⟩
      · obtain ⟨m, hm, rfl⟩ := supEdge_some_iff.mp h
        exact ⟨_, SupEdge.edge k hm, rfl⟩
  map_point := rfl

/-- The morphism that merges the two edges of `twoChildren` into the one edge of
`oneChild empty`. -/
def collapse : Hom twoChildren.{u} (oneChild empty.{u}) :=
  supReindex (fun _ : PUnit.{u + 1} => empty) (fun _ : ULift.{u} Bool => PUnit.unit)
    fun _ => ⟨⟨true⟩, rfl⟩

/-- Counting edges is not invariant under morphisms of presentations. -/
theorem occurrenceCount_not_morphismInvariant : ¬ MorphismInvariant occurrenceCount.{u} :=
  fun inv => occurrenceCount_twoChildren_ne (inv _ _ collapse)

/-- Morphisms may merge occurrences: `collapse` identifies the two edges of `twoChildren`. -/
theorem collapse_mapOccurrence_not_injective :
    ¬ Function.Injective (collapse.{u}.mapOccurrence) := fun h =>
  twoChildrenOccurrence_ne (h (Subsingleton.elim _ _))

/-! ## Examples of descent -/

/-- The point of a presentation is well-founded: every path of edges from it is finite. -/
def WellFoundedPoint (G : AccessiblePointedGraph.{u}) : Prop :=
  Acc (flip G.edge) G.point

/-- Well-foundedness of the point descends to pictures: it is well-foundedness of the
picture. -/
theorem wellFoundedPoint_factors : Factors picture WellFoundedPoint.{u} :=
  ⟨HSet.WF, fun _ => propext HSet.wf_decorate_iff⟩

/-- The point has an edge to itself. -/
def HasLoop (G : AccessiblePointedGraph.{u}) : Prop :=
  G.edge G.point G.point

/-- The presence of a loop at the point does not descend to pictures: the loop and the two-node
cycle both picture `Ω`. -/
theorem hasLoop_not_factors : ¬ Factors picture HasLoop.{u} :=
  have samePicture : picture HSet.loop.{u} = picture HSet.twoCycle :=
    ((picture_eq_mk _).trans HSet.mk_loop).trans ((picture_eq_mk _).trans HSet.mk_twoCycle).symm
  have noLoop : ¬ HasLoop HSet.twoCycle.{u} := fun h => absurd (show true = !true from h) (by decide)
  (NonTrivialFiber.ofProp (invariant := HasLoop) samePicture trivial noLoop).not_factors

end AccessiblePointedGraph

/-! ## Labelled graphs -/

namespace HSet

/-- The nodes of the unlabelled graph of a labelled system: the original nodes, the Kuratowski
pair, its two members, and the nodes of a graph of each label. -/
inductive LabelCarrier {α β : Type u} (N : β → Type u) : Type u where
  | atom : α → LabelCarrier N
  | paired : β → α → LabelCarrier N
  | single : β → LabelCarrier N
  | couple : β → α → LabelCarrier N
  | label : (b : β) → N b → LabelCarrier N

section Labelled

variable {α β : Type u}

/-- A chosen graph of each label. -/
noncomputable def labelGraph (ℓ : β → HSet.{u}) (b : β) : AccessiblePointedGraph.{u} :=
  Presentation.choice.graph (ℓ b)

/-- The carrier of the unlabelled graph built from a labelled graph and its labels. -/
abbrev labelNodes (ℓ : β → HSet.{u}) : Type u :=
  LabelCarrier (α := α) (fun b => (labelGraph ℓ b).Node)

/-- The unlabelled edges: each labelled step becomes the membership graph of a Kuratowski pair. -/
noncomputable def labelEdge (r : α → β → α → Prop) (ℓ : β → HSet.{u}) :
    labelNodes (α := α) ℓ → labelNodes (α := α) ℓ → Prop
  | .atom a, .paired b a' => r a b a'
  | .paired b _, .single b' => b = b'
  | .paired b a', .couple b' a'' => b = b' ∧ a' = a''
  | .single b, .label b' n => ∃ h : b = b', h ▸ (labelGraph ℓ b).point = n
  | .couple b _, .label b' n => ∃ h : b = b', h ▸ (labelGraph ℓ b).point = n
  | .couple _ a', .atom a'' => a' = a''
  | .label b n, .label b' m => ∃ h : b = b', (labelGraph ℓ b).edge n (h ▸ m)
  | _, _ => False

/-- The decoration of a labelled graph: the picture of its unlabelled pair graph. -/
noncomputable def decorateLabelled (r : α → β → α → Prop) (ℓ : β → HSet.{u}) (a : α) :
    HSet.{u} :=
  decorate (labelEdge r ℓ) (LabelCarrier.atom a)

/-- A node of a label's graph pictures the same hyperset in the pair graph. -/
theorem decorate_label (r : α → β → α → Prop) (ℓ : β → HSet.{u}) (b : β)
    (n : (labelGraph ℓ b).Node) :
    decorate (labelEdge r ℓ) (LabelCarrier.label b n) = decorate (labelGraph ℓ b).edge n := by
  exact (decorate_eq_of_bisimilar (bisimilar_apply
    (r := (labelGraph ℓ b).edge)
    (s := labelEdge r ℓ)
    (f := fun m : (labelGraph ℓ b).Node => LabelCarrier.label b m)
    (fun _n m hedge => ⟨rfl, hedge⟩)
    (fun _n t ht => by
      cases t with
      | label b' m =>
        rcases ht with ⟨rfl, hedge⟩
        exact ⟨m, hedge, rfl⟩
      | atom _ => cases ht
      | paired _ _ => cases ht
      | single _ => cases ht
      | couple _ _ => cases ht)
    n)).symm

/-- The singleton node of a label pictures the singleton of the label. -/
theorem decorate_single (r : α → β → α → Prop) (ℓ : β → HSet.{u}) (b : β) :
    decorate (labelEdge r ℓ) (LabelCarrier.single b) = {ℓ b} := by
  ext y
  rw [mem_decorate, mem_singleton]
  constructor
  · rintro ⟨t, ht, rfl⟩
    cases t with
    | label b' n =>
      rcases ht with ⟨rfl, hn⟩
      rw [decorate_label, ← hn, ← mk_eq_decorate, labelGraph, Presentation.choice.mk_graph]
    | atom _ => cases ht
    | paired _ _ => cases ht
    | single _ => cases ht
    | couple _ _ => cases ht
  · intro rfl
    refine ⟨LabelCarrier.label b (labelGraph ℓ b).point, ⟨rfl, rfl⟩, ?_⟩
    rw [decorate_label, ← mk_eq_decorate, labelGraph, Presentation.choice.mk_graph]

/-- The unordered-pair node pictures the label together with the decoration of the target. -/
theorem decorate_couple (r : α → β → α → Prop) (ℓ : β → HSet.{u}) (b : β) (a' : α) :
    decorate (labelEdge r ℓ) (LabelCarrier.couple b a') =
      {ℓ b, decorate (labelEdge r ℓ) (LabelCarrier.atom a')} := by
  ext y
  rw [mem_decorate, mem_pair]
  constructor
  · rintro ⟨t, ht, rfl⟩
    cases t with
    | label b' n =>
      rcases ht with ⟨rfl, hn⟩
      exact Or.inl (by rw [decorate_label, ← hn, ← mk_eq_decorate, labelGraph, Presentation.choice.mk_graph])
    | atom a'' =>
      cases ht
      exact Or.inr rfl
    | paired _ _ => cases ht
    | single _ => cases ht
    | couple _ _ => cases ht
  · rintro (rfl | rfl)
    · refine ⟨LabelCarrier.label b (labelGraph ℓ b).point, ⟨rfl, rfl⟩, ?_⟩
      rw [decorate_label, ← mk_eq_decorate, labelGraph, Presentation.choice.mk_graph]
    · exact ⟨LabelCarrier.atom a', rfl, rfl⟩

/-- The pair node pictures the Kuratowski pair of the label and the target. -/
theorem decorate_paired (r : α → β → α → Prop) (ℓ : β → HSet.{u}) (b : β) (a' : α) :
    decorate (labelEdge r ℓ) (LabelCarrier.paired b a') =
      kpair (ℓ b) (decorateLabelled r ℓ a') := by
  ext y
  rw [mem_decorate, mem_kpair, decorateLabelled]
  constructor
  · rintro ⟨t, ht, rfl⟩
    cases t with
    | single b' =>
      cases ht
      exact Or.inl (decorate_single r ℓ b)
    | couple b' a'' =>
      rcases ht with ⟨rfl, rfl⟩
      exact Or.inr (decorate_couple r ℓ b a')
    | atom _ => cases ht
    | paired _ _ => cases ht
    | label _ _ => cases ht
  · rintro (rfl | rfl)
    · exact ⟨LabelCarrier.single b, rfl, decorate_single r ℓ b⟩
    · exact ⟨LabelCarrier.couple b a', ⟨rfl, rfl⟩, decorate_couple r ℓ b a'⟩

/-- The members at a node are the pairs of a label and the decoration of a child. -/
theorem mem_decorateLabelled {r : α → β → α → Prop} {ℓ : β → HSet.{u}} {a : α} {y : HSet.{u}} :
    y ∈ decorateLabelled r ℓ a ↔
      ∃ b a', r a b a' ∧ y = kpair (ℓ b) (decorateLabelled r ℓ a') := by
  rw [decorateLabelled, mem_decorate]
  constructor
  · rintro ⟨t, ht, rfl⟩
    cases t with
    | paired b a' =>
      exact ⟨b, a', ht, decorate_paired r ℓ b a'⟩
    | atom _ => cases ht
    | single _ => cases ht
    | couple _ _ => cases ht
    | label _ _ => cases ht
  · rintro ⟨b, a', hr, rfl⟩
    exact ⟨LabelCarrier.paired b a', hr, decorate_paired r ℓ b a'⟩

/-- A decoration of a labelled graph: the members at `a` are the pairs along the edges from `a`. -/
def IsLabelledDecoration (r : α → β → α → Prop) (ℓ : β → HSet.{u}) (d : α → HSet.{u}) : Prop :=
  ∀ a y, y ∈ d a ↔ ∃ b a', r a b a' ∧ y = kpair (ℓ b) (d a')

/-- The picture of the pair graph decorates the labelled graph. -/
theorem isLabelledDecoration_decorate (r : α → β → α → Prop) (ℓ : β → HSet.{u}) :
    IsLabelledDecoration r ℓ (decorateLabelled r ℓ) :=
  fun _ _ => mem_decorateLabelled

/-- A labelled decoration, extended by the pairs and by the graphs of the labels. -/
noncomputable def extendLabel (_r : α → β → α → Prop) (ℓ : β → HSet.{u}) (d : α → HSet.{u}) :
    labelNodes (α := α) ℓ → HSet.{u}
  | .atom a => d a
  | .paired b a' => kpair (ℓ b) (d a')
  | .single b => {ℓ b}
  | .couple b a' => {ℓ b, d a'}
  | .label b n => decorate (labelGraph ℓ b).edge n

/-- The extension is a decoration of the unlabelled pair graph. -/
theorem extendLabel_isDecoration {r : α → β → α → Prop} {ℓ : β → HSet.{u}} {d : α → HSet.{u}}
    (hd : IsLabelledDecoration r ℓ d) :
    IsDecoration (labelEdge r ℓ) (extendLabel r ℓ d) := by
  intro n y
  cases n with
  | atom a =>
    rw [extendLabel, hd a y]
    constructor
    · rintro ⟨b, a', hr, rfl⟩
      exact ⟨LabelCarrier.paired b a', hr, rfl⟩
    · rintro ⟨t, ht, he⟩
      cases t with
      | paired b a' => exact ⟨b, a', ht, he.symm⟩
      | atom _ => cases ht
      | single _ => cases ht
      | couple _ _ => cases ht
      | label _ _ => cases ht
  | paired b a' =>
    rw [extendLabel, mem_kpair]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨LabelCarrier.single b, rfl, rfl⟩
      · exact ⟨LabelCarrier.couple b a', ⟨rfl, rfl⟩, rfl⟩
    · rintro ⟨t, ht, he⟩
      cases t with
      | single b' =>
        cases ht
        exact Or.inl he.symm
      | couple b' a'' =>
        rcases ht with ⟨rfl, rfl⟩
        exact Or.inr he.symm
      | atom _ => cases ht
      | paired _ _ => cases ht
      | label _ _ => cases ht
  | single b =>
    rw [extendLabel, mem_singleton]
    constructor
    · rintro rfl
      refine ⟨LabelCarrier.label b (labelGraph ℓ b).point, ⟨rfl, rfl⟩, ?_⟩
      rw [extendLabel, ← mk_eq_decorate, labelGraph, Presentation.choice.mk_graph]
    · rintro ⟨t, ht, he⟩
      cases t with
      | label b' n =>
        rcases ht with ⟨rfl, hn⟩
        rw [← he, extendLabel, ← hn, ← mk_eq_decorate, labelGraph, Presentation.choice.mk_graph]
      | atom _ => cases ht
      | paired _ _ => cases ht
      | single _ => cases ht
      | couple _ _ => cases ht
  | couple b a' =>
    rw [extendLabel, mem_pair]
    constructor
    · rintro (rfl | rfl)
      · refine ⟨LabelCarrier.label b (labelGraph ℓ b).point, ⟨rfl, rfl⟩, ?_⟩
        rw [extendLabel, ← mk_eq_decorate, labelGraph, Presentation.choice.mk_graph]
      · exact ⟨LabelCarrier.atom a', rfl, rfl⟩
    · rintro ⟨t, ht, he⟩
      cases t with
      | label b' n =>
        rcases ht with ⟨rfl, hn⟩
        exact Or.inl (by rw [← he, extendLabel, ← hn, ← mk_eq_decorate, labelGraph, Presentation.choice.mk_graph])
      | atom a'' =>
        cases ht
        exact Or.inr he.symm
      | paired _ _ => cases ht
      | single _ => cases ht
      | couple _ _ => cases ht
  | label b n =>
    rw [extendLabel, mem_decorate]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨LabelCarrier.label b m, ⟨rfl, hm⟩, rfl⟩
    · rintro ⟨t, ht, he⟩
      cases t with
      | label b' m =>
        rcases ht with ⟨rfl, hm⟩
        exact ⟨m, hm, he⟩
      | atom _ => cases ht
      | paired _ _ => cases ht
      | single _ => cases ht
      | couple _ _ => cases ht

/-- A labelled graph has only one decoration. -/
theorem IsLabelledDecoration.eq_decorateLabelled {r : α → β → α → Prop} {ℓ : β → HSet.{u}}
    {d : α → HSet.{u}} (hd : IsLabelledDecoration r ℓ d) : d = decorateLabelled r ℓ := by
  funext a
  exact congrFun (extendLabel_isDecoration hd).eq_decorate (LabelCarrier.atom a)

/-- Every labelled graph has exactly one decoration. -/
theorem existsUnique_isLabelledDecoration (r : α → β → α → Prop) (ℓ : β → HSet.{u}) :
    ∃! d, IsLabelledDecoration r ℓ d :=
  ⟨decorateLabelled r ℓ, isLabelledDecoration_decorate r ℓ, fun _ hd => hd.eq_decorateLabelled⟩

end Labelled

/-- A membership cycle of length three is not well-founded. -/
theorem not_wf_of_cycle {x y z : HSet.{u}} (hy : y ∈ x) (hz : z ∈ y) (hx : x ∈ z) : ¬ x.WF := by
  intro hxwf
  suffices ∀ w, w.WF → w = x ∨ w = y ∨ w = z → False from this x hxwf (Or.inl rfl)
  intro w hw
  induction hw with
  | intro w _ ih =>
    rintro (rfl | rfl | rfl)
    · exact ih y hy (Or.inr (Or.inl rfl))
    · exact ih z hz (Or.inr (Or.inr rfl))
    · exact ih x hx (Or.inl rfl)

/-- The one-node labelled loop: every step carries the same label and returns to the node. -/
def repeatRel (_a _b _a' : PUnit.{u + 1}) : Prop :=
  True

/-- The stream that repeats the label `b`: the unique solution of `x = {kpair b x}`. -/
noncomputable def repeatStream (b : HSet.{u}) : HSet.{u} :=
  decorateLabelled repeatRel (fun _ : PUnit.{u + 1} => b) PUnit.unit

/-- The repeating stream satisfies `x = {kpair b x}`. -/
theorem repeatStream_spec (b : HSet.{u}) : repeatStream b = {kpair b (repeatStream b)} := by
  ext y
  rw [repeatStream, mem_decorateLabelled, mem_singleton]
  constructor
  · rintro ⟨_, a', _, rfl⟩
    cases a'
    rfl
  · rintro rfl
    exact ⟨PUnit.unit, PUnit.unit, trivial, rfl⟩

/-- `x = {kpair b x}` has only the repeating stream as a solution. -/
theorem repeatStream_unique {b x : HSet.{u}} (h : x = {kpair b x}) : x = repeatStream b := by
  have hd : IsLabelledDecoration repeatRel (fun _ : PUnit.{u + 1} => b) (fun _ => x) := by
    intro _ y
    constructor
    · intro hy
      rw [h, mem_singleton] at hy
      cases hy
      exact ⟨PUnit.unit, PUnit.unit, trivial, rfl⟩
    · rintro ⟨_, _, _, rfl⟩
      have hy : kpair b x ∈ {kpair b x} := mem_singleton_self _
      rwa [← h] at hy
  exact congrFun hd.eq_decorateLabelled PUnit.unit

/-- The repeating stream is not well-founded. -/
theorem repeatStream_not_wf (b : HSet.{u}) : ¬ (repeatStream b).WF :=
  not_wf_of_cycle
    ((repeatStream_spec b).symm ▸ mem_singleton_self (kpair b (repeatStream b)))
    (mem_kpair.mpr (Or.inr rfl))
    (mem_pair.mpr (Or.inr rfl))

/-- The repeating stream is the image of no set. -/
theorem repeatStream_ne_ofZFSet (b : HSet.{u}) (a : ZFSet.{u}) : repeatStream b ≠ ofZFSet a :=
  fun h => repeatStream_not_wf b (h ▸ wf_ofZFSet a)

/-- Pairing `Ω` with itself is `Ω`, because `kpair Ω Ω = {{Ω}}` and `Ω = {Ω}`. -/
theorem kpair_quineAtom_self : kpair quineAtom.{u} quineAtom = quineAtom := by
  rw [kpair_self]
  exact (congrArg (fun z : HSet.{u} => ({z} : HSet.{u})) quineAtom_eq_singleton.symm).trans
    quineAtom_eq_singleton.symm

/-- The repeating stream is `Ω` exactly when the label is `Ω`. -/
theorem repeatStream_eq_quineAtom_iff (b : HSet.{u}) : repeatStream b = quineAtom ↔ b = quineAtom := by
  constructor
  · intro h
    have hmem : kpair b (repeatStream b) ∈ repeatStream b := by
      have hy : kpair b (repeatStream b) ∈ {kpair b (repeatStream b)} := mem_singleton_self _
      rwa [← repeatStream_spec] at hy
    rw [h] at hmem
    have hk : kpair b quineAtom = quineAtom := mem_quineAtom.mp hmem
    have hsing : ({b} : HSet.{u}) = quineAtom := by
      have : {b} ∈ kpair b quineAtom := mem_kpair.mpr (Or.inl rfl)
      rw [hk] at this
      exact mem_quineAtom.mp this
    exact singleton_inj.mp (hsing.trans quineAtom_eq_singleton)
  · intro hb
    subst hb
    exact (repeatStream_unique (quineAtom_eq_singleton.trans
      (congrArg (fun z : HSet.{u} => ({z} : HSet.{u})) kpair_quineAtom_self.symm))).symm

/-- One step of the alternating stream: `true` carries the first label to `false`, and back. -/
def alternateRel (a lab a' : ULift.{u} Bool) : Prop :=
  (a.down = true ∧ lab.down = true ∧ a'.down = false) ∨
  (a.down = false ∧ lab.down = false ∧ a'.down = true)

/-- The two nodes of a stream whose labels alternate. -/
noncomputable def alternating (b c : HSet.{u}) : ULift.{u} Bool → HSet.{u} :=
  decorateLabelled alternateRel (fun lab => if lab.down then b else c)

/-- The first node is the pair of the first label with the second node. -/
theorem alternating_left (b c : HSet.{u}) :
    alternating b c ⟨true⟩ = {kpair b (alternating b c ⟨false⟩)} := by
  ext y
  rw [alternating, mem_decorateLabelled, mem_singleton]
  constructor
  · rintro ⟨lab, a', hr, rfl⟩
    rcases hr with ⟨_, hlab, ha'⟩ | ⟨ha, _, _⟩
    · cases lab with
      | up dl =>
        cases dl with
        | false => cases hlab
        | true =>
          cases a' with
          | up da =>
            cases da with
            | false => rfl
            | true => cases ha'
    · cases ha
  · rintro rfl
    exact ⟨⟨true⟩, ⟨false⟩, Or.inl ⟨rfl, rfl, rfl⟩, rfl⟩

/-- The second node is the pair of the second label with the first node. -/
theorem alternating_right (b c : HSet.{u}) :
    alternating b c ⟨false⟩ = {kpair c (alternating b c ⟨true⟩)} := by
  ext y
  rw [alternating, mem_decorateLabelled, mem_singleton]
  constructor
  · rintro ⟨lab, a', hr, rfl⟩
    rcases hr with ⟨ha, _, _⟩ | ⟨_, hlab, ha'⟩
    · cases ha
    · cases lab with
      | up dl =>
        cases dl with
        | true => cases hlab
        | false =>
          cases a' with
          | up da =>
            cases da with
            | true => rfl
            | false => cases ha'
  · rintro rfl
    exact ⟨⟨false⟩, ⟨true⟩, Or.inr ⟨rfl, rfl, rfl⟩, rfl⟩

/-- Distinct labels give two hypersets. -/
theorem alternating_ne_of_ne {b c : HSet.{u}} (h : b ≠ c) :
    alternating b c ⟨true⟩ ≠ alternating b c ⟨false⟩ := by
  intro same
  have hsing : ({kpair b (alternating b c ⟨false⟩)} : HSet.{u}) =
      {kpair c (alternating b c ⟨true⟩)} := by
    rw [← alternating_left, ← alternating_right]
    exact same
  exact h (kpair_inj.mp (singleton_inj.mp hsing)).1

/-- Equal labels are one hyperset: the cycle length is forgotten. -/
theorem alternating_eq_of_eq (b : HSet.{u}) :
    alternating b b ⟨true⟩ = alternating b b ⟨false⟩ := by
  have hmem : ∀ y, y ∈ repeatStream b ↔ y = kpair b (repeatStream b) := by
    intro y
    constructor
    · intro hy
      rw [repeatStream_spec, mem_singleton] at hy
      exact hy
    · intro hy
      rw [repeatStream_spec, hy]
      exact mem_singleton_self _
  have hd : IsLabelledDecoration alternateRel (fun lab => if lab.down then b else b)
      (fun _ : ULift.{u} Bool => repeatStream b) := by
    intro a y
    constructor
    · intro hy
      cases (hmem y).mp hy
      cases a with
      | up d =>
        cases d with
        | false => exact ⟨⟨false⟩, ⟨true⟩, Or.inr ⟨rfl, rfl, rfl⟩, rfl⟩
        | true => exact ⟨⟨true⟩, ⟨false⟩, Or.inl ⟨rfl, rfl, rfl⟩, rfl⟩
    · rintro ⟨lab, _, _, rfl⟩
      apply (hmem _).mpr
      cases lab with
      | up d =>
        cases d <;> rfl
  have h := hd.eq_decorateLabelled
  exact (congrFun h.symm ⟨true⟩).trans (congrFun h.symm ⟨false⟩).symm

end HSet

end Mettapedia.TypeTheory.MaterialSets.Hypersets
