import Mettapedia.TypeTheory.MaterialSets.Hypersets.Finality
import Mettapedia.TypeTheory.MaterialSets.Hypersets.MembershipEvidence
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

No choice is used.

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

end Mettapedia.TypeTheory.MaterialSets.Hypersets
