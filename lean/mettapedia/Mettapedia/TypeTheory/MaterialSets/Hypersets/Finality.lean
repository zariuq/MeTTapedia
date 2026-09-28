import Mettapedia.TypeTheory.MaterialSets.Hypersets.AntiFoundation
import Mathlib.Data.Set.Operations

/-!
# The hypersets form the final graph

A graph `r` on `α` is a coalgebra of the powerset functor: the node `a` has the set of its
children `{a' | r a a'}`. A morphism of such coalgebras is a *bounded morphism*: a map `f` that
preserves edges and reflects them, in the sense that every edge out of an image `f a` is the
image of an edge out of `a`. Equivalently, the children of `f a` are exactly the images of the
children of `a` (`isBoundedMorphism_iff_image_eq`), and equivalently again, the graph of `f` is
a bisimulation (`isBoundedMorphism_iff_isBisimulation`).

The membership graph of hypersets, with an edge from each hyperset to each of its members, is
final among graphs with nodes in `Type u`:

* the decoration of a graph is a bounded morphism into the membership graph
  (`HSet.isBoundedMorphism_decorate`), and it is the only one
  (`IsBoundedMorphism.eq_decorate`, `HSet.existsUnique_boundedMorphism`); a bounded morphism
  into the membership graph is the same thing as a decoration
  (`HSet.isBoundedMorphism_iff_isDecoration`);
* decoration commutes with every bounded morphism, `decorate s ∘ f = decorate r`
  (`IsBoundedMorphism.decorate_comp`);
* the only bounded endomorphism of the membership graph is the identity
  (`HSet.isBoundedMorphism_self_iff`);
* bisimilarity is the kernel of decoration (`HSet.bisimilar_iff_decorate_eq`,
  `HSet.bisimilar_eq_kernel`): every bisimulation lies in the kernel
  (`IsBisimulation.decorate_eq`), and the kernel is a bisimulation
  (`HSet.isBisimulation_kernel`). More generally, the pullback of two bounded morphisms into one
  graph is a bisimulation (`IsBoundedMorphism.isBisimulation_pullback`).

No choice is used.

**Controls.** Both halves of the definition are needed.
* The identity map from a childless node to a node with a loop preserves edges but does not
  reflect them (`preservesEdges_isolatedToLoop`, `not_isBoundedMorphism_isolatedToLoop`), and
  decoration does not commute with it: the node pictures `∅`, its image `Ω`
  (`decorate_comp_isolatedToLoop_ne`).
* The identity map from a node with a loop to a childless node reflects edges vacuously but does
  not preserve them (`reflectsEdges_loopToIsolated`, `not_isBoundedMorphism_loopToIsolated`),
  and decoration does not commute with it either (`decorate_comp_loopToIsolated_ne`).
* The map from the two-node cycle onto the loop is a bounded morphism
  (`isBoundedMorphism_twoCycleToLoop`), so both nodes of the cycle picture `Ω`
  (`decorate_twoCycle_of_morphism`), although the map is not injective.

P. Aczel, *Non-well-founded Sets*, CSLI Lecture Notes 14, 1988 (the final coalgebra theorem);
J. J. M. M. Rutten, *Universal coalgebra: a theory of systems*, Theoretical Computer Science
249, 2000; J. Barwise and L. Moss, *Vicious Circles*, CSLI Lecture Notes 60, 1996.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets

open AccessiblePointedGraph

universe u

/-! ## Bounded morphisms -/

section Morphism

variable {α β γ : Type*} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

/-- A map of graphs that preserves edges: a graph homomorphism. -/
def PreservesEdges (r : α → α → Prop) (s : β → β → Prop) (f : α → β) : Prop :=
  ∀ ⦃a a'⦄, r a a' → s (f a) (f a')

/-- A map of graphs that reflects edges: every edge out of an image `f a` is the image of an
edge out of `a`. -/
def ReflectsEdges (r : α → α → Prop) (s : β → β → Prop) (f : α → β) : Prop :=
  ∀ ⦃a b'⦄, s (f a) b' → ∃ a', r a a' ∧ f a' = b'

/-- A bounded morphism of graphs: a map that preserves and reflects edges. These are the
morphisms of graphs as coalgebras of the powerset functor. -/
structure IsBoundedMorphism (r : α → α → Prop) (s : β → β → Prop) (f : α → β) : Prop where
  /-- Edges are preserved. -/
  map : PreservesEdges r s f
  /-- Edges are reflected. -/
  lift : ReflectsEdges r s f

/-- A bounded morphism is a coalgebra morphism: the children of `f a` are the images of the
children of `a`. -/
theorem isBoundedMorphism_iff_image_eq {f : α → β} :
    IsBoundedMorphism r s f ↔ ∀ a, f '' {a' | r a a'} = {b' | s (f a) b'} := by
  constructor
  · rintro ⟨map, lift⟩ a
    ext b'
    constructor
    · rintro ⟨a', h, rfl⟩
      exact map h
    · intro h
      obtain ⟨a', h', e⟩ := lift h
      exact ⟨a', h', e⟩
  · intro h
    refine ⟨fun a a' ha => ?_, fun a b' hb => ?_⟩
    · have hmem : f a' ∈ f '' {a' | r a a'} := ⟨a', ha, rfl⟩
      rw [h a] at hmem
      exact hmem
    · have hmem : b' ∈ {b' | s (f a) b'} := hb
      rw [← h a] at hmem
      obtain ⟨a', ha', e⟩ := hmem
      exact ⟨a', ha', e⟩

/-- A map is a bounded morphism exactly when its graph is a bisimulation. -/
theorem isBoundedMorphism_iff_isBisimulation {f : α → β} :
    IsBoundedMorphism r s f ↔ IsBisimulation r s fun a b => f a = b := by
  constructor
  · rintro ⟨map, lift⟩ a _ rfl
    exact ⟨fun a' h => ⟨f a', map h, rfl⟩, fun _ h => lift h⟩
  · intro hR
    refine ⟨fun a a' h => ?_, fun a _ h => (hR rfl).2 _ h⟩
    obtain ⟨_, hb, rfl⟩ := (hR (rfl : f a = f a)).1 a' h
    exact hb

namespace IsBoundedMorphism

protected theorem id : IsBoundedMorphism r r id :=
  ⟨fun _ _ h => h, fun _ b' h => ⟨b', h, rfl⟩⟩

protected theorem comp {f : α → β} {g : β → γ} (hg : IsBoundedMorphism s t g)
    (hf : IsBoundedMorphism r s f) : IsBoundedMorphism r t (g ∘ f) where
  map _ _ h := hg.map (hf.map h)
  lift a _ h := by
    obtain ⟨b', hb, rfl⟩ := hg.lift h
    obtain ⟨a', ha, rfl⟩ := hf.lift hb
    exact ⟨a', ha, rfl⟩

theorem isBisimulation {f : α → β} (hf : IsBoundedMorphism r s f) :
    IsBisimulation r s fun a b => f a = b :=
  isBoundedMorphism_iff_isBisimulation.mp hf

/-- Along a bounded morphism, every node is bisimilar to its image. -/
theorem bisimilar {f : α → β} (hf : IsBoundedMorphism r s f) (a : α) : Bisimilar r s a (f a) :=
  hf.isBisimulation.bisimilar rfl

/-- The pullback of two bounded morphisms into one graph is a bisimulation. -/
theorem isBisimulation_pullback {f : α → γ} {g : β → γ} (hf : IsBoundedMorphism r t f)
    (hg : IsBoundedMorphism s t g) : IsBisimulation r s fun a b => f a = g b := by
  intro a b e
  refine ⟨fun a' ha => ?_, fun b' hb => ?_⟩
  · have edge : t (g b) (f a') := by
      rw [← e]
      exact hf.map ha
    obtain ⟨b', hb, e'⟩ := hg.lift edge
    exact ⟨b', hb, e'.symm⟩
  · have edge : t (f a) (g b') := by
      rw [e]
      exact hg.map hb
    exact hf.lift edge

/-- Nodes with the same image under two bounded morphisms into one graph are bisimilar. -/
theorem bisimilar_of_eq {f : α → γ} {g : β → γ} (hf : IsBoundedMorphism r t f)
    (hg : IsBoundedMorphism s t g) {a : α} {b : β} (e : f a = g b) : Bisimilar r s a b :=
  (hf.isBisimulation_pullback hg).bisimilar e

end IsBoundedMorphism

end Morphism

/-! ## Finality of the membership graph -/

namespace HSet

/-- The membership graph of hypersets: an edge from each hyperset to each of its members. -/
abbrev membershipGraph (x y : HSet.{u}) : Prop :=
  y ∈ x

variable {α β : Type u} {r : α → α → Prop} {s : β → β → Prop}

/-- A bounded morphism into the membership graph is a decoration. -/
theorem isBoundedMorphism_iff_isDecoration {d : α → HSet.{u}} :
    IsBoundedMorphism r membershipGraph d ↔ IsDecoration r d := by
  constructor
  · rintro ⟨map, lift⟩ a y
    exact ⟨fun h => lift h, fun ⟨b, hb, e⟩ => e ▸ map hb⟩
  · intro hd
    exact ⟨fun a a' h => (hd a (d a')).mpr ⟨a', h, rfl⟩, fun a y h => (hd a y).mp h⟩

/-- Decoration is a bounded morphism into the membership graph. -/
theorem isBoundedMorphism_decorate (r : α → α → Prop) :
    IsBoundedMorphism r membershipGraph (decorate r) :=
  isBoundedMorphism_iff_isDecoration.mpr (isDecoration_decorate r)

/-- Finality: the decoration of a graph is its unique bounded morphism into the membership
graph. -/
theorem existsUnique_boundedMorphism (r : α → α → Prop) :
    ∃! d : α → HSet.{u}, IsBoundedMorphism r membershipGraph d :=
  ⟨decorate r, isBoundedMorphism_decorate r,
    fun _ hd => (isBoundedMorphism_iff_isDecoration.mp hd).eq_decorate⟩

/-- The only bounded endomorphism of the membership graph is the identity. -/
theorem isBoundedMorphism_self_iff {f : HSet.{u} → HSet.{u}} :
    IsBoundedMorphism membershipGraph membershipGraph f ↔ f = id := by
  constructor
  · intro hf
    funext x
    exact (eq_of_isBisimulation hf.isBisimulation (rfl : f x = f x)).symm
  · rintro rfl
    exact IsBoundedMorphism.id

/-- Bisimilarity is the kernel of decoration. -/
theorem bisimilar_iff_decorate_eq {a : α} {b : β} :
    Bisimilar r s a b ↔ decorate r a = decorate s b :=
  decorate_eq_decorate_iff.symm

theorem bisimilar_eq_kernel :
    Bisimilar r s = fun a b => decorate r a = decorate s b :=
  funext fun _ => funext fun _ => propext bisimilar_iff_decorate_eq

/-- The kernel of decoration is a bisimulation, the largest one. -/
theorem isBisimulation_kernel : IsBisimulation r s fun a b => decorate r a = decorate s b :=
  (isBoundedMorphism_decorate r).isBisimulation_pullback (isBoundedMorphism_decorate s)

/-- A relation lies in the kernel of decoration exactly when it lies in some bisimulation. -/
theorem le_kernel_iff {R : α → β → Prop} :
    (∀ a b, R a b → decorate r a = decorate s b) ↔
      ∃ S, IsBisimulation r s S ∧ ∀ a b, R a b → S a b :=
  ⟨fun h => ⟨_, isBisimulation_kernel, h⟩,
    fun ⟨_, hS, hRS⟩ a b hab => bisimilar_iff_decorate_eq.mp (hS.bisimilar (hRS a b hab))⟩

end HSet

namespace IsBisimulation

variable {α β : Type u} {r : α → α → Prop} {s : β → β → Prop}

/-- Coinduction: nodes related by a bisimulation have the same decoration. -/
theorem decorate_eq {R : α → β → Prop} (hR : IsBisimulation r s R) {a : α} {b : β}
    (h : R a b) : HSet.decorate r a = HSet.decorate s b :=
  HSet.decorate_eq_of_bisimilar (hR.bisimilar h)

end IsBisimulation

namespace IsBoundedMorphism

variable {α β : Type u} {r : α → α → Prop} {s : β → β → Prop}

/-- A bounded morphism into the membership graph is the decoration. -/
theorem eq_decorate {d : α → HSet.{u}} (hd : IsBoundedMorphism r HSet.membershipGraph d) :
    d = HSet.decorate r :=
  (HSet.isBoundedMorphism_iff_isDecoration.mp hd).eq_decorate

/-- Decoration commutes with every bounded morphism. -/
theorem decorate_comp {f : α → β} (hf : IsBoundedMorphism r s f) :
    HSet.decorate s ∘ f = HSet.decorate r :=
  ((HSet.isBoundedMorphism_decorate s).comp hf).eq_decorate

theorem decorate_apply {f : α → β} (hf : IsBoundedMorphism r s f) (a : α) :
    HSet.decorate s (f a) = HSet.decorate r a :=
  congrFun hf.decorate_comp a

end IsBoundedMorphism

/-! ## Examples -/

namespace HSet

/-- One node without edges. -/
def isolated (_ _ : PUnit.{u + 1}) : Prop :=
  False

/-- One node with a loop: the edges of `loop`. -/
def selfLoop (_ _ : PUnit.{u + 1}) : Prop :=
  True

theorem decorate_isolated (a : PUnit.{u + 1}) : decorate isolated a = ∅ :=
  eq_empty_iff.mpr fun _ h =>
    let ⟨_, hb, _⟩ := mem_decorate.mp h
    hb

theorem decorate_selfLoop (a : PUnit.{u + 1}) : decorate selfLoop a = quineAtom :=
  decorate_loop a

theorem preservesEdges_isolatedToLoop :
    PreservesEdges isolated.{u} selfLoop (id : PUnit.{u + 1} → PUnit.{u + 1}) :=
  fun _ _ h => h.elim

/-- The map from a childless node to a loop does not reflect the loop. -/
theorem not_reflectsEdges_isolatedToLoop :
    ¬ ReflectsEdges isolated.{u} selfLoop (id : PUnit.{u + 1} → PUnit.{u + 1}) := fun h =>
  let ⟨_, hb, _⟩ := h (a := PUnit.unit) (b' := PUnit.unit) trivial
  hb

theorem not_isBoundedMorphism_isolatedToLoop :
    ¬ IsBoundedMorphism isolated.{u} selfLoop (id : PUnit.{u + 1} → PUnit.{u + 1}) :=
  fun h => not_reflectsEdges_isolatedToLoop h.lift

/-- Along a map that preserves but does not reflect edges, decoration does not commute: the
childless node pictures `∅`, its image `Ω`. -/
theorem decorate_comp_isolatedToLoop_ne :
    decorate selfLoop ∘ (id : PUnit.{u + 1} → PUnit.{u + 1}) ≠ decorate isolated := fun h =>
  empty_ne_quineAtom <|
    calc (∅ : HSet.{u}) = decorate isolated PUnit.unit := (decorate_isolated _).symm
      _ = decorate selfLoop PUnit.unit := (congrFun h PUnit.unit).symm
      _ = quineAtom := decorate_selfLoop _

theorem reflectsEdges_loopToIsolated :
    ReflectsEdges selfLoop.{u} isolated (id : PUnit.{u + 1} → PUnit.{u + 1}) :=
  fun _ _ h => h.elim

theorem not_preservesEdges_loopToIsolated :
    ¬ PreservesEdges selfLoop.{u} isolated (id : PUnit.{u + 1} → PUnit.{u + 1}) :=
  fun h => h (a := PUnit.unit) (a' := PUnit.unit) trivial

theorem not_isBoundedMorphism_loopToIsolated :
    ¬ IsBoundedMorphism selfLoop.{u} isolated (id : PUnit.{u + 1} → PUnit.{u + 1}) :=
  fun h => not_preservesEdges_loopToIsolated h.map

theorem decorate_comp_loopToIsolated_ne :
    decorate isolated ∘ (id : PUnit.{u + 1} → PUnit.{u + 1}) ≠ decorate selfLoop := fun h =>
  empty_ne_quineAtom <|
    calc (∅ : HSet.{u}) = decorate isolated PUnit.unit := (decorate_isolated _).symm
      _ = decorate selfLoop PUnit.unit := congrFun h PUnit.unit
      _ = quineAtom := decorate_selfLoop _

/-- The two-node cycle maps onto the loop by a bounded morphism. -/
theorem isBoundedMorphism_twoCycleToLoop :
    IsBoundedMorphism twoCycle.{u}.edge loop.{u}.edge fun _ => PUnit.unit :=
  ⟨fun _ _ _ => trivial, fun a _ _ => ⟨⟨!a.down⟩, rfl, rfl⟩⟩

/-- Both nodes of the two-node cycle picture `Ω`, by the morphism onto the loop. -/
theorem decorate_twoCycle_of_morphism (a : twoCycle.{u}.Node) :
    decorate twoCycle.edge a = quineAtom :=
  (isBoundedMorphism_twoCycleToLoop.decorate_apply a).symm.trans (decorate_loop _)

/-- The morphism from the two-node cycle onto the loop is not injective. -/
theorem not_injective_twoCycleToLoop :
    ¬ Function.Injective fun _ : twoCycle.{u}.Node => (PUnit.unit : loop.{u}.Node) := fun h =>
  absurd (congrArg ULift.down (h (a₁ := ⟨true⟩) (a₂ := ⟨false⟩) rfl)) Bool.noConfusion

end HSet

end Mettapedia.TypeTheory.MaterialSets.Hypersets
