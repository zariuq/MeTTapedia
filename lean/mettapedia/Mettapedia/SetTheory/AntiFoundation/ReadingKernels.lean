import Mettapedia.SetTheory.AntiFoundation.Graphs
import Mettapedia.SetTheory.AntiFoundation.ReadingStep
import Mettapedia.TypeTheory.MaterialSets.Hypersets.UnfoldingIdentityComparison

/-!
# The unfolding kernel and the automorphism kernel on finite graphs

The Scott kernel relates nodes whose unfoldings are presentation-isomorphic. The
automorphism kernel relates nodes that are the distinguished points of a pointed
isomorphism of the graph with itself. Neither kernel is a reading on every finite graph.
On each counterexample one application of the child-class step is a reading.

The automorphism kernel compares the whole graph, so a node above one of the two nodes can
separate them, as `marker` does in `OrbitGap`. Finsler's identification compares only what
lies below the two nodes. It is not defined here.

`ScottGap` is the picture of the control `recount` in
`Profiles.ProfileFiniteScottCollapse`. The automorphism kernel is a bisimulation
(`automorphismKernel_le_step`), and so is the Scott kernel of a finite graph
(`Profiles.ProfileFiniteReadings.scottKernel_le_step`). `stepClosure` in `ReadingFinite`
is the least reading above a bisimulation.
-/

set_option autoImplicit false

universe u

namespace Mettapedia.SetTheory.AntiFoundation

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open UnfoldingIdentityComparison

/-! ## Scott -/

/-- Nodes whose unfoldings have a `PresentationIso`. -/
def scottKernel {α : Type u} (edge : Edge α) : Setoid α where
  r a b := Nonempty (PresentationIso (unfold edge a) (unfold edge b))
  iseqv :=
    ⟨fun _ => ⟨PresentationIso.refl _⟩,
      fun ⟨e⟩ => ⟨e.symm⟩,
      fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

inductive ScottGap where
  | rootA
  | rootB
  | leaf1
  | leaf2
  | leaf3
  deriving DecidableEq

/-- Two leaves under `rootA`, one leaf under `rootB`. -/
def scottGapEdge : Edge ScottGap
  | .rootA, .leaf1 => True
  | .rootA, .leaf2 => True
  | .rootB, .leaf3 => True
  | _, _ => False

/-- `2` for `rootA`, `1` for `rootB`, and `0` for a leaf. -/
def scottGapShape : ScottGap → Nat
  | .rootA => 2
  | .rootB => 1
  | .leaf1 | .leaf2 | .leaf3 => 0

theorem scottGap_no_path {x y : ScottGap} (hx : ∀ z, ¬ scottGapEdge x z)
    (p : Path scottGapEdge x y) : y = x := by
  induction p with
  | nil => rfl
  | snoc _ step ih => exact (hx _ (ih ▸ step)).elim

theorem scottGap_node_nil {x : ScottGap} (hx : ∀ z, ¬ scottGapEdge x z)
    (n : PathNode scottGapEdge x) : n = ⟨x, .nil⟩ := by
  rcases n with ⟨y, p⟩
  cases scottGap_no_path hx p
  cases p with
  | nil => rfl
  | snoc path step =>
    cases scottGap_no_path hx path
    exact (hx _ step).elim

def scottGapChildlessEquiv {x y : ScottGap} (hx : ∀ z, ¬ scottGapEdge x z)
    (hy : ∀ z, ¬ scottGapEdge y z) :
    PathNode scottGapEdge x ≃ PathNode scottGapEdge y where
  toFun _ := ⟨y, .nil⟩
  invFun _ := ⟨x, .nil⟩
  left_inv n := (scottGap_node_nil hx n).symm
  right_inv n := (scottGap_node_nil hy n).symm

def scottGapChildlessIso {x y : ScottGap} (hx : ∀ z, ¬ scottGapEdge x z)
    (hy : ∀ z, ¬ scottGapEdge y z) :
    PresentationIso (unfold scottGapEdge x) (unfold scottGapEdge y) where
  nodes := scottGapChildlessEquiv hx hy
  edge_iff _ _ := by
    constructor
    · intro e
      cases e with
      | extend path step =>
        cases scottGap_no_path hx path
        exact (hx _ step).elim
    · intro e
      cases e
  point := rfl

theorem scottGap_shape_zero {x : ScottGap} :
    scottGapShape x = 0 ↔ ∀ z, ¬ scottGapEdge x z := by
  cases x <;> constructor
  · intro h
    cases h
  · intro h
    exact (h .leaf1 trivial).elim
  · intro h
    cases h
  · intro h
    exact (h .leaf3 trivial).elim
  · intro _ z
    cases z <;> simp [scottGapEdge]
  · intro _
    rfl
  · intro _ z
    cases z <;> simp [scottGapEdge]
  · intro _
    rfl
  · intro _ z
    cases z <;> simp [scottGapEdge]
  · intro _
    rfl

theorem scottGap_child_iff_rootA {t : ScottGap} :
    scottGapEdge .rootA t ↔ t = .leaf1 ∨ t = .leaf2 := by
  cases t <;> simp [scottGapEdge]

theorem scottGap_child_iff_rootB {t : ScottGap} :
    scottGapEdge .rootB t ↔ t = .leaf3 := by
  cases t <;> simp [scottGapEdge]

def scottGapChildTransport {x y : ScottGap}
    (iso : PresentationIso (unfold scottGapEdge x) (unfold scottGapEdge y)) :
    {t // scottGapEdge x t} ≃ {t // scottGapEdge y t} :=
  (unfoldOccurrencesEquiv scottGapEdge x).symm.trans
    (iso.occurrenceTransport.trans (unfoldOccurrencesEquiv scottGapEdge y))

theorem scottGap_shape_of_kernel {x y : ScottGap}
    (h : scottKernel scottGapEdge x y) : scottGapShape x = scottGapShape y := by
  obtain ⟨iso⟩ := h
  let e := scottGapChildTransport iso
  cases x with
  | rootA =>
    let i1 : {t // scottGapEdge .rootA t} := ⟨.leaf1, by simp [scottGapEdge]⟩
    let i2 : {t // scottGapEdge .rootA t} := ⟨.leaf2, by simp [scottGapEdge]⟩
    have distinct : (e i1).1 ≠ (e i2).1 := by
      intro same
      have : i1 = i2 := e.injective (Subtype.ext same)
      cases congrArg Subtype.val this
    cases y with
    | rootA => rfl
    | rootB =>
      have h1 : (e i1).1 = .leaf3 := (scottGap_child_iff_rootB).mp (e i1).2
      have h2 : (e i2).1 = .leaf3 := (scottGap_child_iff_rootB).mp (e i2).2
      exact (distinct (h1.trans h2.symm)).elim
    | leaf1 => exact ((scottGap_shape_zero).mp rfl (e i1).1 (e i1).2).elim
    | leaf2 => exact ((scottGap_shape_zero).mp rfl (e i1).1 (e i1).2).elim
    | leaf3 => exact ((scottGap_shape_zero).mp rfl (e i1).1 (e i1).2).elim
  | rootB =>
    let i : {t // scottGapEdge .rootB t} := ⟨.leaf3, by simp [scottGapEdge]⟩
    cases y with
    | rootB => rfl
    | rootA =>
      let j1 : {t // scottGapEdge .rootA t} := ⟨.leaf1, by simp [scottGapEdge]⟩
      let j2 : {t // scottGapEdge .rootA t} := ⟨.leaf2, by simp [scottGapEdge]⟩
      have : j1 = j2 := by
        apply e.symm.injective
        apply Subtype.ext
        have h1 : (e.symm j1).1 = .leaf3 := (scottGap_child_iff_rootB).mp (e.symm j1).2
        have h2 : (e.symm j2).1 = .leaf3 := (scottGap_child_iff_rootB).mp (e.symm j2).2
        exact h1.trans h2.symm
      cases congrArg Subtype.val this
    | leaf1 => exact ((scottGap_shape_zero).mp rfl (e i).1 (e i).2).elim
    | leaf2 => exact ((scottGap_shape_zero).mp rfl (e i).1 (e i).2).elim
    | leaf3 => exact ((scottGap_shape_zero).mp rfl (e i).1 (e i).2).elim
  | leaf1 =>
    have hy : ∀ z, ¬ scottGapEdge y z := by
      intro z hz
      exact (scottGap_shape_zero).mp rfl (e.symm ⟨z, hz⟩).1 (e.symm ⟨z, hz⟩).2
    exact ((scottGap_shape_zero).mpr hy).symm
  | leaf2 =>
    have hy : ∀ z, ¬ scottGapEdge y z := by
      intro z hz
      exact (scottGap_shape_zero).mp rfl (e.symm ⟨z, hz⟩).1 (e.symm ⟨z, hz⟩).2
    exact ((scottGap_shape_zero).mpr hy).symm
  | leaf3 =>
    have hy : ∀ z, ¬ scottGapEdge y z := by
      intro z hz
      exact (scottGap_shape_zero).mp rfl (e.symm ⟨z, hz⟩).1 (e.symm ⟨z, hz⟩).2
    exact ((scottGap_shape_zero).mpr hy).symm

theorem scottGap_kernel_of_shape {x y : ScottGap}
    (h : scottGapShape x = scottGapShape y) : scottKernel scottGapEdge x y := by
  cases x <;> cases y <;> first
    | exact absurd h (by decide)
    | exact ⟨PresentationIso.refl _⟩
    | exact ⟨scottGapChildlessIso ((scottGap_shape_zero).mp rfl)
        ((scottGap_shape_zero).mp rfl)⟩

theorem scottKernel_iff_shape {x y : ScottGap} :
    scottKernel scottGapEdge x y ↔ scottGapShape x = scottGapShape y :=
  ⟨scottGap_shape_of_kernel, scottGap_kernel_of_shape⟩

theorem scottGap_child_shape {x z : ScottGap} (hx : scottGapShape x ≠ 0)
    (hz : scottGapEdge x z) : scottGapShape z = 0 := by
  cases x <;> cases z <;> simp [scottGapShape, scottGapEdge] at hx hz ⊢

theorem scottGap_has_child {x : ScottGap} (hx : scottGapShape x ≠ 0) :
    ∃ z, scottGapEdge x z ∧ scottGapShape z = 0 := by
  cases x <;> simp [scottGapShape] at hx
  · exact ⟨.leaf1, by simp [scottGapEdge], rfl⟩
  · exact ⟨.leaf3, by simp [scottGapEdge], rfl⟩

theorem step_scottKernel_iff {x y : ScottGap} :
    step scottGapEdge (scottKernel scottGapEdge) x y ↔
      ((scottGapShape x = 0) ↔ (scottGapShape y = 0)) := by
  constructor
  · intro h
    simp only [step_apply, SameChildren] at h
    constructor
    · intro hx
      by_contra hy
      obtain ⟨z, hz, _⟩ := scottGap_has_child hy
      obtain ⟨_, hw, _⟩ := h.2 z hz
      exact ((scottGap_shape_zero).mp hx _ hw).elim
    · intro hy
      by_contra hx
      obtain ⟨z, hz, _⟩ := scottGap_has_child hx
      obtain ⟨_, hw, _⟩ := h.1 z hz
      exact ((scottGap_shape_zero).mp hy _ hw).elim
  · intro h
    simp only [step_apply, SameChildren]
    by_cases hx : scottGapShape x = 0
    · have hy : scottGapShape y = 0 := h.mp hx
      have hx' := (scottGap_shape_zero).mp hx
      have hy' := (scottGap_shape_zero).mp hy
      exact ⟨fun z hz => (hx' z hz).elim, fun z hz => (hy' z hz).elim⟩
    · have hy : scottGapShape y ≠ 0 := fun hy => hx (h.mpr hy)
      refine ⟨?_, ?_⟩
      · intro z hz
        obtain ⟨w, hw, hw0⟩ := scottGap_has_child hy
        have hz0 := scottGap_child_shape hx hz
        exact ⟨w, hw, (scottKernel_iff_shape).mpr (hz0.trans hw0.symm)⟩
      · intro z hz
        obtain ⟨w, hw, hw0⟩ := scottGap_has_child hx
        have hz0 := scottGap_child_shape hy hz
        exact ⟨w, hw, (scottKernel_iff_shape).mpr (hw0.trans hz0.symm)⟩

/-- On this finite graph the Scott kernel relates `rootA` and `rootB` only after one step. -/
theorem scottKernel_not_reading_scottGap :
    step scottGapEdge (scottKernel scottGapEdge) ≠ scottKernel scottGapEdge := by
  intro h
  have hstep : step scottGapEdge (scottKernel scottGapEdge) .rootA .rootB :=
    (step_scottKernel_iff).mpr (by simp [scottGapShape])
  have hker : scottKernel scottGapEdge .rootA .rootB := by
    rw [← h]
    exact hstep
  have : scottGapShape .rootA = scottGapShape .rootB :=
    (scottKernel_iff_shape).mp hker
  simp [scottGapShape] at this

theorem step_step_scottKernel_iff {x y : ScottGap} :
    step scottGapEdge (step scottGapEdge (scottKernel scottGapEdge)) x y ↔
      ((scottGapShape x = 0) ↔ (scottGapShape y = 0)) := by
  constructor
  · intro h
    simp only [step_apply, SameChildren] at h
    constructor
    · intro hx
      by_contra hy
      obtain ⟨z, hz, _⟩ := scottGap_has_child hy
      obtain ⟨_, hw, _⟩ := h.2 z hz
      exact ((scottGap_shape_zero).mp hx _ hw).elim
    · intro hy
      by_contra hx
      obtain ⟨z, hz, _⟩ := scottGap_has_child hx
      obtain ⟨_, hw, _⟩ := h.1 z hz
      exact ((scottGap_shape_zero).mp hy _ hw).elim
  · intro h
    simp only [step_apply, SameChildren]
    by_cases hx : scottGapShape x = 0
    · have hy : scottGapShape y = 0 := h.mp hx
      have hx' := (scottGap_shape_zero).mp hx
      have hy' := (scottGap_shape_zero).mp hy
      exact ⟨fun z hz => (hx' z hz).elim, fun z hz => (hy' z hz).elim⟩
    · have hy : scottGapShape y ≠ 0 := fun hy => hx (h.mpr hy)
      refine ⟨?_, ?_⟩
      · intro z hz
        obtain ⟨w, hw, _⟩ := scottGap_has_child hy
        have _ := scottGap_child_shape hx hz
        exact ⟨w, hw, (step_scottKernel_iff).mpr (by
          simp [scottGap_child_shape hx hz, scottGap_child_shape hy hw])⟩
      · intro z hz
        obtain ⟨w, hw, _⟩ := scottGap_has_child hx
        exact ⟨w, hw, (step_scottKernel_iff).mpr (by
          simp [scottGap_child_shape hy hz, scottGap_child_shape hx hw])⟩

/-- One application of `step` to the Scott kernel is a reading of the counterexample. -/
theorem scottGap_iterate_reading :
    step scottGapEdge (step scottGapEdge (scottKernel scottGapEdge)) =
      step scottGapEdge (scottKernel scottGapEdge) := by
  apply Setoid.ext
  intro x y
  rw [step_step_scottKernel_iff, step_scottKernel_iff]

/-! ## Automorphisms -/

/-- Nodes that a pointed isomorphism of the graph with itself carries to one another. -/
def automorphismKernel {β : Type} (edge : Edge β) : Setoid β where
  r a b := Nonempty (PointedIso edge edge a b)
  iseqv :=
    ⟨fun a => ⟨{
        equiv := Equiv.refl _
        point := rfl
        preserve := fun _ _ => Iff.rfl }⟩,
      fun ⟨e⟩ => ⟨{
        equiv := e.equiv.symm
        point := (congrArg e.equiv.symm e.point).symm.trans (e.equiv.symm_apply_apply _)
        preserve := fun x y => by
          simpa [e.point] using (e.preserve (e.equiv.symm x) (e.equiv.symm y)).symm }⟩,
      fun ⟨e⟩ ⟨f⟩ => ⟨{
        equiv := e.equiv.trans f.equiv
        point := (congrArg f.equiv e.point).trans f.point
        preserve := fun x y =>
          (e.preserve x y).trans (f.preserve (e.equiv x) (e.equiv y)) }⟩⟩

/-- The automorphism kernel is a bisimulation: an automorphism carries the children of a
node to the children of its image. -/
theorem automorphismKernel_le_step {β : Type} (edge : Edge β) :
    automorphismKernel edge ≤ step edge (automorphismKernel edge) := by
  apply (le_step_iff_isBisimulation edge (automorphismKernel edge)).mpr
  intro a b ⟨e⟩
  constructor
  · intro a' ha'
    have himage : edge (e.equiv a) (e.equiv a') := (e.preserve a a').mp ha'
    rw [e.point] at himage
    exact ⟨e.equiv a', himage, ⟨{ equiv := e.equiv, point := rfl, preserve := e.preserve }⟩⟩
  · intro b' hb'
    refine ⟨e.equiv.symm b', (e.preserve a (e.equiv.symm b')).mpr ?_,
      ⟨{ equiv := e.equiv, point := e.equiv.apply_symm_apply b', preserve := e.preserve }⟩⟩
    rw [e.point, e.equiv.apply_symm_apply]
    exact hb'

inductive OrbitGap where
  | marker
  | a
  | b
  | leaf
  deriving DecidableEq

/-- `marker` points at `a`. `a` and `b` both point at `leaf`, and nothing points at `b`. -/
def orbitGapEdge : Edge OrbitGap
  | .marker, .a => True
  | .a, .leaf => True
  | .b, .leaf => True
  | _, _ => False

theorem orbitGap_hasChild_iff {x y : OrbitGap}
    (e : PointedIso orbitGapEdge orbitGapEdge x y) :
    (∃ z, orbitGapEdge x z) ↔ (∃ z, orbitGapEdge y z) := by
  constructor
  · intro ⟨z, hz⟩
    have hz0 : orbitGapEdge (e.equiv x) (e.equiv z) := (e.preserve x z).mp hz
    have hz' : orbitGapEdge y (e.equiv z) := by
      rw [e.point] at hz0
      exact hz0
    exact ⟨e.equiv z, hz'⟩
  · intro ⟨z, hz⟩
    refine ⟨e.equiv.symm z, (e.preserve x (e.equiv.symm z)).mpr ?_⟩
    simpa [e.point] using hz

theorem orbitGap_hasGrandchild_iff {x y : OrbitGap}
    (e : PointedIso orbitGapEdge orbitGapEdge x y) :
    (∃ z w, orbitGapEdge x z ∧ orbitGapEdge z w) ↔
      (∃ z w, orbitGapEdge y z ∧ orbitGapEdge z w) := by
  constructor
  · intro ⟨z, w, hz, hw⟩
    have hz0 : orbitGapEdge (e.equiv x) (e.equiv z) := (e.preserve x z).mp hz
    have hz' : orbitGapEdge y (e.equiv z) := by
      rw [e.point] at hz0
      exact hz0
    exact ⟨e.equiv z, e.equiv w, hz', (e.preserve z w).mp hw⟩
  · intro ⟨z, w, hz, hw⟩
    refine ⟨e.equiv.symm z, e.equiv.symm w, ?_, ?_⟩
    · exact (e.preserve x _).mpr (by simpa [e.point] using hz)
    · exact (e.preserve _ _).mpr (by simpa using hw)

theorem orbitGap_hasParent_iff {x y : OrbitGap}
    (e : PointedIso orbitGapEdge orbitGapEdge x y) :
    (∃ z, orbitGapEdge z x) ↔ (∃ z, orbitGapEdge z y) := by
  constructor
  · intro ⟨z, hz⟩
    have hz0 : orbitGapEdge (e.equiv z) (e.equiv x) := (e.preserve z x).mp hz
    have hz' : orbitGapEdge (e.equiv z) y := by
      rw [e.point] at hz0
      exact hz0
    exact ⟨e.equiv z, hz'⟩
  · intro ⟨z, hz⟩
    refine ⟨e.equiv.symm z, (e.preserve _ x).mpr ?_⟩
    simpa [e.point] using hz

theorem orbitGap_marker_grand : ∃ z w, orbitGapEdge .marker z ∧ orbitGapEdge z w :=
  ⟨.a, .leaf, trivial, trivial⟩

theorem orbitGap_not_grand_a : ¬ ∃ z w, orbitGapEdge .a z ∧ orbitGapEdge z w := by
  intro ⟨z, w, hz, hw⟩
  cases z <;> simp [orbitGapEdge] at hz
  cases w <;> simp [orbitGapEdge] at hw

theorem orbitGap_not_grand_b : ¬ ∃ z w, orbitGapEdge .b z ∧ orbitGapEdge z w := by
  intro ⟨z, w, hz, hw⟩
  cases z <;> simp [orbitGapEdge] at hz
  cases w <;> simp [orbitGapEdge] at hw

theorem orbitGap_not_grand_leaf : ¬ ∃ z w, orbitGapEdge .leaf z ∧ orbitGapEdge z w := by
  intro ⟨z, _, hz, _⟩
  cases z <;> simp [orbitGapEdge] at hz

theorem orbitGap_child_a : ∃ z, orbitGapEdge .a z :=
  ⟨.leaf, trivial⟩

theorem orbitGap_child_b : ∃ z, orbitGapEdge .b z :=
  ⟨.leaf, trivial⟩

theorem orbitGap_child_marker : ∃ z, orbitGapEdge .marker z :=
  ⟨.a, trivial⟩

theorem orbitGap_not_child_leaf : ¬ ∃ z, orbitGapEdge .leaf z := by
  intro ⟨z, hz⟩
  cases z <;> simp [orbitGapEdge] at hz

theorem orbitGap_parent_a : ∃ z, orbitGapEdge z .a :=
  ⟨.marker, trivial⟩

theorem orbitGap_not_parent_b : ¬ ∃ z, orbitGapEdge z .b := by
  intro ⟨z, hz⟩
  cases z <;> simp [orbitGapEdge] at hz

theorem orbitGap_not_parent_marker : ¬ ∃ z, orbitGapEdge z .marker := by
  intro ⟨z, hz⟩
  cases z <;> simp [orbitGapEdge] at hz

theorem orbitGap_iso_eq {x y : OrbitGap}
    (h : Nonempty (PointedIso orbitGapEdge orbitGapEdge x y)) : x = y := by
  obtain ⟨e⟩ := h
  have hchild := orbitGap_hasChild_iff e
  have hgrand := orbitGap_hasGrandchild_iff e
  have hparent := orbitGap_hasParent_iff e
  cases x <;> cases y
  · rfl
  · exact (orbitGap_not_grand_a (hgrand.mp orbitGap_marker_grand)).elim
  · exact (orbitGap_not_grand_b (hgrand.mp orbitGap_marker_grand)).elim
  · exact (orbitGap_not_child_leaf (hchild.mp orbitGap_child_marker)).elim
  · exact (orbitGap_not_grand_a (hgrand.mpr orbitGap_marker_grand)).elim
  · rfl
  · exact (orbitGap_not_parent_b (hparent.mp orbitGap_parent_a)).elim
  · exact (orbitGap_not_child_leaf (hchild.mp orbitGap_child_a)).elim
  · exact (orbitGap_not_grand_b (hgrand.mpr orbitGap_marker_grand)).elim
  · exact (orbitGap_not_parent_b (hparent.mpr orbitGap_parent_a)).elim
  · rfl
  · exact (orbitGap_not_child_leaf (hchild.mp orbitGap_child_b)).elim
  · exact (orbitGap_not_child_leaf (hchild.mpr orbitGap_child_marker)).elim
  · exact (orbitGap_not_child_leaf (hchild.mpr orbitGap_child_a)).elim
  · exact (orbitGap_not_child_leaf (hchild.mpr orbitGap_child_b)).elim
  · rfl

theorem automorphismKernel_eq_bot : automorphismKernel orbitGapEdge = ⊥ := by
  apply Setoid.ext
  intro x y
  rw [Setoid.bot_def]
  constructor
  · intro h
    exact orbitGap_iso_eq h
  · intro hxy
    cases hxy
    exact ⟨{ equiv := Equiv.refl _, point := rfl, preserve := fun _ _ => Iff.rfl }⟩

theorem orbitGap_step_bot_iff {x y : OrbitGap} :
    step orbitGapEdge ⊥ x y ↔ x = y ∨ (x = .a ∧ y = .b) ∨ (x = .b ∧ y = .a) := by
  rw [step_apply, Setoid.bot_def]
  cases x <;> cases y
  case marker.marker =>
    exact ⟨fun _ => Or.inl rfl, fun _ =>
      ⟨fun z hz => ⟨z, hz, rfl⟩, fun z hz => ⟨z, hz, rfl⟩⟩⟩
  case a.a =>
    exact ⟨fun _ => Or.inl rfl, fun _ =>
      ⟨fun z hz => ⟨z, hz, rfl⟩, fun z hz => ⟨z, hz, rfl⟩⟩⟩
  case b.b =>
    exact ⟨fun _ => Or.inl rfl, fun _ =>
      ⟨fun z hz => ⟨z, hz, rfl⟩, fun z hz => ⟨z, hz, rfl⟩⟩⟩
  case leaf.leaf =>
    exact ⟨fun _ => Or.inl rfl, fun _ =>
      ⟨fun z hz => ⟨z, hz, rfl⟩, fun z hz => ⟨z, hz, rfl⟩⟩⟩
  case a.b =>
    refine ⟨fun _ => Or.inr (Or.inl ⟨rfl, rfl⟩), fun _ => ⟨?_, ?_⟩⟩
    · intro z hz
      cases z <;> simp [orbitGapEdge] at hz
      exact ⟨.leaf, trivial, rfl⟩
    · intro z hz
      cases z <;> simp [orbitGapEdge] at hz
      exact ⟨.leaf, trivial, rfl⟩
  case b.a =>
    refine ⟨fun _ => Or.inr (Or.inr ⟨rfl, rfl⟩), fun _ => ⟨?_, ?_⟩⟩
    · intro z hz
      cases z <;> simp [orbitGapEdge] at hz
      exact ⟨.leaf, trivial, rfl⟩
    · intro z hz
      cases z <;> simp [orbitGapEdge] at hz
      exact ⟨.leaf, trivial, rfl⟩
  case marker.a =>
    refine ⟨?_, ?_⟩
    · intro h
      obtain ⟨w, hw, heq⟩ := h.1 .a trivial
      cases w <;> simp [orbitGapEdge] at hw; cases heq
    · intro hbad
      exact absurd hbad (by decide)
  case marker.b =>
    refine ⟨?_, ?_⟩
    · intro h
      obtain ⟨w, hw, heq⟩ := h.1 .a trivial
      cases w <;> simp [orbitGapEdge] at hw; cases heq
    · intro hbad
      exact absurd hbad (by decide)
  case marker.leaf =>
    refine ⟨?_, ?_⟩
    · intro h
      obtain ⟨w, hw, _⟩ := h.1 .a trivial
      cases w <;> simp [orbitGapEdge] at hw
    · intro hbad
      exact absurd hbad (by decide)
  case a.marker =>
    refine ⟨?_, ?_⟩
    · intro h
      obtain ⟨w, hw, heq⟩ := h.1 .leaf trivial
      cases w <;> simp [orbitGapEdge] at hw; cases heq
    · intro hbad
      exact absurd hbad (by decide)
  case a.leaf =>
    refine ⟨?_, ?_⟩
    · intro h
      obtain ⟨w, hw, _⟩ := h.1 .leaf trivial
      cases w <;> simp [orbitGapEdge] at hw
    · intro hbad
      exact absurd hbad (by decide)
  case b.marker =>
    refine ⟨?_, ?_⟩
    · intro h
      obtain ⟨w, hw, heq⟩ := h.1 .leaf trivial
      cases w <;> simp [orbitGapEdge] at hw; cases heq
    · intro hbad
      exact absurd hbad (by decide)
  case b.leaf =>
    refine ⟨?_, ?_⟩
    · intro h
      obtain ⟨w, hw, _⟩ := h.1 .leaf trivial
      cases w <;> simp [orbitGapEdge] at hw
    · intro hbad
      exact absurd hbad (by decide)
  case leaf.marker =>
    refine ⟨?_, ?_⟩
    · intro h
      obtain ⟨w, hw, _⟩ := h.2 .a trivial
      cases w <;> simp [orbitGapEdge] at hw
    · intro hbad
      exact absurd hbad (by decide)
  case leaf.a =>
    refine ⟨?_, ?_⟩
    · intro h
      obtain ⟨w, hw, _⟩ := h.2 .leaf trivial
      cases w <;> simp [orbitGapEdge] at hw
    · intro hbad
      exact absurd hbad (by decide)
  case leaf.b =>
    refine ⟨?_, ?_⟩
    · intro h
      obtain ⟨w, hw, _⟩ := h.2 .leaf trivial
      cases w <;> simp [orbitGapEdge] at hw
    · intro hbad
      exact absurd hbad (by decide)

/-- The automorphism kernel is equality on this graph, and equality is not a reading. -/
theorem automorphismKernel_not_reading_orbitGap :
    step orbitGapEdge (automorphismKernel orbitGapEdge) ≠ automorphismKernel orbitGapEdge := by
  intro h
  have hab : step orbitGapEdge (automorphismKernel orbitGapEdge) .a .b := by
    rw [automorphismKernel_eq_bot]
    exact (orbitGap_step_bot_iff).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  have hker : automorphismKernel orbitGapEdge .a .b := by
    rw [← h]
    exact hab
  cases orbitGap_iso_eq hker

theorem orbitGap_step_reading_iff {x y : OrbitGap} :
    step orbitGapEdge (step orbitGapEdge ⊥) x y ↔
      x = y ∨ (x = .a ∧ y = .b) ∨ (x = .b ∧ y = .a) := by
  rw [step_apply]
  cases x <;> cases y
  case marker.marker =>
    exact ⟨fun _ => Or.inl rfl, fun _ => ⟨fun z hz => ⟨z, hz, (orbitGap_step_bot_iff).mpr (Or.inl rfl)⟩,
      fun z hz => ⟨z, hz, (orbitGap_step_bot_iff).mpr (Or.inl rfl)⟩⟩⟩
  case a.a =>
    exact ⟨fun _ => Or.inl rfl, fun _ => ⟨fun z hz => ⟨z, hz, (orbitGap_step_bot_iff).mpr (Or.inl rfl)⟩,
      fun z hz => ⟨z, hz, (orbitGap_step_bot_iff).mpr (Or.inl rfl)⟩⟩⟩
  case b.b =>
    exact ⟨fun _ => Or.inl rfl, fun _ => ⟨fun z hz => ⟨z, hz, (orbitGap_step_bot_iff).mpr (Or.inl rfl)⟩,
      fun z hz => ⟨z, hz, (orbitGap_step_bot_iff).mpr (Or.inl rfl)⟩⟩⟩
  case leaf.leaf =>
    exact ⟨fun _ => Or.inl rfl, fun _ => ⟨fun z hz => ⟨z, hz, (orbitGap_step_bot_iff).mpr (Or.inl rfl)⟩,
      fun z hz => ⟨z, hz, (orbitGap_step_bot_iff).mpr (Or.inl rfl)⟩⟩⟩
  case a.b =>
    refine ⟨fun _ => Or.inr (Or.inl ⟨rfl, rfl⟩), fun _ => ⟨?_, ?_⟩⟩
    · intro z hz
      cases z <;> simp [orbitGapEdge] at hz
      exact ⟨.leaf, trivial, (orbitGap_step_bot_iff).mpr (Or.inl rfl)⟩
    · intro z hz
      cases z <;> simp [orbitGapEdge] at hz
      exact ⟨.leaf, trivial, (orbitGap_step_bot_iff).mpr (Or.inl rfl)⟩
  case b.a =>
    refine ⟨fun _ => Or.inr (Or.inr ⟨rfl, rfl⟩), fun _ => ⟨?_, ?_⟩⟩
    · intro z hz
      cases z <;> simp [orbitGapEdge] at hz
      exact ⟨.leaf, trivial, (orbitGap_step_bot_iff).mpr (Or.inl rfl)⟩
    · intro z hz
      cases z <;> simp [orbitGapEdge] at hz
      exact ⟨.leaf, trivial, (orbitGap_step_bot_iff).mpr (Or.inl rfl)⟩
  case marker.a =>
    refine ⟨?_, ?_⟩
    · intro h
      obtain ⟨w, hw, hS⟩ := h.1 .a trivial
      have hw' : w = .leaf := by
        cases w <;> simp [orbitGapEdge] at hw
        rfl
      rw [hw'] at hS
      have hbot := (orbitGap_step_bot_iff).mp hS
      rcases hbot with hEq | ⟨_, hy⟩ | ⟨hx, _⟩
      · cases hEq
      · cases hy
      · cases hx
    · intro hbad
      exact absurd hbad (by decide)
  case marker.b =>
    refine ⟨?_, ?_⟩
    · intro h
      obtain ⟨w, hw, hS⟩ := h.1 .a trivial
      have hw' : w = .leaf := by
        cases w <;> simp [orbitGapEdge] at hw
        rfl
      rw [hw'] at hS
      have hbot := (orbitGap_step_bot_iff).mp hS
      rcases hbot with hEq | ⟨_, hy⟩ | ⟨hx, _⟩
      · cases hEq
      · cases hy
      · cases hx
    · intro hbad
      exact absurd hbad (by decide)
  case marker.leaf =>
    refine ⟨?_, ?_⟩
    · intro h
      obtain ⟨w, hw, _⟩ := h.1 .a trivial
      cases w <;> simp [orbitGapEdge] at hw
    · intro hbad
      exact absurd hbad (by decide)
  case a.marker =>
    refine ⟨?_, ?_⟩
    · intro h
      obtain ⟨w, hw, hS⟩ := h.2 .a trivial
      have hw' : w = .leaf := by
        cases w <;> simp [orbitGapEdge] at hw
        rfl
      rw [hw'] at hS
      rcases (orbitGap_step_bot_iff).mp hS with hEq | ⟨hx, _⟩ | ⟨hx, _⟩
      · cases hEq
      · cases hx
      · cases hx
    · intro hbad
      exact absurd hbad (by decide)
  case a.leaf =>
    refine ⟨?_, ?_⟩
    · intro h
      obtain ⟨w, hw, _⟩ := h.1 .leaf trivial
      cases w <;> simp [orbitGapEdge] at hw
    · intro hbad
      exact absurd hbad (by decide)
  case b.marker =>
    refine ⟨?_, ?_⟩
    · intro h
      obtain ⟨w, hw, hS⟩ := h.2 .a trivial
      have hw' : w = .leaf := by
        cases w <;> simp [orbitGapEdge] at hw
        rfl
      rw [hw'] at hS
      rcases (orbitGap_step_bot_iff).mp hS with hEq | ⟨hx, _⟩ | ⟨hx, _⟩
      · cases hEq
      · cases hx
      · cases hx
    · intro hbad
      exact absurd hbad (by decide)
  case b.leaf =>
    refine ⟨?_, ?_⟩
    · intro h
      obtain ⟨w, hw, _⟩ := h.1 .leaf trivial
      cases w <;> simp [orbitGapEdge] at hw
    · intro hbad
      exact absurd hbad (by decide)
  case leaf.marker =>
    refine ⟨?_, ?_⟩
    · intro h
      obtain ⟨w, hw, _⟩ := h.2 .a trivial
      cases w <;> simp [orbitGapEdge] at hw
    · intro hbad
      exact absurd hbad (by decide)
  case leaf.a =>
    refine ⟨?_, ?_⟩
    · intro h
      obtain ⟨w, hw, _⟩ := h.2 .leaf trivial
      cases w <;> simp [orbitGapEdge] at hw
    · intro hbad
      exact absurd hbad (by decide)
  case leaf.b =>
    refine ⟨?_, ?_⟩
    · intro h
      obtain ⟨w, hw, _⟩ := h.2 .leaf trivial
      cases w <;> simp [orbitGapEdge] at hw
    · intro hbad
      exact absurd hbad (by decide)

/-- One application of `step` to the automorphism kernel is a reading of the counterexample. -/
theorem orbitGap_iterate_reading :
    step orbitGapEdge (step orbitGapEdge (automorphismKernel orbitGapEdge)) =
      step orbitGapEdge (automorphismKernel orbitGapEdge) := by
  rw [automorphismKernel_eq_bot]
  apply Setoid.ext
  intro x y
  rw [orbitGap_step_reading_iff, orbitGap_step_bot_iff]

end Mettapedia.SetTheory.AntiFoundation
