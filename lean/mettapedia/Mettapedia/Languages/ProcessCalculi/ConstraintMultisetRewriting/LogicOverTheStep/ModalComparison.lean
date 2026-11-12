import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.TransitionMaps

/-!
# Comparing OSLF's modalities along maps: which half needs which lifting

OSLF derives its modalities from a reduction span `E ⇉ X` by change of base
(`DerivedModalities`): possibility `◇ = ∃_src ∘ tgt*`, **successor necessity**
`derivedForwardBox = ∀_src ∘ tgt*` (every successor), and **predecessor necessity**
`derivedBox = ∀_tgt ∘ src*` (every predecessor), the right adjoint of `◇`. The two necessities are
different modalities and are transported under different conditions.

## Beck–Chevalley in the fibration of predicates, square by square

For a commuting square `g ∘ k = h ∘ f` of maps of sets, reindexing and the quantifiers satisfy one
implication always (`di_pb_le`, `pb_ui_le`). The Beck–Chevalley **equality** holds exactly when the
square is a weak pullback (`beckChevalley_di_iff`, `beckChevalley_ui_iff`); for an arbitrary
commuting square only the implication is available. For a morphism of reduction spans this gives
the modal comparison: possibility is always carried forward (`SpanMap.diamond_le`), and is reflected
when the source square is a weak pullback (`SpanMap.diamond_eq`).

## Along a map of transition systems, half by half

* `zig_iff_diamond_le`: a map carries steps exactly when possibility is laxly preserved,
  `◇ (h* φ) ≤ h* (◇ φ)`; `zag_iff_le_diamond`: it lifts steps out of images exactly when the
  converse holds. Together they give `TransitionMaps.pb_diamond`.
* Successor necessity: `zig_iff_le_forwardBox` and `zag_iff_forwardBox_le`.
* Predecessor necessity needs **backward** lifting (`BackZag`: every predecessor of an image lifts
  to a predecessor): `zig_iff_le_predecessorBox` and `backZag_iff_predecessorBox_le`, together
  `predecessorBox_pb_iff`. Lifting the future does not lift the past;
  `TransitionMaps.Controls.past_not_preserved` is an open map along which predecessor necessity is
  not transported.
* `pb_modal_hom`: along an open map, reindexing is a homomorphism of modal algebras: it commutes
  with possibility, successor necessity and the Boolean operations, so with every predicate built
  from them.

## Bisimulations are spans of open maps

`isBisimulation_iff_projections_open`: a relation is a strong bisimulation exactly when both
projections of its graph lift steps (Joyal, Nielsen and Winskel). So along a bisimulation every
modality pulls back to the graph from both sides (`graph_diamond_left`, `graph_diamond_right`), and
related states satisfy possibility together for observations that agree along the relation
(`diamond_iff_of_bisimulation`).

## Controls

* `Controls.zig_only_strict`: a map that carries steps and lifts none; only the implication holds.
* `Controls.not_weak_pullback`: a commuting square that is not a weak pullback, with the
  Beck–Chevalley equality failing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ModalComparison

open Mettapedia.OSLF.Framework.DerivedModalities
open FragmentsOfTheStep.TransitionMaps

universe u v w z

/-! ## Beck–Chevalley in the fibration of predicates -/

section BeckChevalley

variable {E : Type u} {X : Type v} {E' : Type w} {X' : Type z}

/-- **A weak pullback square** `g ∘ k = h ∘ f`: every pair agreeing in the corner comes from the
apex, up to equality of its two legs. -/
def WeakPullback (f : E → X) (g : E' → X') (h : X → X') (k : E → E') : Prop :=
  ∀ (x : X) (e' : E'), g e' = h x → ∃ e, f e = x ∧ k e = e'

variable {f : E → X} {g : E' → X'} {h : X → X'} {k : E → E'}

/-- Reindexing after direct image dominates direct image after reindexing, for every commuting
square. -/
theorem di_pb_le (square : ∀ e, g (k e) = h (f e)) (ψ : E' → Prop) :
    di f (pb k ψ) ≤ pb h (di g ψ) := by
  rintro x ⟨e, rfl, holds⟩
  exact ⟨k e, square e, holds⟩

/-- Universal image after reindexing dominates reindexing after universal image, for every
commuting square. -/
theorem pb_ui_le (square : ∀ e, g (k e) = h (f e)) (ψ : E' → Prop) :
    pb h (ui g ψ) ≤ ui f (pb k ψ) := by
  intro x all e same
  exact all (k e) (by rw [square e, same])

/-- **Beck–Chevalley for direct image**: the equality holds for every predicate exactly when the
commuting square is a weak pullback. -/
theorem beckChevalley_di_iff (square : ∀ e, g (k e) = h (f e)) :
    WeakPullback f g h k ↔ ∀ ψ : E' → Prop, pb h (di g ψ) = di f (pb k ψ) := by
  constructor
  · intro weak ψ
    funext x
    apply propext
    constructor
    · rintro ⟨e', meets, holds⟩
      obtain ⟨e, rfl, rfl⟩ := weak x e' meets
      exact ⟨e, rfl, holds⟩
    · exact di_pb_le square ψ x
  · intro equal x e' meets
    have here : pb h (di g (· = e')) x := ⟨e', meets, rfl⟩
    rw [equal] at here
    obtain ⟨e, sameSource, sameEdge⟩ := here
    exact ⟨e, sameSource, sameEdge⟩

/-- **Beck–Chevalley for universal image**: the equality holds for every predicate exactly when the
commuting square is a weak pullback. -/
theorem beckChevalley_ui_iff (square : ∀ e, g (k e) = h (f e)) :
    WeakPullback f g h k ↔ ∀ ψ : E' → Prop, pb h (ui g ψ) = ui f (pb k ψ) := by
  constructor
  · intro weak ψ
    funext x
    apply propext
    constructor
    · exact pb_ui_le square ψ x
    · intro all e' meets
      obtain ⟨e, rfl, rfl⟩ := weak x e' meets
      exact all e rfl
  · intro equal x e' meets
    by_contra missing
    have here : ui f (pb k (· ≠ e')) x := by
      intro e same sameEdge
      exact missing ⟨e, same, sameEdge⟩
    rw [← equal] at here
    exact here e' meets rfl

end BeckChevalley

/-! ## Morphisms of reduction spans -/

section Spans

variable {X : Type u} {Y : Type v}

/-- **A morphism of reduction spans** over a map of states: edges to edges, sources to sources and
targets to targets. -/
structure SpanMap (SX : ReductionSpan X) (SY : ReductionSpan Y) (h : X → Y) where
  edge : SX.Edge → SY.Edge
  source : ∀ e, SY.source (edge e) = h (SX.source e)
  target : ∀ e, SY.target (edge e) = h (SX.target e)

variable {SX : ReductionSpan X} {SY : ReductionSpan Y} {h : X → Y}

/-- **Possibility is carried forward along every morphism of spans.** -/
theorem SpanMap.diamond_le (m : SpanMap SX SY h) (φ : Y → Prop) :
    derivedDiamond SX (pb h φ) ≤ pb h (derivedDiamond SY φ) := by
  rintro x ⟨e, rfl, holds⟩
  refine ⟨m.edge e, m.source e, ?_⟩
  show φ (SY.target (m.edge e))
  rw [m.target e]
  exact holds

/-- **Possibility is reflected when the source square is a weak pullback.** -/
theorem SpanMap.diamond_eq (m : SpanMap SX SY h) (weak : WeakPullback SX.source SY.source h m.edge)
    (φ : Y → Prop) : pb h (derivedDiamond SY φ) = derivedDiamond SX (pb h φ) := by
  funext x
  apply propext
  constructor
  · rintro ⟨e', meets, holds⟩
    obtain ⟨e, rfl, rfl⟩ := weak x e' meets
    refine ⟨e, rfl, ?_⟩
    show φ (h (SX.target e))
    rw [← m.target e]
    exact holds
  · exact m.diamond_le φ x

/-- **Successor necessity is carried backward along every morphism of spans.** -/
theorem SpanMap.le_forwardBox (m : SpanMap SX SY h) (φ : Y → Prop) :
    pb h (derivedForwardBox SY φ) ≤ derivedForwardBox SX (pb h φ) := by
  intro x all e same
  show φ (h (SX.target e))
  rw [← m.target e]
  exact all (m.edge e) (by rw [m.source e, same])

end Spans

/-! ## Along a map of transition systems, half by half -/

section Halves

variable {X : Type u} {Y : Type v} {stepX : X → X → Prop} {stepY : Y → Y → Prop} {h : X → Y}

/-- **Every predecessor of an image lifts** to a predecessor ending at the point. -/
def BackZag (stepX : X → X → Prop) (stepY : Y → Y → Prop) (h : X → Y) : Prop :=
  ∀ {x : X} {y : Y}, stepY y (h x) → ∃ x', stepX x' x ∧ h x' = y

/-- **Carrying steps is lax preservation of possibility.** -/
theorem zig_iff_diamond_le :
    Zig stepX stepY h ↔
      ∀ φ : Y → Prop, derivedDiamond (span stepX) (pb h φ) ≤ pb h (derivedDiamond (span stepY) φ) := by
  constructor
  · intro zig φ x holds
    obtain ⟨x', s, there⟩ := (diamond_iff stepX _ x).mp holds
    exact (diamond_iff stepY φ (h x)).mpr ⟨h x', zig s, there⟩
  · intro le x x' s
    have here := le (· = h x') x ((diamond_iff stepX _ x).mpr ⟨x', s, rfl⟩)
    obtain ⟨y', s', rfl⟩ := (diamond_iff stepY _ (h x)).mp here
    exact s'

/-- **Lifting steps out of images is the converse comparison of possibility.** -/
theorem zag_iff_le_diamond :
    Zag stepX stepY h ↔
      ∀ φ : Y → Prop, pb h (derivedDiamond (span stepY) φ) ≤ derivedDiamond (span stepX) (pb h φ) := by
  constructor
  · intro zag φ x holds
    obtain ⟨y', s, there⟩ := (diamond_iff stepY φ (h x)).mp holds
    obtain ⟨x', s', rfl⟩ := zag s
    exact (diamond_iff stepX _ x).mpr ⟨x', s', there⟩
  · intro le x y' s
    have here := le (· = y') x ((diamond_iff stepY _ (h x)).mpr ⟨y', s, rfl⟩)
    exact (diamond_iff stepX _ x).mp here

/-- **Carrying steps is the comparison of successor necessity from the target.** -/
theorem zig_iff_le_forwardBox :
    Zig stepX stepY h ↔
      ∀ φ : Y → Prop,
        pb h (derivedForwardBox (span stepY) φ) ≤ derivedForwardBox (span stepX) (pb h φ) := by
  constructor
  · intro zig φ x all
    exact (forwardBox_iff stepX _ x).mpr fun x' s =>
      (forwardBox_iff stepY φ (h x)).mp all (h x') (zig s)
  · intro le x x' s
    by_contra missing
    have here : pb h (derivedForwardBox (span stepY) (· ≠ h x')) x :=
      (forwardBox_iff stepY _ (h x)).mpr fun y' s' same => missing (same ▸ s')
    exact (forwardBox_iff stepX _ x).mp (le _ x here) x' s rfl

/-- **Lifting steps out of images is the comparison of successor necessity into the target.** -/
theorem zag_iff_forwardBox_le :
    Zag stepX stepY h ↔
      ∀ φ : Y → Prop,
        derivedForwardBox (span stepX) (pb h φ) ≤ pb h (derivedForwardBox (span stepY) φ) := by
  constructor
  · intro zag φ x all
    refine (forwardBox_iff stepY φ (h x)).mpr fun y' s => ?_
    obtain ⟨x', s', rfl⟩ := zag s
    exact (forwardBox_iff stepX _ x).mp all x' s'
  · intro le x y' s
    by_contra missing
    have here : derivedForwardBox (span stepX) (pb h (· ≠ y')) x :=
      (forwardBox_iff stepX _ x).mpr fun x' s' same => missing ⟨x', s', same⟩
    exact (forwardBox_iff stepY _ (h x)).mp (le _ x here) y' s rfl

/-- **Carrying steps is the comparison of predecessor necessity from the target.** -/
theorem zig_iff_le_predecessorBox :
    Zig stepX stepY h ↔
      ∀ φ : Y → Prop, pb h (derivedBox (span stepY) φ) ≤ derivedBox (span stepX) (pb h φ) := by
  constructor
  · intro zig φ x all
    exact (box_iff stepX _ x).mpr fun x' s => (box_iff stepY φ (h x)).mp all (h x') (zig s)
  · intro le x x' s
    by_contra missing
    have here : pb h (derivedBox (span stepY) (· ≠ h x)) x' :=
      (box_iff stepY _ (h x')).mpr fun y s' same => missing (same ▸ s')
    exact (box_iff stepX _ x').mp (le _ x' here) x s rfl

/-- **Lifting predecessors is the comparison of predecessor necessity into the target.** -/
theorem backZag_iff_predecessorBox_le :
    BackZag stepX stepY h ↔
      ∀ φ : Y → Prop, derivedBox (span stepX) (pb h φ) ≤ pb h (derivedBox (span stepY) φ) := by
  constructor
  · intro back φ x all
    refine (box_iff stepY φ (h x)).mpr fun y s => ?_
    obtain ⟨x', s', rfl⟩ := back s
    exact (box_iff stepX _ x).mp all x' s'
  · intro le x y s
    by_contra missing
    have here : derivedBox (span stepX) (pb h (· ≠ y)) x :=
      (box_iff stepX _ x).mpr fun x' s' same => missing ⟨x', s', same⟩
    exact (box_iff stepY _ (h x)).mp (le _ x here) y s rfl

/-- **Predecessor necessity pulls back exactly along maps that carry steps and lift
predecessors.** -/
theorem predecessorBox_pb_iff :
    (Zig stepX stepY h ∧ BackZag stepX stepY h) ↔
      ∀ φ : Y → Prop, pb h (derivedBox (span stepY) φ) = derivedBox (span stepX) (pb h φ) := by
  constructor
  · rintro ⟨zig, back⟩ φ
    exact le_antisymm
      ((zig_iff_le_predecessorBox (stepX := stepX) (stepY := stepY) (h := h)).mp zig φ)
      ((backZag_iff_predecessorBox_le (stepX := stepX) (stepY := stepY) (h := h)).mp back φ)
  · intro equal
    exact ⟨(zig_iff_le_predecessorBox (stepX := stepX) (stepY := stepY) (h := h)).mpr
        fun φ => (equal φ).le,
      (backZag_iff_predecessorBox_le (stepX := stepX) (stepY := stepY) (h := h)).mpr
        fun φ => (equal φ).ge⟩

/-- **Reindexing along an open map is a homomorphism of modal algebras**: it commutes with
possibility, successor necessity and every Boolean operation, hence with every predicate built
from them. -/
theorem pb_modal_hom (bisimulation : FunctionalBisimulation stepX stepY h) :
    (∀ φ : Y → Prop, pb h (derivedDiamond (span stepY) φ) = derivedDiamond (span stepX) (pb h φ)) ∧
      (∀ φ : Y → Prop,
        pb h (derivedForwardBox (span stepY) φ) = derivedForwardBox (span stepX) (pb h φ)) ∧
      (∀ φ : Y → Prop, pb h φᶜ = (pb h φ)ᶜ) ∧
      (∀ φ ψ : Y → Prop, pb h (fun y => φ y ∧ ψ y) = fun x => pb h φ x ∧ pb h ψ x) ∧
      (∀ φ ψ : Y → Prop, pb h (fun y => φ y ∨ ψ y) = fun x => pb h φ x ∨ pb h ψ x) :=
  ⟨pb_diamond bisimulation, pb_forwardBox bisimulation, fun _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl⟩

end Halves

/-! ## Bisimulations are spans of open maps -/

section Graphs

variable {X : Type u} {Y : Type v} {stepX : X → X → Prop} {stepY : Y → Y → Prop}

/-- The graph of a relation. -/
abbrev Graph (R : X → Y → Prop) := {p : X × Y // R p.1 p.2}

/-- Steps of the graph: both sides step together. -/
def graphStep (stepX : X → X → Prop) (stepY : Y → Y → Prop) (R : X → Y → Prop)
    (p q : Graph R) : Prop :=
  stepX p.1.1 q.1.1 ∧ stepY p.1.2 q.1.2

/-- **A relation is a bisimulation exactly when both projections of its graph are open.** -/
theorem isBisimulation_iff_projections_open {R : X → Y → Prop} :
    IsBisimulation stepX stepY R ↔
      FunctionalBisimulation (graphStep stepX stepY R) stepX (fun p => p.1.1) ∧
        FunctionalBisimulation (graphStep stepX stepY R) stepY (fun p => p.1.2) := by
  constructor
  · rintro ⟨forth, back⟩
    refine ⟨⟨fun s => s.1, fun {p x'} s => ?_⟩, ⟨fun s => s.2, fun {p y'} s => ?_⟩⟩
    · obtain ⟨y', s', related⟩ := forth p.2 s
      exact ⟨⟨(x', y'), related⟩, ⟨s, s'⟩, rfl⟩
    · obtain ⟨x', s', related⟩ := back p.2 s
      exact ⟨⟨(x', y'), related⟩, ⟨s', s⟩, rfl⟩
  · rintro ⟨left, right⟩
    refine ⟨fun {x y x'} related s => ?_, fun {x y y'} related s => ?_⟩
    · have lift : ∀ {p : Graph R} {x' : X}, stepX p.1.1 x' →
          ∃ q, graphStep stepX stepY R p q ∧ q.1.1 = x' := left.zag
      obtain ⟨⟨⟨x₁, y₁⟩, related₁⟩, ⟨_, s'⟩, rfl⟩ := lift (p := ⟨(x, y), related⟩) s
      exact ⟨y₁, s', related₁⟩
    · have lift : ∀ {p : Graph R} {y' : Y}, stepY p.1.2 y' →
          ∃ q, graphStep stepX stepY R p q ∧ q.1.2 = y' := right.zag
      obtain ⟨⟨⟨x₁, y₁⟩, related₁⟩, ⟨s', _⟩, rfl⟩ := lift (p := ⟨(x, y), related⟩) s
      exact ⟨x₁, s', related₁⟩

variable {R : X → Y → Prop}

/-- Possibility pulls back to the graph of a bisimulation from the left. -/
theorem graph_diamond_left (bisimulation : IsBisimulation stepX stepY R) (φ : X → Prop) :
    pb (fun p : Graph R => p.1.1) (derivedDiamond (span stepX) φ) =
      derivedDiamond (span (graphStep stepX stepY R)) (pb (fun p : Graph R => p.1.1) φ) :=
  pb_diamond (isBisimulation_iff_projections_open.mp bisimulation).1 φ

/-- Possibility pulls back to the graph of a bisimulation from the right. -/
theorem graph_diamond_right (bisimulation : IsBisimulation stepX stepY R) (φ : Y → Prop) :
    pb (fun p : Graph R => p.1.2) (derivedDiamond (span stepY) φ) =
      derivedDiamond (span (graphStep stepX stepY R)) (pb (fun p : Graph R => p.1.2) φ) :=
  pb_diamond (isBisimulation_iff_projections_open.mp bisimulation).2 φ

/-- **Related states satisfy possibility together**, for observations that agree along the
relation. -/
theorem diamond_iff_of_bisimulation (bisimulation : IsBisimulation stepX stepY R)
    {ψ : X → Prop} {φ : Y → Prop} (agree : ∀ x y, R x y → (ψ x ↔ φ y)) {x : X} {y : Y}
    (related : R x y) : derivedDiamond (span stepX) ψ x ↔ derivedDiamond (span stepY) φ y := by
  rw [diamond_iff, diamond_iff]
  constructor
  · rintro ⟨x', s, holds⟩
    obtain ⟨y', s', related'⟩ := bisimulation.1 related s
    exact ⟨y', s', (agree x' y' related').mp holds⟩
  · rintro ⟨y', s, holds⟩
    obtain ⟨x', s', related'⟩ := bisimulation.2 related s
    exact ⟨x', s', (agree x' y' related').mpr holds⟩

/-- **Related states satisfy successor necessity together**, for observations that agree along
the relation. -/
theorem forwardBox_iff_of_bisimulation (bisimulation : IsBisimulation stepX stepY R)
    {ψ : X → Prop} {φ : Y → Prop} (agree : ∀ x y, R x y → (ψ x ↔ φ y)) {x : X} {y : Y}
    (related : R x y) : derivedForwardBox (span stepX) ψ x ↔ derivedForwardBox (span stepY) φ y := by
  rw [forwardBox_iff, forwardBox_iff]
  constructor
  · intro all y' s
    obtain ⟨x', s', related'⟩ := bisimulation.2 related s
    exact (agree x' y' related').mp (all x' s')
  · intro all x' s
    obtain ⟨y', s', related'⟩ := bisimulation.1 related s
    exact (agree x' y' related').mpr (all y' s')

end Graphs

/-! ## Controls -/

namespace Controls

/-- One state with no step, and one state with a loop. -/
def still : Unit → Unit → Prop := fun _ _ => False
def loop : Unit → Unit → Prop := fun _ _ => True

/-- **Control: only the implication.** The identity carries every step of the stepless system and
lifts none of the loop's: the lax square holds and the equality fails. -/
theorem zig_only_strict :
    Zig still loop id ∧
      (∀ φ : Unit → Prop, derivedDiamond (span still) (pb id φ) ≤ pb id (derivedDiamond (span loop) φ)) ∧
      pb id (derivedDiamond (span loop) (fun _ => True)) () ∧
      ¬ derivedDiamond (span still) (pb id (fun _ => True)) () := by
  refine ⟨fun s => absurd s id, zig_iff_diamond_le.mp fun s => absurd s id,
    (diamond_iff loop _ ()).mpr ⟨(), trivial, trivial⟩, fun holds => ?_⟩
  obtain ⟨_, s, _⟩ := (diamond_iff still _ ()).mp holds
  exact s

/-- The empty apex over a point. -/
def fromEmpty : Empty → Unit := fun e => e.elim

/-- **Control: a commuting square that is not a weak pullback.** The apex is empty over a point:
the implication holds and Beck–Chevalley fails. -/
theorem not_weak_pullback :
    (∀ e : Empty, id (fromEmpty e) = id (fromEmpty e)) ∧
      ¬ WeakPullback fromEmpty (id : Unit → Unit) (id : Unit → Unit) fromEmpty ∧
      pb (id : Unit → Unit) (di (id : Unit → Unit) (fun _ => True)) () ∧
      ¬ di fromEmpty (pb fromEmpty (fun _ : Unit => True)) () := by
  refine ⟨fun _ => rfl, fun weak => ?_, ⟨(), rfl, trivial⟩, fun holds => ?_⟩
  · obtain ⟨e, _, _⟩ := weak () () rfl
    exact e.elim
  · obtain ⟨e, _, _⟩ := holds
    exact e.elim

end Controls

#print axioms beckChevalley_di_iff
#print axioms beckChevalley_ui_iff
#print axioms SpanMap.diamond_le
#print axioms SpanMap.diamond_eq
#print axioms SpanMap.le_forwardBox
#print axioms zig_iff_diamond_le
#print axioms zag_iff_le_diamond
#print axioms zig_iff_le_forwardBox
#print axioms zag_iff_forwardBox_le
#print axioms zig_iff_le_predecessorBox
#print axioms backZag_iff_predecessorBox_le
#print axioms predecessorBox_pb_iff
#print axioms pb_modal_hom
#print axioms isBisimulation_iff_projections_open
#print axioms diamond_iff_of_bisimulation
#print axioms forwardBox_iff_of_bisimulation
#print axioms Controls.zig_only_strict
#print axioms Controls.not_weak_pullback

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ModalComparison
