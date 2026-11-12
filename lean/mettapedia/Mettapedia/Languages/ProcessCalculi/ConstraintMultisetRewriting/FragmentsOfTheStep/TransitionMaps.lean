import Mettapedia.OSLF.Framework.DerivedModalities
import Mettapedia.GSLT.Core.FunctionalBisimulation

/-!
# Maps of transition systems: observations, open maps and their lifts

An **observation** of a transition system is a view of its states. The observed system steps
between two views when some step joins states with those views (`observed`). The identity view is
the system itself (`observed_id`). Views compose, and so do their properties below.

A map of states is a **functional bisimulation** when it carries steps to steps (`Zig`) and every
step out of an image lifts to a step whose end maps to that step's end (`Zag`). `Zag` is the
path-lifting condition that makes a map of transition systems open in the sense of Joyal, Nielsen and
Winskel, here for paths of length one; it lifts every finite path (`Zag.path`). A map is a functional
bisimulation exactly when its graph is a strong bisimulation between the two systems
(`graph_isBisimulation_iff`).

* **The image is the quotient.** For an onto functional bisimulation, the target's step is the image
  of the source's step (`step_eq_image`): the target is the source read up to the kernel of the map.
  Lifts are unique up to that kernel; whether they are unique up to something finer is a property of
  the kernel, settled for each narrowing separately.
* **OSLF types.** The possibility modality of a reduction span (`derivedDiamond`) and the necessity
  of every successor (`derivedForwardBox`) commute with pulling a predicate back along a functional
  bisimulation (`pb_diamond`, `pb_forwardBox`), and commuting with the possibility of every predicate
  characterizes functional bisimulations (`functionalBisimulation_iff_pb_diamond`).
* **GSLT.** As discrete-equation theories, a functional bisimulation carries bisimilar states to
  bisimilar states (by the tree's `bisimilar_map_of_zigzag`) and reflects bisimilarity
  (`bisimilar_iff_map`), and it is a `GSLT.Morphism` (`morphism`).

## Controls

* `Controls.zig_without_zag`: a map that carries steps but does not lift them; possibility does not
  commute with pullback there.
* `Controls.past_not_preserved`: a functional bisimulation along which the past modality
  (`derivedBox`, every predecessor) does not commute with pullback. A map that lifts futures need not
  lift pasts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.TransitionMaps

open Mettapedia.OSLF.Framework.DerivedModalities

universe u v w

section Maps

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- Steps are carried to steps. -/
def Zig (stepX : X → X → Prop) (stepY : Y → Y → Prop) (map : X → Y) : Prop :=
  ∀ {x x' : X}, stepX x x' → stepY (map x) (map x')

/-- Every step out of an image lifts to a step ending over its end. -/
def Zag (stepX : X → X → Prop) (stepY : Y → Y → Prop) (map : X → Y) : Prop :=
  ∀ {x : X} {y' : Y}, stepY (map x) y' → ∃ x', stepX x x' ∧ map x' = y'

/-- **A functional bisimulation**: steps are carried, and steps out of images lift. -/
structure FunctionalBisimulation (stepX : X → X → Prop) (stepY : Y → Y → Prop) (map : X → Y) :
    Prop where
  zig : Zig stepX stepY map
  zag : Zag stepX stepY map

/-- A strong bisimulation between two systems. -/
def IsBisimulation (stepX : X → X → Prop) (stepY : Y → Y → Prop) (R : X → Y → Prop) : Prop :=
  (∀ {x : X} {y : Y} {x' : X}, R x y → stepX x x' → ∃ y', stepY y y' ∧ R x' y') ∧
    (∀ {x : X} {y y' : Y}, R x y → stepY y y' → ∃ x', stepX x x' ∧ R x' y')

/-- **A map is a functional bisimulation exactly when its graph is a strong bisimulation.** -/
theorem graph_isBisimulation_iff {stepX : X → X → Prop} {stepY : Y → Y → Prop} {map : X → Y} :
    IsBisimulation stepX stepY (fun x y => map x = y) ↔ FunctionalBisimulation stepX stepY map := by
  constructor
  · rintro ⟨forward, backward⟩
    refine ⟨fun {x x'} step => ?_, fun {x y'} step => backward rfl step⟩
    obtain ⟨y', step', same⟩ := forward rfl step
    exact same ▸ step'
  · rintro ⟨zig, zag⟩
    refine ⟨fun {x y x'} same step => ⟨map x', same ▸ zig step, rfl⟩, ?_⟩
    rintro x y y' rfl step
    exact zag step

theorem FunctionalBisimulation.id (step : X → X → Prop) : FunctionalBisimulation step step id :=
  ⟨fun step' => step', fun {_ y'} step' => ⟨y', step', rfl⟩⟩

theorem FunctionalBisimulation.comp {stepX : X → X → Prop} {stepY : Y → Y → Prop}
    {stepZ : Z → Z → Prop} {first : X → Y} {second : Y → Z}
    (inner : FunctionalBisimulation stepX stepY first)
    (outer : FunctionalBisimulation stepY stepZ second) :
    FunctionalBisimulation stepX stepZ (second ∘ first) := by
  refine ⟨fun step => outer.zig (inner.zig step), fun {x z'} step => ?_⟩
  obtain ⟨y', stepY', toZ⟩ := outer.zag step
  obtain ⟨x', stepX', toY⟩ := inner.zag stepY'
  exact ⟨x', stepX', by simp [Function.comp, toY, toZ]⟩

/-- Steps carried one at a time carry paths. -/
theorem Zig.path {stepX : X → X → Prop} {stepY : Y → Y → Prop} {map : X → Y}
    (zig : Zig stepX stepY map) {x x' : X} (path : Relation.ReflTransGen stepX x x') :
    Relation.ReflTransGen stepY (map x) (map x') := by
  induction path with
  | refl => exact .refl
  | tail _ last earlier => exact earlier.tail (zig last)

/-- **Open maps lift paths**: lifting one step at a time lifts every finite path. -/
theorem Zag.path {stepX : X → X → Prop} {stepY : Y → Y → Prop} {map : X → Y}
    (zag : Zag stepX stepY map) {y y' : Y} (path : Relation.ReflTransGen stepY y y') :
    ∀ x, map x = y → ∃ x', Relation.ReflTransGen stepX x x' ∧ map x' = y' := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun x same => ⟨x, .refl, same⟩
  | head first _ later =>
      intro x same
      subst same
      obtain ⟨x₁, step, mapped⟩ := zag first
      obtain ⟨x', rest, last⟩ := later x₁ mapped
      exact ⟨x', .head step rest, last⟩

/-- **The image is the quotient**: for an onto functional bisimulation the target's step is exactly
the image of the source's step. -/
theorem step_eq_image {stepX : X → X → Prop} {stepY : Y → Y → Prop} {map : X → Y}
    (bisimulation : FunctionalBisimulation stepX stepY map) (onto : Function.Surjective map) :
    ∀ y y', stepY y y' ↔ ∃ x x', map x = y ∧ map x' = y' ∧ stepX x x' := by
  intro y y'
  constructor
  · intro step
    obtain ⟨x, rfl⟩ := onto y
    obtain ⟨x', step', mapped⟩ := bisimulation.zag step
    exact ⟨x, x', rfl, mapped, step'⟩
  · rintro ⟨x, x', rfl, rfl, step⟩
    exact bisimulation.zig step

end Maps

/-! ## Observations -/

section Observations

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- The system seen through a view: a step between two views when some step joins states with
those views. -/
def observed (step : X → X → Prop) (view : X → Y) : Y → Y → Prop :=
  fun y y' => ∃ x x', view x = y ∧ view x' = y' ∧ step x x'

/-- **The identity view is the system itself.** -/
theorem observed_id (step : X → X → Prop) : observed step id = step := by
  funext x x'
  apply propext
  constructor
  · rintro ⟨a, b, rfl, rfl, s⟩
    exact s
  · intro s
    exact ⟨x, x', rfl, rfl, s⟩

theorem zig_observed (step : X → X → Prop) (view : X → Y) : Zig step (observed step view) view :=
  fun {x x'} s => ⟨x, x', rfl, rfl, s⟩

/-- Views compose. -/
theorem observed_comp (step : X → X → Prop) (first : X → Y) (second : Y → Z) :
    observed step (second ∘ first) = observed (observed step first) second := by
  funext z z'
  apply propext
  constructor
  · rintro ⟨x, x', rfl, rfl, s⟩
    exact ⟨first x, first x', rfl, rfl, x, x', rfl, rfl, s⟩
  · rintro ⟨y, y', rfl, rfl, x, x', rfl, rfl, s⟩
    exact ⟨x, x', rfl, rfl, s⟩

/-- A view is a functional bisimulation onto what it observes exactly when observed steps lift. -/
theorem functionalBisimulation_observed_iff (step : X → X → Prop) (view : X → Y) :
    FunctionalBisimulation step (observed step view) view ↔ Zag step (observed step view) view :=
  ⟨fun b => b.zag, fun zag => ⟨zig_observed step view, zag⟩⟩

end Observations

/-! ## OSLF types along a functional bisimulation -/

section OSLF

variable {X : Type u} {Y : Type v}

/-- The reduction span of a step relation. -/
def span (step : X → X → Prop) : ReductionSpan X where
  Edge := {pair : X × X // step pair.1 pair.2}
  source edge := edge.val.1
  target edge := edge.val.2

theorem diamond_iff (step : X → X → Prop) (φ : X → Prop) (x : X) :
    derivedDiamond (span step) φ x ↔ ∃ x', step x x' ∧ φ x' := by
  constructor
  · rintro ⟨⟨⟨a, b⟩, s⟩, rfl, holds⟩
    exact ⟨b, s, holds⟩
  · rintro ⟨x', s, holds⟩
    exact ⟨⟨(x, x'), s⟩, rfl, holds⟩

theorem forwardBox_iff (step : X → X → Prop) (φ : X → Prop) (x : X) :
    derivedForwardBox (span step) φ x ↔ ∀ x', step x x' → φ x' := by
  constructor
  · intro all x' s
    exact all ⟨(x, x'), s⟩ rfl
  · rintro all ⟨⟨a, b⟩, s⟩ rfl
    exact all b s

theorem box_iff (step : X → X → Prop) (φ : X → Prop) (x : X) :
    derivedBox (span step) φ x ↔ ∀ x', step x' x → φ x' := by
  constructor
  · intro all x' s
    exact all ⟨(x', x), s⟩ rfl
  · rintro all ⟨⟨a, b⟩, s⟩ rfl
    exact all a s

variable {stepX : X → X → Prop} {stepY : Y → Y → Prop} {map : X → Y}

/-- **Possibility pulls back**: along a functional bisimulation, the possibility type of the target
pulled back is the possibility type of the source of the pulled-back predicate. -/
theorem pb_diamond (bisimulation : FunctionalBisimulation stepX stepY map) (φ : Y → Prop) :
    pb map (derivedDiamond (span stepY) φ) = derivedDiamond (span stepX) (pb map φ) := by
  funext x
  apply propext
  change derivedDiamond (span stepY) φ (map x) ↔ _
  rw [diamond_iff, diamond_iff]
  constructor
  · rintro ⟨y', s, holds⟩
    obtain ⟨x', s', rfl⟩ := bisimulation.zag s
    exact ⟨x', s', holds⟩
  · rintro ⟨x', s, holds⟩
    exact ⟨map x', bisimulation.zig s, holds⟩

/-- **Necessity of every successor pulls back** along a functional bisimulation. -/
theorem pb_forwardBox (bisimulation : FunctionalBisimulation stepX stepY map) (φ : Y → Prop) :
    pb map (derivedForwardBox (span stepY) φ) = derivedForwardBox (span stepX) (pb map φ) := by
  funext x
  apply propext
  change derivedForwardBox (span stepY) φ (map x) ↔ _
  rw [forwardBox_iff, forwardBox_iff]
  constructor
  · intro all x' s
    exact all (map x') (bisimulation.zig s)
  · intro all y' s
    obtain ⟨x', s', rfl⟩ := bisimulation.zag s
    exact all x' s'

/-- **Commuting with possibility characterizes functional bisimulations.** -/
theorem functionalBisimulation_iff_pb_diamond :
    FunctionalBisimulation stepX stepY map ↔
      ∀ φ : Y → Prop, pb map (derivedDiamond (span stepY) φ) = derivedDiamond (span stepX) (pb map φ) := by
  refine ⟨fun bisimulation φ => pb_diamond bisimulation φ, fun commutes => ⟨?_, ?_⟩⟩
  · intro x x' s
    have here : derivedDiamond (span stepX) (pb map (· = map x')) x :=
      (diamond_iff stepX _ x).mpr ⟨x', s, rfl⟩
    rw [← commutes] at here
    obtain ⟨y', s', same⟩ := (diamond_iff stepY _ (map x)).mp here
    exact same ▸ s'
  · intro x y' s
    have here : pb map (derivedDiamond (span stepY) (· = y')) x :=
      (diamond_iff stepY _ (map x)).mpr ⟨y', s, rfl⟩
    rw [commutes] at here
    obtain ⟨x', s', same⟩ := (diamond_iff stepX _ x).mp here
    exact ⟨x', s', same⟩

end OSLF

/-! ## Discrete-equation theories -/

section GSLT

open Mettapedia.GSLT

variable {X : Type u} {Y : Type u}

/-- A step relation as a theory with discrete equations. -/
def theoryOf (X : Type u) (step : X → X → Prop) : GSLT.{u} where
  Term := X
  equations := ⟨Eq, eq_equivalence⟩
  rewrites := step
  rewrites_resp_left := by
    intro t t' u same s
    exact ⟨u, (same : t = t') ▸ s, rfl⟩
  rewrites_resp_right := by
    intro t u u' s same
    exact (same : u = u') ▸ s

variable {stepX : X → X → Prop} {stepY : Y → Y → Prop} {map : X → Y}

theorem bisimilar_map (bisimulation : FunctionalBisimulation stepX stepY map) {x x' : X}
    (same : (theoryOf X stepX).Bisimilar x x') : (theoryOf Y stepY).Bisimilar (map x) (map x') :=
  GSLT.bisimilar_map_of_zigzag (source := theoryOf X stepX) (target := theoryOf Y stepY) map
    (fun s => bisimulation.zig s)
    (fun {_ next} s => by
      obtain ⟨x', s', mapped⟩ := bisimulation.zag s
      exact ⟨x', s', mapped ▸ (theoryOf Y stepY).bisimilar_refl _⟩)
    same

/-- **A functional bisimulation reflects bisimilarity.** -/
theorem bisimilar_of_map (bisimulation : FunctionalBisimulation stepX stepY map) {x x' : X}
    (same : (theoryOf Y stepY).Bisimilar (map x) (map x')) : (theoryOf X stepX).Bisimilar x x' := by
  obtain ⟨R, ⟨forward, backward⟩, related⟩ := same
  refine ⟨fun a b => R (map a) (map b), ⟨?_, ?_⟩, related⟩
  · intro a b ab a' s
    obtain ⟨y', s', related'⟩ := forward ab (bisimulation.zig s)
    obtain ⟨b', sb, rfl⟩ := bisimulation.zag s'
    exact ⟨b', sb, related'⟩
  · intro a b ab b' s
    obtain ⟨y', s', related'⟩ := backward ab (bisimulation.zig s)
    obtain ⟨a', sa, rfl⟩ := bisimulation.zag s'
    exact ⟨a', sa, related'⟩

/-- **Bisimilarity is read the same through a functional bisimulation.** -/
theorem bisimilar_iff_map (bisimulation : FunctionalBisimulation stepX stepY map) {x x' : X} :
    (theoryOf X stepX).Bisimilar x x' ↔ (theoryOf Y stepY).Bisimilar (map x) (map x') :=
  ⟨bisimilar_map bisimulation, bisimilar_of_map bisimulation⟩

/-- A functional bisimulation as a behavioural morphism of theories. -/
def morphism (bisimulation : FunctionalBisimulation stepX stepY map) :
    GSLT.Morphism (theoryOf X stepX) (theoryOf Y stepY) where
  toFun := map
  preserves_bisim := bisimilar_map bisimulation

end GSLT

/-! ## Controls -/

namespace Controls

/-- No steps. -/
def still : Bool → Bool → Prop := fun _ _ => False

/-- One step, from `false` to `true`. -/
def rises : Bool → Bool → Prop := fun b b' => b = false ∧ b' = true

/-- **Control.** The identity carries every step of the stepless system but lifts none of the
rising system's, and possibility does not commute with pullback. -/
theorem zig_without_zag :
    Zig still rises id ∧ ¬ Zag still rises id ∧
      pb id (derivedDiamond (span rises) (· = true)) false ∧
      ¬ derivedDiamond (span still) (pb id (· = true)) false := by
  refine ⟨fun s => absurd s id, fun zag => ?_, (diamond_iff rises _ false).mpr ⟨true, ⟨rfl, rfl⟩, rfl⟩, ?_⟩
  · obtain ⟨_, s, _⟩ := zag (x := false) (y' := true) ⟨rfl, rfl⟩
    exact s
  · intro holds
    obtain ⟨_, s, _⟩ := (diamond_iff still _ false).mp holds
    exact s

/-- Source: `0 → 1`, with `2` apart. -/
def source : Fin 3 → Fin 3 → Prop := fun a b => a = 0 ∧ b = 1

/-- Target: `false → true`. -/
def target : Bool → Bool → Prop := rises

/-- `0` to `false`; `1` and `2` to `true`. -/
def collapse : Fin 3 → Bool := fun a => decide (a ≠ 0)

theorem collapse_bisimulation : FunctionalBisimulation source target collapse := by
  refine ⟨?_, ?_⟩
  · rintro a b ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩
  · intro a y' s
    obtain ⟨starts, rfl⟩ := s
    have zero : a = 0 := by
      by_contra other
      simp [collapse, other] at starts
    subst zero
    exact ⟨1, ⟨rfl, rfl⟩, rfl⟩

/-- **Control.** A functional bisimulation along which the past modality does not commute with
pullback: `2` lies over `true`, which has a predecessor, while `2` has none. -/
theorem past_not_preserved :
    FunctionalBisimulation source target collapse ∧
      pb collapse (derivedBox (span target) (· ≠ false)) ≠
        derivedBox (span source) (pb collapse (· ≠ false)) := by
  refine ⟨collapse_bisimulation, fun same => ?_⟩
  have atTwo := congrFun same 2
  have vacuous : derivedBox (span source) (pb collapse (· ≠ false)) 2 :=
    (box_iff source _ 2).mpr (fun x' s => absurd s.2 (by decide))
  rw [← atTwo] at vacuous
  have fromFalse := (box_iff target _ (collapse 2)).mp vacuous false ⟨rfl, by decide⟩
  exact fromFalse rfl

end Controls

#print axioms graph_isBisimulation_iff
#print axioms FunctionalBisimulation.comp
#print axioms Zag.path
#print axioms step_eq_image
#print axioms observed_id
#print axioms observed_comp
#print axioms pb_diamond
#print axioms pb_forwardBox
#print axioms functionalBisimulation_iff_pb_diamond
#print axioms bisimilar_iff_map
#print axioms Controls.zig_without_zag
#print axioms Controls.past_not_preserved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.TransitionMaps
