import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ModalComparison
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface
import Mettapedia.GSLT.Logic.HennessyMilnerAdequacy

/-!
# The step's own reduction span

OSLF derives its modalities from a reduction span. The step has one of its own, proof-relevant:
its edges are the admitted firings, with their sources and results (`firingSpan`). Its image is the
successor relation (`Succ`).

* `toSucc`, `toSucc_source_weakPullback`, `toSucc_target_weakPullback`: the firing span maps onto
  the successor span, and both of its squares are weak pullbacks. So OSLF's possibility, successor
  necessity and predecessor necessity over firings are those of the successor relation
  (`firing_diamond_eq`, `firing_forwardBox_eq`, `firing_predecessorBox_eq`), and every comparison
  of `ModalComparison` applies to the step's own modalities. They read only which results are
  reachable; how many firings reach them is not seen by them.
* **Hennessy–Milner adequacy, by the tree's theorem.** `stepSystem` is the step as a system of the
  GSLT Hennessy–Milner library (`Mettapedia.GSLT.HennessyMilner`), with any observation set; its
  diamond is OSLF's possibility over the firing span (`sat_dia_iff`). Logical equivalence is
  bisimilarity whenever the successor sets have finite covers up to bisimilarity
  (`logicallyEquivalent_iff_bisimilar`). The cover is the hypothesis to discharge per step: a step
  that chooses fresh occurrence identities has infinitely many successors on the nose.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.StepSpan

open Interface
open Mettapedia.OSLF.Framework.DerivedModalities
open FragmentsOfTheStep.TransitionMaps
open ModalComparison

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} {X : Frames Tm Hom}
  {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (P : Interface.Step X O State Firing)

/-- **The step's reduction span**: its edges are the admitted firings. -/
def firingSpan : ReductionSpan State where
  Edge := Σ s : State, {f : Firing s // P.Admits f}
  source e := e.1
  target e := P.result e.2.1 e.2.2

/-- **The successor relation**: some admitted firing reaches the state. -/
def Succ (s s' : State) : Prop := ∃ (f : Firing s) (a : P.Admits f), P.result f a = s'

/-- The firing span maps onto the successor span. -/
def toSucc : SpanMap (firingSpan P) (span (Succ P)) id where
  edge e := ⟨(e.1, P.result e.2.1 e.2.2), ⟨e.2.1, e.2.2, rfl⟩⟩
  source _ := rfl
  target _ := rfl

/-- Every successor edge comes from a firing with its source. -/
theorem toSucc_source_weakPullback :
    WeakPullback (firingSpan P).source (span (Succ P)).source id (toSucc P).edge := by
  rintro x ⟨⟨s, s'⟩, f, a, reached⟩ same
  refine ⟨⟨s, f, a⟩, same, ?_⟩
  apply Subtype.ext
  exact Prod.ext rfl reached

/-- Every successor edge comes from a firing with its target. -/
theorem toSucc_target_weakPullback :
    WeakPullback (firingSpan P).target (span (Succ P)).target id (toSucc P).edge := by
  rintro y ⟨⟨s, s'⟩, f, a, reached⟩ same
  have arrives : s' = y := same
  refine ⟨⟨s, f, a⟩, reached.trans arrives, ?_⟩
  apply Subtype.ext
  exact Prod.ext rfl reached

/-- **Possibility over firings is possibility over successors.** -/
theorem firing_diamond_eq (φ : State → Prop) :
    derivedDiamond (firingSpan P) φ = derivedDiamond (span (Succ P)) φ :=
  ((toSucc P).diamond_eq (toSucc_source_weakPullback P) φ).symm

/-- **Successor necessity over firings is successor necessity over successors.** -/
theorem firing_forwardBox_eq (φ : State → Prop) :
    derivedForwardBox (firingSpan P) φ = derivedForwardBox (span (Succ P)) φ := by
  have square : ∀ e, (span (Succ P)).source ((toSucc P).edge e) = id ((firingSpan P).source e) :=
    fun _ => rfl
  have bc := (beckChevalley_ui_iff (f := (firingSpan P).source) (g := (span (Succ P)).source)
    (h := id) (k := (toSucc P).edge) square).mp (toSucc_source_weakPullback P)
    (pb (span (Succ P)).target φ)
  exact bc.symm

/-- **Predecessor necessity over firings is predecessor necessity over successors.** -/
theorem firing_predecessorBox_eq (φ : State → Prop) :
    derivedBox (firingSpan P) φ = derivedBox (span (Succ P)) φ := by
  have square : ∀ e, (span (Succ P)).target ((toSucc P).edge e) = id ((firingSpan P).target e) :=
    fun _ => rfl
  have bc := (beckChevalley_ui_iff (f := (firingSpan P).target) (g := (span (Succ P)).target)
    (h := id) (k := (toSucc P).edge) square).mp (toSucc_target_weakPullback P)
    (pb (span (Succ P)).source φ)
  exact bc.symm

/-! ## Hennessy–Milner adequacy, by the tree's theorem -/

section Adequacy

open Mettapedia.GSLT Mettapedia.GSLT.HennessyMilner

variable {Atom : Type} (observes : Atom → State → Prop)

/-- **The step as a Hennessy–Milner system**: one label, the successor relation, and an
observation set. -/
def stepSystem : System.{0, 0} (theoryOf State (Succ P)) where
  Atom := Atom
  observes := observes
  observes_resp := fun _ {_ _} same => by
    have equal : _ = _ := same
    subst equal
    exact Iff.rfl
  Label := Unit
  act _ := Succ P
  act_resp_left := fun {_ _ _ target} same step => by
    have equal : _ = _ := same
    subst equal
    exact ⟨target, step, rfl⟩
  act_resp_right := fun step same => by
    have equal : _ = _ := same
    subst equal
    exact step

/-- **The diamond of Hennessy–Milner logic over the step is OSLF's possibility over its firing
span.** -/
theorem sat_dia_iff (φ : Formula (stepSystem P observes).Atom (stepSystem P observes).Label)
    (s : State) :
    (stepSystem P observes).sat (.dia () φ) s ↔
      derivedDiamond (firingSpan P) ((stepSystem P observes).sat φ) s := by
  constructor
  · rintro ⟨t, step, holds⟩
    exact (congrFun (firing_diamond_eq P _) s).mpr ((diamond_iff _ _ _).mpr ⟨t, step, holds⟩)
  · intro holds
    obtain ⟨t, step, there⟩ :=
      (diamond_iff _ _ _).mp ((congrFun (firing_diamond_eq P _) s).mp holds)
    exact ⟨t, step, there⟩

/-- **Hennessy–Milner adequacy for the step**: logical equivalence is bisimilarity, when the
successor sets have finite covers up to bisimilarity. -/
theorem logicallyEquivalent_iff_bisimilar
    (finite : (stepSystem P observes).ImageFiniteBisimilar) (left right : State) :
    (stepSystem P observes).LogicallyEquivalent left right ↔
      (stepSystem P observes).Bisimilar left right :=
  (stepSystem P observes).logicallyEquivalent_iff_bisimilar_of_imageFiniteBisimilar finite left right

end Adequacy

#print axioms toSucc_source_weakPullback
#print axioms toSucc_target_weakPullback
#print axioms firing_diamond_eq
#print axioms firing_forwardBox_eq
#print axioms firing_predecessorBox_eq
#print axioms sat_dia_iff
#print axioms logicallyEquivalent_iff_bisimilar

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.StepSpan
