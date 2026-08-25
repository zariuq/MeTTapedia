import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Observer-indexed distinction and variety

Variety is not installed as a scalar.  An observer first determines a family
of observable values; finite cardinality is a derived readout of that family.
This keeps explicit Francis Heylighen's point that a distinction visible at one
level can be redundant at another.

The exact-presentation theorem is structural: a commuting equivalence of
states and views induces an equivalence of observed varieties.  The
micro/macro example is the required negative control against an
observer-independent count.

References:

- F. Heylighen, *Relational Closure: a mathematical concept for
  distinction-making and complexity analysis* (1990).
- F. Heylighen, *(Meta)Systems as Constraints on Variation* (1995).
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics

universe uState uView uState' uView'

/-- An observer presents a state through a selected view language. -/
structure Observer (State : Type uState) (View : Type uView) where
  observe : State → View

namespace Observer

variable {State : Type uState} {View : Type uView}

/-- Two states are distinguished when their observed views differ. -/
def Distinguishes (observer : Observer State View) (left right : State) : Prop :=
  observer.observe left ≠ observer.observe right

/-- The states presented as one selected view. -/
def Fibre (observer : Observer State View) (view : View) : Type uState :=
  {state : State // observer.observe state = view}

/-- The informative observed variety: the type of views actually presented by
some state.  It precedes every cardinal or entropy readout. -/
abbrev Variety (observer : Observer State View) : Type uView :=
  Set.range observer.observe

/-- Every state determines one inhabitant of the observed variety. -/
def toVariety (observer : Observer State View) (state : State) : observer.Variety :=
  ⟨observer.observe state, ⟨state, rfl⟩⟩

/-- Observed variety contains no invented views. -/
theorem toVariety_surjective (observer : Observer State View) :
    Function.Surjective observer.toVariety := by
  rintro ⟨view, state, equal⟩
  subst equal
  exact ⟨state, rfl⟩

/-- The fully informative observer. -/
def identity (State : Type uState) : Observer State State where
  observe := _root_.id

/-- Postcomposition deliberately forgets distinctions that `summarize` does
not retain. -/
def postcompose {Summary : Type*} (observer : Observer State View)
    (summarize : View → Summary) : Observer State Summary where
  observe := summarize ∘ observer.observe

/-- A coarser observation cannot create a distinction absent from the finer
observation. -/
theorem distinguishes_of_postcompose_distinguishes {Summary : Type*}
    (observer : Observer State View) (summarize : View → Summary)
    {left right : State}
    (distinguished : (observer.postcompose summarize).Distinguishes left right) :
    observer.Distinguishes left right := by
  intro equal
  exact distinguished (congrArg summarize equal)

/-- Finite observed values on a selected finite collection of states. -/
def observedOn [DecidableEq View] (observer : Observer State View)
    (states : Finset State) : Finset View :=
  states.image observer.observe

/-- Finite cardinal variety is a readout, not the underlying variety. -/
def cardinalOn [DecidableEq View] (observer : Observer State View)
    (states : Finset State) : Nat :=
  (observer.observedOn states).card

theorem cardinalOn_postcompose_le [DecidableEq View]
    {Summary : Type*} [DecidableEq Summary]
    (observer : Observer State View) (summarize : View → Summary)
    (states : Finset State) :
    (observer.postcompose summarize).cardinalOn states ≤
      observer.cardinalOn states := by
  simpa [cardinalOn, observedOn, postcompose, Function.comp_def,
    Finset.image_image] using
      (Finset.card_image_le
        (f := summarize) (s := observer.observedOn states))

/-! ## Exact changes of presentation -/

/-- An exact change of presentation transports both states and views and makes
observation commute. -/
structure ExactPresentation
    {State' : Type uState'} {View' : Type uView'}
    (left : Observer State View) (right : Observer State' View') where
  stateEquiv : State ≃ State'
  viewEquiv : View ≃ View'
  observe_commutes : ∀ state,
    viewEquiv (left.observe state) = right.observe (stateEquiv state)

namespace ExactPresentation

variable {State' : Type uState'} {View' : Type uView'}
  {left : Observer State View} {right : Observer State' View'}

/-- Exact presentation preserves every distinction. -/
theorem distinguishes_iff (presentation : ExactPresentation left right)
    (first second : State) :
    left.Distinguishes first second ↔
      right.Distinguishes (presentation.stateEquiv first)
        (presentation.stateEquiv second) := by
  simp only [Distinguishes]
  rw [← presentation.observe_commutes first,
    ← presentation.observe_commutes second]
  exact presentation.viewEquiv.injective.eq_iff.not.symm

/-- Exact presentation preserves the full observed variety by equivalence,
not merely by equality of a finite count. -/
def varietyEquiv (presentation : ExactPresentation left right) :
    left.Variety ≃ right.Variety where
  toFun observed :=
    ⟨presentation.viewEquiv observed.1, by
      rcases observed.2 with ⟨state, equal⟩
      refine ⟨presentation.stateEquiv state, ?_⟩
      calc
        right.observe (presentation.stateEquiv state) =
            presentation.viewEquiv (left.observe state) :=
          (presentation.observe_commutes state).symm
        _ = presentation.viewEquiv observed.1 :=
          congrArg presentation.viewEquiv equal⟩
  invFun observed :=
    ⟨presentation.viewEquiv.symm observed.1, by
      rcases observed.2 with ⟨state, equal⟩
      refine ⟨presentation.stateEquiv.symm state, ?_⟩
      apply presentation.viewEquiv.injective
      rw [presentation.observe_commutes,
        presentation.stateEquiv.apply_symm_apply,
        presentation.viewEquiv.apply_symm_apply]
      exact equal⟩
  left_inv observed := by
    apply Subtype.ext
    exact presentation.viewEquiv.symm_apply_apply observed.1
  right_inv observed := by
    apply Subtype.ext
    exact presentation.viewEquiv.apply_symm_apply observed.1

/-- Finite cardinality is invariant because the informative varieties are
equivalent. -/
theorem natCard_variety_eq (presentation : ExactPresentation left right) :
    Nat.card left.Variety = Nat.card right.Variety :=
  Nat.card_congr presentation.varietyEquiv

end ExactPresentation

/-! ## Observer-relativity canary -/

namespace ObserverRelativity

abbrev MicroState := Bool × Bool

/-- The micro observer retains both coordinates. -/
def micro : Observer MicroState MicroState := Observer.identity MicroState

/-- The macro observer retains only the first coordinate. -/
def macroView : Observer MicroState Bool where
  observe := Prod.fst

theorem micro_distinguishes_hidden_coordinate :
    micro.Distinguishes (false, false) (false, true) := by
  simp [Distinguishes, micro, identity]

theorem macro_identifies_hidden_coordinate :
    ¬ macroView.Distinguishes (false, false) (false, true) := by
  simp [Distinguishes, macroView]

theorem micro_cardinalOn_univ :
    micro.cardinalOn Finset.univ = 4 := by
  decide

theorem macro_cardinalOn_univ :
    macroView.cardinalOn Finset.univ = 2 := by
  decide

/-- There is no single cardinal value agreeing with both legitimate observer
readouts on this state space. -/
theorem no_observer_independent_cardinality :
    ¬ ∃ cardinal : Nat,
      micro.cardinalOn Finset.univ = cardinal ∧
      macroView.cardinalOn Finset.univ = cardinal := by
  intro existsCardinal
  rcases existsCardinal with ⟨cardinal, microEqual, macroEqual⟩
  rw [micro_cardinalOn_univ] at microEqual
  rw [macro_cardinalOn_univ] at macroEqual
  omega

end ObserverRelativity

end Observer

end Mettapedia.Cybernetics

#print axioms Mettapedia.Cybernetics.Observer.ExactPresentation.varietyEquiv
#print axioms Mettapedia.Cybernetics.Observer.ObserverRelativity.no_observer_independent_cardinality
