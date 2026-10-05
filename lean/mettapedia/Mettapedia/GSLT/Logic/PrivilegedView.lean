import Mettapedia.GSLT.Logic.Views
import Mettapedia.Coalgebra.StreamFinality
import Mettapedia.TypeTheory.MaterialSets.Hypersets.Finality
import Mathlib.Computability.MyhillNerode

/-!
# What makes a view privileged: a purpose

A finest view is lossless, and finest views come as a class
(`Mettapedia.GSLT.Logic.Views`), so losslessness singles out no view.  A view
can be singled out only relative to a purpose.  Here a purpose is a subject with
deterministic dynamics `step : A → A` and an evaluation `evaluation : A → E`:
what is to be evaluated, now and after every step.

* A view is **stable** when the points it identifies have successors it
  identifies (`Stable`): it can be updated without looking back at the subject.
  It **keeps** the evaluation when the evaluation factors through it.
* The **behaviour** of a point is the stream of its evaluations along its run
  (`behaviour`, `behaviour_apply`): the map into the final coalgebra of streams
  of `Mettapedia.Coalgebra.StreamFinality`.  It is stable (`stable_behaviour`)
  and keeps the evaluation (`factors_behaviour_evaluation`).
* **It is the coarsest such view** (`factors_behaviour`): it factors through
  every stable view that keeps the evaluation.  The proof reads the values of
  the view as a coalgebra and uses that every coalgebra morphism into streams is
  the unfolding (`hom_to_stream_eq_unfold`).  In the vocabulary of `Views`, the
  behaviour is a common coarsening of all stable views that keep the evaluation
  (`commonCoarsening_behaviour`), and it is one of them (`behaviourView`).
* **It is unique only as a bubble.**  A stable view that keeps the evaluation and
  factors through the behaviour factors both ways with it and identifies the
  same points (`mutual_of_coarsest`, `sameFibres_of_coarsest`).  Two points have
  one behaviour exactly when some relation that keeps the evaluation and is
  closed under the step relates them (`behaviour_eq_iff`): the bubble is
  bisimilarity.

So privilege is relative twice over: to the evaluation, and to the dynamics
under which it must stay computable.  Change either and another view is
privileged.

**Examples** on a four-state signal (`Signal`): an idle state, a primed state,
and two lit states that alternate.

* Positive: the two lit states have one behaviour (`behaviour_onA_eq_onB`), as
  in a minimal automaton, while the idle and the primed state, alike now, have
  two (`behaviour_idle_ne_primed`).
* Negative: the evaluation alone keeps itself but is not stable
  (`not_stable_light`); it forgets an evaluation one step ahead
  (`light_forgets_next`), and the behaviour does not factor through it
  (`not_factors_light_behaviour`), so stability cannot be dropped from
  `factors_behaviour`.
* Negative: the identity is stable and keeps the evaluation
  (`stable_id`), but it is not the coarsest: it does not factor through the
  behaviour (`not_factors_behaviour_id`).

**Inputs.**  With dynamics driven by inputs, `step : A → Input → A`, streams are
replaced by functions of input words, and the same holds: the word behaviour is
stable for every input (`stableUnder_wordBehaviour`), keeps the evaluation, and
is the coarsest such view (`factors_wordBehaviour`, `sameFibres_of_coarsest_word`).
On histories extended by one letter at a time the word behaviour of a history
is the evaluation of its continuations (`wordBehaviour_history`); for
membership in a language this is the left quotient of the Myhill–Nerode theorem
(`wordBehaviour_membership`), and the privileged view is the minimal automaton.
For prediction, with the evaluation "the conditional law of the next symbol",
it is the causal state of computational mechanics (J. P. Crutchfield and
C. R. Shalizi, *Computational mechanics: pattern and prediction, structure and
simplicity*, J. Stat. Phys. 104, 2001).

**Finite depth.**  On streams, every view at a fixed finite depth is lossy: none
is finest in the family of finite views (`no_prefixView_finest`), while the
family together separates streams (`joint_prefixViews_injective`).  The lossless
view lives at the limit of the tower, the finite-depth form of the diagonal
limit of `Views`.

**Branching dynamics.**  For a successor relation, a view is stable when the
relation it induces is a bisimulation (`StableBranching`).  The decoration by
hypersets of `Mettapedia.TypeTheory.MaterialSets.Hypersets.Finality` is stable
(`stableBranching_decorate`) and is the coarsest stable view
(`factors_decorate`), unique as a bubble (`sameFibres_of_coarsest_branching`).
Here the only evaluation is the branching itself, kept by every stable view
(`deadlocked_factors`); a separate evaluation of states would need the labelled
decoration together with the fact that labelled bisimilarity is its bubble.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.PrivilegedView

open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.ViewPluralism
open Mettapedia.Coalgebra.StreamFinality

universe u v w x

/-! ## Deterministic dynamics -/

section Stream

variable {A : Type u} {E : Type w} {step : A → A} {evaluation : A → E}

/-- A view is **stable** under `step` when the points it identifies have
successors it identifies. -/
def Stable {V : Sort v} (step : A → A) (view : A → V) : Prop :=
  ∀ a b, view a = view b → view (step a) = view (step b)

/-- The subject, its dynamics and its evaluation, as a stream coalgebra. -/
def system (step : A → A) (evaluation : A → E) : Coalgebra.{w, u} E where
  Carrier := A
  observe := evaluation
  next := step

/-- The **behaviour** of a point: the stream of its evaluations along its run. -/
def behaviour (step : A → A) (evaluation : A → E) : A → Stream E :=
  unfold (system step evaluation)

theorem behaviour_apply (step : A → A) (evaluation : A → E) (a : A) (n : Nat) :
    behaviour step evaluation a n = evaluation (step^[n] a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n inductionHypothesis =>
      rw [Function.iterate_succ_apply]
      exact inductionHypothesis (step a)

theorem behaviour_step (a : A) :
    behaviour step evaluation (step a) = tail (behaviour step evaluation a) :=
  (tail_unfold (system step evaluation) a).symm

/-- **The behaviour is stable.** -/
theorem stable_behaviour : Stable step (behaviour step evaluation) := fun a b same => by
  rw [behaviour_step, behaviour_step, same]

/-- **The behaviour keeps the evaluation.** -/
theorem factors_behaviour_evaluation : Factors (behaviour step evaluation) evaluation :=
  ⟨head, fun _ => rfl⟩

open scoped Classical in
/-- The values of a view, read as a coalgebra: the observation is the recovered
evaluation, and the successor of a value is the value of the successor of any
point with that value. -/
noncomputable def valueSystem {V : Type v} (step : A → A) (view : A → V) (recover : V → E) :
    Coalgebra.{w, v} E where
  Carrier := V
  observe := recover
  next := fun value => if seen : ∃ a, view a = value then view (step seen.choose) else value

open scoped Classical in
/-- A stable view that keeps the evaluation is a coalgebra morphism onto its
values. -/
noncomputable def viewHom {V : Type v} {view : A → V} (stable : Stable step view)
    {recover : V → E} (recovers : ∀ a, recover (view a) = evaluation a) :
    Hom (system step evaluation) (valueSystem step view recover) where
  toFun := view
  observe_preserved := recovers
  next_preserved := fun a => by
    have seen : ∃ a', view a' = view a := ⟨a, rfl⟩
    show (if seen : ∃ a', view a' = view a then view (step seen.choose) else view a) =
      view (step a)
    rw [dif_pos seen]
    exact stable _ _ seen.choose_spec

/-- **The behaviour is the coarsest stable view that keeps the evaluation**: it
factors through every such view, by the finality of streams. -/
theorem factors_behaviour {V : Type v} {view : A → V} (stable : Stable step view)
    (keeps : Factors view evaluation) : Factors view (behaviour step evaluation) := by
  obtain ⟨recover, recovers⟩ := keeps
  refine ⟨unfold (valueSystem step view recover), fun a => ?_⟩
  exact congrFun (hom_to_stream_eq_unfold (system step evaluation)
    ((viewHom stable recovers).comp (unfoldHom (valueSystem step view recover)))) a

/-- A stable view of the subject that keeps the evaluation. -/
structure StableKeepingView (step : A → A) (evaluation : A → E) where
  Carrier : Type v
  view : A → Carrier
  stable : Stable step view
  keeps : Factors view evaluation

/-- The behaviour as a stable view that keeps the evaluation. -/
def behaviourView (step : A → A) (evaluation : A → E) :
    StableKeepingView.{u, w, w} step evaluation where
  Carrier := Stream E
  view := behaviour step evaluation
  stable := stable_behaviour
  keeps := factors_behaviour_evaluation

/-- **The behaviour is a common coarsening of all stable views that keep the
evaluation.** -/
theorem commonCoarsening_behaviour :
    CommonCoarsening (fun member : StableKeepingView.{u, v, w} step evaluation => member.view)
      (behaviour step evaluation) :=
  fun member => factors_behaviour member.stable member.keeps

/-- **Unique up to mutual factoring**: a stable view that keeps the evaluation and
factors through the behaviour factors both ways with it. -/
theorem mutual_of_coarsest {V : Type v} {view : A → V} (stable : Stable step view)
    (keeps : Factors view evaluation) (coarsest : Factors (behaviour step evaluation) view) :
    Factors view (behaviour step evaluation) ∧ Factors (behaviour step evaluation) view :=
  ⟨factors_behaviour stable keeps, coarsest⟩

/-- ... and identifies the same points. -/
theorem sameFibres_of_coarsest {V : Type v} {view : A → V} (stable : Stable step view)
    (keeps : Factors view evaluation) (coarsest : Factors (behaviour step evaluation) view)
    (a b : A) : view a = view b ↔ behaviour step evaluation a = behaviour step evaluation b :=
  ⟨(factors_behaviour stable keeps).constantOnFibers a b, coarsest.constantOnFibers a b⟩

/-- **The bubble of the behaviour is bisimilarity**: two points have one
behaviour exactly when a relation that keeps the evaluation and is closed under
the step relates them. -/
theorem behaviour_eq_iff {a b : A} :
    behaviour step evaluation a = behaviour step evaluation b ↔
      ∃ related : A → A → Prop,
        (∀ first second, related first second →
          evaluation first = evaluation second ∧ related (step first) (step second)) ∧
        related a b := by
  constructor
  · intro same
    refine ⟨fun first second => behaviour step evaluation first = behaviour step evaluation second,
      fun first second sameBehaviour => ⟨congrFun sameBehaviour 0, ?_⟩, same⟩
    show behaviour step evaluation (step first) = behaviour step evaluation (step second)
    rw [behaviour_step, behaviour_step, sameBehaviour]
  · rintro ⟨related, closed, relatedAB⟩
    funext n
    induction n generalizing a b with
    | zero => exact (closed a b relatedAB).1
    | succ n inductionHypothesis =>
        exact inductionHypothesis (closed a b relatedAB).2

end Stream

/-! ## Examples: a signal with an idle, a primed and two lit states -/

/-- A four-state signal. -/
inductive Signal
  | idle
  | primed
  | onA
  | onB
  deriving DecidableEq

namespace Signal

/-- The idle state stays idle; the primed state lights; the lit states alternate. -/
def step : Signal → Signal
  | idle => idle
  | primed => onA
  | onA => onB
  | onB => onA

/-- The evaluation: whether the signal is lit. -/
def light : Signal → Bool
  | idle => false
  | primed => false
  | onA => true
  | onB => true

end Signal

/-- **Positive example**: the two lit states have one behaviour. -/
theorem behaviour_onA_eq_onB :
    behaviour Signal.step Signal.light .onA = behaviour Signal.step Signal.light .onB := by
  refine behaviour_eq_iff.mpr ⟨fun first second => Signal.light first = true ∧
    Signal.light second = true, ?_, ⟨rfl, rfl⟩⟩
  rintro (_ | _ | _ | _) (_ | _ | _ | _) ⟨first, second⟩ <;>
    simp_all [Signal.light, Signal.step]

/-- The idle and the primed state agree now and differ one step later. -/
theorem behaviour_idle_ne_primed :
    behaviour Signal.step Signal.light .idle ≠ behaviour Signal.step Signal.light .primed :=
  fun same => Bool.false_ne_true (congrFun same 1)

/-- **Negative example**: the evaluation alone is not stable. -/
theorem not_stable_light : ¬ Stable Signal.step Signal.light :=
  fun stable => Bool.false_ne_true (stable .idle .primed rfl)

/-- The evaluation alone forgets the evaluation one step ahead. -/
def light_forgets_next : NonTrivialFiber Signal.light (Signal.light ∘ Signal.step) where
  left := .idle
  right := .primed
  sameShadow := rfl
  differentValue := Bool.false_ne_true

/-- **Stability cannot be dropped**: the evaluation keeps itself, and the
behaviour does not factor through it. -/
theorem not_factors_light_behaviour :
    Factors Signal.light Signal.light ∧
      ¬ Factors Signal.light (behaviour Signal.step Signal.light) :=
  ⟨⟨id, fun _ => rfl⟩, fun factors =>
    behaviour_idle_ne_primed (factors.constantOnFibers .idle .primed rfl)⟩

/-- The identity is stable and keeps the evaluation. -/
theorem stable_id :
    Stable Signal.step (id : Signal → Signal) ∧ Factors (id : Signal → Signal) Signal.light :=
  ⟨fun _ _ same => congrArg Signal.step same, ⟨Signal.light, fun _ => rfl⟩⟩

/-- **Negative example**: the identity is not the coarsest; it does not factor
through the behaviour. -/
theorem not_factors_behaviour_id :
    ¬ Factors (behaviour Signal.step Signal.light) (id : Signal → Signal) :=
  NonTrivialFiber.not_factors
    ⟨.onA, .onB, behaviour_onA_eq_onB, fun same => by cases same⟩

/-! ## Dynamics driven by inputs -/

section Words

variable {A : Type u} {Input : Type x} {E : Type w} {step : A → Input → A}
  {evaluation : A → E}

/-- A view is stable under input-driven dynamics when the points it identifies
have successors it identifies, for every input. -/
def StableUnder {V : Sort v} (step : A → Input → A) (view : A → V) : Prop :=
  ∀ a b, view a = view b → ∀ input, view (step a input) = view (step b input)

/-- The **word behaviour** of a point: its evaluation after each input word. -/
def wordBehaviour (step : A → Input → A) (evaluation : A → E) (a : A) : List Input → E :=
  fun word => evaluation (word.foldl step a)

theorem stableUnder_wordBehaviour : StableUnder step (wordBehaviour step evaluation) :=
  fun _ _ same input => funext fun word => congrFun same (input :: word)

theorem factors_wordBehaviour_evaluation : Factors (wordBehaviour step evaluation) evaluation :=
  ⟨fun behaviourOfPoint => behaviourOfPoint [], fun _ => rfl⟩

theorem wordBehaviour_constantOnFibers {V : Sort v} {view : A → V}
    (stable : StableUnder step view) (keeps : Factors view evaluation) :
    ConstantOnFibers view (wordBehaviour step evaluation) := by
  intro a b same
  funext word
  induction word generalizing a b with
  | nil => exact keeps.constantOnFibers a b same
  | cons input word inductionHypothesis =>
      exact inductionHypothesis (step a input) (step b input) (stable a b same input)

/-- **The word behaviour is the coarsest view stable for every input that keeps
the evaluation.** -/
theorem factors_wordBehaviour {V : Sort v} {view : A → V} (stable : StableUnder step view)
    (keeps : Factors view evaluation) : Factors view (wordBehaviour step evaluation) := by
  classical
  obtain ⟨recover, recovers⟩ := keeps
  refine ⟨fun value => if seen : ∃ a, view a = value then wordBehaviour step evaluation seen.choose
    else fun _ => recover value, fun a => ?_⟩
  have seen : ∃ a', view a' = view a := ⟨a, rfl⟩
  simp only [dif_pos seen]
  exact wordBehaviour_constantOnFibers stable ⟨recover, recovers⟩ _ _ seen.choose_spec

/-- The word behaviour is unique as a bubble: a stable view that keeps the
evaluation and factors through it identifies the same points. -/
theorem sameFibres_of_coarsest_word {V : Sort v} {view : A → V} (stable : StableUnder step view)
    (keeps : Factors view evaluation) (coarsest : Factors (wordBehaviour step evaluation) view)
    (a b : A) :
    view a = view b ↔ wordBehaviour step evaluation a = wordBehaviour step evaluation b :=
  ⟨(factors_wordBehaviour stable keeps).constantOnFibers a b, coarsest.constantOnFibers a b⟩

end Words

section Histories

variable {Input : Type x} {E : Type w}

/-- Extending a history by one input. -/
def extend (history : List Input) (input : Input) : List Input :=
  history ++ [input]

theorem foldl_extend (history word : List Input) : word.foldl extend history = history ++ word := by
  induction word generalizing history with
  | nil => simp
  | cons input word inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis]
      simp [extend]

/-- On histories, the word behaviour is the evaluation of the continuations. -/
theorem wordBehaviour_history (evaluation : List Input → E) (history : List Input) :
    wordBehaviour extend evaluation history = fun word => evaluation (history ++ word) :=
  funext fun word => congrArg evaluation (foldl_extend history word)

/-- **Positive example (Myhill–Nerode)**: for membership in a language, the word
behaviour of a history is its left quotient, so the privileged view is the
minimal automaton. -/
theorem wordBehaviour_membership (language : Language Input) (history : List Input) :
    wordBehaviour extend (· ∈ language) history = fun word => word ∈ language.leftQuotient history :=
  wordBehaviour_history _ history

end Histories

/-! ## Finite depth: every finite view is lossy, the tower is not -/

section FiniteDepth

variable {Label : Type w}

/-- The family of finite views of streams, one per depth. -/
def prefixViews : (depth : Nat) → Stream Label → Prefix Label depth :=
  fun depth => finiteView depth

/-- **No finite view is finest** when two labels differ: the view at the next
depth separates two streams it identifies. -/
theorem no_prefixView_finest {ordinary changed : Label} (different : ordinary ≠ changed)
    (depth : Nat) : ¬ Finest (prefixViews (Label := Label)) depth :=
  not_finest_of_fiber _ (depth + 1)
    ⟨constant ordinary, changedAt depth ordinary changed,
      finiteView_constant_changedAt depth ordinary changed, fun same => by
        have atDepth := congrFun same ⟨depth, Nat.lt_succ_self depth⟩
        simp [prefixViews, finiteView, constant, changedAt] at atDepth
        exact different atDepth⟩

/-- **The family of finite views together is lossless.** -/
theorem joint_prefixViews_injective :
    Function.Injective (joint (prefixViews (Label := Label))) :=
  allPrefixes_injective

end FiniteDepth

/-! ## Branching dynamics: the hyperset decoration -/

section Branching

open Mettapedia.TypeTheory.MaterialSets.Hypersets

variable {A : Type u} (successor : A → A → Prop)

/-- A view is stable under branching dynamics when the relation it induces is a
bisimulation. -/
def StableBranching {V : Sort v} (view : A → V) : Prop :=
  IsBisimulation successor successor fun a b => view a = view b

/-- **The decoration is stable.** -/
theorem stableBranching_decorate : StableBranching successor (HSet.decorate successor) :=
  HSet.isBisimulation_kernel

/-- **The decoration is the coarsest stable view.** -/
theorem factors_decorate {V : Sort v} {view : A → V} (stable : StableBranching successor view) :
    Factors view (HSet.decorate successor) :=
  haveI : Nonempty HSet.{u} := ⟨∅⟩
  factors_of_constantOnFibers fun _ _ same => IsBisimulation.decorate_eq stable same

/-- It is unique as a bubble. -/
theorem sameFibres_of_coarsest_branching {V : Sort v} {view : A → V}
    (stable : StableBranching successor view) (coarsest : Factors (HSet.decorate successor) view)
    (a b : A) : view a = view b ↔ HSet.decorate successor a = HSet.decorate successor b :=
  ⟨(factors_decorate successor stable).constantOnFibers a b, coarsest.constantOnFibers a b⟩

/-- Whether a state has no successor. -/
def Deadlocked (a : A) : Prop :=
  ∀ a', ¬ successor a a'

/-- **Every stable view keeps deadlock.** -/
theorem deadlocked_factors {V : Sort v} {view : A → V} (stable : StableBranching successor view) :
    ConstantOnFibers view (Deadlocked successor) := fun _ _ same =>
  propext ⟨fun deadlocked b' step =>
      let ⟨a', stepA, _⟩ := (stable same).2 b' step
      deadlocked a' stepA,
    fun deadlocked a' step =>
      let ⟨b', stepB, _⟩ := (stable same).1 a' step
      deadlocked b' stepB⟩

end Branching

/-! ## Axiom audit -/

#print axioms behaviour_apply
#print axioms stable_behaviour
#print axioms factors_behaviour
#print axioms commonCoarsening_behaviour
#print axioms sameFibres_of_coarsest
#print axioms behaviour_eq_iff
#print axioms behaviour_onA_eq_onB
#print axioms not_factors_light_behaviour
#print axioms not_factors_behaviour_id
#print axioms factors_wordBehaviour
#print axioms wordBehaviour_membership
#print axioms no_prefixView_finest
#print axioms joint_prefixViews_injective
#print axioms factors_decorate
#print axioms deadlocked_factors

end Mettapedia.GSLT.PrivilegedView
