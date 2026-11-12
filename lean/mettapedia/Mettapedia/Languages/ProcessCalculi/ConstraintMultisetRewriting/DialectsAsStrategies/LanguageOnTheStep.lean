import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.RefinedScheduler
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.LinearTake
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SearchStep

/-!
# A language is a step, a strategy over its runs, and an observation

The calculus has no evaluation default. A **language** (`Language`) adds two things to a step:

* a **strategy**, which selects runs of the step. A run is a word of many firings, so a strategy
  spans many steps: it is a selection on the free category of runs, not a property of one firing;
* an **observation**: each firing emits a bag of answers, and a run's answers are their sum
  (`answers`, an account of the run into the commutative monoid of bags, `answers_eq_account`).

Bags are unordered, so the observation of a language from a state is the **set of possible
outcomes** (`outcomes`): pairs of an answer bag and the state reached.

* `outcome_sound`: every strategy is sound; an outcome's state is reached by a run along which
  knowledge only refines (`Run.models_start`).
* `Refines`: fewer possible outcomes. Every language refines the free one (`refines_free`).
* **Schedulers are strategies.** `scheduler_outcome`: the states a scheduler reaches are outcomes of
  the free language (`Scheduler.refines`), with knowledge pulled back (`Scheduler.sound`).
  `ofScheduler` is the language whose strategy selects exactly the erasures of a scheduler's walks;
  its reached states are exactly the scheduler's (`ofScheduler_reached_iff`).

## Handler independence, in three readings

A program that observes no control has the same observation under every handler that neither
prunes answers nor loses a branch. Which handlers and which observation make this true is the
content: each reading states its completeness, progress, termination and effect assumptions, and
each has its control. A pruning handler, or an unfair search stuck in an infinite branch, can change
which answers are available.

1. **Search handlers** (alternatives explored with the state restored, as in backtracking):
   `search_handler_independence`. On the run space of the step, when both searches terminate (`all`
   is defined), `all` gives the same bag under every policy, and that bag is the complete runs, each
   at its address (`Search.all_eq_all`, `Alternatives.item_answer_iff`). `all` keeps every answer;
   with an infinite branch it is undefined, and nothing here covers a search that does not
   terminate. Control: `Controls.first_sees_order`: the first answer, a pruning observation that
   sees order, differs between depth-first and breadth-first on one space whose `all` agrees.
2. **Schedulers on one run** (no backtracking): `monotone_handler_independence`. On the monotone
   fragment (rules read and make; Datalog), any two schedulers within the rule set end where the
   same facts remain reachable, the least model (`MonotoneInference.confluent`). This is about what
   stays reachable, not what a scheduler derives: a scheduler that stops, or fires forever within
   part of the program, derives less; reaching the least model needs progress and fairness, which
   are not assumed. This is the CALM reading: monotone programs need no coordination, a sufficient
   condition. Controls: `Controls.monotone_handlers_agree`:
   two priority schedulers over transitive closure fire different rules first and reach different
   stores, from which the same facts remain reachable; `Controls.takes_handler_dependent`: with two
   rules taking one fact, the priority scheduler never reaches a fact the step reaches, and the two
   runs part ways for good.
3. **Effect orders** (one store threaded through the branches): `effect_order_independence`. For
   check-free firings with no identity reuse, every order respecting causality and asymmetric
   conflict runs, ends in the same configuration up to solutions, and emits the same bag
   (`GuardFreeProcessOrders.linearization_executes`). Controls: `Controls.effects_commute`, two
   independent takers in both orders; the pair of takers of one fact above: interfering effects make
   several outcomes possible.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies

open Interface

universe uO uT uH uOcc uS uF

section Generic

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Interface.Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS}
  {Firing : State → Type uF}

/-- **A language on a step**: a strategy selecting runs, and the bag of answers each firing
emits. -/
structure Language (P : Interface.Step X O State Firing) (Ans : Type*) where
  selects : {s : State} → P.Run s → Prop
  emit : (t : State) → Firing t → Multiset Ans

namespace Language

variable {P : Interface.Step X O State Firing} {Ans : Type*}

/-- **The answers of a run**: the bags its firings emit, summed. -/
def answers (emit : (t : State) → Firing t → Multiset Ans) : {s : State} → P.Run s → Multiset Ans
  | _, .nil _ => 0
  | _, .cons f _ rest => emit _ f + answers emit rest

/-- Answers are a functor out of the free category of runs. -/
theorem answers_append (emit : (t : State) → Firing t → Multiset Ans) :
    ∀ {s : State} (r : P.Run s) (later : P.Run r.last),
      answers emit (r.append later) = answers emit r + answers emit later
  | _, .nil _, _ => (zero_add _).symm
  | _, .cons f _ rest, later => by
      change emit _ f + answers emit (rest.append later) = (emit _ f + answers emit rest) + _
      rw [answers_append emit rest later, add_assoc]
      rfl

/-- **Answers are the run's account in bags**, written multiplicatively. -/
theorem answers_eq_account (emit : (t : State) → Firing t → Multiset Ans) :
    ∀ {s : State} (r : P.Run s),
      answers emit r = Multiplicative.toAdd (r.account fun t f => Multiplicative.ofAdd (emit t f))
  | _, .nil _ => rfl
  | _, .cons f _ rest => by
      change emit _ f + answers emit rest = Multiplicative.toAdd
        (Multiplicative.ofAdd (emit _ f) * rest.account fun t f => Multiplicative.ofAdd (emit t f))
      rw [toAdd_mul, toAdd_ofAdd, answers_eq_account emit rest]

/-- **The observation**: the possible outcomes, each an answer bag with the state reached. -/
def outcomes (L : Language P Ans) (s : State) : Set (Multiset Ans × State) :=
  {o | ∃ r : P.Run s, L.selects r ∧ o = (answers L.emit r, r.last)}

/-- **The free strategy** selects every run. -/
def free (emit : (t : State) → Firing t → Multiset Ans) : Language P Ans := ⟨fun _ => True, emit⟩

/-- One language refines another when its possible outcomes are among the other's. -/
def Refines (L L' : Language P Ans) : Prop := ∀ s, L.outcomes s ⊆ L'.outcomes s

theorem refines_free (L : Language P Ans) : L.Refines (free L.emit) := by
  rintro s o ⟨r, _, rfl⟩
  exact ⟨r, trivial, rfl⟩

/-- **Every strategy is sound**: an outcome's state is reached by a run along which knowledge only
refines. -/
theorem outcome_sound (L : Language P Ans) {s : State} {o : Multiset Ans × State}
    (h : o ∈ L.outcomes s) : ∃ r : P.Run s, r.last = o.2 ∧
      ∀ {b : Obj} (σ : Hom (P.frame r.last) b), X.Models σ (P.knowledge r.last) →
        X.Models (X.comp σ r.toLast) (P.knowledge s) := by
  obtain ⟨r, _, rfl⟩ := h
  exact ⟨r, rfl, fun σ solved => r.models_start σ solved⟩

end Language

/-! ## Schedulers are strategies -/

open FragmentsOfTheStep.RefinedScheduler

variable {P : Interface.Step X O State Firing} {Ans : Type*}

/-- **The states a scheduler reaches are outcomes of the free language**, and knowledge pulls back
along a run to them. -/
theorem scheduler_outcome (Q : Scheduler P) (emit : (t : State) → Firing t → Multiset Ans)
    {x y : State × Q.Book} (path : Relation.ReflTransGen Q.Transition x y) :
    (∃ A, (A, y.1) ∈ (Language.free (P := P) emit).outcomes x.1) ∧
      ∃ r : P.Run x.1, r.last = y.1 ∧ ∀ {b : Obj} (σ : Hom (P.frame r.last) b),
        X.Models σ (P.knowledge r.last) → X.Models (X.comp σ r.toLast) (P.knowledge x.1) := by
  obtain ⟨r, last⟩ := Scheduler.refines path
  exact ⟨⟨Language.answers emit r, r, trivial, by rw [last]; rfl⟩, Scheduler.sound path⟩

/-- **A walk of a scheduler**: a path that keeps its firings, the data a strategy selects. -/
inductive Walk (Q : Scheduler P) : State × Q.Book → State × Q.Book → Type (max uS uF)
  | refl (x : State × Q.Book) : Walk Q x x
  | fire {s : State} {b b' : Q.Book} {y : State × Q.Book} (f : Firing s) (admitted : P.Admits f)
      (chosen : Q.fires s b f admitted b') (rest : Walk Q (P.result f admitted, b') y) :
      Walk Q (s, b) y
  | move {s : State} {b b' : Q.Book} {y : State × Q.Book} (moved : Q.moves s b b')
      (rest : Walk Q (s, b') y) : Walk Q (s, b) y

namespace Walk

variable {Q : Scheduler P}

/-- A walk erases to a run of the step. -/
def erase : {x y : State × Q.Book} → Walk Q x y → P.Run x.1
  | _, _, .refl x => .nil x.1
  | _, _, .fire f admitted _ rest => .cons f admitted rest.erase
  | _, _, .move _ rest => rest.erase

theorem erase_last : ∀ {x y : State × Q.Book} (w : Walk Q x y), w.erase.last = y.1
  | _, _, .refl _ => rfl
  | _, _, .fire _ _ _ rest => erase_last rest
  | _, _, .move _ rest => erase_last rest

theorem toPath : ∀ {x y : State × Q.Book}, Walk Q x y → Relation.ReflTransGen Q.Transition x y
  | _, _, .refl _ => .refl
  | _, _, .fire f admitted chosen rest => .head (.fire f admitted chosen) (toPath rest)
  | _, _, .move moved rest => .head (.move moved) (toPath rest)

theorem ofPath {x y : State × Q.Book} (path : Relation.ReflTransGen Q.Transition x y) :
    Nonempty (Walk Q x y) := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨.refl _⟩
  | head step _ later =>
      obtain ⟨rest⟩ := later
      cases step with
      | fire f admitted chosen => exact ⟨.fire f admitted chosen rest⟩
      | move moved => exact ⟨.move moved rest⟩

end Walk

/-- **The language of a scheduler**: its strategy selects the erasures of the scheduler's walks
from a starting bookkeeping. -/
def ofScheduler (Q : Scheduler P) (start : Q.Book) (emit : (t : State) → Firing t → Multiset Ans) :
    Language P Ans where
  selects {s} r := ∃ (y : State × Q.Book) (w : Walk Q (s, start) y), w.erase = r
  emit := emit

/-- **The states the scheduler's language reaches are exactly the scheduler's.** -/
theorem ofScheduler_reached_iff (Q : Scheduler P) (start : Q.Book)
    (emit : (t : State) → Firing t → Multiset Ans) (s t : State) :
    (∃ A, (A, t) ∈ (ofScheduler Q start emit).outcomes s) ↔
      ∃ b, Relation.ReflTransGen Q.Transition (s, start) (t, b) := by
  constructor
  · rintro ⟨A, r, ⟨y, w, rfl⟩, same⟩
    have last : t = y.1 := (congrArg Prod.snd same).trans (Walk.erase_last w)
    exact ⟨y.2, last ▸ Walk.toPath w⟩
  · rintro ⟨b, path⟩
    obtain ⟨w⟩ := Walk.ofPath path
    exact ⟨Language.answers emit w.erase, w.erase, ⟨_, w, rfl⟩, by rw [Walk.erase_last]; rfl⟩

theorem ofScheduler_refines (Q : Scheduler P) (start : Q.Book)
    (emit : (t : State) → Firing t → Multiset Ans) :
    (ofScheduler Q start emit).Refines (Language.free emit) :=
  (ofScheduler Q start emit).refines_free

/-! ## Handler independence, search reading -/

open Search in
/-- **Handler independence for search handlers.** On the run space of the step, when the searches
under both policies terminate (`defined`, `defined'`), `all` gives the same bag under every policy,
and its members are exactly the complete runs, each at its address. `all` keeps every answer, so a
pruning observation such as the first answer is outside it (`Controls.first_sees_order`); a search
that does not terminate is outside it too. -/
theorem search_handler_independence (A : Alternatives P) (H H' : Policy (List ℕ × (State ⊕ State)))
    {s : State} (defined : (A.space.all H (.inr s)).Dom) (defined' : (A.space.all H' (.inr s)).Dom) :
    (A.space.all H (.inr s)).get defined = (A.space.all H' (.inr s)).get defined' ∧
      ∀ (w : List ℕ) (t : State), (w, t) ∈ (A.space.all H (.inr s)).get defined ↔
        ∃ (r : P.Run s) (w' : List ℕ), A.Path r w' ∧ w = w' ++ [0] ∧ r.last = t ∧ A.next t = [] :=
  ⟨A.space.all_eq_all H H' defined defined', fun w t =>
    (A.space.mem_all H defined (w, t)).trans (A.item_answer_iff s w t)⟩

end Generic

/-! ## Handler independence, effect reading -/

section Effects

variable {T S O : Type*} [DecidableEq O] (A : SubstitutionAction T S) (label : O → T)

open GuardFreeProcessOrders in
/-- **Handler independence for effect orders.** For check-free firings with no identity reuse,
every order respecting causality and asymmetric conflict runs, ends in the same configuration up
to solutions, and emits the same bag of answers. -/
theorem effect_order_independence {Ans : Type*} (emit : ConditionalSchedule.Firing T O → Multiset Ans)
    (order schedule : List (ConditionalSchedule.Firing T O)) (C : Configuration T O)
    (perm : schedule.Perm order) (free : ∀ x ∈ schedule, x.1.checks = [])
    (noReuse : schedule.Pairwise NoReuse) (respects : order.Pairwise LaterIndependent)
    (executable : ConditionalSchedule.Executable A label C schedule) :
    ConditionalSchedule.Executable A label C order ∧
      SameUpTo A (ConditionalSchedule.follow label C schedule)
        (ConditionalSchedule.follow label C order) ∧
      (order.map emit).sum = (schedule.map emit).sum := by
  obtain ⟨run, same⟩ :=
    linearization_executes A label order schedule C perm free noReuse respects executable
  exact ⟨run, same, ((perm.map emit).sum_eq).symm⟩

end Effects

/-! ## Handler independence, scheduler reading: the monotone fragment -/

section Monotone

open FragmentsOfTheStep FragmentsOfTheStep.RefinedScheduler FragmentsOfTheStep.GroundFirings
open NamesOnTheStep NamesOnTheStep.IssuingControls
open HeatingBisimulation (RuleSet)

/-- A scheduler over the ground step **within a rule set**: it fires only rules of the set, without
predicate queries. -/
def Within (Q : Scheduler base) (R : RuleSet Expr) : Prop :=
  ∀ (s : Conf) (b : Q.Book) (f : Fir) (admitted : base.Admits (s := s) f) (b' : Q.Book),
    Q.fires s b f admitted b' → R f.rule ∧ f.queries = []

/-- A scheduler within a rule set moves along steps of that rule set. -/
theorem scheduler_ground_steps {R : RuleSet Expr} {Q : Scheduler base} (within : Within Q R)
    {x y : Conf × Q.Book} (path : Relation.ReflTransGen Q.Transition x y) :
    Relation.ReflTransGen (GroundStep R) x.1 y.1 := by
  induction path with
  | refl => exact .refl
  | tail _ step earlier =>
      cases step with
      | fire f admitted chosen =>
          obtain ⟨inR, noQueries⟩ := within _ _ f admitted _ chosen
          exact earlier.tail ⟨f.rule, inR, f.selection, valid_of_admits noQueries admitted, rfl⟩
      | move _ => exact earlier

/-- **Handler independence on the monotone fragment.** Any two schedulers within a monotone rule
set, firing its rules without predicate queries, started at one store whose knowledge has identical
sides, end where the same facts remain reachable: the least model of the start's facts. No choice of
a scheduler makes an inference unreachable. This is about reachability, not about what a scheduler
derives: deriving the least model needs a scheduler that keeps firing, fairly, which is not
assumed. -/
theorem monotone_handler_independence {R : RuleSet Expr} (monotone : MonotoneInference.Monotone R)
    {Q₁ Q₂ : Scheduler base} (within₁ : Within Q₁ R) (within₂ : Within Q₂ R) {C : Conf}
    (trivial : ∀ e ∈ C.equations, e.1 = e.2) {b₁ : Q₁.Book} {b₂ : Q₂.Book}
    {y₁ : Conf × Q₁.Book} {y₂ : Conf × Q₂.Book}
    (path₁ : Relation.ReflTransGen Q₁.Transition (C, b₁) y₁)
    (path₂ : Relation.ReflTransGen Q₂.Transition (C, b₂) y₂) (p : Expr) :
    ((∃ D, Relation.ReflTransGen (GroundStep R) y₁.1 D ∧ p ∈ facts D) ↔
      ∃ D, Relation.ReflTransGen (GroundStep R) y₂.1 D ∧ p ∈ facts D) ∧
    ((∃ D, Relation.ReflTransGen (GroundStep R) y₁.1 D ∧ p ∈ facts D) ↔
      MonotoneInference.Derivable R (facts C) p) :=
  ⟨MonotoneInference.confluent monotone trivial (scheduler_ground_steps within₁ path₁)
      (scheduler_ground_steps within₂ path₂) p,
    MonotoneInference.eventual_facts monotone trivial (scheduler_ground_steps within₁ path₁) p⟩

/-- A priority scheduler fires only rules of its program. -/
theorem within_priority (program : List (RuleInstance Expr)) :
    Within (priority program) (fun r => r ∈ program) := by
  rintro s b f admitted b' ⟨i, found, noQueries, -⟩
  exact ⟨List.mem_of_getElem? found, noQueries⟩

end Monotone

/-! ## Controls -/

namespace Controls

open Search

/-- Two answers: `1` at depth one, and `0` at depth two below the first alternative. -/
def twoDepths : Space Bool ℕ := ⟨fun b => if b then [.inr false, .inl 1] else [.inl 0]⟩

/-- **Negative control for search handlers: the first answer sees order.** Depth-first finds `0`
first, breadth-first finds `1` first. -/
theorem first_sees_order :
    twoDepths.first .dfs 3 (.inr true) = some ([0, 0], 0) ∧
      twoDepths.first .bfs 3 (.inr true) = some ([1], 1) := by
  constructor <;> rfl

theorem dfs_all_defined : (twoDepths.all .dfs (.inr true)).Dom := ⟨4, rfl⟩
theorem bfs_all_defined : (twoDepths.all .bfs (.inr true)).Dom := ⟨4, rfl⟩

/-- **Positive control for search handlers.** On the same space `all` agrees, and it holds both
answers. -/
theorem all_agrees :
    (twoDepths.all .dfs (.inr true)).get dfs_all_defined =
        (twoDepths.all .bfs (.inr true)).get bfs_all_defined ∧
      ([0, 0], 0) ∈ (twoDepths.all .dfs (.inr true)).get dfs_all_defined ∧
      ([1], 1) ∈ (twoDepths.all .dfs (.inr true)).get dfs_all_defined := by
  refine ⟨twoDepths.all_eq_all .dfs .bfs _ _, ?_, ?_⟩ <;>
    exact (twoDepths.mem_all .dfs dfs_all_defined _).mpr rfl

open FragmentsOfTheStep FragmentsOfTheStep.RefinedScheduler FragmentsOfTheStep.GroundFirings
open FragmentsOfTheStep.MonotoneInference.Controls

/-- **Negative control for schedulers: takes make the handler matter.** The priority scheduler over
two rules taking `item` stays within them, the rule set is not monotone, the step reaches `right`
and the scheduler never does, and the two first runs part ways for good. -/
theorem takes_handler_dependent :
    Within (RefinedScheduler.Controls.leftFirst) choice ∧
      ¬ MonotoneInference.Monotone choice ∧
      (Relation.ReflTransGen (GroundStep choice) single afterRight ∧ right ∈ facts afterRight ∧
        ∀ y, Relation.ReflTransGen (RefinedScheduler.Controls.leftFirst).Transition (single, []) y →
          right ∉ facts y.1) ∧
      ((∃ D, Relation.ReflTransGen (GroundStep choice) afterRight D ∧ right ∈ facts D) ∧
        ¬ ∃ D, Relation.ReflTransGen (GroundStep choice) afterLeft D ∧ right ∈ facts D) := by
  obtain ⟨notMonotone, _, _, fromRight, notFromLeft⟩ := choice_not_confluent
  refine ⟨fun s b f admitted b' chosen => ?_, notMonotone, RefinedScheduler.Controls.priority_incomplete,
    fromRight, notFromLeft⟩
  obtain ⟨inProgram, noQueries⟩ := within_priority [toLeft, toRight] s b f admitted b' chosen
  refine ⟨?_, noQueries⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at inProgram
  exact inProgram

open NamesOnTheStep NamesOnTheStep.IssuingControls in
/-- Transitive closure's first firing on the edge `1 → 2`. -/
def firstOneTwo : Fir :=
  ⟨MonotoneInference.Controls.base 1 2, [], ⟨[], [(edge 1 2, 0)], [(path 1 2, 0)]⟩⟩

open NamesOnTheStep NamesOnTheStep.IssuingControls in
/-- Transitive closure's first firing on the edge `2 → 3`. -/
def firstTwoThree : Fir :=
  ⟨MonotoneInference.Controls.base 2 3, [], ⟨[], [(edge 2 3, 0)], [(path 2 3, 0)]⟩⟩

open NamesOnTheStep NamesOnTheStep.IssuingControls in
theorem oneTwo_admitted : NamesOnTheStep.IssuingControls.base.Admits (s := graph) firstOneTwo :=
  admits_of_valid (ground_valid (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl
    (no_checks rfl))

open NamesOnTheStep NamesOnTheStep.IssuingControls in
theorem twoThree_admitted : NamesOnTheStep.IssuingControls.base.Admits (s := graph) firstTwoThree :=
  admits_of_valid (ground_valid (by decide) (by decide) rfl rfl rfl (by decide) (by decide) rfl
    (no_checks rfl))

/-- The two orders of closure's base rules. -/
abbrev upward : Scheduler NamesOnTheStep.IssuingControls.base :=
  priority [MonotoneInference.Controls.base 1 2, MonotoneInference.Controls.base 2 3]
abbrev downward : Scheduler NamesOnTheStep.IssuingControls.base :=
  priority [MonotoneInference.Controls.base 2 3, MonotoneInference.Controls.base 1 2]

theorem within_closure (program : List (RuleInstance NamesOnTheStep.Expr))
    (inClosure : ∀ r ∈ program, closure r) : Within (priority program) closure := by
  intro s b f admitted b' chosen
  obtain ⟨inProgram, noQueries⟩ := within_priority program s b f admitted b' chosen
  exact ⟨inClosure _ inProgram, noQueries⟩

/-- **Positive control for schedulers on the monotone fragment.** Two priority schedulers over
transitive closure take different first firings and reach different stores, and from both the same
facts remain reachable. -/
theorem monotone_handlers_agree :
    ∃ (y₁ : NamesOnTheStep.IssuingControls.Conf × upward.Book)
      (y₂ : NamesOnTheStep.IssuingControls.Conf × downward.Book),
      Relation.ReflTransGen upward.Transition (graph, []) y₁ ∧
      Relation.ReflTransGen downward.Transition (graph, []) y₂ ∧ y₁.1.present ≠ y₂.1.present ∧
      ∀ p, (∃ D, Relation.ReflTransGen (GroundStep closure) y₁.1 D ∧ p ∈ facts D) ↔
        ∃ D, Relation.ReflTransGen (GroundStep closure) y₂.1 D ∧ p ∈ facts D := by
  have first : upward.Transition (graph, []) _ :=
    Scheduler.Transition.fire (Q := upward) firstOneTwo oneTwo_admitted
      ⟨0, rfl, rfl, by simp, rfl, fun j less => absurd less (Nat.not_lt_zero j)⟩
  have second : downward.Transition (graph, []) _ :=
    Scheduler.Transition.fire (Q := downward) firstTwoThree twoThree_admitted
      ⟨0, rfl, rfl, by simp, rfl, fun j less => absurd less (Nat.not_lt_zero j)⟩
  have upwardWithin : Within upward closure := within_closure _ fun r member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact Or.inl ⟨1, 2, rfl⟩
    · exact Or.inl ⟨2, 3, rfl⟩
  have downwardWithin : Within downward closure := within_closure _ fun r member => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact Or.inl ⟨2, 3, rfl⟩
    · exact Or.inl ⟨1, 2, rfl⟩
  refine ⟨_, _, .single first, .single second, by decide, fun p =>
    (monotone_handler_independence closure_monotone upwardWithin downwardWithin (by decide)
      (.single first) (.single second) p).1⟩

open GuardFreeProcessOrders FragmentsOfTheStep.LinearTake.Controls in
/-- **Positive control for effect orders.** The takers of `A` and of `B` from `LinearTake`, in the
two orders: both run, end in the same configuration up to solutions, and make the same bag. -/
theorem effects_commute :
    ConditionalSchedule.Executable NamesOnTheStep.IssuingControls.ground Prod.fst both [takeB, takeA] ∧
      SameUpTo NamesOnTheStep.IssuingControls.ground
        (ConditionalSchedule.follow Prod.fst both [takeA, takeB])
        (ConditionalSchedule.follow Prod.fst both [takeB, takeA]) ∧
      ([takeB, takeA].map fun x => ((x.1.produce : List NamesOnTheStep.Expr) : Multiset NamesOnTheStep.Expr)).sum =
        ([takeA, takeB].map fun x => ((x.1.produce : List NamesOnTheStep.Expr) : Multiset NamesOnTheStep.Expr)).sum :=
  effect_order_independence NamesOnTheStep.IssuingControls.ground Prod.fst _ [takeB, takeA] [takeA, takeB] both
    (.swap _ _ _) (fun x member => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> rfl)
    (List.pairwise_pair.mpr (by unfold NoReuse; decide))
    (List.pairwise_pair.mpr ⟨by unfold NoCause; decide, by unfold NoAsym; decide⟩)
    ⟨takeA_valid, takeB_after, (), fun e member => result_knowledge takeB_after e member⟩

end Controls

open Language in
#print axioms answers_append
open Language in
#print axioms answers_eq_account
open Language in
#print axioms outcome_sound
#print axioms scheduler_outcome
#print axioms ofScheduler_reached_iff
#print axioms search_handler_independence
#print axioms effect_order_independence
#print axioms scheduler_ground_steps
#print axioms monotone_handler_independence
#print axioms Controls.first_sees_order
#print axioms Controls.all_agrees
#print axioms Controls.takes_handler_dependent
#print axioms Controls.monotone_handlers_agree
#print axioms Controls.effects_commute

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies
