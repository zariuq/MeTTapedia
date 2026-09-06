import Mettapedia.GSLT.LanguageDef.CompiledAnswerEffectControl

/-!
# Recursive answer producers as branching coalgebras

A compiled relation may expose several source-ordered alternatives.  Each
alternative either emits one answer or continues with a tail call.  This
module gives that shape a dialect-independent semantics and connects it to
the existing occurrence-preserving controller interface.

The semantic authority is a branching machine plus an answer-effect
denotation satisfying one unfolding law.  A physical provider is partial:
failure to realize an unfolding is `none`, never semantic zero.  Recursive
machines need not terminate, so exact completed-answer theorems require an
actual completion witness rather than hiding a totality assumption.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CompiledRecursiveAnswerProducer

open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.Dynamics.AnswerEffects

universe u v

/-- One source occurrence either emits or continues at another call state. -/
inductive Branch (State : Type u) (Answer : Type v) where
  | answer (value : Answer)
  | tail (state : State)
deriving DecidableEq, Repr

/-- The strategy-neutral recursive producer interface.  List position is
source-occurrence order; equal branch values remain distinct occurrences. -/
structure Machine (State : Type u) (Answer : Type v) where
  branches : State → List (Branch State Answer)

/-- Interpret a finite source-ordered branch family in an answer effect. -/
def foldBranches {State : Type u} {Answer : Type v}
    (effect : AnswerEffect.{v})
    (value : State → effect.Carrier Answer) :
    List (Branch State Answer) → effect.Carrier Answer
  | [] => effect.empty
  | .answer answer :: rest =>
      effect.choice (effect.pure answer) (foldBranches effect value rest)
  | .tail state :: rest =>
      effect.choice (value state) (foldBranches effect value rest)

/-- A completed denotation is a solution of the recursive unfolding equation
at one explicitly selected answer profile.  Productive infinite machines may
have no finite-list or finite-bag solution. -/
structure Denotation {State : Type u} {Answer : Type v}
    (machine : Machine State Answer) (effect : AnswerEffect.{v}) where
  value : State → effect.Carrier Answer
  unfold : ∀ state,
    value state = foldBranches effect value (machine.branches state)

theorem foldBranches_natural {State : Type u} {Answer : Type v}
    {source target : AnswerEffect.{v}}
    (morphism : AnswerEffect.Morphism source target)
    (value : State → source.Carrier Answer)
    (branches : List (Branch State Answer)) :
    morphism.map (foldBranches source value branches) =
      foldBranches target (fun state => morphism.map (value state)) branches := by
  induction branches with
  | nil => exact morphism.map_empty
  | cons branch rest inductionHypothesis =>
      cases branch with
      | answer answer =>
          rw [foldBranches, morphism.map_choice, morphism.map_pure,
            inductionHypothesis]
          rfl
      | tail state =>
          rw [foldBranches, morphism.map_choice, inductionHypothesis]
          rfl

namespace Denotation

/-- Observation forgetting transports recursive denotations.  In particular,
an ordered-list denotation induces the exact occurrence-bag denotation. -/
def map {State : Type u} {Answer : Type v}
    {machine : Machine State Answer} {source target : AnswerEffect.{v}}
    (denotation : Denotation machine source)
    (morphism : AnswerEffect.Morphism source target) :
    Denotation machine target where
  value state := morphism.map (denotation.value state)
  unfold state := by
    rw [denotation.unfold, foldBranches_natural]

end Denotation

/-! ## Coalgebra and controller integration -/

/-- Residual work distinguishes a callable state from an answer occurrence. -/
inductive Residual (State : Type u) (Answer : Type v) where
  | call (state : State)
  | answer (value : Answer)
deriving DecidableEq, Repr

def branchResidual {State : Type u} {Answer : Type v} :
    Branch State Answer → Residual State Answer
  | .answer answer => .answer answer
  | .tail state => .call state

/-- Recursive answer production is a finitely branching coalgebra.  It may
still generate an infinite process through tail calls. -/
def system {State : Type u} {Answer : Type v}
    (machine : Machine State Answer) :
    BranchingSystem (Residual State Answer) Answer where
  emit
    | .call _ => none
    | .answer answer => some answer
  successors
    | .call state => (machine.branches state).map branchResidual
    | .answer _ => []

def residualBagValue {State : Type u} {Answer : Type v}
    {machine : Machine State Answer}
    (denotation : Denotation machine bagEffect) :
    Residual State Answer → Multiset Answer
  | .call state => denotation.value state
  | .answer answer => {answer}

theorem foldValues_branchResidual {State : Type u} {Answer : Type v}
    {machine : Machine State Answer}
    (denotation : Denotation machine bagEffect)
    (branches : List (Branch State Answer)) :
    foldValues (residualBagValue denotation)
        (branches.map branchResidual) =
      foldBranches bagEffect denotation.value branches := by
  induction branches with
  | nil => rfl
  | cons branch rest inductionHypothesis =>
      cases branch <;>
        simp [foldValues, foldBranches, branchResidual,
          residualBagValue, inductionHypothesis, bagEffect]

/-- The recursive unfolding equation is precisely the additive account
needed by the generic controller theorem. -/
def additiveDenotation {State : Type u} {Answer : Type v}
    {machine : Machine State Answer}
    (denotation : Denotation machine bagEffect) :
    AdditiveDenotation (system machine) where
  value := residualBagValue denotation
  unfold residual := by
    cases residual with
    | answer answer =>
        simp [residualBagValue, system, optionBag, foldValues]
    | call state =>
        rw [residualBagValue, denotation.unfold]
        simp [system, optionBag, foldValues_branchResidual denotation]

/-- Any completed controller run realizes exactly the recursive producer's
occurrence bag.  No DFS, FIFO, adaptive, or parallel policy is privileged. -/
theorem completed_controller_exact_bag
    {State : Type u} {Answer : Type v}
    {machine : Machine State Answer}
    (denotation : Denotation machine bagEffect)
    {Memory : Type*}
    (controller : Controller (Residual State Answer) Answer Memory)
    (state : State) (fuel : Nat)
    (complete :
      (Snapshot.run (system machine) controller fuel
        (Snapshot.initial controller [.call state])).search.frontier = []) :
    eventBag
        (Snapshot.run (system machine) controller fuel
          (Snapshot.initial controller [.call state])).search.events =
      denotation.value state := by
  have exact := Snapshot.completed_run_denotation
    (system machine) controller (additiveDenotation denotation)
      [.call state] fuel complete
  simpa [foldValues, additiveDenotation, residualBagValue] using exact

/-- Completed runs under two possibly stateful strategies agree as bags even
when their answer streams and completion budgets differ. -/
theorem completed_controllers_exact_bag
    {State : Type u} {Answer : Type v}
    {machine : Machine State Answer}
    (denotation : Denotation machine bagEffect)
    {FirstMemory SecondMemory : Type*}
    (first : Controller (Residual State Answer) Answer FirstMemory)
    (second : Controller (Residual State Answer) Answer SecondMemory)
    (state : State) (firstFuel secondFuel : Nat)
    (firstComplete :
      (Snapshot.run (system machine) first firstFuel
        (Snapshot.initial first [.call state])).search.frontier = [])
    (secondComplete :
      (Snapshot.run (system machine) second secondFuel
        (Snapshot.initial second [.call state])).search.frontier = []) :
    eventBag
        (Snapshot.run (system machine) first firstFuel
          (Snapshot.initial first [.call state])).search.events =
      eventBag
        (Snapshot.run (system machine) second secondFuel
          (Snapshot.initial second [.call state])).search.events := by
  rw [completed_controller_exact_bag denotation first state firstFuel
      firstComplete,
    completed_controller_exact_bag denotation second state secondFuel
      secondComplete]

/-! ## Partial physical unfolding -/

/-- A physical provider may decline a call-state unfolding.  Every admitted
branch family must be the semantic source-occurrence family exactly. -/
structure Provider {State : Type u} {Answer : Type v}
    (machine : Machine State Answer) where
  branches? : State → Option (List (Branch State Answer))
  sound : ∀ state branches,
    branches? state = some branches → branches = machine.branches state

/-- One physical expansion, reusing the shared expansion boundary from the
finite answer-effect controller. -/
def expand? {State : Type u} {Answer : Type v}
    {machine : Machine State Answer} (provider : Provider machine) :
    Residual State Answer →
      Option
        (Mettapedia.GSLT.LanguageDef.CompiledAnswerEffectControl.Expansion
          (Residual State Answer) Answer)
  | .answer answer => some ⟨some answer, []⟩
  | .call state =>
      match provider.branches? state with
      | none => none
      | some branches => some ⟨none, branches.map branchResidual⟩

/-- Admitted physical expansion is exactly one semantic coalgebra step. -/
theorem expand?_sound {State : Type u} {Answer : Type v}
    {machine : Machine State Answer} (provider : Provider machine)
    (residual : Residual State Answer)
    (expansion :
      Mettapedia.GSLT.LanguageDef.CompiledAnswerEffectControl.Expansion
        (Residual State Answer) Answer)
    (executed : expand? provider residual = some expansion) :
    expansion.emit = (system machine).emit residual ∧
      expansion.successors = (system machine).successors residual := by
  cases residual with
  | answer answer =>
      simp [expand?] at executed
      subst expansion
      simp [system]
  | call state =>
      cases equation : provider.branches? state with
      | none => simp [expand?, equation] at executed
      | some branches =>
          simp [expand?, equation] at executed
          subst expansion
          have exactBranches := provider.sound state branches equation
          subst branches
          simp [system]

/-! ## Ordered speculative collection and the stream-fusion interface

The non-Prolog reference is the `Done / Skip / Yield` step algebra of Haskell
stream fusion (Coutts, Leshchinskiy, Stewart, ICFP 2007).  Physical refusal is
an outer `Option`, not `Done`.  A finite work allowance is likewise a physical
boundary, not the answer-effect zero.

The bridge below compares two independently recursive observers: direct
source-frontier collection and interpretation of the lowered stream step.
It concerns exact ordered finite observations; it does not certify C pointer
ownership, byte allocation, or the compiler's admitted matcher and guards.
-/

inductive StreamStep (State : Type u) (Answer : Type v) where
  | done
  | skip (next : State)
  | yield (answer : Answer) (next : State)

/-- One source-ordered frontier step in the stream-fusion vocabulary. -/
def streamStep? {State : Type u} {Answer : Type v}
    {machine : Machine State Answer} (provider : Provider machine) :
    List (Residual State Answer) →
      Option (StreamStep (List (Residual State Answer)) Answer)
  | [] => some .done
  | .answer answer :: rest => some (.yield answer rest)
  | .call state :: rest =>
      (provider.branches? state).map fun branches =>
        .skip (branches.map branchResidual ++ rest)

/-- A bounded interpreter of an independently supplied stream step.  Even an
already observed prefix remains private when a later step refuses. -/
def unstream? {State : Type u} {Answer : Type v}
    (step : State → Option (StreamStep State Answer)) :
    Nat → State → Option (List Answer)
  | 0, _ => none
  | fuel + 1, state =>
      match step state with
      | none => none
      | some .done => some []
      | some (.skip next) => unstream? step fuel next
      | some (.yield answer next) => (unstream? step fuel next).map (answer :: ·)

/-- Direct bounded collection over the existing recursive producer.  No
result is published until the whole frontier has completed. -/
def collect? {State : Type u} {Answer : Type v}
    {machine : Machine State Answer} (provider : Provider machine) :
    Nat → List (Residual State Answer) → Option (List Answer)
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, .answer answer :: rest =>
      (collect? provider fuel rest).map (answer :: ·)
  | fuel + 1, .call state :: rest =>
      match provider.branches? state with
      | none => none
      | some branches => collect? provider fuel (branches.map branchResidual ++ rest)

theorem collect?_eq_unstream {State : Type u} {Answer : Type v}
    {machine : Machine State Answer} (provider : Provider machine)
    (fuel : Nat) (frontier : List (Residual State Answer)) :
    collect? provider fuel frontier = unstream? (streamStep? provider) fuel frontier := by
  induction fuel generalizing frontier with
  | zero => rfl
  | succ fuel ih =>
      cases frontier with
      | nil => rfl
      | cons node rest =>
          cases node with
          | answer answer => simp [collect?, unstream?, streamStep?, ih]
          | call state =>
              cases equation : provider.branches? state <;>
                simp [collect?, unstream?, streamStep?, equation, ih]

def frontierListValue {State : Type u} {Answer : Type v}
    {machine : Machine State Answer} (denotation : Denotation machine listEffect) :
    List (Residual State Answer) → List Answer
  | [] => []
  | .answer answer :: rest => answer :: frontierListValue denotation rest
  | .call state :: rest =>
      List.append (denotation.value state) (frontierListValue denotation rest)

theorem frontierListValue_append {State : Type u} {Answer : Type v}
    {machine : Machine State Answer} (denotation : Denotation machine listEffect)
    (left right : List (Residual State Answer)) :
    frontierListValue denotation (left ++ right) =
      frontierListValue denotation left ++ frontierListValue denotation right := by
  induction left with
  | nil => rfl
  | cons node rest ih =>
      cases node <;> simp [frontierListValue, ih, List.append_assoc]

theorem frontierListValue_branches {State : Type u} {Answer : Type v}
    {machine : Machine State Answer} (denotation : Denotation machine listEffect)
    (branches : List (Branch State Answer)) :
    frontierListValue denotation (branches.map branchResidual) =
      foldBranches listEffect denotation.value branches := by
  induction branches with
  | nil => rfl
  | cons branch rest ih =>
      cases branch <;>
        simp [frontierListValue, branchResidual, foldBranches, listEffect, ih]

/-- Success reflects to the exact source list, including order and duplicate
occurrences.  A provider law is still required; a cost policy cannot supply it. -/
theorem collect?_exact_list {State : Type u} {Answer : Type v}
    {machine : Machine State Answer} (provider : Provider machine)
    (denotation : Denotation machine listEffect)
    (fuel : Nat) (frontier : List (Residual State Answer)) (answers : List Answer)
    (completed : collect? provider fuel frontier = some answers) :
    answers = frontierListValue denotation frontier := by
  induction fuel generalizing frontier answers with
  | zero => simp [collect?] at completed
  | succ fuel ih =>
      cases frontier with
      | nil => simpa [collect?, frontierListValue] using completed.symm
      | cons node rest =>
          cases node with
          | answer answer =>
              cases equation : collect? provider fuel rest with
              | none => simp [collect?, equation] at completed
              | some tail =>
                  have exactAnswers : answer :: tail = answers := by
                    simpa [collect?, equation] using completed
                  subst answers
                  rw [frontierListValue, ih rest tail equation]
          | call state =>
              cases equation : provider.branches? state with
              | none => simp [collect?, equation] at completed
              | some branches =>
                  have executed : collect? provider fuel
                      (branches.map branchResidual ++ rest) = some answers := by
                    simpa [collect?, equation] using completed
                  have exactBranches := provider.sound state branches equation
                  subst branches
                  rw [ih _ _ executed, frontierListValue_append,
                    frontierListValue_branches, ← denotation.unfold]
                  rfl

theorem exhausted_collection_is_not_zero {State : Type u} {Answer : Type v}
    {machine : Machine State Answer} (provider : Provider machine)
    (frontier : List (Residual State Answer)) :
    collect? provider 0 frontier ≠ some [] := by
  simp [collect?]

/-! ## Executable positive and negative boundaries -/

inductive PickState where
  | one
  | two
deriving DecidableEq, Repr

/-- A two-cell source-order analogue of the recursive `pick` relation: emit
the current head, then continue at the suffix. -/
def pickMachine : Machine PickState Nat where
  branches
    | .one => [.answer 1]
    | .two => [.answer 2, .tail .one]

def pickListDenotation : Denotation pickMachine listEffect where
  value
    | .one => [1]
    | .two => [2, 1]
  unfold state := by cases state <;> rfl

def pickBagDenotation : Denotation pickMachine bagEffect :=
    pickListDenotation.map listToBag

def partialPickProvider : Provider pickMachine where
  branches?
    | .one => none
    | .two => some [.answer 2, .tail .one]
  sound state branches equation := by
    cases state <;> simp_all [pickMachine]

/-- The first answer exists, but a later physical refusal prevents atomic
publication of that prefix.  Replaying the canonical source cannot duplicate it. -/
theorem late_decline_discards_prefix :
    collect? partialPickProvider 10 [.call .two] = none := by
  rfl

/-- Depth-first control is one exact ordered realization, not the semantic
definition of the producer. -/
theorem pick_depthFirst_source_order :
    (Snapshot.run (system pickMachine)
      (Controller.fixed Scheduler.depthFirst) 4
      (Snapshot.initial (Controller.fixed Scheduler.depthFirst)
        [.call .two])).search.events.map Emission.value = [2, 1] := by
  rfl

theorem pick_depthFirst_completes :
    (Snapshot.run (system pickMachine)
      (Controller.fixed Scheduler.depthFirst) 4
      (Snapshot.initial (Controller.fixed Scheduler.depthFirst)
        [.call .two])).search.frontier = [] := by
  rfl

/-- Equal values from two source branches remain two occurrences. -/
def duplicateMachine : Machine Unit Nat where
  branches _ := [.answer 7, .answer 7]

def duplicateBagDenotation : Denotation duplicateMachine bagEffect where
  value := fun _ => ({7, 7} : Multiset Nat)
  unfold _ := by simp [duplicateMachine, foldBranches, bagEffect]

theorem duplicate_occurrences_remain_two :
    duplicateBagDenotation.value () = ({7, 7} : Multiset Nat) := by
  rfl

def unavailablePickProvider : Provider pickMachine where
  branches? _ := none
  sound state branches equation := by simp at equation

/-- Physical unavailability declines even though the semantic answer bag is
nonempty.  Decline therefore cannot be implemented as zero answers. -/
theorem unavailable_declines_not_zero :
    expand? unavailablePickProvider (.call .two) = none ∧
      pickBagDenotation.value .two ≠ (0 : Multiset Nat) := by
  constructor
  · rfl
  · simp [pickBagDenotation, Denotation.map, pickListDenotation]
    intro empty
    have cardEquality := congrArg Multiset.card empty
    simp at cardEquality

#print axioms foldBranches_natural
#print axioms completed_controller_exact_bag
#print axioms completed_controllers_exact_bag
#print axioms expand?_sound
#print axioms pick_depthFirst_source_order
#print axioms pick_depthFirst_completes
#print axioms duplicate_occurrences_remain_two
#print axioms unavailable_declines_not_zero
#print axioms collect?_eq_unstream
#print axioms collect?_exact_list
#print axioms exhausted_collection_is_not_zero
#print axioms late_decline_discards_prefix

end Mettapedia.GSLT.LanguageDef.CompiledRecursiveAnswerProducer
