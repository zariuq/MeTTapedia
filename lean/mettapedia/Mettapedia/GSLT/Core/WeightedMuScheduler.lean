/-
# Weighted temporal policy for GSLT inference control

This module separates three structures which interact but must not be
identified:

* a graded clause changes the weight of an authored transition and is part of
  the reduction semantics;
* a quantale-valued objective aggregates evidence, weakness, or resource
  information over candidate work;
* an occurrence-preserving controller orders already-authorized work and can
  neither create nor discard an inference occurrence.

The separation sharpens the scheduler safety line.  Arbitrary controllers are
sound and all completed controllers have the same additive answer bag, but
temporal acceptance is not policy-independent: an unfair legal scheduler can
starve a reachable answer.  Liveness therefore requires a separate fairness or
parity-progress certificate.
-/

import Mettapedia.Algebra.QuantaleWeakness
import Mettapedia.GSLT.Core.InferenceControl
import Mettapedia.GSLT.LanguageDef.CertificateGSLTMuCalculusBoundary
import Mettapedia.GSLT.LanguageDef.CertificateGSLTParityAuthority
import Mettapedia.Logic.ModalMuCalculus
import Provenance.Semirings.Bool

namespace Mettapedia.GSLT.Core.WeightedMuScheduler

open Mettapedia.Algebra.QuantaleWeakness
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.Logic.ModalMuCalculus

universe uValue uCandidate uNode uAnswer uMemory uState uAct

/-! ## Graded clauses use Mathlib's commutative-semiring hierarchy -/

/-- A small graded-clause language.  `observe` is the candidate-sensitive
atom; the two connectives use the standard commutative-semiring operations. -/
inductive WeighClause (Value : Type uValue) (Candidate : Type uCandidate) where
  | scalar (value : Value)
  | observe (value : Candidate → Value)
  | plus (left right : WeighClause Value Candidate)
  | tensor (left right : WeighClause Value Candidate)

namespace WeighClause

def eval [CommSemiring Value] (candidate : Candidate) :
    WeighClause Value Candidate → Value
  | .scalar value => value
  | .observe value => value candidate
  | .plus left right =>
      eval candidate left + eval candidate right
  | .tensor left right =>
      eval candidate left * eval candidate right

/-- Boolean `where True` is exactly the constant unit grade. -/
theorem crisp_true_conservative (candidate : Candidate) :
    eval candidate (.scalar true : WeighClause Bool Candidate) = true :=
  rfl

/-- Boolean `where False` is exactly the zero grade. -/
theorem crisp_false_rejects (candidate : Candidate) :
    eval candidate (.scalar false : WeighClause Bool Candidate) = false :=
  rfl

/-- A one-state grade is simply one clause evaluated at each candidate; no
temporal state or controller memory is required. -/
def oneStateGrade [CommSemiring Value]
    (clause : WeighClause Value Candidate) : Candidate → Value :=
  fun candidate => eval candidate clause

end WeighClause

/-! ## Quantale-valued ordering of already-authorized work -/

section QuantalePolicy

variable {Q : Type uValue} [Semigroup Q] [CompleteLattice Q]
  [IsQuantale Q]

/-- A typed, stateful policy whose grade lives in an existing quantale.
Grades affect ordering only.  `advance` may learn from an expansion, but the
branching system remains the sole authority for successors.  Multiplication is
not assumed commutative: path order can matter even when a particular evidence
or cost instance happens to commute. -/
structure QuantalePolicy
    (Q : Type uValue) (Node : Type uNode) (Answer : Type uAnswer)
    (Memory : Type uMemory) [Semigroup Q] [CompleteLattice Q]
    [IsQuantale Q] where
  /-- Grade of an empty path.  It is explicit because Mathlib's `IsQuantale`
  deliberately assumes only a semigroup, and a carrier can expose several
  meaningful products without a globally privileged `One` instance. -/
  pathUnit : Q
  pathUnit_mul : ∀ grade, pathUnit * grade = grade
  mul_pathUnit : ∀ grade, grade * pathUnit = grade
  initialMemory : Memory
  grade : Memory → Node → Q
  prefer : Q → Q → Bool
  base : Memory → Scheduler Node
  advance : Memory → Node → Option Answer → List Node → Memory

namespace QuantalePolicy

/-- Aggregate the grades of a finite live frontier with the quantale join. -/
noncomputable def frontierGrade
    (policy : QuantalePolicy Q Node Answer Memory)
    (memory : Memory) (frontier : List Node) : Q :=
  sSup (policy.grade memory '' {node | node ∈ frontier})

/-- Sequential grades compose with the quantale multiplication. -/
def pathGrade (policy : QuantalePolicy Q Node Answer Memory)
    (memory : Memory) : List Node → Q
  | [] => policy.pathUnit
  | node :: rest => policy.grade memory node * pathGrade policy memory rest

/-- The policy refines only frontier order.  Integration and occurrence
multiplicity are inherited from the base scheduler. -/
noncomputable def scheduler
    (policy : QuantalePolicy Q Node Answer Memory) (memory : Memory) :
    Scheduler Node where
  reorder frontier :=
    List.insertionSort
      (fun first second =>
        policy.prefer (policy.grade memory first) (policy.grade memory second) = true)
      ((policy.base memory).reorder frontier)
  reorder_complete frontier :=
    (List.perm_insertionSort _ ((policy.base memory).reorder frontier)).trans
      ((policy.base memory).reorder_complete frontier)
  integrate := (policy.base memory).integrate
  integrate_complete := (policy.base memory).integrate_complete

/-- Realization at the existing trusted boundary: a typed policy is an
occurrence-preserving controller program. -/
noncomputable def controller
    (policy : QuantalePolicy Q Node Answer Memory) :
    Controller Node Answer Memory where
  initialMemory := policy.initialMemory
  scheduler := policy.scheduler
  advance := policy.advance

/-- A neutral policy carries a quantale value but performs exactly the base
scheduling policy. -/
def neutral (base : Scheduler Node) (pathUnit : Q)
    (pathUnit_mul : ∀ grade, pathUnit * grade = grade)
    (mul_pathUnit : ∀ grade, grade * pathUnit = grade) :
    QuantalePolicy Q Node Answer Unit where
  pathUnit := pathUnit
  pathUnit_mul := pathUnit_mul
  mul_pathUnit := mul_pathUnit
  initialMemory := ()
  grade _ _ := ⊤
  prefer _ _ := true
  base _ := base
  advance _ _ _ _ := ()

private theorem orderedInsert_always (head : Node) (values : List Node) :
    List.orderedInsert (fun _ _ : Node => True) head values =
      head :: values := by
  cases values with
  | nil => rfl
  | cons next rest =>
      exact List.orderedInsert_cons_of_le _ _ trivial

private theorem insertionSort_always
    (values : List Node) :
    List.insertionSort (fun _ _ : Node => True) values = values := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change List.orderedInsert (fun _ _ : Node => True) head
          (List.insertionSort (fun _ _ : Node => True) tail) = head :: tail
      rw [inductionHypothesis, orderedInsert_always]

/-- Semantic zero-overhead law: neutral graded control elaborates to the exact
ordinary scheduler, not merely a scheduler proved extensionally equivalent. -/
theorem neutral_scheduler_eq (base : Scheduler Node) (pathUnit : Q)
    (pathUnit_mul : ∀ grade, pathUnit * grade = grade)
    (mul_pathUnit : ∀ grade, grade * pathUnit = grade) :
    (neutral (Q := Q) (Answer := Answer) base pathUnit pathUnit_mul
      mul_pathUnit).scheduler () = base := by
  cases base
  simp [neutral, scheduler, insertionSort_always]

/-- **Safety line.**  A quantale policy cannot emit an unauthorized answer or
place an unauthorized node in the live frontier. -/
theorem run_sound
    (policy : QuantalePolicy Q Node Answer Memory)
    (system : BranchingSystem Node Answer) (roots : List Node) (fuel : Nat) :
    (Snapshot.run system policy.controller fuel
      (Snapshot.initial policy.controller roots)).search.Sound system roots := by
  exact Snapshot.sound_run system policy.controller
    (initial_sound system roots) fuel

/-- If two policies both finish, their additive answer bags agree.  This is
the policy-independent acceptance theorem that is valid without a fairness
hypothesis. -/
theorem completed_policies_bag_agree
    (system : BranchingSystem Node Answer)
    {FirstMemory SecondMemory : Type*}
    (first : QuantalePolicy Q Node Answer FirstMemory)
    (second : QuantalePolicy Q Node Answer SecondMemory)
    (denotation : AdditiveDenotation system) (roots : List Node)
    (firstFuel secondFuel : Nat)
    (firstComplete :
      (Snapshot.run system first.controller firstFuel
        (Snapshot.initial first.controller roots)).search.frontier = [])
    (secondComplete :
      (Snapshot.run system second.controller secondFuel
        (Snapshot.initial second.controller roots)).search.frontier = []) :
    eventBag
        (Snapshot.run system first.controller firstFuel
          (Snapshot.initial first.controller roots)).search.events =
      eventBag
        (Snapshot.run system second.controller secondFuel
          (Snapshot.initial second.controller roots)).search.events :=
  Snapshot.completed_controllers_bag_agree system first.controller
    second.controller denotation roots firstFuel secondFuel firstComplete
    secondComplete

end QuantalePolicy

end QuantalePolicy

/-! ## Temporal objectives and weighted alternating automata -/

/-- A typed temporal objective is an actual modal mu-calculus formula with one
distinguished observation predicate.  The environment closes that variable;
this avoids pretending that the current proposition-free formula grammar can
name answer states by itself. -/
structure TemporalObjective (State : Type uState) (Act : Type uAct) where
  lts : LTS State Act
  observed : Set State
  formula : Formula Act 1
  fixedPointsPositive :
    Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary.fixedPointsPositive
      formula = true

namespace TemporalObjective

/-- Satisfaction closes the one observation variable with the declared set. -/
def Accepts (objective : TemporalObjective State Act) (state : State) : Prop :=
  satisfies objective.lts (fun _ => objective.observed) objective.formula state

/-- `mu X. observed or diamond X`: eventually reach an observed state. -/
def eventuallyObserved (action : Act) : Formula Act 1 :=
  .mu (.disj (.var 1) (.diamond action (.var 0)))

/-- `nu X. observed and box X`: remain observed forever. -/
def alwaysObserved (action : Act) : Formula Act 1 :=
  .nu (.conj (.var 1) (.box action (.var 0)))

/-- `nu Y. (mu X. observed or diamond X) and box Y`: observation recurs
forever.  This is the fairness/liveness shape consumed by scheduler policies. -/
def alwaysEventuallyObserved (action : Act) : Formula Act 1 :=
  let eventuallyAtOuterLevel : Formula Act 2 :=
    .mu (.disj (.var 2) (.diamond action (.var 0)))
  .nu (.conj eventuallyAtOuterLevel (.box action (.var 0)))

theorem eventuallyObserved_positive (action : Act) :
    Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary.fixedPointsPositive
      (eventuallyObserved action) = true := by
  rfl

theorem alwaysObserved_positive (action : Act) :
    Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary.fixedPointsPositive
      (alwaysObserved action) = true := by
  rfl

theorem alwaysEventuallyObserved_positive (action : Act) :
    Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary.fixedPointsPositive
      (alwaysEventuallyObserved action) = true := by
  rfl

/-- Negative control: a fixed-point variable under negation cannot be packaged
as a temporal scheduler objective. -/
def negativeObjectiveFormula : Formula Unit 1 :=
  .mu (.neg (.var 0))

theorem negativeObjectiveFormula_rejected :
    Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary.fixedPointsPositive
      negativeObjectiveFormula = false := by
  rfl

theorem no_negativeObjective :
    ¬ ∃ objective : TemporalObjective Unit Unit,
      objective.formula = negativeObjectiveFormula := by
  rintro ⟨objective, formulaEq⟩
  have positive := objective.fixedPointsPositive
  rw [formulaEq, negativeObjectiveFormula_rejected] at positive
  contradiction

end TemporalObjective

/-- A quantale-weighted alternating parity automaton.  The parity game carries
alternation and the mu/nu priority discipline; weights decorate only authored
game edges.  A zero-weight authored edge is permitted, but a nonzero weight
may never invent an edge. -/
structure WeightedParityAutomaton
    (Q : Type uValue) (State : Type uState)
    [Semigroup Q] [CompleteLattice Q] [IsQuantale Q] where
  pathUnit : Q
  pathUnit_mul : ∀ grade, pathUnit * grade = grade
  mul_pathUnit : ∀ grade, grade * pathUnit = grade
  game : Mettapedia.GSLT.LanguageDef.CertificateGSLT.Parity.Game State
  weight : State → State → Q
  nonbottom_authorized : ∀ source target,
    weight source target ≠ ⊥ → game.edge source target = true

namespace WeightedParityAutomaton

variable {Q : Type uValue} {State : Type uState}
  [Semigroup Q] [CompleteLattice Q] [IsQuantale Q]

/-- Quantale join aggregates alternative outgoing transition grades. -/
noncomputable def outgoingGrade
    (automaton : WeightedParityAutomaton Q State) (source : State) : Q :=
  sSup (Set.range (automaton.weight source))

/-- Multiplication composes the grades along a finite automaton path. -/
def pathGrade (automaton : WeightedParityAutomaton Q State) :
    List (State × State) → Q
  | [] => automaton.pathUnit
  | edge :: rest => automaton.weight edge.1 edge.2 * pathGrade automaton rest

/-- A nonbottom one-edge path is necessarily an authored automaton edge. -/
theorem singleton_nonbottom_authorized
    (automaton : WeightedParityAutomaton Q State)
    (source target : State)
    (nonbottom : automaton.pathGrade [(source, target)] ≠ ⊥) :
    automaton.game.edge source target = true := by
  simp only [pathGrade, automaton.mul_pathUnit] at nonbottom
  exact automaton.nonbottom_authorized source target nonbottom

/-- Uniformly decorate every authored game edge with the path unit and every
non-edge with bottom.  This is the canonical uninformative weighting of an
existing parity game. -/
noncomputable def uniform (pathUnit : Q)
    (pathUnit_mul : ∀ grade, pathUnit * grade = grade)
    (mul_pathUnit : ∀ grade, grade * pathUnit = grade)
    (game : Mettapedia.GSLT.LanguageDef.CertificateGSLT.Parity.Game State) :
    WeightedParityAutomaton Q State where
  pathUnit := pathUnit
  pathUnit_mul := pathUnit_mul
  mul_pathUnit := mul_pathUnit
  game := game
  weight source target := if game.edge source target then pathUnit else ⊥
  nonbottom_authorized source target nonbottom := by
    by_cases edge : game.edge source target = true
    · exact edge
    · simp [edge] at nonbottom

end WeightedParityAutomaton

/-- An executable cyclic progress certificate for the nu/liveness side. -/
structure CyclicProgressCertificate
    {Q : Type uValue} {State : Type uState}
    [Semigroup Q] [CompleteLattice Q] [IsQuantale Q]
    [Fintype State] [DecidableEq State]
    (automaton : WeightedParityAutomaton Q State)
    (strategy : Mettapedia.GSLT.LanguageDef.CertificateGSLT.Parity.Strategy State)
    (root : State) where
  measure : Mettapedia.GSLT.LanguageDef.CertificateGSLT.Parity.ProgressMeasure
    automaton.game
  accepted : measure.check automaton.game strategy root = true

namespace CyclicProgressCertificate

open Mettapedia.GSLT.LanguageDef.CertificateGSLT.Parity

variable {Q : Type uValue} {State : Type uState}
  [Semigroup Q] [CompleteLattice Q] [IsQuantale Q]
  [Fintype State] [DecidableEq State]

/-- Construct the checked cyclic certificate canonically from the exact
finite controlled-graph condition characterized by the parity authority. -/
noncomputable def ofNoOddThresholdReturn
    {automaton : WeightedParityAutomaton Q State}
    {strategy : Strategy State} {root : State}
    (locallyValid : strategy.LocallyValid automaton.game root)
    (noReturn : ProgressMeasure.NoOddThresholdReturn
      automaton.game strategy) :
    CyclicProgressCertificate automaton strategy root where
  measure := ProgressMeasure.ofNoOddThresholdReturn automaton.game strategy
  accepted := (ProgressMeasure.check_eq_true_iff automaton.game strategy
    (ProgressMeasure.ofNoOddThresholdReturn automaton.game strategy) root).2
      ⟨locallyValid,
        ProgressMeasure.ofNoOddThresholdReturn_globallyValid
          automaton.game strategy noReturn⟩

/-- Generate and check a cyclic certificate from any root-winning policy.
The certificate stores the canonical root-reachable restriction, so an
irrelevant disconnected active component cannot obstruct certification. -/
noncomputable def ofParityWinning
    {automaton : WeightedParityAutomaton Q State}
    {strategy : Strategy State} {root : State}
    (winning : strategy.ParityWinning automaton.game root) :
    CyclicProgressCertificate automaton
      (strategy.reachableRestriction automaton.game root) root where
  measure := ProgressMeasure.ofNoOddThresholdReturn automaton.game
    (strategy.reachableRestriction automaton.game root)
  accepted := (ProgressMeasure.check_eq_true_iff automaton.game
    (strategy.reachableRestriction automaton.game root)
    (ProgressMeasure.ofNoOddThresholdReturn automaton.game
      (strategy.reachableRestriction automaton.game root)) root).2
        ⟨Strategy.reachableRestriction_locallyValid winning.1,
          ProgressMeasure.ofNoOddThresholdReturn_globallyValid
            automaton.game (strategy.reachableRestriction automaton.game root)
            (ProgressMeasure.noOddThresholdReturn_reachableRestriction winning)⟩

/-- A checked finite cyclic certificate rules out every odd-dominant infinite
play. -/
theorem winning
    {automaton : WeightedParityAutomaton Q State}
    {strategy : Strategy State} {root : State}
    (certificate : CyclicProgressCertificate automaton strategy root) :
    strategy.ParityWinning automaton.game root := by
  apply ProgressMeasure.parity_sound
  exact (ProgressMeasure.check_eq_true_iff automaton.game strategy
    certificate.measure root).mp certificate.accepted

end CyclicProgressCertificate

/-! ## Executable parity controls -/

open scoped ENNReal
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.Parity

/-- The existing even-dominant two-state game with explicit nonnegative edge
weights. -/
noncomputable def weightedGoodAutomaton :
    WeightedParityAutomaton ℝ≥0∞ Bool :=
  WeightedParityAutomaton.uniform 1 one_mul mul_one Canary.goodGame

def weightedGoodCertificate :
    CyclicProgressCertificate weightedGoodAutomaton Canary.goodStrategy false where
  measure := Canary.goodMeasure
  accepted := Canary.goodCertificate

/-- The same positive certificate can be synthesized from the graph
condition, rather than supplied as a hand-written rank table. -/
noncomputable def weightedGoodGeneratedCertificate :
    CyclicProgressCertificate weightedGoodAutomaton
      Canary.goodStrategy false :=
  CyclicProgressCertificate.ofNoOddThresholdReturn
    Canary.goodStrategy_wins.1 Canary.goodStrategy_noOddThresholdReturn

theorem weightedGood_generated_winning :
    Canary.goodStrategy.ParityWinning weightedGoodAutomaton.game false :=
  weightedGoodGeneratedCertificate.winning

/-- Positive control: the finite cyclic certificate proves the weighted
automaton's parity objective. -/
theorem weightedGood_winning :
    Canary.goodStrategy.ParityWinning weightedGoodAutomaton.game false :=
  weightedGoodCertificate.winning

/-- The odd self-loop with explicit edge weight. -/
noncomputable def weightedOddLoopAutomaton :
    WeightedParityAutomaton ℝ≥0∞ Unit :=
  WeightedParityAutomaton.uniform 1 one_mul mul_one Canary.oddLoopGame

/-- Negative control: no cyclic progress certificate can launder the losing
odd loop into an accepted liveness policy. -/
theorem weightedOddLoop_has_no_certificate :
    ¬ Nonempty
      (CyclicProgressCertificate weightedOddLoopAutomaton
        Canary.oddLoopStrategy ()) := by
  rintro ⟨certificate⟩
  exact Canary.oddLoop_not_winning certificate.winning

/-! ## The liveness boundary is nontrivial -/

/-- Legal scheduling policies can differ on liveness even though both satisfy
the occurrence safety interface. -/
theorem scheduler_order_can_change_liveness :
    (∃ fuel,
      (⟨Mettapedia.GSLT.Core.BranchingTemporal.Starvation.Node.answer, 42⟩ :
          Emission
            Mettapedia.GSLT.Core.BranchingTemporal.Starvation.Node Nat) ∈
        (run Mettapedia.GSLT.Core.BranchingTemporal.Starvation.system
          Scheduler.breadthFirst fuel
          (initial Mettapedia.GSLT.Core.BranchingTemporal.Starvation.roots)).events) ∧
      (∀ fuel,
        (⟨Mettapedia.GSLT.Core.BranchingTemporal.Starvation.Node.answer, 42⟩ :
            Emission
              Mettapedia.GSLT.Core.BranchingTemporal.Starvation.Node Nat) ∉
          (run Mettapedia.GSLT.Core.BranchingTemporal.Starvation.system
            Scheduler.depthFirst fuel
            (initial Mettapedia.GSLT.Core.BranchingTemporal.Starvation.roots)).events) := by
  constructor
  · exact ⟨2,
      Mettapedia.GSLT.Core.BranchingTemporal.Starvation.breadthFirst_emits_answer⟩
  · exact Mettapedia.GSLT.Core.BranchingTemporal.Starvation.depthFirst_starves_answer

end Mettapedia.GSLT.Core.WeightedMuScheduler
