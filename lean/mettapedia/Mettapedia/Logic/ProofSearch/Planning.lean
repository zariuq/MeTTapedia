import Mettapedia.GSLT.Core.OperationalPathFibration

/-!
# Typed proof planning with displayed cost

A proof search has four observably different outcomes.  Success retains the
actual proof object.  Refutation retains a certificate accepted by a sound
counter-certificate system.  A constrained result exposes work still owed,
while exhaustion records failure of the selected search budget or search
space.  Neither of the latter is evidence that the goal is false.

The search dynamics are proof relevant.  Resource accounting is a displayed
fold over the same transition witnesses, rather than a second operational
relation.  Consequently two routes to the same indexed theorem may retain
different proof trees and different costs without disagreeing about the
theorem proved.
-/


set_option autoImplicit false

namespace Mettapedia.Logic.ProofSearch

universe u v w x y z

/-- A checked counter-certificate interface.  Acceptance rules out an actual
solution at the same indexed goal; it is stronger than a search procedure
returning no candidate. -/
structure CounterSystem (Goal : Type u) (Solution : Goal → Type u) where
  Certificate : Goal → Type u
  check : {goal : Goal} → Certificate goal → Bool
  sound : ∀ {goal : Goal} {certificate : Certificate goal},
    check certificate = true → Solution goal → False

/-- A nonempty collection of residual constraints. -/
structure Residual (Constraint : Type u) where
  head : Constraint
  tail : List Constraint

namespace Residual

def toList {Constraint : Type u} (residual : Residual Constraint) : List Constraint :=
  residual.head :: residual.tail

@[simp] theorem toList_ne_nil {Constraint : Type u}
    (residual : Residual Constraint) : residual.toList ≠ [] := by
  simp [toList]

end Residual

/-- Exhausting a bounded search and completely exploring a chosen finite
search space are both algorithmic failures.  Neither constructor is a
counter-certificate. -/
inductive Exhaustion where
  | budget (limit spent : Nat) (reached : limit ≤ spent)
  | searchSpace (visited : Nat)

/-- The four terminal observations of a typed proof plan. -/
inductive Outcome {Goal : Type u} (Solution : Goal → Type u)
    (counter : CounterSystem Goal Solution) (Constraint : Goal → Type u)
    (goal : Goal) : Type u where
  | solved (proof : Solution goal)
  | refuted (certificate : counter.Certificate goal)
      (accepted : counter.check certificate = true)
  | constrained (residual : Residual (Constraint goal))
  | exhausted (failure : Exhaustion)

namespace Outcome

/-- A checked refutation and an actual solution of the same indexed goal
cannot coexist. -/
theorem refuted_excludes_solution {Goal : Type u} {Solution : Goal → Type u}
    {counter : CounterSystem Goal Solution}
    {goal : Goal} (certificate : counter.Certificate goal)
    (accepted : counter.check certificate = true) (proof : Solution goal) : False :=
  counter.sound accepted proof

end Outcome

/-- A typed proof plan is a proof-relevant transition system with one indexed
goal and a partial terminal observation. -/
structure System {Goal : Type u} (Solution : Goal → Type u)
    (counter : CounterSystem Goal Solution) (Constraint : Goal → Type u)
    (goal : Goal) where
  State : Type u
  initial : State
  Step : State → State → Type u
  observe : State → Option (Outcome Solution counter Constraint goal)

namespace System

/-- An execution trace retains the exact plan-step witness at every edge. -/
inductive Trace {Goal : Type u} {Solution : Goal → Type u}
    {counter : CounterSystem Goal Solution} {Constraint : Goal → Type u}
    {goal : Goal} (plan : System Solution counter Constraint goal) :
    plan.State → plan.State → Type u where
  | nil (state : plan.State) : Trace plan state state
  | cons {source middle target : plan.State} :
      plan.Step source middle → Trace plan middle target →
        Trace plan source target

namespace Trace

def append {Goal : Type u} {Solution : Goal → Type u}
    {counter : CounterSystem Goal Solution} {Constraint : Goal → Type u}
    {goal : Goal} {plan : System Solution counter Constraint goal}
    {first middle last : plan.State} :
    Trace plan first middle → Trace plan middle last → Trace plan first last
  | .nil _, suffix => suffix
  | .cons step rest, suffix => .cons step (append rest suffix)

@[simp] theorem append_nil {Goal : Type u} {Solution : Goal → Type u}
    {counter : CounterSystem Goal Solution} {Constraint : Goal → Type u}
    {goal : Goal} {plan : System Solution counter Constraint goal}
    {source target : plan.State} (trace : Trace plan source target) :
    trace.append (.nil target) = trace := by
  induction trace with
  | nil => rfl
  | cons step rest induction => simp [append, induction]

@[simp] theorem append_assoc {Goal : Type u} {Solution : Goal → Type u}
    {counter : CounterSystem Goal Solution} {Constraint : Goal → Type u}
    {goal : Goal} {plan : System Solution counter Constraint goal}
    {first second third fourth : plan.State}
    (left : Trace plan first second) (middle : Trace plan second third)
    (right : Trace plan third fourth) :
    (left.append middle).append right = left.append (middle.append right) := by
  induction left with
  | nil => rfl
  | cons step rest induction => simp [append, induction]

end Trace

/-- A selected additive resource interpretation of the exact plan events. -/
structure CostModel {Goal : Type u} {Solution : Goal → Type u}
    {counter : CounterSystem Goal Solution} {Constraint : Goal → Type u}
    {goal : Goal} (plan : System Solution counter Constraint goal)
    (Grade : Type v) [AddMonoid Grade] where
  charge : {source target : plan.State} → plan.Step source target → Grade

namespace CostModel

def total {Goal : Type u} {Solution : Goal → Type u}
    {counter : CounterSystem Goal Solution} {Constraint : Goal → Type u}
    {goal : Goal} {plan : System Solution counter Constraint goal}
    {Grade : Type v} [AddMonoid Grade] (cost : CostModel plan Grade)
    {source target : plan.State} : Trace plan source target → Grade
  | .nil _ => 0
  | .cons step rest => cost.charge step + cost.total rest

@[simp] theorem total_append {Goal : Type u} {Solution : Goal → Type u}
    {counter : CounterSystem Goal Solution} {Constraint : Goal → Type u}
    {goal : Goal} {plan : System Solution counter Constraint goal}
    {Grade : Type v} [AddMonoid Grade] (cost : CostModel plan Grade)
    {first middle last : plan.State}
    (firstTrace : Trace plan first middle) (suffix : Trace plan middle last) :
    cost.total (firstTrace.append suffix) =
      cost.total firstTrace + cost.total suffix := by
  induction firstTrace with
  | nil => simp [total, Trace.append]
  | cons step rest induction => simp [total, Trace.append, induction, add_assoc]

end CostModel

/-- A completed run packages one terminal observation with the exact trace
that reached it. -/
structure Run {Goal : Type u} {Solution : Goal → Type u}
    {counter : CounterSystem Goal Solution} {Constraint : Goal → Type u}
    {goal : Goal} (plan : System Solution counter Constraint goal)
    (outcome : Outcome Solution counter Constraint goal) where
  final : plan.State
  trace : plan.Trace plan.initial final
  observed : plan.observe final = some outcome

end System

/-! ## Evidence-bearing stages and displayed cost -/

/-- A stage is specified by the exact evidence connecting each input and
output.  Search runs, successful compilation equations, and operational paths
are instances of this one interface. -/
structure Stage (Input : Type u) (Output : Type v) where
  Evidence : Input → Output → Type w

namespace Stage

/-- Composition retains the intermediate object and both pieces of evidence. -/
def comp {Input : Type u} {Middle : Type v} {Output : Type w}
    (first : Stage Input Middle) (second : Stage Middle Output) :
    Stage Input Output where
  Evidence input output :=
    Sigma fun middle => first.Evidence input middle × second.Evidence middle output

/-- Rebracketing composed stages loses no intermediate evidence. -/
def associator {Input : Type u} {FirstMiddle : Type v}
    {SecondMiddle : Type w} {Output : Type x}
    (first : Stage Input FirstMiddle) (second : Stage FirstMiddle SecondMiddle)
    (third : Stage SecondMiddle Output) (input : Input) (output : Output) :
    ((first.comp second).comp third).Evidence input output ≃
      (first.comp (second.comp third)).Evidence input output where
  toFun evidence :=
    ⟨evidence.2.1.1, evidence.2.1.2.1,
      ⟨evidence.1, evidence.2.1.2.2, evidence.2.2⟩⟩
  invFun evidence :=
    ⟨evidence.2.2.1, ⟨evidence.1, evidence.2.1, evidence.2.2.2.1⟩,
      evidence.2.2.2.2⟩
  left_inv evidence := by rcases evidence with ⟨_, ⟨⟨_, _, _⟩, _⟩⟩; rfl
  right_inv evidence := by rcases evidence with ⟨_, _, ⟨_, _, _⟩⟩; rfl

/-- A displayed resource interpretation of the exact evidence of one stage. -/
structure Cost {Input : Type u} {Output : Type v} (stage : Stage Input Output)
    (Grade : Type w) [AddMonoid Grade] where
  charge : {input : Input} → {output : Output} → stage.Evidence input output → Grade

namespace Cost

/-- Costs of composed evidence add in execution order. -/
def comp {Input : Type u} {Middle : Type v} {Output : Type w}
    {Grade : Type x} [AddMonoid Grade]
    {first : Stage Input Middle} {second : Stage Middle Output}
    (firstCost : Cost first Grade) (secondCost : Cost second Grade) :
    Cost (first.comp second) Grade where
  charge evidence :=
    firstCost.charge evidence.2.1 + secondCost.charge evidence.2.2

@[simp] theorem comp_charge {Input : Type u} {Middle : Type v}
    {Output : Type w} {Grade : Type x} [AddMonoid Grade]
    {first : Stage Input Middle} {second : Stage Middle Output}
    (firstCost : Cost first Grade) (secondCost : Cost second Grade)
    {input : Input} {middle : Middle} {output : Output}
    (firstEvidence : first.Evidence input middle)
    (secondEvidence : second.Evidence middle output) :
    (firstCost.comp secondCost).charge
        ⟨middle, firstEvidence, secondEvidence⟩ =
      firstCost.charge firstEvidence + secondCost.charge secondEvidence :=
  rfl

end Cost
end Stage

namespace System

/-- A complete plan run is the evidence of a stage from a trigger to one of
the plan's four typed outcomes. -/
def completionStage {Goal : Type u} {Solution : Goal → Type u}
    {counter : CounterSystem Goal Solution} {Constraint : Goal → Type u}
    {goal : Goal} (plan : System Solution counter Constraint goal) :
    Stage Unit (Outcome Solution counter Constraint goal) where
  Evidence _ outcome := Run plan outcome

/-- The cost of the completion stage is exactly the fold over the run's own
transition trace. -/
def completionCost {Goal : Type u} {Solution : Goal → Type u}
    {counter : CounterSystem Goal Solution} {Constraint : Goal → Type u}
    {goal : Goal} {plan : System Solution counter Constraint goal}
    {Grade : Type v} [AddMonoid Grade] (cost : CostModel plan Grade) :
    Stage.Cost plan.completionStage Grade where
  charge run := cost.total run.trace

end System

/-! ## Operational execution instance -/

namespace OperationalAdapter

open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational

/-- Finite proof-relevant GSLT paths are the evidence of an execution stage. -/
def executionStage (system : GSLT.{u}) : Stage system.Term system.Term where
  Evidence := ExecutionPath system

/-- Primitive-path length is a displayed cost of the path itself. -/
def pathLengthCost (system : GSLT.{0}) : Stage.Cost (executionStage system) Nat where
  charge path := path.length

@[simp] theorem pathLengthCost_charge {system : GSLT.{0}}
    {source target : system.Term} (path : ExecutionPath system source target) :
    (pathLengthCost system).charge path = path.length := rfl

end OperationalAdapter


end Mettapedia.Logic.ProofSearch
