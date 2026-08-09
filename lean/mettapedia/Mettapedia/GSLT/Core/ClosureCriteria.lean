import Mettapedia.GSLT.Core.GSLT
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Two closure criteria for a language and its host

"Does this language need an outside manager?" bundles several different
questions, and a rebuttal to one reads as a rebuttal to all.  Two of them are
separable and checkable, and they are stated here.

A reduction relation says which steps exist.  It does not say which to take,
in what order, or how far — so every implementation supplies a driver, and the
existence of a driver settles nothing.  The useful questions are about *where
things live*:

* **Control closure** — does the driver keep private state that changes what is
  observed?  If two private states over the same configuration give different
  runs, the driver holds semantics rather than mechanism.
* **Extension closure** — is the available vocabulary determined by the
  language's own declarations, or by which host was built?  If two hosts of one
  language offer different operations, the vocabulary lives in the host.

Both are instances of one criterion: something is *mechanism* when the
observation factors through the language's own data, and *semantics* when it
does not.  That is `Core.NonFactorization`, applied one level up.

Each comes with a negative, because a closure property with no refutation is a
definition that cannot fail.
-/

namespace Mettapedia.GSLT.Core.ClosureCriteria

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.NonFactorization

universe u

/-! ## Drivers with private state

A driver chooses the next configuration.  It may carry state of its own — a
work queue, a cursor, a random seed — which the language cannot see. -/

/-- A driver for a theory, with private host state. -/
structure HostedDriver (theory : GSLT) where
  /-- State the host keeps and the language cannot name. -/
  State : Type u
  /-- Choose a next configuration, or stop. -/
  step : theory.Term → State → Option (theory.Term × State)
  /-- Every move the driver makes is a step of the theory. -/
  sound : ∀ term state next state',
    step term state = some (next, state') → theory.Step term next

namespace HostedDriver

variable {theory : GSLT}

/-- Run a driver for a bounded number of moves. -/
def run (driver : HostedDriver theory) :
    theory.Term → driver.State → Nat → theory.Term
  | term, _, 0 => term
  | term, state, fuel + 1 =>
      match driver.step term state with
      | none => term
      | some (next, state') => driver.run next state' fuel

/-- Every configuration a run reaches is reachable in the theory, so a driver
adds no steps of its own. -/
theorem run_multiStep (driver : HostedDriver theory) :
    ∀ (fuel : Nat) (term : theory.Term) (state : driver.State),
      theory.MultiStep term (driver.run term state fuel)
  | 0, term, _ => .refl term
  | fuel + 1, term, state => by
      unfold run
      cases hstep : driver.step term state with
      | none => exact .refl term
      | some pair =>
          exact .step (driver.sound term state pair.1 pair.2 hstep)
            (driver.run_multiStep fuel pair.1 pair.2)

end HostedDriver

/-! ## Control closure

The driver's private state is mechanism exactly when the run does not depend on
it. -/

/-- **Control closure**: the run is a function of the configuration alone, so
whatever the host remembers is not semantics. -/
def ControlClosed {theory : GSLT} (driver : HostedDriver theory) : Prop :=
  ∀ (term : theory.Term) (first second : driver.State) (fuel : Nat),
    driver.run term first fuel = driver.run term second fuel

/-- A driver that keeps no state is control closed.  This is the sanity check
on the definition, not a result. -/
theorem controlClosed_of_subsingleton {theory : GSLT}
    (driver : HostedDriver theory) (only : ∀ first second : driver.State, first = second) :
    ControlClosed driver := by
  intro term first second fuel
  rw [only first second]

/-! ### The negative

A driver whose private bit decides between two available steps, over a theory
where those steps lead to different configurations.  Same term, different host
state, different run — so the bit is semantics. -/

/-- Zero branches to one or two; both are final. -/
private inductive ForkStep : Nat → Nat → Prop
  | left : ForkStep 0 1
  | right : ForkStep 0 2

@[reducible] private def forkTheory : GSLT where
  Term := Nat
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := ForkStep
  rewrites_resp_left := by
    intro source source' target equal step
    subst equal
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst equal
    exact step

/-- The private bit chooses the branch. -/
@[reducible] private def forkDriver : HostedDriver forkTheory where
  State := Bool
  step := fun term state =>
    match term with
    | 0 => if state then some (1, state) else some (2, state)
    | _ => none
  sound := by
    intro term state next state' moved
    cases term with
    | zero =>
        cases state with
        | true =>
            cases moved
            exact ForkStep.left
        | false =>
            cases moved
            exact ForkStep.right
    | succ _ => simp at moved

/-- **Private host state can be semantics.**  One configuration, two host
states, two different runs — so this driver is not control closed, and its
queue is program logic rather than mechanism. -/
theorem forkDriver_not_controlClosed : ¬ ControlClosed forkDriver := by
  intro closed
  have collision := closed 0 true false 1
  simp [HostedDriver.run] at collision

/-- The same fact in the criterion's own vocabulary: the run does not factor
through the configuration. -/
private def forkFiber :
    NonTrivialFiber (fun pair : forkTheory.Term × Bool => pair.1)
      (fun pair => forkDriver.run pair.1 pair.2 1) where
  left := (0, true)
  right := (0, false)
  sameShadow := rfl
  differentValue := by decide

theorem forkDriver_run_not_factors :
    ¬ Factors (fun pair : forkTheory.Term × Bool => pair.1)
      (fun pair => forkDriver.run pair.1 pair.2 1) :=
  forkFiber.not_factors

/-! ## Extension closure

Whether new vocabulary can be added in the language, or only by building a
different host.  This is independent of control closure: a language can hold
all its control state and still be extensible only in its host's source. -/

/-- **Extension closure**: the operations actually available are determined by
the language's own declarations, not by which host was built. -/
def ExtensionClosed {Language Host Vocabulary : Type}
    (available : Language × Host → Vocabulary) : Prop :=
  Factors (fun pair : Language × Host => pair.1) available

/-- If every host offers the declared vocabulary and nothing else, the language
is extension closed. -/
theorem extensionClosed_of_declared {Language Host Vocabulary : Type}
    (declared : Language → Vocabulary) (available : Language × Host → Vocabulary)
    (agrees : ∀ pair, available pair = declared pair.1) :
    ExtensionClosed available :=
  ⟨declared, fun pair => (agrees pair).symm⟩

/-! ### The negative

Two builds of one host offering different operations for the same program.
The extra operation is real vocabulary, and no declaration of the language
mentions it. -/

private inductive HostBuild where
  | withSolver
  | withoutSolver
deriving DecidableEq

private def availableOperations : Unit × HostBuild → List String
  | (_, .withSolver) => ["query", "add", "solve"]
  | (_, .withoutSolver) => ["query", "add"]

private def hostFiber :
    NonTrivialFiber (fun pair : Unit × HostBuild => pair.1) availableOperations where
  left := ((), .withSolver)
  right := ((), .withoutSolver)
  sameShadow := rfl
  differentValue := by decide

/-- **A host case split is vocabulary, not mechanism.**  One program, two
builds, different operations — so the available vocabulary does not factor
through the language, and the host is where the language is extended. -/
theorem hostCaseSplit_not_extensionClosed :
    ¬ ExtensionClosed availableOperations :=
  hostFiber.not_factors

/-! ## The two are independent

Neither criterion implies the other, so they have to be checked separately —
which is why a rebuttal to one should not read as a rebuttal to both. -/

/-- A control-closed driver over a language whose vocabulary is still chosen by
the host: closure of control does not give closure of extension. -/
theorem controlClosed_does_not_give_extensionClosed :
    (∀ (driver : HostedDriver forkTheory),
        (∀ first second : driver.State, first = second) → ControlClosed driver) ∧
      ¬ ExtensionClosed availableOperations :=
  ⟨fun driver only => controlClosed_of_subsingleton driver only,
    hostCaseSplit_not_extensionClosed⟩

end Mettapedia.GSLT.Core.ClosureCriteria
