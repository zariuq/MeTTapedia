/-!
# Static individuation, becoming, and persistence

This interface separates three notions that must not be identified:

* `Individuated`: a boundary is closed in one system state;
* `Process`: a proof-relevant path by which system states change;
* `Persistence`: an already-closed boundary remains closed and observationally
  agreed across a change.

The interface does not claim that becoming closed creates a task hierarchy.
That additional interpretation is supplied downstream when it exists.

The terminology follows David Weinbaum and Viktoras Veitas's process account
of open-ended individuation; the abstraction is project-original.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.Individuation

universe uSystem uBoundary uStep

/-- A theory of system change, boundary closure, and boundary agreement. -/
structure Theory (System : Type uSystem) (Boundary : Type uBoundary) where
  Step : System → System → Type uStep
  Closed : System → Boundary → Prop
  Agrees : System → System → Boundary → Prop

variable {System : Type uSystem} {Boundary : Type uBoundary}

/-- A static individuated state with its witnessed boundary. -/
structure Individuated (theory : Theory.{uSystem, uBoundary, uStep}
    System Boundary) (system : System) : Type (max uBoundary uStep) where
  boundary : Boundary
  closed : theory.Closed system boundary

/-- A proof-relevant process of becoming.  The path retains every selected
step rather than quotienting the endpoints. -/
inductive Process (theory : Theory.{uSystem, uBoundary, uStep}
    System Boundary) : Nat → System → System → Type (max uSystem uStep) where
  | refl (system : System) : Process theory 0 system system
  | snoc {steps : Nat} {first middle last : System} :
      Process theory steps first middle → theory.Step middle last →
        Process theory (steps + 1) first last

namespace Process

variable {theory : Theory.{uSystem, uBoundary, uStep} System Boundary}
  {first middle last : System} {firstSteps lastSteps : Nat}

/-- Processes compose without discarding their intermediate steps. -/
def append (earlier : Process theory firstSteps first middle) :
    {lastSteps : Nat} → {last : System} →
      Process theory lastSteps middle last →
        Process theory (firstSteps + lastSteps) first last
  | 0, _, .refl _ => by simpa using earlier
  | _ + 1, _, .snoc history step => by
      simpa [Nat.add_assoc] using (append earlier history).snoc step

end Process

/-- A becoming process together with the closure it eventually reaches. -/
structure BecomingIndividuated
    (theory : Theory.{uSystem, uBoundary, uStep} System Boundary)
    (first last : System) : Type (max uSystem uBoundary uStep) where
  steps : Nat
  process : Process theory steps first last
  result : Individuated theory last

/-- Persistence of one selected boundary across two system states. -/
structure Persistence
    (theory : Theory.{uSystem, uBoundary, uStep} System Boundary)
    (first last : System) (boundary : Boundary) : Type uStep where
  sourceClosed : theory.Closed first boundary
  targetClosed : theory.Closed last boundary
  agrees : theory.Agrees first last boundary

end Mettapedia.Cybernetics.Individuation
