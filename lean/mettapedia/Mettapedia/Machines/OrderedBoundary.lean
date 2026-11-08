import Mettapedia.Machines.BoundaryCore
import Mathlib.Data.List.Forall2
import Mathlib.Data.Multiset.Bind

/-!
# Ordered finite-answer boundaries

This carrier preserves result order as well as occurrence multiplicity.
It is required when a consumer can turn answer order into ordinary data,
as an ordered collection operation does. Selection acts on the completed
ordered batch, not independently on each producer alternative.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedBoundary

universe u
variable {I F G V W O : Type u}

/-- Ordered specialization of the shared boundary algebra. -/
abbrev Boundary (I F V O : Type u) :=
  BoundaryCore.Protocol List I F V O (· ++ ·)

def Boundary.run (b : Boundary I F V O) (body : F → List V) (input : I) : List O :=
  b.select (b.early input ++ (b.enter input).flatMap fun frame =>
    (body frame).flatMap (b.leave frame))

theorem Boundary.run_core (b : Boundary I F V O) (body : F → List V) (input : I) :
    b.run body input = BoundaryCore.Protocol.run b body input := rfl

/-- Related occurrences are aligned by position, rather than only by bag
membership. Their complete ordered continuations therefore compose. -/
theorem flatMap_eq_of_related {A B C : Type u} {related : A → B → Prop}
    {left : List A} {right : List B} (h : List.Forall₂ related left right)
    (f : A → List C) (g : B → List C)
    (same : ∀ a b, related a b → f a = g b) :
    left.flatMap f = right.flatMap g := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp only [List.flatMap_cons, same _ _ hab, ih]

theorem Boundary.run_eq_of_related
    (source : Boundary I F V O) (target : Boundary I G W O)
    (body : F → List V) (compiled : G → List W)
    (frames : F → G → Prop) (values : V → W → Prop)
    (early : ∀ input, source.early input = target.early input)
    (entry : ∀ input, List.Forall₂ frames (source.enter input) (target.enter input))
    (work : ∀ f g, frames f g → List.Forall₂ values (body f) (compiled g))
    (returns : ∀ f g, frames f g → ∀ v w, values v w →
      source.leave f v = target.leave g w)
    (selection : source.select = target.select) (input : I) :
    source.run body input = target.run compiled input := by
  have bodies : (source.enter input).flatMap (fun f => (body f).flatMap (source.leave f)) =
      (target.enter input).flatMap (fun g => (compiled g).flatMap (target.leave g)) := by
    apply flatMap_eq_of_related (entry input)
    intro f g hfg
    exact flatMap_eq_of_related (work f g hfg) _ _ (returns f g hfg)
  simp only [Boundary.run, early input, bodies, selection]

/-- Ordered boundary equality is safe under an arbitrary completed-batch
consumer, including consumers that expose the order as data. -/
theorem Boundary.consume_eq {R : Type u}
    (source : Boundary I F V O) (target : Boundary I G W O)
    (body : F → List V) (compiled : G → List W) (input : I)
    (same : source.run body input = target.run compiled input)
    (consume : List O → R) :
    consume (source.run body input) = consume (target.run compiled input) :=
  congrArg consume same

namespace Controls

def repeatOrdered : Boundary Unit Unit Nat Nat where
  early := fun _ => []
  enter := fun _ => [()]
  leave := fun _ value => [value, value]
  select := id

theorem ordered_occurrences : repeatOrdered.run (fun _ => [3, 1]) () = [3, 3, 1, 1] := rfl

/-- Equal output bags do not justify a consumer that observes position. -/
theorem equal_bags_different_heads :
    (([3, 1] : List Nat) : Multiset Nat) = ([1, 3] : List Nat) ∧
      ([3, 1] : List Nat).head? ≠ ([1, 3] : List Nat).head? := by
  constructor <;> decide

end Controls

end Mettapedia.Machines.OrderedBoundary
