import Mettapedia.Computability.ComputationalTrinity

/-!
# Triangles of three faces over the one-point context

A Prime candidate has three faces: operational (what runs), intensional (what is typed) and
extensional (what it is as a set). `Mettapedia.Computability.ComputationalTrinity.Comparison`
is the triangle between three such faces, with no face prior. A closed specimen has no
context, so its faces are plain types and its triangle lives over the one-point context.

`triangleOfThree` builds that triangle from three maps that are given separately: from what
runs to what is typed, from what is typed to the set it means, and from what runs directly to
a set (by running it and reading the result, or by a recursion on the set side). Its
commutation is a hypothesis to prove: the set of the typed term is the set reached directly.
That proof is the content of a triangle.

`triangleOfMaps` is the special case in which the direct map is taken to be the composite of
the other two (`triangleOfMaps_programToSpace`). Its triangle commutes by definition, so it
says nothing about running; it only packages two maps. `losesProgramInformation_of` turns two
different programs with one meaning into the statement that the triangle is not exact.

Positive examples: the identity triangle on a type; doubling a number reached as `n + n` and
directly as `2 * n` (`doubling`). Negative examples: three maps that disagree give no
triangle (`successor_disagrees`), and the triangle that forgets the second component of a
pair loses program information (`secondForgotten_loses`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity

universe w

/-- The one-point context of closed specimens. -/
abbrev Closed := Discrete PUnit.{1}

/-- A plain type as a face over the one-point context. -/
abbrev closedFace (carrier : Type w) : Face.{0, 0, w} Closed :=
  (Functor.const Closedᵒᵖ).obj carrier

/-- **The triangle of three maps given separately**: what runs is mapped to what is typed,
what is typed to the set it means, and what runs directly to a set. The triangle commutes by
the hypothesis that the two ways to a set agree. -/
def triangleOfThree {Program Typed Meaning : Type w} (typing : Program → Typed)
    (meaning : Typed → Meaning) (direct : Program → Meaning)
    (agree : ∀ program, meaning (typing program) = direct program) :
    Comparison.{0, 0, w} Closed where
  program := closedFace Program
  logic := closedFace Typed
  space := closedFace Meaning
  programToLogic := (Functor.const Closedᵒᵖ).map (↾typing)
  logicToSpace := (Functor.const Closedᵒᵖ).map (↾meaning)
  programToSpace := (Functor.const Closedᵒᵖ).map (↾direct)
  coherence := by
    ext context program
    exact agree program

/-- The direct map of a triangle of three maps is the map that was given. -/
theorem triangleOfThree_programToSpace {Program Typed Meaning : Type w} (typing : Program → Typed)
    (meaning : Typed → Meaning) (direct : Program → Meaning)
    (agree : ∀ program, meaning (typing program) = direct program) (program : Program) :
    (triangleOfThree typing meaning direct agree).programToSpace.app
        (Opposite.op (Discrete.mk PUnit.unit)) program =
      direct program :=
  rfl

/-- **Two different programs with one set**: a triangle of three maps loses program
information when the direct map sends two different programs to one set. -/
theorem triangleOfThree_loses {Program Typed Meaning : Type w} (typing : Program → Typed)
    (meaning : Typed → Meaning) (direct : Program → Meaning)
    (agree : ∀ program, meaning (typing program) = direct program) {left right : Program}
    (distinct : left ≠ right) (same : direct left = direct right) :
    (triangleOfThree typing meaning direct agree).LosesProgramInformation :=
  ⟨Opposite.op (Discrete.mk PUnit.unit), left, right, distinct, same⟩

/-- Positive example: a number is doubled as `n + n` on the typed side and as `2 * n`
directly; the two ways agree by arithmetic, not by definition. -/
def doubling : Comparison.{0, 0, 0} Closed :=
  triangleOfThree (fun n : Nat => (n, n)) (fun pair : Nat × Nat => pair.1 + pair.2)
    (fun n => 2 * n) fun n => (Nat.two_mul n).symm

/-- Negative example: with the successor as the direct map the two ways to a set disagree, so
these three maps form no triangle. -/
theorem successor_disagrees : ¬ ∀ n : Nat, id (id n) = Nat.succ n :=
  fun agree => absurd (agree 0) (by decide)

/-- **The triangle of three carriers and two maps**: what runs is mapped to what is typed,
and what is typed to the set it means. The direct map is their composite, so this triangle
commutes by definition and states nothing about running. -/
def triangleOfMaps {Program Typed Meaning : Type w} (typing : Program → Typed)
    (meaning : Typed → Meaning) : Comparison.{0, 0, w} Closed where
  program := closedFace Program
  logic := closedFace Typed
  space := closedFace Meaning
  programToLogic := (Functor.const Closedᵒᵖ).map (↾typing)
  logicToSpace := (Functor.const Closedᵒᵖ).map (↾meaning)
  programToSpace := (Functor.const Closedᵒᵖ).map (↾(meaning ∘ typing))
  coherence := by
    ext context program
    rfl

variable {Program Typed Meaning : Type w} (typing : Program → Typed) (meaning : Typed → Meaning)

/-- The direct map from what runs to its meaning is the composite. -/
theorem triangleOfMaps_programToSpace (program : Program) :
    (triangleOfMaps typing meaning).programToSpace.app (Opposite.op (Discrete.mk PUnit.unit))
        program =
      meaning (typing program) :=
  rfl

/-- **Two different programs with one meaning**: the triangle loses program information, so
it is not the image of an exact trinity. -/
theorem losesProgramInformation_of {left right : Program} (distinct : left ≠ right)
    (same : meaning (typing left) = meaning (typing right)) :
    (triangleOfMaps typing meaning).LosesProgramInformation :=
  ⟨Opposite.op (Discrete.mk PUnit.unit), left, right, distinct, same⟩

/-- Positive example: the identity triangle on the natural numbers sends a program to
itself. -/
example : (triangleOfMaps (id : Nat → Nat) id).programToSpace.app
    (Opposite.op (Discrete.mk PUnit.unit)) (3 : Nat) = (3 : Nat) :=
  rfl

/-- Negative example: forgetting the second component of a pair loses program
information. -/
theorem secondForgotten_loses :
    (triangleOfMaps (id : Nat × Nat → Nat × Nat) Prod.fst).LosesProgramInformation :=
  losesProgramInformation_of id Prod.fst (left := (0, 0)) (right := (0, 1)) (by decide) rfl

end Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity
