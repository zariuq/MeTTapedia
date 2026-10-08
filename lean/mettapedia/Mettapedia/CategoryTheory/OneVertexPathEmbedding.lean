import Mathlib.Combinatorics.Quiver.Path

/-!
# Exact factor lifting for an embedded one-vertex frame language

A list stores outer frames first. Its actual path action is built with path
constructors. Any factorization of an embedded path has an embedded middle
vertex and lifts both complete factors. This property is stronger than mere
injectivity and supports actual relative-pushout comparison with an extension.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.OneVertexPathEmbedding

universe u v w

variable {V : Type u} [Quiver.{v} V] {Frames : Type w} {base : V}
variable (embed : Frames → (base ⟶ base))

def path : List Frames → Quiver.Path base base
  | [] => .nil
  | frame :: previous => (path previous).cons (embed frame)

theorem path_append (outer inner : List Frames) :
    path embed (outer ++ inner) = (path embed inner).comp (path embed outer) := by
  induction outer with
  | nil => rfl
  | cons frame previous inductionHypothesis =>
    exact congrArg (fun path => path.cons (embed frame)) inductionHypothesis

theorem path_injective (frames : Function.Injective embed) : Function.Injective (path embed) := by
  intro first
  induction first with
  | nil =>
    intro second same
    cases second with
    | nil => rfl
    | cons frame previous => cases same
  | cons frame previous inductionHypothesis =>
    intro second same
    cases second with
    | nil => cases same
    | cons other otherPrevious =>
      have frameEq := frames (eq_of_heq (Quiver.Path.hom_heq_of_cons_eq_cons same))
      have previousEq := inductionHypothesis
        (eq_of_heq (Quiver.Path.heq_of_cons_eq_cons same))
      exact congrArg₂ List.cons frameEq previousEq

/-- Both factors are reconstructed from the given actual path equality. A
new vertex or an extra frame cannot be hidden inside the source path. -/
theorem factors_lift (supplied : List Frames) {middle : V}
    (inner : Quiver.Path base middle) (outer : Quiver.Path middle base)
    (same : inner.comp outer = path embed supplied) :
    middle = base ∧ ∃ first second : List Frames,
      HEq inner (path embed first) ∧ HEq outer (path embed second) := by
  induction supplied generalizing middle with
  | nil =>
    have counted := congrArg Quiver.Path.length same
    simp only [path, Quiver.Path.length_comp, Quiver.Path.length_nil] at counted
    have innerZero : inner.length = 0 := by omega
    have outerZero : outer.length = 0 := by omega
    have vertex := Quiver.Path.eq_of_length_zero outer outerZero
    cases vertex
    exact ⟨rfl, [], [], heq_of_eq (Quiver.Path.eq_nil_of_length_zero inner innerZero),
      heq_of_eq (Quiver.Path.eq_nil_of_length_zero outer outerZero)⟩
  | cons frame previous inductionHypothesis =>
    cases outer with
    | nil => exact ⟨rfl, frame :: previous, [], heq_of_eq same, HEq.rfl⟩
    | @cons otherMiddle _ otherPrevious otherFrame =>
      have vertex := Quiver.Path.obj_eq_of_cons_eq_cons same
      cases vertex
      have prefixSame := eq_of_heq (Quiver.Path.heq_of_cons_eq_cons same)
      have frameSame := eq_of_heq (Quiver.Path.hom_heq_of_cons_eq_cons same)
      obtain ⟨middleSame, first, second, innerSame, outerSame⟩ := inductionHypothesis inner otherPrevious prefixSame
      cases middleSame
      cases eq_of_heq outerSame
      cases frameSame
      exact ⟨rfl, first, frame :: second, innerSame, HEq.rfl⟩

end Mettapedia.CategoryTheory.OneVertexPathEmbedding
