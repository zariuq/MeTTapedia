import Mettapedia.Order.AccessibilityCode

/-!
# The accessibility route, read in Lean

The accessibility package of the candidate calculus
(`TypeTheory.Calculi.ParameterizedPiSigmaId.AccessibleRecursion`) has three
parts: an accessibility code with introduction and inversion, an inert
recursor, and its propositional unfolding. Its consistency model reads the code
as `Mettapedia.Order.AccCode` (`AccessibleRecursion.truth_acc`). This file is
the reading of the recursor at the level of Lean programs.

`InertRecursor r` is a recursor over `AccCode` known only through its
propositional unfolding
`recursor F a q = F a (fun y h => recursor F y (q.inv y h))`.
Nothing about it computes definitionally.

**Uniqueness** (`InertRecursor.rec_eq`): two inert recursors agree at every
accessible point, and any function satisfying the unfolding equation agrees with
them (`InertRecursor.rec_eq_of_fix`). So a program written through the inert
recursor computes the function its measure-based twin computes, and every fact
about it follows from the unfolding equation alone. An instance exists
(`InertRecursor.ofAcc`, through Lean's `Acc.rec`).
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.WellFoundedServices

open Mettapedia.Order

universe u v

variable {α : Sort u} {r : α → α → Prop}

/-- **An inert recursor** over the accessibility code: a recursor into every
motive, known only through its propositional unfolding. -/
structure InertRecursor (r : α → α → Prop) where
  recursor : {C : α → Sort v} → (∀ x, (∀ y, r y x → C y) → C x) → ∀ a, AccCode r a → C a
  unfold : ∀ {C : α → Sort v} (F : ∀ x, (∀ y, r y x → C y) → C x) (a : α) (q : AccCode r a),
    recursor F a q = F a fun y h => recursor F y (q.inv y h)

namespace InertRecursor

/-- **Uniqueness.** A function satisfying the unfolding equation at the
accessible points below `a` is the recursor's value there. -/
theorem rec_eq_of_fix (I : InertRecursor.{u, v} r) {C : α → Sort v}
    (F : ∀ x, (∀ y, r y x → C y) → C x) (g : ∀ x, C x)
    (fix : ∀ x, g x = F x fun y _ => g y) {a : α} (q : AccCode r a) : I.recursor F a q = g a := by
  induction acc_of_accCode q with
  | intro x _ ih =>
      rw [I.unfold, fix x]
      congr 1
      funext y h
      exact ih y h _

/-- **Two inert recursors agree** at every accessible point. -/
theorem rec_eq (I J : InertRecursor.{u, v} r) {C : α → Sort v} (F : ∀ x, (∀ y, r y x → C y) → C x)
    {a : α} (q : AccCode r a) : I.recursor F a q = J.recursor F a q := by
  induction acc_of_accCode q with
  | intro x _ ih =>
      rw [I.unfold, J.unfold]
      congr 1
      funext y h
      exact ih y h _

/-- The recursor at an accessible point does not depend on the accessibility
proof: the code is a proposition. -/
theorem rec_proof_irrel (I : InertRecursor.{u, v} r) {C : α → Sort v}
    (F : ∀ x, (∀ y, r y x → C y) → C x) {a : α} (q q' : AccCode r a) :
    I.recursor F a q = I.recursor F a q' := rfl

/-- **An inert recursor exists**: Lean's `Acc.rec`, which computes, satisfies
the propositional unfolding. The route itself never uses its computation. -/
noncomputable def ofAcc (r : α → α → Prop) : InertRecursor.{u, v} r where
  recursor := fun {C} F a q =>
    Acc.rec (motive := fun a _ => C a) (fun x _ ih => F x ih) (acc_of_accCode q)
  unfold := by
    intro C F a q
    have e : acc_of_accCode q = Acc.intro a fun y h => acc_of_accCode (q.inv y h) :=
      Subsingleton.elim _ _
    rw [e]

end InertRecursor

end Mettapedia.Algorithms.WellFoundedServices
