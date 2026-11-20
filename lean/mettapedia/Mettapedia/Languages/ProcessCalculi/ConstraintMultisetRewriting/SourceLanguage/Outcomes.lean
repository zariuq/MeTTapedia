import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Semantics

/-!
# What a program answers when its alternatives share the world: a set of bags

In the reference semantics the alternatives of a configuration share the world: the scope counter,
the handle counter and the spaces. A step may move any live alternative. So one query can have runs
that end with different bags of answers, when an alternative writes a space another one reads
(`ExampleRace`). What a program answers is then the **set** of the bags of its quiescent runs
(`Outcomes`).

* **Races** (`Race`): a configuration with two live alternatives, one about to write (`add`, `remove`)
  at an address its store determines, the other about to read or write the same address.
* **Moves that leave the world as it is commute** (`moves_commute`): two such moves of different
  alternatives reach the same configuration in either order. Moves that take a fresh scope (`apply`,
  a bind, `query`, `remove`, `new`, `delay`) commute only up to exchanging the two scopes they take:
  in one order the first alternative's copy is at scope `n` and the second's at `n + 1`, in the other
  order the reverse (`ExampleScopes.orders_differ`, `ExampleScopes.orders_answer_alike`). Answers do
  not see names (`Laws.answers_rename`), but that every move is equivariant under exchanging two
  scopes is not proved here.
* **The handle counter is shared too**: two `new`s of different alternatives take the supply's values
  in the order in which they move, and answers see those values. So a query that reaches no race on a
  space can still have two bags (`ExampleHandles.two_bags`): `RaceFree`, a condition on spaces only,
  does not give one bag. A statement that programs without races have one bag has to count `new` as a
  write of the counter, or compare bags up to a permutation of the supply's values; neither is proved
  here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.SharedWorld

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}
variable (D : Discipline S Γ star) (P : Program κ Γ star D.Ty) (supply : ℕ → Term S Γ star)

/-- **What a program answers from a configuration**: the bags of answers of its quiescent runs. -/
def Outcomes (C₀ : Config κ Γ star D.Ty) : Set (Multiset (Set (Term S Γ star))) :=
  {A | ∃ C, Runs D P supply C₀ C ∧ C.Quiescent P supply ∧ C.answers = A}

variable {D}

/-- The alternative is about to write the space at `h`. -/
def WritesAt (b : Branch κ Γ star D.Ty) (h : Term S Γ star) : Prop :=
  ∃ sp t k, (b.focus = .eval (.add sp t k) ∨ b.focus = .eval (.remove sp t k)) ∧ Determines b.store sp h

/-- The alternative is about to read or write the space at `h`. -/
def TouchesAt (b : Branch κ Γ star D.Ty) (h : Term S Γ star) : Prop :=
  ∃ sp t k, (b.focus = .eval (.query sp t k) ∨ b.focus = .eval (.add sp t k) ∨
    b.focus = .eval (.remove sp t k)) ∧ Determines b.store sp h

/-- **A race**: one live alternative about to write a space that another is about to read or write. -/
def Race (C : Config κ Γ star D.Ty) : Prop :=
  ∃ b₁ b₂ rest h, C.branches = b₁ ::ₘ b₂ ::ₘ rest ∧ Solvable b₁.store ∧ Solvable b₂.store ∧
    WritesAt b₁ h ∧ TouchesAt b₂ h

/-- A run from `C₀` never reaches a race on a space. It does not give one bag of answers: the handle
counter is shared as well (`ExampleHandles.two_bags`). -/
def RaceFree (C₀ : Config κ Γ star D.Ty) : Prop := ∀ C, Runs D P supply C₀ C → ¬ Race C

variable {P supply}

/-- **Two moves of different alternatives that leave the world as it is commute**: moving the first
alternative and then the second, or the second and then the first, reaches the same configuration. -/
theorem moves_commute {w : World κ Γ star} {b₁ b₂ : Branch κ Γ star D.Ty}
    {bs₁ bs₂ rest : Multiset (Branch κ Γ star D.Ty)} (live₁ : Solvable b₁.store) (live₂ : Solvable b₂.store)
    (m₁ : Move D P supply w b₁ w bs₁) (m₂ : Move D P supply w b₂ w bs₂) :
    (Step D P supply ⟨w, b₁ ::ₘ b₂ ::ₘ rest⟩ ⟨w, bs₁ + (b₂ ::ₘ rest)⟩ ∧
        Step D P supply ⟨w, bs₁ + (b₂ ::ₘ rest)⟩ ⟨w, bs₁ + bs₂ + rest⟩) ∧
      (Step D P supply ⟨w, b₁ ::ₘ b₂ ::ₘ rest⟩ ⟨w, bs₂ + (b₁ ::ₘ rest)⟩ ∧
        Step D P supply ⟨w, bs₂ + (b₁ ::ₘ rest)⟩ ⟨w, bs₁ + bs₂ + rest⟩) := by
  refine ⟨⟨Step.of_eq rfl rfl live₁ m₁, ?_⟩, ⟨Step.of_eq (Multiset.cons_swap _ _ _) rfl live₂ m₂, ?_⟩⟩
  · refine Step.of_eq (rest := bs₁ + rest) (by rw [Multiset.add_cons]) ?_ live₂ m₂
    rw [add_comm bs₁ bs₂, add_assoc]
  · refine Step.of_eq (rest := bs₂ + rest) (by rw [Multiset.add_cons]) ?_ live₁ m₁
    rw [add_assoc]

#print axioms moves_commute

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.SharedWorld
