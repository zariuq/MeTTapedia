import Mettapedia.Machines.ScopedCommit

/-!
# Composing finite answer demands

Successive demands use the retained continuation and the world left by the
previous demand. The theorem concerns the existing delimited search evaluator;
it introduces neither a new evaluator nor a different commitment policy.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ScopedCommit

universe u v
variable {Local : Type u} {World : Type v}

theorem selectFrom_stopped (demand : Nat) (world : World) :
    selectFrom (Local := Local) demand stopAnswers world =
      ([], world, stopAnswers) := by
  cases demand <;> rfl

/-- Answer quotas compose without replay, including the continuation itself.
An exhausted first demand remains exhausted under any second quota. -/
theorem selectFrom_add (first second : Nat) (search : World → Answers Local World)
    (world : World) :
    selectFrom (first + second) search world =
      let earlier := selectFrom first search world
      let later := selectFrom second earlier.2.2 earlier.2.1
      (earlier.1 ++ later.1, later.2.1, later.2.2) := by
  induction first generalizing search world with
  | zero => simp [selectFrom]
  | succ first ih =>
    rw [Nat.succ_add]
    simp only [selectFrom]
    cases produced : search world with
    | stop final => simp [selectFrom_stopped]
    | more value here residual =>
      simp only [ih, List.cons_append]

/-- A bounded demand contributes a prefix of the actual completed search,
with multiplicity. This does not equate the intermediate and final worlds. -/
theorem selectFrom_prefix (demand : Nat) (search : World → Answers Local World)
    (world : World) :
    (selectFrom demand search world).1 <+: (resume search world).1 := by
  have full := congrArg Prod.fst (selectFrom_resume demand search world)
  exact ⟨_, full⟩

theorem selectFrom_length_le (demand : Nat) (search : World → Answers Local World)
    (world : World) : (selectFrom demand search world).1.length ≤ demand := by
  induction demand generalizing search world with
  | zero => simp [selectFrom]
  | succ demand ih =>
    simp only [selectFrom]
    cases produced : search world with
    | stop final => simp
    | more value here residual =>
      simpa using Nat.succ_le_succ (ih residual here)

end Mettapedia.Machines.ScopedCommit
