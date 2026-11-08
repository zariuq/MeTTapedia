import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramNestedSource

/-!
# Call by need at first order: a heap of shared thunks, and the frame-stack machine

R95's nested calls are evaluated by value (`ProgramNestedSource`). The Prime draft evaluates `Proc`
and undeclared positions by need. This file adds sharing to R95's expressions and machine.

**Expressions** (`NEx`): held data `val t`, a pair, a call (as in R95), a heap location `loc ℓ`, and
`bind ℓ a b`, which binds the location `ℓ` to the unevaluated thunk `a` in `b`. Data is ground
(`Sx`), and a call is answered by matching against the program's equations (`NEquation`, R95's).

**The reference** (`NEval`) is Launchbury's natural semantics: `H : e ⇓ H' : v`. A demand of a
thunk evaluates it with its cell marked busy, and overwrites the cell with the value; a demand of a
value reads it.

**The machine** (`NStep`) is R95's frame-stack machine with a heap and one more frame, `update ℓ`
(Sestoft's update marker): forcing a thunk pushes it, and returning to it writes the value.

- `eval_runs`: every reference evaluation is a machine run, at every stack.
- `split_ev`: a machine run from an expression to a halted state first evaluates the expression,
  as a reference evaluation, and returns to the stack.
- `runs_eval`, `need_adequacy`: machine runs from an expression to a halted state are exactly the
  reference evaluations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNeed

open ProgramRows
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested (EPat NEquation)

/-! ## Expressions, programs and heaps -/

/-- **Expressions with sharing.** -/
inductive NEx where
  | val (t : Sx)
  | loc (ℓ : ℕ)
  | pair (a b : NEx)
  | call (a : NEx)
  | bind (ℓ : ℕ) (a b : NEx)

/-- Instantiate an equation's right-hand side by a matching assignment. -/
def instE (θ : ℕ → Sx) : EPat → NEx
  | .val p => .val (p.inst θ)
  | .pair a b => .pair (instE θ a) (instE θ b)
  | .call a => .call (instE θ a)

/-- A program: equations, a data pattern and an expression pattern each. -/
abbrev Program := List NEquation

/-- A heap cell: unallocated, a thunk, a thunk being evaluated, or a value. -/
inductive Cell where
  | empty
  | thunk (e : NEx)
  | busy
  | value (v : Sx)

/-- A heap of cells, by location. -/
abbrev Heap := ℕ → Cell

/-- The empty heap. -/
def Heap.none : Heap := fun _ => .empty

/-- Overwrite one cell. -/
def Heap.set (H : Heap) (ℓ : ℕ) (c : Cell) : Heap := Function.update H ℓ c

theorem Heap.set_same (H : Heap) (ℓ : ℕ) (c : Cell) : H.set ℓ c ℓ = c := by
  unfold Heap.set
  exact Function.update_self ℓ c H

theorem Heap.set_other (H : Heap) {ℓ ℓ' : ℕ} (c : Cell) (ne : ℓ' ≠ ℓ) : H.set ℓ c ℓ' = H ℓ' := by
  unfold Heap.set
  exact Function.update_of_ne ne c H

theorem Heap.set_set (H : Heap) (ℓ : ℕ) (c c' : Cell) : (H.set ℓ c).set ℓ c' = H.set ℓ c' := by
  unfold Heap.set
  exact Function.update_idem c c' H

/-! ## The reference: Launchbury's natural semantics -/

/-- **Call by need**, as a natural semantics over a heap. -/
inductive NEval (prog : Program) : Heap → NEx → Heap → Sx → Prop
  | val (H : Heap) (t : Sx) : NEval prog H (.val t) H t
  | pair {H H₁ H₂ : Heap} {a b : NEx} {v w : Sx} (left : NEval prog H a H₁ v) (right : NEval prog H₁ b H₂ w) :
      NEval prog H (.pair a b) H₂ (.cell v w)
  | call {H H₁ H₂ : Heap} {a : NEx} {w v : Sx} (j : Fin prog.length) (θ : ℕ → Sx)
      (argument : NEval prog H a H₁ w) (matched : (prog.get j).lhs.inst θ = w)
      (answer : NEval prog H₁ (instE θ (prog.get j).rhs) H₂ v) : NEval prog H (.call a) H₂ v
  | bind {H H' : Heap} {ℓ : ℕ} {a b : NEx} {v : Sx} (fresh : H ℓ = .empty)
      (body : NEval prog (H.set ℓ (.thunk a)) b H' v) : NEval prog H (.bind ℓ a b) H' v
  | read {H : Heap} {ℓ : ℕ} {v : Sx} (stored : H ℓ = .value v) : NEval prog H (.loc ℓ) H v
  | force {H H' : Heap} {ℓ : ℕ} {e : NEx} {v : Sx} (stored : H ℓ = .thunk e)
      (thunk : NEval prog (H.set ℓ .busy) e H' v) : NEval prog H (.loc ℓ) (H'.set ℓ (.value v)) v

/-! ## The frame-stack machine -/

/-- Frames: R95's three, and the update marker of a forced thunk. -/
inductive Frame where
  | left (b : NEx)
  | right (v : Sx)
  | arg
  | update (ℓ : ℕ)

/-- What the thread does: evaluate, return a value, or call data. -/
inductive Control where
  | ev (e : NEx)
  | ret (v : Sx)
  | ap (w : Sx)

/-- A configuration: the thread, its frames, innermost first, and the heap. -/
abbrev Conf := Control × List Frame × Heap

/-- **The by-need machine.** -/
inductive NStep (prog : Program) : Conf → Conf → Prop
  | val (t : Sx) (K : List Frame) (H : Heap) : NStep prog (.ev (.val t), K, H) (.ret t, K, H)
  | pair (a b : NEx) (K : List Frame) (H : Heap) : NStep prog (.ev (.pair a b), K, H) (.ev a, .left b :: K, H)
  | call (a : NEx) (K : List Frame) (H : Heap) : NStep prog (.ev (.call a), K, H) (.ev a, .arg :: K, H)
  | bind (ℓ : ℕ) (a b : NEx) (K : List Frame) (H : Heap) (fresh : H ℓ = .empty) :
      NStep prog (.ev (.bind ℓ a b), K, H) (.ev b, K, H.set ℓ (.thunk a))
  | read (ℓ : ℕ) (K : List Frame) (H : Heap) (v : Sx) (stored : H ℓ = .value v) :
      NStep prog (.ev (.loc ℓ), K, H) (.ret v, K, H)
  | force (ℓ : ℕ) (K : List Frame) (H : Heap) (e : NEx) (stored : H ℓ = .thunk e) :
      NStep prog (.ev (.loc ℓ), K, H) (.ev e, .update ℓ :: K, H.set ℓ .busy)
  | left (v : Sx) (b : NEx) (K : List Frame) (H : Heap) : NStep prog (.ret v, .left b :: K, H) (.ev b, .right v :: K, H)
  | right (v w : Sx) (K : List Frame) (H : Heap) : NStep prog (.ret w, .right v :: K, H) (.ret (.cell v w), K, H)
  | arg (w : Sx) (K : List Frame) (H : Heap) : NStep prog (.ret w, .arg :: K, H) (.ap w, K, H)
  | update (ℓ : ℕ) (v : Sx) (K : List Frame) (H : Heap) :
      NStep prog (.ret v, .update ℓ :: K, H) (.ret v, K, H.set ℓ (.value v))
  | apply (w : Sx) (K : List Frame) (H : Heap) (j : Fin prog.length) (θ : ℕ → Sx)
      (matched : (prog.get j).lhs.inst θ = w) : NStep prog (.ap w, K, H) (.ev (instE θ (prog.get j).rhs), K, H)

/-! ## Reference evaluations are machine runs -/

variable {prog : Program}

/-- **Every reference evaluation is a machine run**, at every stack. -/
theorem eval_runs {H H' : Heap} {e : NEx} {v : Sx} (eval : NEval prog H e H' v) :
    ∀ K, Relation.ReflTransGen (NStep prog) (.ev e, K, H) (.ret v, K, H') := by
  induction eval with
  | val H t => exact fun K => .single (.val t K H)
  | pair _ _ ihA ihB =>
      intro K
      exact ((((Relation.ReflTransGen.single (.pair _ _ K _)).trans (ihA _)).tail (.left _ _ K _)).trans
        (ihB _)).tail (.right _ _ K _)
  | call j θ _ matched _ ihA ihR =>
      intro K
      exact ((((Relation.ReflTransGen.single (.call _ K _)).trans (ihA _)).tail (.arg _ K _)).tail
        (.apply _ K _ j θ matched)).trans (ihR K)
  | bind fresh _ ih =>
      intro K
      exact (Relation.ReflTransGen.single (.bind _ _ _ K _ fresh)).trans (ih K)
  | read stored => exact fun K => .single (.read _ K _ _ stored)
  | force stored _ ih =>
      intro K
      exact ((Relation.ReflTransGen.single (.force _ K _ _ stored)).trans (ih _)).tail (.update _ _ K _)

/-! ## Machine runs are reference evaluations -/

/-- Runs counted by their steps. -/
inductive RunN (prog : Program) : ℕ → Conf → Conf → Prop
  | refl (c : Conf) : RunN prog 0 c c
  | step {n : ℕ} {c c' c'' : Conf} (first : NStep prog c c') (rest : RunN prog n c' c'') : RunN prog (n + 1) c c''

theorem runN_of {c c' : Conf} (run : Relation.ReflTransGen (NStep prog) c c') : ∃ n, RunN prog n c c' := by
  induction run using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .refl _⟩
  | head first _ ih =>
      obtain ⟨n, rest⟩ := ih
      exact ⟨n + 1, .step first rest⟩

/-- A halted configuration: a value returned to the empty stack. -/
def Halted (c : Conf) : Prop := ∃ v H, c = (.ret v, [], H)

theorem run_cases {n : ℕ} {c c'' : Conf} (run : RunN prog n c c'') :
    (n = 0 ∧ c = c'') ∨ ∃ k c', n = k + 1 ∧ NStep prog c c' ∧ RunN prog k c' c'' := by
  cases run with
  | refl => exact .inl ⟨rfl, rfl⟩
  | step first rest => exact .inr ⟨_, _, rfl, first, rest⟩

/-- A frame left on the stack is not halted. -/
theorem not_halted_frame {v : Sx} {f : Frame} {K : List Frame} {H : Heap} {c : Conf} (halted : Halted c)
    (same : ((.ret v, f :: K, H) : Conf) = c) : False := by
  obtain ⟨v', H', rfl⟩ := halted
  simp at same

/-- Returning to a frame: the run's first step is the frame's. -/
theorem ret_step {m : ℕ} {v : Sx} {f : Frame} {K : List Frame} {H : Heap} {c : Conf} (halted : Halted c)
    (run : RunN prog m (.ret v, f :: K, H) c) :
    ∃ k c', m = k + 1 ∧ NStep prog (.ret v, f :: K, H) c' ∧ RunN prog k c' c := by
  rcases run_cases run with ⟨-, same⟩ | step
  · exact (not_halted_frame halted same).elim
  · exact step

/-- **A run to a halted state first evaluates the expression**, as a reference evaluation, and
returns its value to the stack. -/
theorem split_ev : ∀ (n : ℕ) (e : NEx) (K : List Frame) (H : Heap) (c : Conf), RunN prog n (.ev e, K, H) c →
    Halted c → ∃ v H₁ m, m < n ∧ NEval prog H e H₁ v ∧ RunN prog m (.ret v, K, H₁) c := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro e K H c run halted
      rcases run_cases run with ⟨-, same⟩ | ⟨k, c₁, rfl, first, rest⟩
      · obtain ⟨v', H', rfl⟩ := halted
        simp at same
      cases first with
      | val t _ _ => exact ⟨t, H, k, Nat.lt_succ_self k, .val H t, rest⟩
      | pair a b _ _ =>
          obtain ⟨va, H₁, m₁, lt₁, evalA, run₁⟩ := ih k (Nat.lt_succ_self k) a _ H c rest halted
          obtain ⟨k₁, c₂, rfl, second, rest₁⟩ := ret_step halted run₁
          cases second with
          | left =>
              obtain ⟨vb, H₂, m₂, lt₂, evalB, run₂⟩ := ih k₁ (by omega) b _ H₁ c rest₁ halted
              obtain ⟨k₂, c₃, rfl, third, rest₂⟩ := ret_step halted run₂
              cases third with
              | right => exact ⟨_, H₂, k₂, by omega, .pair evalA evalB, rest₂⟩
      | call a _ _ =>
          obtain ⟨w, H₁, m₁, lt₁, evalA, run₁⟩ := ih k (Nat.lt_succ_self k) a _ H c rest halted
          obtain ⟨k₁, c₂, rfl, second, rest₁⟩ := ret_step halted run₁
          cases second with
          | arg =>
              rcases run_cases rest₁ with ⟨-, same⟩ | ⟨k₂, c₃, rfl, third, rest₂⟩
              · obtain ⟨v', H', rfl⟩ := halted
                simp at same
              cases third with
              | apply _ _ _ j θ matched =>
                  obtain ⟨v, H₂, m₂, lt₂, evalR, run₂⟩ := ih k₂ (by omega) _ K H₁ c rest₂ halted
                  exact ⟨v, H₂, m₂, by omega, .call j θ evalA matched evalR, run₂⟩
      | bind ℓ a b _ _ fresh =>
          obtain ⟨v, H₁, m₁, lt₁, evalB, run₁⟩ := ih k (Nat.lt_succ_self k) b K _ c rest halted
          exact ⟨v, H₁, m₁, by omega, .bind fresh evalB, run₁⟩
      | read ℓ _ _ v stored => exact ⟨v, H, k, Nat.lt_succ_self k, .read stored, rest⟩
      | force ℓ _ _ e stored =>
          obtain ⟨v, H₁, m₁, lt₁, evalE, run₁⟩ := ih k (Nat.lt_succ_self k) e _ _ c rest halted
          obtain ⟨k₁, c₂, rfl, second, rest₁⟩ := ret_step halted run₁
          cases second with
          | update => exact ⟨v, _, k₁, by omega, .force stored evalE, rest₁⟩

/-- A value returned to the empty stack ends every run. -/
theorem halted_final {n : ℕ} {v : Sx} {H : Heap} {c : Conf} (run : RunN prog n (.ret v, [], H) c) :
    c = (.ret v, [], H) := by
  rcases run_cases run with ⟨-, same⟩ | ⟨k, c', -, first, -⟩
  · exact same.symm
  · cases first

/-- **Every machine run from an expression to a halted state is a reference evaluation.** -/
theorem runs_eval {H H' : Heap} {e : NEx} {v : Sx}
    (run : Relation.ReflTransGen (NStep prog) (.ev e, [], H) (.ret v, [], H')) : NEval prog H e H' v := by
  obtain ⟨n, counted⟩ := runN_of run
  obtain ⟨v₁, H₁, m, -, eval, rest⟩ := split_ev n e [] H _ counted ⟨v, H', rfl⟩
  have same := halted_final rest
  simp only [Prod.mk.injEq, Control.ret.injEq, true_and] at same
  obtain ⟨rfl, rfl⟩ := same
  exact eval

/-- **Adequacy of the machine, both ways.** -/
theorem need_adequacy {H H' : Heap} {e : NEx} {v : Sx} :
    Relation.ReflTransGen (NStep prog) (.ev e, [], H) (.ret v, [], H') ↔ NEval prog H e H' v :=
  ⟨runs_eval, fun eval => eval_runs eval []⟩

#print axioms Heap.set_set
#print axioms eval_runs
#print axioms runN_of
#print axioms split_ev
#print axioms halted_final
#print axioms runs_eval
#print axioms need_adequacy

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNeed
