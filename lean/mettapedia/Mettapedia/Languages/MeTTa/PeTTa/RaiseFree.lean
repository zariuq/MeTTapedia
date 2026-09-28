import Mathlib.Data.List.Basic

/-!
# Callees that raise nothing

A run-time dispatch runs its callee under a handler, and a handler around a
body that raises nothing is not observable
(`DispatchErrorScope.recoverList_map_answer_of_no_raise`).  So when a
specialization learns that a head variable holds a callee that can never
raise, it may write the call directly instead of keeping the dispatch.

Whether a callee can raise is decided on its equations' bodies.  Only an
operation raises.  A body raises nothing when it is built from leaves
(variables, data, quoted syntax), control over such parts, `catch` (which
turns a raise into a value), run-time dispatches (each of which recovers its
own callee's raise, so only its arguments count), and calls of callees that
themselves raise nothing.  Callees may call one another in cycles; the check
takes a list `S` of callees closed under it (`Closed`), which includes every
cycle, and every callee in such a set raises nothing on any path, however
deep the calls go (`not_mayRaise`).  Nothing smaller would do: an operation
raises (`op_mayRaise`), and a callee is only as safe as the callees it calls
(`call_of_raising_callee_mayRaise`).

What a call runs is every equation it may try: matching the call against an
equation's argument pattern runs the callables written in that pattern,
before the body.  So the check reads every pattern as well as every body
(`equation_callee_not_mayRaise`); reading the bodies alone accepts a callee
whose pattern raises (`bodies_only_unsound`).
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.RaiseFree

/-- Equation bodies over callee names `F`, with binary composition standing
for any number of parts. -/
inductive Body (F : Type*) where
  /-- A variable, data, or quoted syntax: nothing runs. -/
  | leaf : Body F
  /-- An operation on the values of its parts, which may raise. -/
  | op : Body F → Body F → Body F
  /-- A call of the callee `f` on the value of its argument. -/
  | call : F → Body F → Body F
  /-- A control form over its parts: `if`, `let`, `case`, `superpose`, … -/
  | ctrl : Body F → Body F → Body F
  /-- A run-time dispatch on the value of its argument: the dispatched
  callee runs under a handler that recovers anything it raises. -/
  | dyn : Body F → Body F
  /-- `catch`: a raise inside becomes a value. -/
  | caught : Body F → Body F

variable {F : Type*}

/-- Whether some path of `b` raises, when calls may go `n` deep and callee
`f` runs the body `defs f`. -/
def mayRaise (defs : F → Body F) : ℕ → Body F → Prop
  | _, .leaf => False
  | _, .op _ _ => True
  | 0, .call _ a => mayRaise defs 0 a
  | n + 1, .call f a => mayRaise defs (n + 1) a ∨ mayRaise defs n (defs f)
  | n, .ctrl a b => mayRaise defs n a ∨ mayRaise defs n b
  | n, .dyn a => mayRaise defs n a
  | _, .caught _ => False

/-- The check, relative to the callees `S` taken to raise nothing. -/
def raisesNothing [DecidableEq F] (S : List F) : Body F → Bool
  | .leaf => true
  | .op _ _ => false
  | .call f a => raisesNothing S a && decide (f ∈ S)
  | .ctrl a b => raisesNothing S a && raisesNothing S b
  | .dyn a => raisesNothing S a
  | .caught _ => true

/-- `S` is closed under the check: every callee in it has a body the check
accepts, taking the callees in `S` to raise nothing. -/
def Closed [DecidableEq F] (defs : F → Body F) (S : List F) : Prop :=
  ∀ f ∈ S, raisesNothing S (defs f) = true

/-- Soundness: under a closed set, a body the check accepts raises on no
path, at any call depth. -/
theorem not_mayRaise [DecidableEq F] {defs : F → Body F} {S : List F}
    (hS : Closed defs S) :
    ∀ (n : ℕ) (b : Body F), raisesNothing S b = true → ¬ mayRaise defs n b := by
  intro n
  induction n with
  | zero =>
      intro b
      induction b with
      | leaf => intro _ h; simp only [mayRaise] at h
      | op a c _ _ => intro h; exact absurd h Bool.false_ne_true
      | call f a iha =>
          intro h hr
          simp only [raisesNothing, Bool.and_eq_true] at h
          simp only [mayRaise] at hr
          exact iha h.1 hr
      | ctrl a c iha ihc =>
          intro h hr
          simp only [raisesNothing, Bool.and_eq_true] at h
          simp only [mayRaise] at hr
          rcases hr with hr | hr
          · exact iha h.1 hr
          · exact ihc h.2 hr
      | dyn a iha =>
          intro h hr
          simp only [raisesNothing] at h
          simp only [mayRaise] at hr
          exact iha h hr
      | caught a _ => intro _ h; simp only [mayRaise] at h
  | succ m ihm =>
      intro b
      induction b with
      | leaf => intro _ h; simp only [mayRaise] at h
      | op a c _ _ => intro h; exact absurd h Bool.false_ne_true
      | call f a iha =>
          intro h hr
          simp only [raisesNothing, Bool.and_eq_true, decide_eq_true_eq] at h
          simp only [mayRaise] at hr
          rcases hr with hr | hr
          · exact iha h.1 hr
          · exact ihm (defs f) (hS f h.2) hr
      | ctrl a c iha ihc =>
          intro h hr
          simp only [raisesNothing, Bool.and_eq_true] at h
          simp only [mayRaise] at hr
          rcases hr with hr | hr
          · exact iha h.1 hr
          · exact ihc h.2 hr
      | dyn a iha =>
          intro h hr
          simp only [raisesNothing] at h
          simp only [mayRaise] at hr
          exact iha h hr
      | caught a _ => intro _ h; simp only [mayRaise] at h

/-- So every callee in a closed set raises nothing on any path. -/
theorem callee_not_mayRaise [DecidableEq F] {defs : F → Body F}
    {S : List F} (hS : Closed defs S) {f : F} (hf : f ∈ S) (n : ℕ) :
    ¬ mayRaise defs n (defs f) :=
  not_mayRaise hS n (defs f) (hS f hf)

/-- An operation may raise, so the check cannot accept one. -/
theorem op_mayRaise (defs : F → Body F) (n : ℕ) (a b : Body F) :
    mayRaise defs n (.op a b) := by
  cases n <;> simp only [mayRaise]

/-- A call of a callee whose body may raise may raise, once calls may go
one deeper: a caller is only as safe as its callees. -/
theorem call_of_raising_callee_mayRaise (defs : F → Body F) (n : ℕ) (f : F)
    (a : Body F) (h : mayRaise defs n (defs f)) :
    mayRaise defs (n + 1) (.call f a) := by
  simp only [mayRaise]
  exact Or.inr h

/-- A run-time dispatch hides its callee's raises: a dispatch on a leaf
raises nothing whatever the callee does. -/
theorem dyn_leaf_not_mayRaise (defs : F → Body F) (n : ℕ) :
    ¬ mayRaise defs n (.dyn .leaf) := by
  cases n <;> simp only [mayRaise, not_false_eq_true]

/-- A cycle whose members only call each other is closed, so it raises
nothing: two callees that call each other forever. -/
example :
    Closed (fun b : Bool => Body.call (!b) Body.leaf) [true, false] := by
  intro f _
  cases f <;> decide

/-- A cycle through an operation is not closed. -/
example :
    ¬ Closed (fun b : Bool => if b then Body.call false Body.leaf
                              else Body.op Body.leaf Body.leaf)
        [true, false] := by
  intro h
  exact absurd (h false (by decide)) (by decide)

/-! ## Equations: a pattern's callables run during matching -/

/-- One equation of a callee: what matching its argument pattern runs, and
its body. -/
structure Equation (F : Type*) where
  pattern : Body F
  body : Body F

/-- What a call of `f` may run: every equation's pattern and body. -/
def runs (eqs : F → List (Equation F)) (f : F) : Body F :=
  (eqs f).foldr (fun e acc => Body.ctrl (Body.ctrl e.pattern e.body) acc)
    Body.leaf

/-- The check over equations: every pattern and every body of every callee
in `S`, taking the callees in `S` to raise nothing. -/
def EquationsClosed [DecidableEq F] (eqs : F → List (Equation F))
    (S : List F) : Prop :=
  ∀ f ∈ S, ∀ e ∈ eqs f,
    raisesNothing S e.pattern = true ∧ raisesNothing S e.body = true

theorem raisesNothing_runs [DecidableEq F] {S : List F} :
    ∀ l : List (Equation F),
      (∀ e ∈ l, raisesNothing S e.pattern = true ∧
        raisesNothing S e.body = true) →
      raisesNothing S (l.foldr
        (fun e acc => Body.ctrl (Body.ctrl e.pattern e.body) acc)
        Body.leaf) = true
  | [], _ => rfl
  | e :: l, h => by
      have he := h e List.mem_cons_self
      have hl : ∀ e' ∈ l, raisesNothing S e'.pattern = true ∧
          raisesNothing S e'.body = true :=
        fun e' he' => h e' (List.mem_cons_of_mem _ he')
      show ((raisesNothing S e.pattern && raisesNothing S e.body) &&
        raisesNothing S (l.foldr
          (fun e acc => Body.ctrl (Body.ctrl e.pattern e.body) acc)
          Body.leaf)) = true
      rw [he.1, he.2, raisesNothing_runs l hl]
      rfl

/-- Checking patterns and bodies closes the set over what calls run. -/
theorem closed_of_equationsClosed [DecidableEq F]
    {eqs : F → List (Equation F)} {S : List F}
    (h : EquationsClosed eqs S) : Closed (runs eqs) S :=
  fun f hf => raisesNothing_runs (eqs f) (h f hf)

/-- So a callee in a set closed over its patterns and bodies raises nothing
on any path, however deep the calls go. -/
theorem equation_callee_not_mayRaise [DecidableEq F]
    {eqs : F → List (Equation F)} {S : List F}
    (h : EquationsClosed eqs S) {f : F} (hf : f ∈ S) (n : ℕ) :
    ¬ mayRaise (runs eqs) n (runs eqs f) :=
  callee_not_mayRaise (closed_of_equationsClosed h) hf n

/-- The check over bodies alone. -/
def BodiesClosed [DecidableEq F] (eqs : F → List (Equation F))
    (S : List F) : Prop :=
  ∀ f ∈ S, ∀ e ∈ eqs f, raisesNothing S e.body = true

/-- Reading the bodies alone is unsound: a callee whose only equation has a
raising operation in its pattern and a leaf for its body passes it, and a
call of it may raise. -/
theorem bodies_only_unsound :
    ∃ eqs : Unit → List (Equation Unit),
      BodiesClosed eqs [()] ∧ mayRaise (runs eqs) 0 (runs eqs ()) := by
  refine ⟨fun _ => [⟨Body.op Body.leaf Body.leaf, Body.leaf⟩], ?_, ?_⟩
  · intro f _ e he
    rw [List.mem_singleton.mp he]
    rfl
  · show mayRaise _ 0 (Body.ctrl
      (Body.ctrl (Body.op Body.leaf Body.leaf) Body.leaf) Body.leaf)
    simp only [mayRaise]
    exact Or.inl (Or.inl trivial)

end Mettapedia.Languages.MeTTa.PeTTa.RaiseFree
