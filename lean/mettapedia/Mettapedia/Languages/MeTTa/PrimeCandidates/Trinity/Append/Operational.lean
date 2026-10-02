import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append.Source
import Mathlib.Logic.Relation

/-!
# Running lists and their append: one value, reached in a fixed number of steps

Running a list expression means rewriting it by the two equations of the source,

    append nil ys         = ys
    append (cons a as) ys = cons a (append as ys)

at any place inside it and in any order (`ListExpr.Step`), until no equation applies. For
this source running behaves as well as it can:

* the expressions that take no step are exactly the values, the lists built from `nil` and
  `cons` (`ListExpr.isValue_iff_no_step`);
* an evaluation function computes the value directly (`ListExpr.eval`); every expression
  reaches it (`ListExpr.reaches_eval`) and a step does not change it (`ListExpr.eval_step`),
  so whatever order the steps are taken in, the value reached is the same
  (`ListExpr.eq_eval_of_reaches`);
* every step lowers a cost by exactly one (`ListExpr.cost_step`), so every run of an
  expression to its value takes the same number of steps, its cost
  (`ListExpr.steps_eq_cost`), and no run goes on for ever (`ListExpr.wellFounded_step`);
* two different steps from one expression are each completed by one more step to a common
  expression (`ListExpr.step_diamond`); this alone already makes any two runs from one
  expression meet again (`ListExpr.join_of_reaches`);
* the theorem of the source holds when run: `append l nil` has the value of `l`
  (`ListExpr.eval_append_nil`), and for a value `l` it runs to `l` itself in `length + 1`
  steps (`ListExpr.stepsIn_append_nil`).

Values do not see how a list was built, costs do: both ways of nesting three appends have one
value (`ListExpr.eval_append_assoc`), and the left nesting costs the length of the first list
more (`ListExpr.cost_append_assoc`).

Positive example: `one ++ two` runs in two steps to the list of the two numbers; its cost is
two. Negative example: a value takes no step and its cost is zero; and the two steps of
`nil ++ nil` are one and the same step, which no further step completes
(`ListExpr.not_step_diamond_without_eq`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append

namespace ListExpr

/-! ## The evaluation function -/

/-- Append a value to a list: the second equation, used until the first one ends it. On a left
argument that is not a value it does nothing and leaves the `append` as written. -/
def appendValue : ListExpr → ListExpr → ListExpr
  | .nil, right => right
  | .cons head tail, right => .cons head (appendValue tail right)
  | .append first second, right => .append (.append first second) right

/-- **The evaluation function**: the value of a list expression, by structural recursion. -/
def eval : ListExpr → ListExpr
  | .nil => .nil
  | .cons head tail => .cons head tail.eval
  | .append left right => left.eval.appendValue right.eval

theorem appendValue_isValue {left right : ListExpr} (hleft : left.IsValue)
    (hright : right.IsValue) : (left.appendValue right).IsValue := by
  induction left with
  | nil => exact hright
  | cons head tail ih => exact ih hleft
  | append first second _ _ => exact hleft.elim

/-- The value of every expression is a value. -/
theorem eval_isValue (e : ListExpr) : e.eval.IsValue := by
  induction e with
  | nil => trivial
  | cons head tail ih => exact ih
  | append l r ihl ihr => exact appendValue_isValue ihl ihr

/-- A value evaluates to itself. -/
theorem eval_of_isValue {e : ListExpr} (h : e.IsValue) : e.eval = e := by
  induction e with
  | nil => rfl
  | cons head tail ih => exact congrArg (ListExpr.cons head) (ih h)
  | append l r _ _ => exact h.elim

/-- An expression is its own value exactly when it is a value. -/
theorem eval_eq_self_iff {e : ListExpr} : e.eval = e ↔ e.IsValue :=
  ⟨fun h => h ▸ eval_isValue e, eval_of_isValue⟩

/-! ## Values are the expressions that take no step -/

/-- An expression that takes a step is not a value. -/
theorem not_isValue_of_step {e e' : ListExpr} (step : Step e e') : ¬ e.IsValue := by
  induction step with
  | appendNil _ => exact id
  | appendCons _ _ _ => exact id
  | consTail _ ih => exact ih
  | appendLeft _ _ => exact id
  | appendRight _ _ => exact id

/-- A value takes no step. -/
theorem not_step_of_isValue {e e' : ListExpr} (h : e.IsValue) : ¬ Step e e' :=
  fun step => not_isValue_of_step step h

/-- Every expression is a value or takes a step. -/
theorem isValue_or_exists_step (e : ListExpr) : e.IsValue ∨ ∃ e', Step e e' := by
  induction e with
  | nil => exact Or.inl trivial
  | cons head tail ih =>
      rcases ih with hv | ⟨tail', step⟩
      · exact Or.inl hv
      · exact Or.inr ⟨.cons head tail', .consTail step⟩
  | append l r ihl _ =>
      refine Or.inr ?_
      cases l with
      | nil => exact ⟨r, .appendNil r⟩
      | cons head tail => exact ⟨.cons head (.append tail r), .appendCons head tail r⟩
      | append first second =>
          rcases ihl with hv | ⟨l', step⟩
          · exact hv.elim
          · exact ⟨.append l' r, .appendLeft step⟩

/-- **The values are exactly the expressions that take no step.** -/
theorem isValue_iff_no_step {e : ListExpr} : e.IsValue ↔ ∀ e', ¬ Step e e' := by
  constructor
  · intro h e'
    exact not_step_of_isValue h
  · intro h
    rcases isValue_or_exists_step e with hv | ⟨e', step⟩
    · exact hv
    · exact (h e' step).elim

/-! ## Every expression reaches its value -/

theorem reaches_consTail (head : NumExpr) {tail tail' : ListExpr}
    (h : Relation.ReflTransGen Step tail tail') :
    Relation.ReflTransGen Step (.cons head tail) (.cons head tail') := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (.consTail step)

theorem reaches_appendLeft {l l' : ListExpr} (r : ListExpr)
    (h : Relation.ReflTransGen Step l l') :
    Relation.ReflTransGen Step (.append l r) (.append l' r) := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (.appendLeft step)

theorem reaches_appendRight (l : ListExpr) {r r' : ListExpr}
    (h : Relation.ReflTransGen Step r r') :
    Relation.ReflTransGen Step (.append l r) (.append l r') := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (.appendRight step)

/-- The `append` of a value and a list reaches what the helper computes. -/
theorem reaches_appendValue {l : ListExpr} (h : l.IsValue) (r : ListExpr) :
    Relation.ReflTransGen Step (.append l r) (l.appendValue r) := by
  induction l with
  | nil => exact .single (.appendNil r)
  | cons head tail ih =>
      exact Relation.ReflTransGen.head (.appendCons head tail r) (reaches_consTail head (ih h))
  | append first second _ _ => exact h.elim

/-- **Every expression reaches its value.** -/
theorem reaches_eval (e : ListExpr) : Relation.ReflTransGen Step e e.eval := by
  induction e with
  | nil => exact .refl
  | cons head tail ih => exact reaches_consTail head ih
  | append l r ihl ihr =>
      exact ((reaches_appendLeft r ihl).trans (reaches_appendRight l.eval ihr)).trans
        (reaches_appendValue (eval_isValue l) r.eval)

/-! ## The value does not depend on the order of the steps -/

/-- **A step does not change the value.** -/
theorem eval_step {e e' : ListExpr} (step : Step e e') : e.eval = e'.eval := by
  induction step with
  | appendNil _ => rfl
  | appendCons _ _ _ => rfl
  | consTail _ ih => exact congrArg (ListExpr.cons _) ih
  | appendLeft _ ih => exact congrArg (fun value => ListExpr.appendValue value _) ih
  | appendRight _ ih => exact congrArg (ListExpr.appendValue _) ih

/-- A run does not change the value. -/
theorem eval_reaches {e e' : ListExpr} (h : Relation.ReflTransGen Step e e') :
    e.eval = e'.eval := by
  induction h with
  | refl => rfl
  | tail _ step ih => exact ih.trans (eval_step step)

/-- **Uniqueness of the result**: whatever order the steps are taken in, a value reached from
`e` is `e.eval`. -/
theorem eq_eval_of_reaches {e v : ListExpr} (h : Relation.ReflTransGen Step e v)
    (hv : v.IsValue) : v = e.eval :=
  ((eval_reaches h).trans (eval_of_isValue hv)).symm

/-- The value of `e` is the one value that running `e` reaches. -/
theorem reaches_value_iff {e v : ListExpr} :
    Relation.ReflTransGen Step e v ∧ v.IsValue ↔ v = e.eval := by
  constructor
  · rintro ⟨h, hv⟩
    exact eq_eval_of_reaches h hv
  · rintro rfl
    exact ⟨reaches_eval e, eval_isValue e⟩

/-! ## The cost of running -/

/-- The number of elements of the list an expression evaluates to. -/
def length : ListExpr → Nat
  | .nil => 0
  | .cons _ tail => tail.length + 1
  | .append left right => left.length + right.length

/-- **The cost of running an expression**: appending a list of `n` elements takes `n + 1`
steps, `n` by the second equation and one by the first, on top of the costs of the two lists
appended. -/
def cost : ListExpr → Nat
  | .nil => 0
  | .cons _ tail => tail.cost
  | .append left right => left.cost + right.cost + left.length + 1

/-- `StepsIn n e e'`: running `e` reaches `e'` in exactly `n` steps. -/
inductive StepsIn : Nat → ListExpr → ListExpr → Prop
  | refl (e : ListExpr) : StepsIn 0 e e
  | head {n : Nat} {e e' e'' : ListExpr} : Step e e' → StepsIn n e' e'' → StepsIn (n + 1) e e''

/-- A step does not change the number of elements. -/
theorem length_step {e e' : ListExpr} (step : Step e e') : e.length = e'.length := by
  induction step with
  | appendNil r => exact Nat.zero_add r.length
  | @appendCons _ tail r => exact Nat.succ_add tail.length r.length
  | consTail _ ih => exact congrArg (· + 1) ih
  | @appendLeft _ _ r _ ih => exact congrArg (· + r.length) ih
  | @appendRight l _ _ _ ih => exact congrArg (l.length + ·) ih

/-- A run does not change the number of elements. -/
theorem length_reaches {e e' : ListExpr} (h : Relation.ReflTransGen Step e e') :
    e.length = e'.length := by
  induction h with
  | refl => rfl
  | tail _ step ih => exact ih.trans (length_step step)

/-- The number of elements of an expression is that of its value. -/
theorem length_eval (e : ListExpr) : e.eval.length = e.length :=
  (length_reaches (reaches_eval e)).symm

/-- **Every step lowers the cost by exactly one.** -/
theorem cost_step {e e' : ListExpr} (step : Step e e') : e.cost = e'.cost + 1 := by
  induction step with
  | appendNil r => exact congrArg (· + 1) (Nat.zero_add r.cost)
  | appendCons _ _ _ => rfl
  | consTail _ ih => exact ih
  | @appendLeft l l' r step ih =>
      show l.cost + r.cost + l.length + 1 = l'.cost + r.cost + l'.length + 1 + 1
      rw [ih, length_step step, Nat.add_right_comm l'.cost 1 r.cost,
        Nat.add_right_comm (l'.cost + r.cost) 1 l'.length]
  | @appendRight l r r' _ ih =>
      show l.cost + r.cost + l.length + 1 = l.cost + r'.cost + l.length + 1 + 1
      rw [ih, ← Nat.add_assoc, Nat.add_right_comm (l.cost + r'.cost) 1 l.length]

/-- A value costs nothing. -/
theorem cost_of_isValue {e : ListExpr} (h : e.IsValue) : e.cost = 0 := by
  induction e with
  | nil => rfl
  | cons head tail ih => exact ih h
  | append l r _ _ => exact h.elim

theorem StepsIn.reaches {n : Nat} {e e' : ListExpr} (h : StepsIn n e e') :
    Relation.ReflTransGen Step e e' := by
  induction h with
  | refl => exact .refl
  | head step _ ih => exact .head step ih

theorem exists_stepsIn_of_reaches {e e' : ListExpr} (h : Relation.ReflTransGen Step e e') :
    ∃ n, StepsIn n e e' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .refl _⟩
  | head step _ ih =>
      obtain ⟨n, run⟩ := ih
      exact ⟨n + 1, .head step run⟩

/-- A run of `n` steps lowers the cost by `n`. -/
theorem cost_stepsIn {n : Nat} {e e' : ListExpr} (h : StepsIn n e e') : e.cost = e'.cost + n := by
  induction h with
  | refl => rfl
  | head step _ ih => rw [cost_step step, ih, Nat.add_assoc]

/-- **Every run of an expression to a value takes exactly its cost in steps**, whatever order
the steps are taken in. -/
theorem steps_eq_cost {n : Nat} {e v : ListExpr} (h : StepsIn n e v) (hv : v.IsValue) :
    n = e.cost := by
  have count := cost_stepsIn h
  rw [cost_of_isValue hv, Nat.zero_add] at count
  exact count.symm

/-- Running `e` reaches its value in exactly `e.cost` steps. -/
theorem stepsIn_cost_eval (e : ListExpr) : StepsIn e.cost e e.eval := by
  obtain ⟨n, run⟩ := exists_stepsIn_of_reaches (reaches_eval e)
  rw [← steps_eq_cost run (eval_isValue e)]
  exact run

/-- No run is longer than the cost. -/
theorem le_cost_of_stepsIn {n : Nat} {e e' : ListExpr} (h : StepsIn n e e') : n ≤ e.cost := by
  rw [cost_stepsIn h]
  exact Nat.le_add_left n e'.cost

/-- **Running always ends**: there is no endless run. -/
theorem wellFounded_step : WellFounded (fun later earlier : ListExpr => Step earlier later) :=
  Subrelation.wf (r := InvImage (· < ·) cost)
    (fun {later earlier} (step : Step earlier later) => by
      show later.cost < earlier.cost
      rw [cost_step step]
      exact Nat.lt_succ_self later.cost)
    (InvImage.wf cost Nat.lt_wfRel.wf)

/-! ## Two steps at independent places commute -/

/-- **Two steps from one expression either are the same step or are each completed by one more
step to a common expression.** The two equations do not overlap, and each uses its variables
once, so a step never destroys or copies the place of another step. -/
theorem step_diamond {e e₁ e₂ : ListExpr} (h₁ : Step e e₁) (h₂ : Step e e₂) :
    e₁ = e₂ ∨ ∃ e₃, Step e₁ e₃ ∧ Step e₂ e₃ := by
  induction h₁ generalizing e₂ with
  | appendNil r =>
      cases h₂ with
      | appendNil _ => exact Or.inl rfl
      | appendLeft step => exact nomatch step
      | appendRight step => exact Or.inr ⟨_, step, .appendNil _⟩
  | appendCons head tail r =>
      cases h₂ with
      | appendCons _ _ _ => exact Or.inl rfl
      | appendLeft step =>
          cases step with
          | consTail step => exact Or.inr ⟨_, .consTail (.appendLeft step), .appendCons _ _ _⟩
      | appendRight step => exact Or.inr ⟨_, .consTail (.appendRight step), .appendCons _ _ _⟩
  | consTail _ ih =>
      cases h₂ with
      | consTail step =>
          rcases ih step with same | ⟨_, s₁, s₂⟩
          · exact Or.inl (same ▸ rfl)
          · exact Or.inr ⟨_, .consTail s₁, .consTail s₂⟩
  | appendLeft step ih =>
      cases h₂ with
      | appendNil _ => exact nomatch step
      | appendCons _ _ _ =>
          cases step with
          | consTail step => exact Or.inr ⟨_, .appendCons _ _ _, .consTail (.appendLeft step)⟩
      | appendLeft step' =>
          rcases ih step' with same | ⟨_, s₁, s₂⟩
          · exact Or.inl (same ▸ rfl)
          · exact Or.inr ⟨_, .appendLeft s₁, .appendLeft s₂⟩
      | appendRight step' => exact Or.inr ⟨_, .appendRight step', .appendLeft step⟩
  | appendRight step ih =>
      cases h₂ with
      | appendNil _ => exact Or.inr ⟨_, .appendNil _, step⟩
      | appendCons _ _ _ => exact Or.inr ⟨_, .appendCons _ _ _, .consTail (.appendRight step)⟩
      | appendLeft step' => exact Or.inr ⟨_, .appendLeft step', .appendRight step⟩
      | appendRight step' =>
          rcases ih step' with same | ⟨_, s₁, s₂⟩
          · exact Or.inl (same ▸ rfl)
          · exact Or.inr ⟨_, .appendRight s₁, .appendRight s₂⟩

/-- **Any two runs from one expression meet again**, from commuting steps alone, without the
evaluation function. -/
theorem join_of_reaches {e e₁ e₂ : ListExpr} (h₁ : Relation.ReflTransGen Step e e₁)
    (h₂ : Relation.ReflTransGen Step e e₂) : Relation.Join (Relation.ReflTransGen Step) e₁ e₂ := by
  refine Relation.church_rosser (fun _ b c s₁ s₂ => ?_) h₁ h₂
  rcases step_diamond s₁ s₂ with same | ⟨d, t₁, t₂⟩
  · subst same
    exact ⟨b, .refl, .refl⟩
  · exact ⟨d, .single t₁, .single t₂⟩

/-- Negative example: the case of one and the same step cannot be dropped. Both steps of
`nil ++ nil` lead to `nil`, which takes no step. -/
theorem not_step_diamond_without_eq :
    ¬ ∀ e e₁ e₂ : ListExpr, Step e e₁ → Step e e₂ → ∃ e₃, Step e₁ e₃ ∧ Step e₂ e₃ := by
  intro diamond
  obtain ⟨_, step, _⟩ :=
    diamond (.append .nil .nil) .nil .nil (.appendNil .nil) (.appendNil .nil)
  exact nomatch step

/-! ## The theorem of the source, run -/

theorem appendValue_nil {v : ListExpr} (h : v.IsValue) : v.appendValue .nil = v := by
  induction v with
  | nil => rfl
  | cons head tail ih => exact congrArg (ListExpr.cons head) (ih h)
  | append first second _ _ => exact h.elim

/-- **`append l nil = l`, run**: `append l nil` has the value of `l`. -/
theorem eval_append_nil (l : ListExpr) : (ListExpr.append l .nil).eval = l.eval :=
  appendValue_nil (eval_isValue l)

/-- For a value `l`, `append l nil` runs to `l` itself in `length + 1` steps. -/
theorem stepsIn_append_nil {l : ListExpr} (h : l.IsValue) :
    StepsIn (l.length + 1) (.append l .nil) l := by
  have run := stepsIn_cost_eval (.append l .nil)
  rw [eval_append_nil, eval_of_isValue h] at run
  have count : (ListExpr.append l .nil).cost = l.length + 1 := by
    show l.cost + l.length + 1 = l.length + 1
    rw [cost_of_isValue h, Nat.zero_add]
  rw [count] at run
  exact run

theorem appendValue_assoc {x : ListExpr} (h : x.IsValue) (y z : ListExpr) :
    (x.appendValue y).appendValue z = x.appendValue (y.appendValue z) := by
  induction x with
  | nil => rfl
  | cons head tail ih => exact congrArg (ListExpr.cons head) (ih h)
  | append first second _ _ => exact h.elim

/-- Both ways of nesting three appends have one value. -/
theorem eval_append_assoc (a b c : ListExpr) :
    (ListExpr.append (.append a b) c).eval = (ListExpr.append a (.append b c)).eval :=
  appendValue_assoc (eval_isValue a) b.eval c.eval

/-- The left nesting costs the length of the first list more than the right nesting. -/
theorem cost_append_assoc (a b c : ListExpr) :
    (ListExpr.append (.append a b) c).cost = (ListExpr.append a (.append b c)).cost + a.length := by
  show a.cost + b.cost + a.length + 1 + c.cost + (a.length + b.length) + 1 =
    a.cost + (b.cost + c.cost + b.length) + 1 + a.length + 1 + a.length
  rw [← Nat.add_assoc (a.cost + b.cost + a.length + 1 + c.cost) a.length b.length,
    ← Nat.add_assoc a.cost (b.cost + c.cost) b.length, ← Nat.add_assoc a.cost b.cost c.cost,
    Nat.add_right_comm (a.cost + b.cost + a.length) 1 c.cost,
    Nat.add_right_comm (a.cost + b.cost) a.length c.cost,
    Nat.add_right_comm (a.cost + b.cost + c.cost + a.length + 1) a.length b.length,
    Nat.add_right_comm (a.cost + b.cost + c.cost + a.length) 1 b.length,
    Nat.add_right_comm (a.cost + b.cost + c.cost) a.length b.length,
    Nat.add_right_comm (a.cost + b.cost + c.cost + b.length) a.length 1,
    Nat.add_right_comm (a.cost + b.cost + c.cost + b.length + 1 + a.length) a.length 1]

/-! ## Examples -/

/-- Positive example: `one ++ two` evaluates to the list of the two numbers. -/
example : (ListExpr.append one two).eval = .cons .zero (.cons (.suc .zero) .nil) := rfl

/-- Positive example: its cost is two. -/
example : (ListExpr.append one two).cost = 2 := rfl

/-- Positive example: the run of `one ++ two` by the second equation and then the first takes
those two steps. -/
example : StepsIn 2 (.append one two) (.cons .zero (.cons (.suc .zero) .nil)) :=
  .head (.appendCons .zero .nil two) (.head (.consTail (.appendNil two)) (.refl _))

/-- Positive example: `(nil ++ one) ++ (nil ++ two)` has two different next steps, so running is
not a function; each is completed by the other step to `one ++ two`. -/
example :
    ListExpr.Step (.append (.append .nil one) (.append .nil two)) (.append one (.append .nil two)) ∧
      ListExpr.Step (.append (.append .nil one) (.append .nil two)) (.append (.append .nil one) two) ∧
      (ListExpr.append one (.append .nil two)) ≠ .append (.append .nil one) two ∧
      ListExpr.Step (.append one (.append .nil two)) (.append one two) ∧
      ListExpr.Step (.append (.append .nil one) two) (.append one two) :=
  ⟨.appendLeft (.appendNil one), .appendRight (.appendNil two), by decide,
    .appendRight (.appendNil two), .appendLeft (.appendNil one)⟩

/-- Positive example: one value and two costs; the left nesting of `one ++ two ++ one` takes
five steps, the right nesting four. -/
example : (ListExpr.append (.append one two) one).eval = (ListExpr.append one (.append two one)).eval ∧
    (ListExpr.append (.append one two) one).cost = 5 ∧
    (ListExpr.append one (.append two one)).cost = 4 :=
  ⟨rfl, rfl, rfl⟩

/-- Negative example: a value costs nothing. -/
example : one.cost = 0 := rfl

/-- Negative example: a value takes no step. -/
example (target : ListExpr) : ¬ ListExpr.Step one target := not_step_of_isValue trivial

/-- Negative example: `one ++ two` is not its own value. -/
example : (ListExpr.append one two).eval ≠ .append one two := by decide

end ListExpr

end Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append
