import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append.Source
import Mathlib.Logic.Relation
import Mathlib.Tactic.Linarith

/-!
# Two reversals of a list: the program, its running, and its typing

The source, over the lists of numbers and their append:

    rev nil          = nil
    rev (cons a as)  = append (rev as) (cons a nil)

    rev-onto acc nil         = acc
    rev-onto acc (cons x xs) = rev-onto (cons x acc) xs

Both reverse a list: `rev l` and `rev-onto nil l` are one function. They are different
programs and they cost differently. This module gives the source and two of its faces.

**Running** (`RevExpr`, `RevExpr.Step`). A closed expression is built from `nil`, `cons`,
`append`, `rev` and `rev-onto`; a step rewrites by one of the six equations anywhere inside.

* The expressions that take no step are exactly the values, the lists built from `nil` and
  `cons` (`RevExpr.isValue_iff_no_step`). Every expression reaches its value
  (`RevExpr.reaches_eval`) and a step does not change it (`RevExpr.eval_step`), so whatever order
  the steps are taken in, one value is reached (`RevExpr.eq_eval_of_reaches`).
* **The two reversals reach one value** at every closed list (`RevExpr.eval_rev_eq_revOnto`),
  because the accumulator holds what the plain reversal appends
  (`RevExpr.revOntoValue_eq_appendValue`).
* **Cost.** Every step lowers a cost by exactly one (`RevExpr.cost_step`), so every run of an
  expression to its value takes the same number of steps (`RevExpr.steps_eq_cost`). For a list
  of `n` elements the plain reversal takes `(n + 1)(n + 2) / 2` steps
  (`RevExpr.two_mul_steps_rev`: twice the count is `(n + 1)(n + 2)`), the accumulator
  reversal `n + 1` steps (`RevExpr.steps_revOnto`); the first is quadratic, the second linear,
  and they differ at every length from one on (`RevExpr.cost_rev_ne_revOnto`).

**The program as declarations** over the object package (`reversalProgram`), in the order
in which they are made: the lists, the append and its proof `append-nil` (`listProgram`); the
associativity of the append, a proof by induction (`appendAssocDef`); the plain reversal by
its two equations (`revDef`, `revDef_equations`); the accumulator reversal with the list first
and as authored (`revOntoFirstDef`, `revOntoDef`); the lemma
`Π (l acc : list). Id list (rev-onto acc l) (append (rev l) acc)` by induction on `l`, using
the hypothesis at a longer accumulator and associativity (`revOntoAppendDef`); and the theorem
`Π (l : list). Id list (rev l) (rev-onto nil l)`, from the lemma at the empty accumulator and
`append-nil` (`revIsRevOntoDef`). Each declaration is admissible over the package of the ones
before it; the rules of a declaration (its typing and its equations) are stated once for every
later list of declarations (`Extends`). The list is admissible (`reversalProgram_admissible`),
so the package has a set model and is consistent (`objectReversal_model`,
`objectReversal_consistent`).

**Typing.** Every expression's term is a list (`RevExpr.toTerm_typed`); **what runs is typed**:
a step is a derivable typed equality of the terms (`RevExpr.Step.typedEqual`); so the two
reversals of every closed list are equal in the judgment (`rev_typedEqual_revOnto`), and so
are the two functions `λ l. rev l` and `λ l. rev-onto nil l` applied to it
(`revFn_app_typedEqual`). **The theorem as a typed proof**: the constant `rev-is-rev-onto` is a
closed term of `Π (l : list). Id list (rev l) (rev-onto nil l)` (`revIsRevOnto_typed`), and so
are the lemma and associativity at their types (`revOntoAppend_typed`, `appendAssoc_typed`).

Positive examples: the list of zero, one and two reversed both ways is the list of two, one
and zero, in ten steps by `rev` and four by `rev-onto` (`zeroOneTwo_rev`); a palindrome is its
own reversal (`palindrome_rev`); reversing twice gives the list back
(`RevExpr.eval_rev_rev`). Negative examples: at the empty list the two costs agree, so the
difference begins at length one (`cost_rev_nil`); a value takes no step; the reversal of the
list of zero and one is not that list (`zeroOne_rev_ne`); and the theorem declared before its
lemma is not admissible (`theorem_before_lemma_not_admissible`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Reverse

open Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Append (NumExpr)

/-! ## The source -/

/-- A closed list expression of the source: the two constructors, the append, and the two
reversals. -/
inductive RevExpr where
  | nil
  | cons (head : NumExpr) (tail : RevExpr)
  | append (left right : RevExpr)
  | rev (list : RevExpr)
  | revOnto (acc list : RevExpr)
  deriving DecidableEq, Repr

namespace RevExpr

/-- A value: a list expression built from `nil` and `cons` only. -/
def IsValue : RevExpr → Prop
  | .nil => True
  | .cons _ tail => tail.IsValue
  | .append _ _ => False
  | .rev _ => False
  | .revOnto _ _ => False

/-- **One step of the source**: an instance of one of the six equations, anywhere in an
expression. -/
inductive Step : RevExpr → RevExpr → Prop
  | appendNil (right : RevExpr) : Step (.append .nil right) right
  | appendCons (head : NumExpr) (tail right : RevExpr) :
      Step (.append (.cons head tail) right) (.cons head (.append tail right))
  | revNil : Step (.rev .nil) .nil
  | revCons (head : NumExpr) (tail : RevExpr) :
      Step (.rev (.cons head tail)) (.append (.rev tail) (.cons head .nil))
  | revOntoNil (acc : RevExpr) : Step (.revOnto acc .nil) acc
  | revOntoCons (acc : RevExpr) (head : NumExpr) (tail : RevExpr) :
      Step (.revOnto acc (.cons head tail)) (.revOnto (.cons head acc) tail)
  | consTail {head : NumExpr} {tail tail' : RevExpr} :
      Step tail tail' → Step (.cons head tail) (.cons head tail')
  | appendLeft {left left' right : RevExpr} :
      Step left left' → Step (.append left right) (.append left' right)
  | appendRight {left right right' : RevExpr} :
      Step right right' → Step (.append left right) (.append left right')
  | revArg {list list' : RevExpr} : Step list list' → Step (.rev list) (.rev list')
  | revOntoAcc {acc acc' list : RevExpr} :
      Step acc acc' → Step (.revOnto acc list) (.revOnto acc' list)
  | revOntoList {acc list list' : RevExpr} :
      Step list list' → Step (.revOnto acc list) (.revOnto acc list')

/-! ## The evaluation function -/

/-- Append a value to a list by the two equations of the append; on a left argument that is
not a value the `append` is left as written. -/
def appendValue : RevExpr → RevExpr → RevExpr
  | .nil, right => right
  | .cons head tail, right => .cons head (appendValue tail right)
  | left, right => .append left right

/-- Reverse a value by the two equations of `rev`; on an argument that is not a value the
`rev` is left as written. -/
def revValue : RevExpr → RevExpr
  | .nil => .nil
  | .cons head tail => appendValue (revValue tail) (.cons head .nil)
  | list => .rev list

/-- Reverse a value onto an accumulator by the two equations of `rev-onto`. -/
def revOntoValue : RevExpr → RevExpr → RevExpr
  | acc, .nil => acc
  | acc, .cons head tail => revOntoValue (.cons head acc) tail
  | acc, list => .revOnto acc list

/-- **The evaluation function**: the value of an expression, by structural recursion. -/
def eval : RevExpr → RevExpr
  | .nil => .nil
  | .cons head tail => .cons head tail.eval
  | .append left right => appendValue left.eval right.eval
  | .rev list => revValue list.eval
  | .revOnto acc list => revOntoValue acc.eval list.eval

theorem appendValue_isValue {left right : RevExpr} (hleft : left.IsValue)
    (hright : right.IsValue) : (appendValue left right).IsValue := by
  induction left with
  | nil => exact hright
  | cons head tail ih => exact ih hleft
  | append _ _ _ _ => exact hleft.elim
  | rev _ _ => exact hleft.elim
  | revOnto _ _ _ _ => exact hleft.elim

theorem revValue_isValue {list : RevExpr} (h : list.IsValue) : (revValue list).IsValue := by
  induction list with
  | nil => trivial
  | cons head tail ih => exact appendValue_isValue (ih h) trivial
  | append _ _ _ _ => exact h.elim
  | rev _ _ => exact h.elim
  | revOnto _ _ _ _ => exact h.elim

theorem revOntoValue_isValue {list : RevExpr} (h : list.IsValue) :
    ∀ {acc : RevExpr}, acc.IsValue → (revOntoValue acc list).IsValue := by
  induction list with
  | nil => exact fun hacc => hacc
  | cons head tail ih => exact fun hacc => ih h (show (RevExpr.cons head _).IsValue from hacc)
  | append _ _ _ _ => exact h.elim
  | rev _ _ => exact h.elim
  | revOnto _ _ _ _ => exact h.elim

/-- The value of every expression is a value. -/
theorem eval_isValue (e : RevExpr) : e.eval.IsValue := by
  induction e with
  | nil => trivial
  | cons head tail ih => exact ih
  | append l r ihl ihr => exact appendValue_isValue ihl ihr
  | rev l ih => exact revValue_isValue ih
  | revOnto acc l ihacc ihl => exact revOntoValue_isValue ihl ihacc

/-- A value evaluates to itself. -/
theorem eval_of_isValue {e : RevExpr} (h : e.IsValue) : e.eval = e := by
  induction e with
  | nil => rfl
  | cons head tail ih => exact congrArg (RevExpr.cons head) (ih h)
  | append _ _ _ _ => exact h.elim
  | rev _ _ => exact h.elim
  | revOnto _ _ _ _ => exact h.elim

/-! ## Values are the expressions that take no step -/

/-- An expression that takes a step is not a value. -/
theorem not_isValue_of_step {e e' : RevExpr} (step : Step e e') : ¬ e.IsValue := by
  induction step with
  | consTail _ ih => exact ih
  | _ => exact id

/-- A value takes no step. -/
theorem not_step_of_isValue {e e' : RevExpr} (h : e.IsValue) : ¬ Step e e' :=
  fun step => not_isValue_of_step step h

/-- A value is the empty list or a number before a value. -/
theorem isValue_cases {e : RevExpr} (h : e.IsValue) :
    e = .nil ∨ ∃ head tail, e = .cons head tail := by
  cases e with
  | nil => exact Or.inl rfl
  | cons head tail => exact Or.inr ⟨head, tail, rfl⟩
  | append _ _ => exact h.elim
  | rev _ => exact h.elim
  | revOnto _ _ => exact h.elim

/-- Every expression is a value or takes a step. -/
theorem isValue_or_exists_step (e : RevExpr) : e.IsValue ∨ ∃ e', Step e e' := by
  induction e with
  | nil => exact Or.inl trivial
  | cons head tail ih =>
      rcases ih with hv | ⟨tail', step⟩
      · exact Or.inl hv
      · exact Or.inr ⟨.cons head tail', .consTail step⟩
  | append l r ihl _ =>
      refine Or.inr ?_
      rcases ihl with hv | ⟨l', step⟩
      · rcases isValue_cases hv with rfl | ⟨head, tail, rfl⟩
        · exact ⟨r, .appendNil r⟩
        · exact ⟨.cons head (.append tail r), .appendCons head tail r⟩
      · exact ⟨.append l' r, .appendLeft step⟩
  | rev l ih =>
      refine Or.inr ?_
      rcases ih with hv | ⟨l', step⟩
      · rcases isValue_cases hv with rfl | ⟨head, tail, rfl⟩
        · exact ⟨.nil, .revNil⟩
        · exact ⟨.append (.rev tail) (.cons head .nil), .revCons head tail⟩
      · exact ⟨.rev l', .revArg step⟩
  | revOnto acc l _ ihl =>
      refine Or.inr ?_
      rcases ihl with hv | ⟨l', step⟩
      · rcases isValue_cases hv with rfl | ⟨head, tail, rfl⟩
        · exact ⟨acc, .revOntoNil acc⟩
        · exact ⟨.revOnto (.cons head acc) tail, .revOntoCons acc head tail⟩
      · exact ⟨.revOnto acc l', .revOntoList step⟩

/-- **The values are exactly the expressions that take no step.** -/
theorem isValue_iff_no_step {e : RevExpr} : e.IsValue ↔ ∀ e', ¬ Step e e' := by
  constructor
  · intro h e'
    exact not_step_of_isValue h
  · intro h
    rcases isValue_or_exists_step e with hv | ⟨e', step⟩
    · exact hv
    · exact (h e' step).elim

/-! ## Every expression reaches its value -/

/-- Running anywhere inside an expression: a run of a part is a run of the whole. -/
theorem reaches_congr {f : RevExpr → RevExpr} (lift : ∀ {a b}, Step a b → Step (f a) (f b))
    {a b : RevExpr} (h : Relation.ReflTransGen Step a b) :
    Relation.ReflTransGen Step (f a) (f b) := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (lift step)

/-- The `append` of a value and a list reaches what the helper computes. -/
theorem reaches_appendValue {l : RevExpr} (h : l.IsValue) (r : RevExpr) :
    Relation.ReflTransGen Step (.append l r) (appendValue l r) := by
  induction l with
  | nil => exact .single (.appendNil r)
  | cons head tail ih =>
      exact Relation.ReflTransGen.head (.appendCons head tail r)
        (reaches_congr (f := RevExpr.cons head) .consTail (ih h))
  | append _ _ _ _ => exact h.elim
  | rev _ _ => exact h.elim
  | revOnto _ _ _ _ => exact h.elim

/-- `rev` of a value reaches what the helper computes. -/
theorem reaches_revValue {l : RevExpr} (h : l.IsValue) :
    Relation.ReflTransGen Step (.rev l) (revValue l) := by
  induction l with
  | nil => exact .single .revNil
  | cons head tail ih =>
      exact Relation.ReflTransGen.head (.revCons head tail)
        ((reaches_congr (f := fun x => RevExpr.append x (.cons head .nil)) .appendLeft
          (ih h)).trans (reaches_appendValue (revValue_isValue (list := tail) h) _))
  | append _ _ _ _ => exact h.elim
  | rev _ _ => exact h.elim
  | revOnto _ _ _ _ => exact h.elim

/-- `rev-onto` of an accumulator and a value reaches what the helper computes. -/
theorem reaches_revOntoValue {l : RevExpr} (h : l.IsValue) :
    ∀ acc : RevExpr, Relation.ReflTransGen Step (.revOnto acc l) (revOntoValue acc l) := by
  induction l with
  | nil => exact fun acc => .single (.revOntoNil acc)
  | cons head tail ih =>
      exact fun acc => Relation.ReflTransGen.head (.revOntoCons acc head tail) (ih h _)
  | append _ _ _ _ => exact h.elim
  | rev _ _ => exact h.elim
  | revOnto _ _ _ _ => exact h.elim

/-- **Every expression reaches its value.** -/
theorem reaches_eval (e : RevExpr) : Relation.ReflTransGen Step e e.eval := by
  induction e with
  | nil => exact .refl
  | cons head tail ih => exact reaches_congr (f := RevExpr.cons head) .consTail ih
  | append l r ihl ihr =>
      exact ((reaches_congr (f := fun x => RevExpr.append x r) .appendLeft ihl).trans
        (reaches_congr (f := RevExpr.append l.eval) .appendRight ihr)).trans
        (reaches_appendValue (eval_isValue l) r.eval)
  | rev l ih =>
      exact (reaches_congr (f := RevExpr.rev) .revArg ih).trans
        (reaches_revValue (eval_isValue l))
  | revOnto acc l ihacc ihl =>
      exact ((reaches_congr (f := fun x => RevExpr.revOnto x l) .revOntoAcc ihacc).trans
        (reaches_congr (f := RevExpr.revOnto acc.eval) .revOntoList ihl)).trans
        (reaches_revOntoValue (eval_isValue l) acc.eval)

/-! ## The value does not depend on the order of the steps -/

/-- **A step does not change the value.** -/
theorem eval_step {e e' : RevExpr} (step : Step e e') : e.eval = e'.eval := by
  induction step with
  | appendNil _ => rfl
  | appendCons _ _ _ => rfl
  | revNil => rfl
  | revCons _ _ => rfl
  | revOntoNil _ => rfl
  | revOntoCons _ _ _ => rfl
  | consTail _ ih => exact congrArg (RevExpr.cons _) ih
  | appendLeft _ ih => exact congrArg (fun value => appendValue value _) ih
  | appendRight _ ih => exact congrArg (appendValue _) ih
  | revArg _ ih => exact congrArg revValue ih
  | revOntoAcc _ ih => exact congrArg (fun value => revOntoValue value _) ih
  | revOntoList _ ih => exact congrArg (revOntoValue _) ih

/-- A run does not change the value. -/
theorem eval_reaches {e e' : RevExpr} (h : Relation.ReflTransGen Step e e') :
    e.eval = e'.eval := by
  induction h with
  | refl => rfl
  | tail _ step ih => exact ih.trans (eval_step step)

/-- **Uniqueness of the result**: whatever order the steps are taken in, a value reached from
`e` is `e.eval`. -/
theorem eq_eval_of_reaches {e v : RevExpr} (h : Relation.ReflTransGen Step e v)
    (hv : v.IsValue) : v = e.eval :=
  ((eval_reaches h).trans (eval_of_isValue hv)).symm

/-- The value of `e` is the one value that running `e` reaches. -/
theorem reaches_value_iff {e v : RevExpr} :
    Relation.ReflTransGen Step e v ∧ v.IsValue ↔ v = e.eval := by
  constructor
  · rintro ⟨h, hv⟩
    exact eq_eval_of_reaches h hv
  · rintro rfl
    exact ⟨reaches_eval e, eval_isValue e⟩

/-! ## The two reversals reach one value -/

theorem appendValue_nil {v : RevExpr} (h : v.IsValue) : appendValue v .nil = v := by
  induction v with
  | nil => rfl
  | cons head tail ih => exact congrArg (RevExpr.cons head) (ih h)
  | append _ _ _ _ => exact h.elim
  | rev _ _ => exact h.elim
  | revOnto _ _ _ _ => exact h.elim

theorem appendValue_assoc {x : RevExpr} (h : x.IsValue) (y z : RevExpr) :
    appendValue (appendValue x y) z = appendValue x (appendValue y z) := by
  induction x with
  | nil => rfl
  | cons head tail ih => exact congrArg (RevExpr.cons head) (ih h)
  | append _ _ _ _ => exact h.elim
  | rev _ _ => exact h.elim
  | revOnto _ _ _ _ => exact h.elim

/-- **The accumulator holds what the plain reversal appends**: a value reversed onto an
accumulator is its reversal followed by the accumulator. -/
theorem revOntoValue_eq_appendValue {v : RevExpr} (h : v.IsValue) :
    ∀ acc : RevExpr, revOntoValue acc v = appendValue (revValue v) acc := by
  induction v with
  | nil => exact fun _ => rfl
  | cons head tail ih =>
      intro acc
      show revOntoValue (.cons head acc) tail =
        appendValue (appendValue (revValue tail) (.cons head .nil)) acc
      rw [ih h, appendValue_assoc (revValue_isValue (list := tail) h)]
      rfl
  | append _ _ _ _ => exact h.elim
  | rev _ _ => exact h.elim
  | revOnto _ _ _ _ => exact h.elim

/-- **The two reversals reach one value**: `rev l` and `rev-onto nil l` have one value, for
every closed list expression `l`. -/
theorem eval_rev_eq_revOnto (l : RevExpr) : (RevExpr.rev l).eval = (RevExpr.revOnto .nil l).eval := by
  show revValue l.eval = revOntoValue .nil l.eval
  rw [revOntoValue_eq_appendValue (eval_isValue l), appendValue_nil
    (revValue_isValue (eval_isValue l))]

theorem revValue_appendValue {x : RevExpr} (hx : x.IsValue) {y : RevExpr} (hy : y.IsValue) :
    revValue (appendValue x y) = appendValue (revValue y) (revValue x) := by
  induction x with
  | nil => exact (appendValue_nil (revValue_isValue hy)).symm
  | cons head tail ih =>
      show appendValue (revValue (appendValue tail y)) (.cons head .nil) =
        appendValue (revValue y) (appendValue (revValue tail) (.cons head .nil))
      rw [ih hx, appendValue_assoc (revValue_isValue hy)]
  | append _ _ _ _ => exact hx.elim
  | rev _ _ => exact hx.elim
  | revOnto _ _ _ _ => exact hx.elim

theorem revValue_revValue {v : RevExpr} (h : v.IsValue) : revValue (revValue v) = v := by
  induction v with
  | nil => rfl
  | cons head tail ih =>
      show revValue (appendValue (revValue tail) (.cons head .nil)) = .cons head tail
      rw [revValue_appendValue (revValue_isValue (list := tail) h)
        (show (RevExpr.cons head .nil).IsValue from trivial), ih h]
      rfl
  | append _ _ _ _ => exact h.elim
  | rev _ _ => exact h.elim
  | revOnto _ _ _ _ => exact h.elim

/-- Positive example: **reversing twice gives the list back**, run. -/
theorem eval_rev_rev (l : RevExpr) : (RevExpr.rev (.rev l)).eval = l.eval :=
  revValue_revValue (eval_isValue l)

/-! ## The cost of running -/

/-- The number of elements of the list an expression evaluates to. -/
def length : RevExpr → Nat
  | .nil => 0
  | .cons _ tail => tail.length + 1
  | .append left right => left.length + right.length
  | .rev list => list.length
  | .revOnto acc list => acc.length + list.length

/-- **The steps of `rev` on a list of `n` elements**: one at the empty list; at a longer one,
one step, the reversal of the rest, and the append of a list of `n` elements to a one-element
list, which takes `n + 1` steps. -/
def revCost : Nat → Nat
  | 0 => 1
  | n + 1 => revCost n + n + 2

/-- **The quadratic formula**: twice the steps of `rev` on `n` elements is `(n + 1)(n + 2)`. -/
theorem two_mul_revCost (n : Nat) : 2 * revCost n = (n + 1) * (n + 2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [revCost]
      nlinarith [ih]

/-- **The cost of running an expression**: the append costs the length of its first list and
one more; `rev` costs `revCost` of the length; `rev-onto` costs the length of its list and one
more; each on top of the costs of its arguments. -/
def cost : RevExpr → Nat
  | .nil => 0
  | .cons _ tail => tail.cost
  | .append left right => left.cost + right.cost + left.length + 1
  | .rev list => list.cost + revCost list.length
  | .revOnto acc list => acc.cost + list.cost + list.length + 1

/-- `StepsIn n e e'`: running `e` reaches `e'` in exactly `n` steps. -/
inductive StepsIn : Nat → RevExpr → RevExpr → Prop
  | refl (e : RevExpr) : StepsIn 0 e e
  | head {n : Nat} {e e' e'' : RevExpr} : Step e e' → StepsIn n e' e'' → StepsIn (n + 1) e e''

/-- A step does not change the number of elements. -/
theorem length_step {e e' : RevExpr} (step : Step e e') : e.length = e'.length := by
  induction step with
  | consTail _ ih => simp only [length, ih]
  | appendLeft _ ih => simp only [length, ih]
  | appendRight _ ih => simp only [length, ih]
  | revArg _ ih => simp only [length, ih]
  | revOntoAcc _ ih => simp only [length, ih]
  | revOntoList _ ih => simp only [length, ih]
  | _ => simp only [length] <;> omega

/-- A run does not change the number of elements. -/
theorem length_reaches {e e' : RevExpr} (h : Relation.ReflTransGen Step e e') :
    e.length = e'.length := by
  induction h with
  | refl => rfl
  | tail _ step ih => exact ih.trans (length_step step)

/-- The number of elements of an expression is that of its value. -/
theorem length_eval (e : RevExpr) : e.eval.length = e.length :=
  (length_reaches (reaches_eval e)).symm

/-- **Every step lowers the cost by exactly one.** -/
theorem cost_step {e e' : RevExpr} (step : Step e e') : e.cost = e'.cost + 1 := by
  induction step with
  | revCons _ _ => simp only [cost, length, revCost]; omega
  | consTail _ ih => simp only [cost]; omega
  | appendLeft step ih => simp only [cost, length_step step]; omega
  | appendRight _ ih => simp only [cost]; omega
  | revArg step ih => simp only [cost, length_step step]; omega
  | revOntoAcc _ ih => simp only [cost]; omega
  | revOntoList step ih => simp only [cost, length_step step]; omega
  | _ => simp only [cost, length, revCost] <;> omega

/-- A value costs nothing. -/
theorem cost_of_isValue {e : RevExpr} (h : e.IsValue) : e.cost = 0 := by
  induction e with
  | nil => rfl
  | cons head tail ih => exact ih h
  | append _ _ _ _ => exact h.elim
  | rev _ _ => exact h.elim
  | revOnto _ _ _ _ => exact h.elim

theorem StepsIn.reaches {n : Nat} {e e' : RevExpr} (h : StepsIn n e e') :
    Relation.ReflTransGen Step e e' := by
  induction h with
  | refl => exact .refl
  | head step _ ih => exact .head step ih

theorem exists_stepsIn_of_reaches {e e' : RevExpr} (h : Relation.ReflTransGen Step e e') :
    ∃ n, StepsIn n e e' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .refl _⟩
  | head step _ ih =>
      obtain ⟨n, run⟩ := ih
      exact ⟨n + 1, .head step run⟩

/-- A run of `n` steps lowers the cost by `n`. -/
theorem cost_stepsIn {n : Nat} {e e' : RevExpr} (h : StepsIn n e e') : e.cost = e'.cost + n := by
  induction h with
  | refl => rfl
  | head step _ ih => rw [cost_step step, ih, Nat.add_assoc]

/-- **Every run of an expression to a value takes exactly its cost in steps**, whatever order
the steps are taken in. -/
theorem steps_eq_cost {n : Nat} {e v : RevExpr} (h : StepsIn n e v) (hv : v.IsValue) :
    n = e.cost := by
  have count := cost_stepsIn h
  rw [cost_of_isValue hv, Nat.zero_add] at count
  exact count.symm

/-- Running `e` reaches its value in exactly `e.cost` steps. -/
theorem stepsIn_cost_eval (e : RevExpr) : StepsIn e.cost e e.eval := by
  obtain ⟨n, run⟩ := exists_stepsIn_of_reaches (reaches_eval e)
  rw [← steps_eq_cost run (eval_isValue e)]
  exact run

/-- **Running always ends**: there is no endless run. -/
theorem wellFounded_step : WellFounded (fun later earlier : RevExpr => Step earlier later) :=
  Subrelation.wf (r := InvImage (· < ·) cost)
    (fun {later earlier} (step : Step earlier later) => by
      show later.cost < earlier.cost
      rw [cost_step step]
      exact Nat.lt_succ_self later.cost)
    (InvImage.wf cost Nat.lt_wfRel.wf)

/-! ## The two cost formulas -/

/-- The cost of `rev` at a value of `n` elements is `revCost n`. -/
theorem cost_rev {v : RevExpr} (h : v.IsValue) : (RevExpr.rev v).cost = revCost v.length := by
  show v.cost + revCost v.length = revCost v.length
  rw [cost_of_isValue h, Nat.zero_add]

/-- The cost of `rev-onto nil` at a value of `n` elements is `n + 1`. -/
theorem cost_revOnto {v : RevExpr} (h : v.IsValue) :
    (RevExpr.revOnto .nil v).cost = v.length + 1 := by
  show 0 + v.cost + v.length + 1 = v.length + 1
  rw [cost_of_isValue h]
  omega

/-- **The plain reversal is quadratic**: every run of `rev v` to a value, for a value `v` of
`n` elements, takes `k` steps with `2 k = (n + 1)(n + 2)`. -/
theorem two_mul_steps_rev {k : Nat} {v w : RevExpr} (hv : v.IsValue)
    (run : StepsIn k (.rev v) w) (hw : w.IsValue) : 2 * k = (v.length + 1) * (v.length + 2) := by
  rw [steps_eq_cost run hw, cost_rev hv, two_mul_revCost]

/-- **The accumulator reversal is linear**: every run of `rev-onto nil v` to a value, for a
value `v` of `n` elements, takes `n + 1` steps. -/
theorem steps_revOnto {k : Nat} {v w : RevExpr} (hv : v.IsValue)
    (run : StepsIn k (.revOnto .nil v) w) (hw : w.IsValue) : k = v.length + 1 := by
  rw [steps_eq_cost run hw, cost_revOnto hv]

theorem lt_revCost (n : Nat) : n + 1 < revCost n + 1 := by
  induction n with
  | zero => decide
  | succ n ih => simp only [revCost]; omega

/-- **The two costs differ at every length from one on**: `rev` takes more steps. -/
theorem cost_rev_ne_revOnto {v : RevExpr} (h : v.IsValue) (long : 1 ≤ v.length) :
    (RevExpr.revOnto .nil v).cost < (RevExpr.rev v).cost := by
  rw [cost_rev h, cost_revOnto h]
  obtain ⟨m, hm⟩ : ∃ m, v.length = m + 1 := ⟨v.length - 1, by omega⟩
  rw [hm]
  have := lt_revCost m
  simp only [revCost]
  omega

end RevExpr

/-! ## Examples -/

open RevExpr

/-- The numeral one and two. -/
abbrev oneN : NumExpr := .suc .zero
abbrev twoN : NumExpr := .suc (.suc .zero)

/-- The list of zero, one and two. -/
abbrev zeroOneTwo : RevExpr := .cons .zero (.cons oneN (.cons twoN .nil))

/-- The list of zero and one. -/
abbrev zeroOne : RevExpr := .cons .zero (.cons oneN .nil)

/-- Positive example: **the list of zero, one and two, reversed both ways**, is the list of
two, one and zero; `rev` takes ten steps and `rev-onto nil` four. -/
theorem zeroOneTwo_rev :
    (RevExpr.rev zeroOneTwo).eval = .cons twoN (.cons oneN (.cons .zero .nil)) ∧
      (RevExpr.revOnto .nil zeroOneTwo).eval = .cons twoN (.cons oneN (.cons .zero .nil)) ∧
      (RevExpr.rev zeroOneTwo).cost = 10 ∧ (RevExpr.revOnto .nil zeroOneTwo).cost = 4 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Positive example: the list of zero and one reversed both ways, in six and three steps. -/
example : (RevExpr.rev zeroOne).eval = .cons oneN (.cons .zero .nil) ∧
    (RevExpr.rev zeroOne).cost = 6 ∧ (RevExpr.revOnto .nil zeroOne).cost = 3 :=
  ⟨rfl, rfl, rfl⟩

/-- Positive example: the run of `rev-onto nil` on the list of zero and one, step by step. -/
example : StepsIn 3 (.revOnto .nil zeroOne) (.cons oneN (.cons .zero .nil)) :=
  .head (.revOntoCons .nil .zero (.cons oneN .nil))
    (.head (.revOntoCons (.cons .zero .nil) oneN .nil)
      (.head (.revOntoNil _) (.refl _)))

/-- Positive example: **a palindrome is its own reversal**, both ways. -/
theorem palindrome_rev :
    (RevExpr.rev (.cons .zero (.cons oneN (.cons .zero .nil)))).eval =
        .cons .zero (.cons oneN (.cons .zero .nil)) ∧
      (RevExpr.revOnto .nil (.cons .zero (.cons oneN (.cons .zero .nil)))).eval =
        .cons .zero (.cons oneN (.cons .zero .nil)) :=
  ⟨rfl, rfl⟩

/-- Negative example: **at the empty list the two costs agree**; the difference begins at
length one. -/
theorem cost_rev_nil : (RevExpr.rev .nil).cost = (RevExpr.revOnto .nil .nil).cost := rfl

/-- Negative example: the reversal of the list of zero and one is not that list. -/
theorem zeroOne_rev_ne : (RevExpr.rev zeroOne).eval ≠ zeroOne := by decide

/-- Negative example: a value takes no step. -/
example (target : RevExpr) : ¬ RevExpr.Step zeroOne target := not_step_of_isValue trivial

/-! ## The program as declarations -/

section Declarations

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Presentation.TypedEquality Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Annotated
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
open CodeModel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)

universe u

/-- The name of the plain reversal. -/
def revN : DeclName := .str .anonymous "rev"

/-- The name of the proof that the append is associative. -/
def appendAssocN : DeclName := .str .anonymous "append-assoc"

/-- The name of the lemma relating the two reversals. -/
def revOntoAppendN : DeclName := .str .anonymous "rev-onto-append"

/-- The name of the theorem that the two reversals agree. -/
def revIsRevOntoN : DeclName := .str .anonymous "rev-is-rev-onto"

/-- `rev` applied to a term. -/
abbrev crev {n : Nat} (l : CTm Tower.Head n) : CTm Tower.Head n := .app (.const revN) l

/-- The statement of associativity at three lists. -/
abbrev assocAt {n : Nat} (a b c : CTm Tower.Head n) : CTm Tower.Head n :=
  .id clist (cappend (cappend a b) c) (cappend a (cappend b c))

/-- The statement of the lemma at a list and an accumulator. -/
abbrev revOntoAppendAt {n : Nat} (l acc : CTm Tower.Head n) : CTm Tower.Head n :=
  .id clist (crevOnto acc l) (cappend (crev l) acc)

/-- The statement of the theorem at a list. -/
abbrev revIsRevOntoAt {n : Nat} (l : CTm Tower.Head n) : CTm Tower.Head n :=
  .id clist (crev l) (crevOnto cnil l)

/-! ### The associativity of the append, by induction -/

/-- The two later arguments of associativity: two lists. -/
abbrev twoLists : CTele Tower.Head 1 3 := .cons clist (.cons clist .nil)

/-- **The right sides of associativity**: reflexivity at the empty list; at a longer list the
congruence of the hypothesis at the two later lists under "the number before". -/
def appendAssocBody : (k : DeclName) → (fields : List CtorField) →
    CTm Tower.Head (twoLists.endAt (fields.length + (recPositions fields).length))
  | _, [] => (.refl (cappend (.var 1) (.var 0)) : CTm Tower.Head 2)
  | _, [.closed _, .recursive] =>
      (congOf clist clist (.app (.const consN) (.var 4)) (cappend (cappend (.var 3) (.var 1)) (.var 0))
        (cappend (.var 3) (cappend (.var 1) (.var 0))) (.app (.app (.var 2) (.var 1)) (.var 0)) :
        CTm Tower.Head 5)
  | _, _ => .const .anonymous

/-- **Associativity of the append as a declaration**: a proof by structural recursion on the
first list, of type `Π (a b c : list). Id list (append (append a b) c) (append a (append b c))`. -/
def appendAssocDef : RecursiveDefinition Tower.Head where
  name := appendAssocN
  datatype := listDecl
  width := 3
  later := twoLists
  result := assocAt (.var 2) (.var 1) (.var 0)
  body := appendAssocBody

section InAppend

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- A dependent function type between types of the lowest universe is one. -/
theorem piU0A {A : CTm Tower.Head n} {B : CTm Tower.Head (n + 1)}
    (domain : CTyped objectAppend Γ A cU0) (codomain : CTyped objectAppend (.snoc Γ A) B cU0) :
    CTyped objectAppend Γ (.pi A B) cU0 :=
  CDerivable.cumul (.piForm domain (.sort _) codomain (.sort _) (.sorts _ _))
    (fun valuation => by simp [LevelExpr.eval])

theorem listA_typed : CTyped objectAppend Γ clist cU0 := ofListsAppend list_typed

theorem assocAt_typed {a b c : CTm Tower.Head n} (ha : CTyped objectAppend Γ a clist)
    (hb : CTyped objectAppend Γ b clist) (hc : CTyped objectAppend Γ c clist) :
    CTyped objectAppend Γ (assocAt a b c) cU0 :=
  .idForm listA_typed (LevelTower.IsUniverse.sort _) (cappend_typed (cappend_typed ha hb) hc)
    (cappend_typed ha (cappend_typed hb hc))

/-- The statement over the two later lists, in a context whose last entry is a list. -/
theorem assocFamily_typed :
    CTyped objectAppend (.snoc Γ clist) (.pi clist (.pi clist (assocAt (.var 2) (.var 1) (.var 0))))
      cU0 :=
  piU0A listA_typed (piU0A listA_typed (assocAt_typed (.var 2) (.var 1) (.var 0)))

theorem assocType_typed :
    CTyped objectAppend Γ (.pi clist (.pi clist (.pi clist (assocAt (.var 2) (.var 1) (.var 0)))))
      cU0 :=
  piU0A listA_typed assocFamily_typed

/-- The context of the step: a number, a list, the hypothesis at the list, and two lists. -/
abbrev assocStepCtx : CCtx Tower.Head 5 :=
  .snoc (.snoc (.snoc (.snoc (.snoc .nil cnum) clist)
    (.pi clist (.pi clist (assocAt (.var 2) (.var 1) (.var 0))))) clist) clist

theorem assocStepCtx_formed : CCtxFormed objectAppend assocStepCtx :=
  .snoc (.snoc (.snoc (.snoc (.snoc .nil ⟨_, LevelTower.IsUniverse.sort _,
      ofListsAppend (ofObject cnum_typed)⟩) ⟨_, LevelTower.IsUniverse.sort _, listA_typed⟩)
      ⟨_, LevelTower.IsUniverse.sort _, assocFamily_typed⟩) ⟨_, LevelTower.IsUniverse.sort _,
      listA_typed⟩) ⟨_, LevelTower.IsUniverse.sort _, listA_typed⟩

/-- **The congruence of identity proofs** in the package with the append. -/
theorem congA_typed {A B f x y p : CTm Tower.Head n}
    (hA : CTyped objectAppend Γ A cU0) (hB : CTyped objectAppend Γ B cU0)
    (hf : CTyped objectAppend Γ f (.pi A (B.rename wk))) (hx : CTyped objectAppend Γ x A)
    (hy : CTyped objectAppend Γ y A) (hp : CTyped objectAppend Γ p (.id A x y)) :
    CTyped objectAppend Γ (congOf A B f x y p) (.id B (.app f x) (.app f y)) :=
  CTyped.substitute (ofListsAppend (ofObject congTerm_typed))
    (σ := fun i => [p, y, x, f, B, A].getD i.val A)
    (fun j => match j with
      | ⟨0, _⟩ => hp
      | ⟨1, _⟩ => hy
      | ⟨2, _⟩ => hx
      | ⟨3, _⟩ => hf
      | ⟨4, _⟩ => hB
      | ⟨5, _⟩ => hA)

/-- The two lists appended in either nesting compute in the same way at the empty list. -/
theorem assocBase_typed :
    CTyped objectAppend (CCtx.snoc (.snoc .nil clist) clist)
      (.refl (cappend (.var 1) (.var 0)) : CTm Tower.Head 2) (assocAt cnil (.var 1) (.var 0)) := by
  have b : CTyped objectAppend (CCtx.snoc (.snoc .nil clist) clist) (.var 1 : CTm Tower.Head 2)
      clist := .var 1
  have c : CTyped objectAppend (CCtx.snoc (.snoc .nil clist) clist) (.var 0 : CTm Tower.Head 2)
      clist := .var 0
  have computed : CEqual objectAppend (CCtx.snoc (.snoc .nil clist) clist)
      (assocAt cnil (.var 1) (.var 0))
      (.id clist (cappend (.var 1) (.var 0)) (cappend (.var 1) (.var 0))) cU0 :=
    .idCong (.refl listA_typed) (LevelTower.IsUniverse.sort _)
      (.appCong (B := clist) (.appCong (B := clistFn) (.refl append_typed) (append_nil_rule b))
        (.refl c))
      (append_nil_rule (cappend_typed b c))
  exact .conv (.reflIntro (cappend_typed b c)) (.symm computed) (LevelTower.IsUniverse.sort _)

/-- **The step of associativity**: the hypothesis at the two later lists, carried under "the
number before", after both nestings at the longer list have computed. -/
theorem assocStep_typed :
    CTyped objectAppend assocStepCtx
      (congOf clist clist (.app (.const consN) (.var 4)) (cappend (cappend (.var 3) (.var 1)) (.var 0))
        (cappend (.var 3) (cappend (.var 1) (.var 0))) (.app (.app (.var 2) (.var 1)) (.var 0)))
      (assocAt (ccons (.var 4) (.var 3)) (.var 1) (.var 0)) := by
  have a : CTyped objectAppend assocStepCtx (.var 4) cnum := .var 4
  have as : CTyped objectAppend assocStepCtx (.var 3) clist := .var 3
  have b : CTyped objectAppend assocStepCtx (.var 1) clist := .var 1
  have c : CTyped objectAppend assocStepCtx (.var 0) clist := .var 0
  have ihType : CTyped objectAppend assocStepCtx (.var 2)
      (.pi clist (.pi clist (assocAt (.var 5) (.var 1) (.var 0)))) := .var 2
  have hypothesis : CTyped objectAppend assocStepCtx (.app (.app (.var 2) (.var 1)) (.var 0))
      (assocAt (.var 3) (.var 1) (.var 0)) := CDerivable.appElim (CDerivable.appElim ihType b) c
  have before : CTyped objectAppend assocStepCtx (.app (.const consN) (.var 4)) (.pi clist clist) :=
    .appElim (B := .pi clist clist) (ofListsAppend consConst_typed) a
  have congruent := congA_typed listA_typed listA_typed before
    (cappend_typed (cappend_typed as b) c) (cappend_typed as (cappend_typed b c)) hypothesis
  have left : CEqual objectAppend assocStepCtx (cappend (cappend (ccons (.var 4) (.var 3)) (.var 1)) (.var 0))
      (ccons (.var 4) (cappend (cappend (.var 3) (.var 1)) (.var 0))) clist :=
    .trans (.appCong (B := clist) (.appCong (B := clistFn) (.refl append_typed)
        (append_cons_rule a as b)) (.refl c))
      (append_cons_rule a (cappend_typed as b) c)
  have right : CEqual objectAppend assocStepCtx (cappend (ccons (.var 4) (.var 3)) (cappend (.var 1) (.var 0)))
      (ccons (.var 4) (cappend (.var 3) (cappend (.var 1) (.var 0)))) clist :=
    append_cons_rule a as (cappend_typed b c)
  have computed : CEqual objectAppend assocStepCtx (assocAt (ccons (.var 4) (.var 3)) (.var 1) (.var 0))
      (.id clist (ccons (.var 4) (cappend (cappend (.var 3) (.var 1)) (.var 0)))
        (ccons (.var 4) (cappend (.var 3) (cappend (.var 1) (.var 0))))) cU0 :=
    .idCong (.refl listA_typed) (LevelTower.IsUniverse.sort _) left right
  exact .conv congruent (.symm computed) (LevelTower.IsUniverse.sort _)

end InAppend

theorem appendAssocDef_formed {i : Nat} {k : DeclName} {fields : List CtorField}
    (entry : listCtors[i]? = some (k, fields)) :
    CCtxFormed objectAppend
      (laterCtx listN twoLists (assocAt (.var 2) (.var 1) (.var 0)) k fields) := by
  match i, entry with
  | 0, entry =>
    obtain ⟨rfl, rfl⟩ : nilN = k ∧ ([] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    have formed : CCtxFormed objectAppend (CCtx.snoc (.snoc .nil clist) clist) :=
      .snoc (.snoc .nil ⟨_, LevelTower.IsUniverse.sort _, listA_typed⟩)
        ⟨_, LevelTower.IsUniverse.sort _, listA_typed⟩
    exact formed
  | 1, entry =>
    obtain ⟨rfl, rfl⟩ :
        consN = k ∧ ([.closed (.const numN), .recursive] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    exact assocStepCtx_formed
  | i + 2, entry => exact nomatch entry

theorem appendAssocDef_resultType {i : Nat} {k : DeclName} {fields : List CtorField}
    (entry : listCtors[i]? = some (k, fields)) :
    CIsType objectAppend (laterCtx listN twoLists (assocAt (.var 2) (.var 1) (.var 0)) k fields)
      (laterResult twoLists (assocAt (.var 2) (.var 1) (.var 0)) k fields) := by
  match i, entry with
  | 0, entry =>
    obtain ⟨rfl, rfl⟩ : nilN = k ∧ ([] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    have typed : CTyped objectAppend (CCtx.snoc (.snoc .nil clist) clist)
        (assocAt cnil (.var 1) (.var 0) : CTm Tower.Head 2) cU0 :=
      assocAt_typed (ofListsAppend nil_typed) (.var 1) (.var 0)
    exact ⟨_, LevelTower.IsUniverse.sort _, typed⟩
  | 1, entry =>
    obtain ⟨rfl, rfl⟩ :
        consN = k ∧ ([.closed (.const numN), .recursive] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    have typed : CTyped objectAppend assocStepCtx (assocAt (ccons (.var 4) (.var 3)) (.var 1) (.var 0))
        cU0 := assocAt_typed (ofListsAppend (cons_typed (.var 4) (.var 3))) (.var 1) (.var 0)
    exact ⟨_, LevelTower.IsUniverse.sort _, typed⟩
  | i + 2, entry => exact nomatch entry

theorem appendAssocDef_bodies {i : Nat} {k : DeclName} {fields : List CtorField}
    (entry : listCtors[i]? = some (k, fields)) :
    CTyped objectAppend (laterCtx listN twoLists (assocAt (.var 2) (.var 1) (.var 0)) k fields)
      (appendAssocBody k fields) (laterResult twoLists (assocAt (.var 2) (.var 1) (.var 0)) k fields) := by
  match i, entry with
  | 0, entry =>
    obtain ⟨rfl, rfl⟩ : nilN = k ∧ ([] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    exact assocBase_typed
  | 1, entry =>
    obtain ⟨rfl, rfl⟩ :
        consN = k ∧ ([.closed (.const numN), .recursive] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    exact assocStep_typed
  | i + 2, entry => exact nomatch entry

/-- **Associativity is admissible over the package with the lists and the append.** -/
theorem appendAssocDef_admissibleA : appendAssocDef.Admissible objectAppend where
  new := by decide
  typeFormed := ⟨_, LevelTower.IsUniverse.sort _, assocType_typed⟩
  family := ⟨_, LevelTower.IsUniverse.sort _, assocFamily_typed⟩
  formed := appendAssocDef_formed
  resultType := appendAssocDef_resultType
  bodies := appendAssocDef_bodies

/-- The package with the append is contained in the package of the lists, the append and
`append-nil`. -/
theorem append_sub_program : ChurchRulesSub objectAppend objectProgram :=
  withDeclarations_sub objectChurch [.definition (.recursive appendDef), .datatype listDecl]
    [.definition (.recursive appendNilDef)]

/-- The lists, the append, `append-nil`, and associativity. -/
abbrev assocStage : List (Declaration Tower.Head) :=
  .definition (.recursive appendAssocDef) :: listProgram

theorem assocStage_admissible : AdmissibleDeclarations objectChurch assocStage :=
  ⟨listProgram_admissible, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
    appendAssocDef_admissibleA.mono append_sub_program (by decide)⟩

/-! ### The plain reversal -/

/-- **The right sides of `rev`**: the empty list at the empty list; at a longer list the
hypothesis followed by the one-element list of the first number. -/
def revBody : (k : DeclName) → (fields : List CtorField) →
    CTm Tower.Head
      ((CTele.nil : CTele Tower.Head 1 1).endAt (fields.length + (recPositions fields).length))
  | _, [] => (cnil : CTm Tower.Head 0)
  | _, [.closed _, .recursive] => (cappend (.var 0) (ccons (.var 2) cnil) : CTm Tower.Head 3)
  | _, _ => .const .anonymous

/-- **The plain reversal as a declaration**, by structural recursion on the list. -/
def revDef : RecursiveDefinition Tower.Head where
  name := revN
  datatype := listDecl
  width := 1
  later := .nil
  result := clist
  body := revBody

/-- `rev nil ⟶ nil`. -/
def revNilEquation : DefiningEquation Tower.Head where
  arity := 0
  telescope := .nil
  left := .app (.const revN) cnil
  right := cnil

/-- `rev (cons a as) ⟶ append (rev as) (cons a nil)`, over a number and a list. -/
def revConsEquation : DefiningEquation Tower.Head where
  arity := 2
  telescope := .snoc (.snoc .nil cnum) clist
  left := .app (.const revN) (ccons (.var 1) (.var 0))
  right := cappend (.app (.const revN) (.var 0)) (ccons (.var 1) cnil)

/-- **The written equations of `rev` are its two equations of the source.** -/
theorem revDef_equations : revDef.equations = [revNilEquation, revConsEquation] := rfl

theorem revDef_formed {i : Nat} {k : DeclName} {fields : List CtorField}
    (entry : listCtors[i]? = some (k, fields)) :
    CCtxFormed objectAppend (laterCtx listN (CTele.nil : CTele Tower.Head 1 1) clist k fields) := by
  match i, entry with
  | 0, entry =>
    obtain ⟨rfl, rfl⟩ : nilN = k ∧ ([] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    exact .nil
  | 1, entry =>
    obtain ⟨rfl, rfl⟩ :
        consN = k ∧ ([.closed (.const numN), .recursive] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    have formed : CCtxFormed objectAppend (CCtx.snoc (.snoc (.snoc .nil cnum) clist) clist) :=
      .snoc (.snoc (.snoc .nil ⟨_, LevelTower.IsUniverse.sort _, ofListsAppend num_typed_one⟩)
          ⟨_, LevelTower.IsUniverse.sort _, ofListsAppend list_typed_one⟩)
        ⟨_, LevelTower.IsUniverse.sort _, ofListsAppend list_typed_one⟩
    exact formed
  | i + 2, entry => exact nomatch entry

theorem revDef_bodies {i : Nat} {k : DeclName} {fields : List CtorField}
    (entry : listCtors[i]? = some (k, fields)) :
    CTyped objectAppend (laterCtx listN (CTele.nil : CTele Tower.Head 1 1) clist k fields)
      (revBody k fields) (laterResult (CTele.nil : CTele Tower.Head 1 1) clist k fields) := by
  match i, entry with
  | 0, entry =>
    obtain ⟨rfl, rfl⟩ : nilN = k ∧ ([] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    have typed : CTyped objectAppend (.nil : CCtx Tower.Head 0) (cnil : CTm Tower.Head 0) clist :=
      ofListsAppend nil_typed
    exact typed
  | 1, entry =>
    obtain ⟨rfl, rfl⟩ :
        consN = k ∧ ([.closed (.const numN), .recursive] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    have typed : CTyped objectAppend (CCtx.snoc (.snoc (.snoc .nil cnum) clist) clist)
        (cappend (.var 0) (ccons (.var 2) cnil) : CTm Tower.Head 3) clist :=
      cappend_typed (.var 0) (ofListsAppend (cons_typed (.var 2) nil_typed))
    exact typed
  | i + 2, entry => exact nomatch entry

/-- **The plain reversal is admissible over the package with the lists and the append.** -/
theorem revDef_admissibleA : revDef.Admissible objectAppend where
  new := by decide
  typeFormed := ⟨_, LevelTower.IsUniverse.sort _, ofListsAppend listFn_typed_one⟩
  family := ⟨_, LevelTower.IsUniverse.sort _, ofListsAppend list_typed_one⟩
  formed := revDef_formed
  resultType := fun _ => ⟨_, LevelTower.IsUniverse.sort _, ofListsAppend list_typed_one⟩
  bodies := revDef_bodies

/-- The program so far and the plain reversal. -/
abbrev revStage : List (Declaration Tower.Head) := .definition (.recursive revDef) :: assocStage

theorem revStage_admissible : AdmissibleDeclarations objectChurch revStage :=
  ⟨assocStage_admissible,
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
    revDef_admissibleA.mono
      (append_sub_program.trans
        (withDeclarations_sub objectChurch listProgram [.definition (.recursive appendAssocDef)]))
      (by decide)⟩

/-! ### The accumulator reversal -/

/-- The program so far and the reversal with the list first. -/
abbrev firstStage : List (Declaration Tower.Head) :=
  .definition (.recursive revOntoFirstDef) :: revStage

theorem firstStage_admissible : AdmissibleDeclarations objectChurch firstStage :=
  ⟨revStage_admissible,
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))),
    revOntoFirstDef_admissible.mono
      (withDeclarations_sub objectChurch [.datatype listDecl]
        [.definition (.recursive revDef), .definition (.recursive appendAssocDef),
          .definition (.recursive appendNilDef), .definition (.recursive appendDef)])
      (by decide)⟩

/-- The reversal with the list first, in the package of the stage that declares it. -/
theorem revOntoFirst_typedFirst {n : Nat} {Γ : CCtx Tower.Head n} :
    CTyped (withDeclarations objectChurch firstStage) Γ (.const revOntoFirstN) (.pi clist clistFn) :=
  firstStage_admissible.definition_typed ConvRules.objectLevels
    (D := .recursive revOntoFirstDef) List.mem_cons_self

/-- A derivation of the package with the lists is one of every stage. -/
theorem liftLists {ds : List (Declaration Tower.Head)} (pre : List (Declaration Tower.Head))
    (same : ds = pre ++ [.datatype listDecl]) {s : CStatement Tower.Head}
    (derivation : CDerivable objectLists s) : CDerivable (withDeclarations objectChurch ds) s := by
  subst same
  exact derivation.mono (withDeclarations_sub objectChurch [.datatype listDecl] pre)

/-- The body of the authored reversal is a list, over an accumulator and a list. -/
theorem revOntoBody_typedFirst :
    CTyped (withDeclarations objectChurch firstStage) (CCtx.snoc (.snoc .nil clist) clist)
      (.app (.app (.const revOntoFirstN) (.var 0)) (.var 1) : CTm Tower.Head 2) clist :=
  .appElim (B := clist) (.appElim (B := clistFn) revOntoFirst_typedFirst (.var 0)) (.var 1)

/-- **The authored accumulator reversal is admissible** over the package with the form it
unfolds to. -/
theorem revOntoDef_admissible' : revOntoDef.Admissible (withDeclarations objectChurch firstStage) where
  new := by decide
  formed :=
    .snoc (.snoc .nil ⟨_, LevelTower.IsUniverse.sort _,
        liftLists [.definition (.recursive revOntoFirstDef), .definition (.recursive revDef),
          .definition (.recursive appendAssocDef), .definition (.recursive appendNilDef),
          .definition (.recursive appendDef)] rfl list_typed_one⟩)
      ⟨_, LevelTower.IsUniverse.sort _,
        liftLists [.definition (.recursive revOntoFirstDef), .definition (.recursive revDef),
          .definition (.recursive appendAssocDef), .definition (.recursive appendNilDef),
          .definition (.recursive appendDef)] rfl list_typed_one⟩
  resultType := ⟨_, LevelTower.IsUniverse.sort _,
    liftLists [.definition (.recursive revOntoFirstDef), .definition (.recursive revDef),
      .definition (.recursive appendAssocDef), .definition (.recursive appendNilDef),
      .definition (.recursive appendDef)] rfl list_typed_one⟩
  body := revOntoBody_typedFirst

/-- **The program of the two reversals**: the lists, the append and `append-nil`,
associativity, `rev`, and the accumulator reversal with the list first and as authored. -/
abbrev ontoStage : List (Declaration Tower.Head) :=
  .definition (.explicit revOntoDef) :: firstStage

/-- **The program of the two reversals is admissible.** -/
theorem ontoStage_admissible : AdmissibleDeclarations objectChurch ontoStage :=
  ⟨firstStage_admissible, revOntoDef_admissible'⟩

/-! ### Rules in every later package -/

variable {ds : List (Declaration Tower.Head)} {n : Nat} {Γ : CCtx Tower.Head n}

/-- The package of `ds`. -/
local notation "PD" => withDeclarations objectChurch ds

/-! The facts about `Extends` that are particular to this program are stated in the namespace
of `Extends` (`TypedEquality.Annotated.DeclarationLists`), so that they apply to an extension
`ext` as `ext.liftLists`, `ext.ontoList`. -/

section Lists

variable (ext : Extends objectChurch listProgram ds)
include ext

theorem _root_.Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Annotated.Extends.liftProgram
    {s : CStatement Tower.Head} (derivation : CDerivable objectProgram s) : CDerivable PD s :=
  derivation.mono ext.sub

theorem _root_.Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Annotated.Extends.liftAppend
    {s : CStatement Tower.Head} (derivation : CDerivable objectAppend s) : CDerivable PD s :=
  ext.liftProgram (ofAppend derivation)

theorem _root_.Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Annotated.Extends.liftLists
    {s : CStatement Tower.Head} (derivation : CDerivable objectLists s) : CDerivable PD s :=
  ext.liftAppend (ofListsAppend derivation)

theorem list_in : CTyped PD Γ clist cU0 := ext.liftLists list_typed

theorem nil_in : CTyped PD Γ cnil clist := ext.liftLists nil_typed

theorem consBefore_in {a : CTm Tower.Head n} (ha : CTyped PD Γ a cnum) :
    CTyped PD Γ (.app (.const consN) a) (.pi clist clist) :=
  .appElim (B := .pi clist clist) (ext.liftLists consConst_typed) ha

theorem cons_in {a as : CTm Tower.Head n} (ha : CTyped PD Γ a cnum) (has : CTyped PD Γ as clist) :
    CTyped PD Γ (ccons a as) clist :=
  .appElim (B := clist) (consBefore_in ext ha) has

theorem append_in : CTyped PD Γ (.const appendN) (.pi clist clistFn) := ext.liftAppend append_typed

theorem cappend_in {x y : CTm Tower.Head n} (hx : CTyped PD Γ x clist) (hy : CTyped PD Γ y clist) :
    CTyped PD Γ (cappend x y) clist :=
  .appElim (B := clist) (.appElim (B := clistFn) (append_in ext) hx) hy

/-- **The first equation of the append**, in every later package. -/
theorem append_nil_in {ys : CTm Tower.Head n} (hys : CTyped PD Γ ys clist) :
    CEqual PD Γ (cappend cnil ys) ys clist :=
  have typed : CSubstMor PD (CCtx.snoc .nil clist) Γ (fun _ : Fin 1 => ys) :=
    fun j => match j with
      | ⟨0, _⟩ => hys
  definition_equation_holds (ds := ds) (D := .recursive appendDef)
    (ext.mem (List.mem_cons_of_mem _ List.mem_cons_self)) (e := appendNilEquation)
    List.mem_cons_self (fun _ => ys) typed (cappend_in ext (nil_in ext) hys) hys

/-- **The second equation of the append**, in every later package. -/
theorem append_cons_in {a as ys : CTm Tower.Head n} (ha : CTyped PD Γ a cnum)
    (has : CTyped PD Γ as clist) (hys : CTyped PD Γ ys clist) :
    CEqual PD Γ (cappend (ccons a as) ys) (ccons a (cappend as ys)) clist :=
  have typed : CSubstMor PD (CCtx.snoc (.snoc (.snoc .nil cnum) clist) clist) Γ
      (fun i : Fin 3 => [ys, as, a].getD i.val a) :=
    fun j => match j with
      | ⟨0, _⟩ => hys
      | ⟨1, _⟩ => has
      | ⟨2, _⟩ => ha
  definition_equation_holds (ds := ds) (D := .recursive appendDef)
    (ext.mem (List.mem_cons_of_mem _ List.mem_cons_self)) (e := appendConsEquation)
    (List.mem_cons_of_mem _ List.mem_cons_self) (fun i => [ys, as, a].getD i.val a) typed
    (cappend_in ext (cons_in ext ha has) hys) (cons_in ext ha (cappend_in ext has hys))

theorem cappend_cong {x x' y y' : CTm Tower.Head n} (hx : CEqual PD Γ x x' clist)
    (hy : CEqual PD Γ y y' clist) : CEqual PD Γ (cappend x y) (cappend x' y') clist :=
  .appCong (B := clist) (.appCong (B := clistFn) (.refl (append_in ext)) hx) hy

theorem ccons_cong {a as as' : CTm Tower.Head n} (ha : CTyped PD Γ a cnum)
    (h : CEqual PD Γ as as' clist) : CEqual PD Γ (ccons a as) (ccons a as') clist :=
  .appCong (B := clist) (.refl (consBefore_in ext ha)) h

/-- The proof `append-nil`, in every later package. -/
theorem appendNil_in : CTyped PD Γ (.const appendNilN) (.pi clist (appendNilAt (.var 0))) :=
  ext.liftProgram appendNilDef_typed

/-- **Symmetry of identity proofs**, in every later package. -/
theorem sym_in {A x y p : CTm Tower.Head n} (hA : CTyped PD Γ A cU0) (hx : CTyped PD Γ x A)
    (hy : CTyped PD Γ y A) (hp : CTyped PD Γ p (.id A x y)) :
    CTyped PD Γ (symOf A x y p) (.id A y x) :=
  CTyped.substitute (ext.liftLists (ofObject symTerm_typed))
    (σ := fun i => [p, y, x, A].getD i.val A)
    (fun j => match j with
      | ⟨0, _⟩ => hp
      | ⟨1, _⟩ => hy
      | ⟨2, _⟩ => hx
      | ⟨3, _⟩ => hA)

/-- **Transitivity of identity proofs**, in every later package. -/
theorem trans_in {A x y z p q : CTm Tower.Head n} (hA : CTyped PD Γ A cU0)
    (hx : CTyped PD Γ x A) (hy : CTyped PD Γ y A) (hz : CTyped PD Γ z A)
    (hp : CTyped PD Γ p (.id A x y)) (hq : CTyped PD Γ q (.id A y z)) :
    CTyped PD Γ (transOf A x y z p q) (.id A x z) :=
  CTyped.substitute (ext.liftLists (ofObject transTerm_typed))
    (σ := fun i => [q, p, z, y, x, A].getD i.val A)
    (fun j => match j with
      | ⟨0, _⟩ => hq
      | ⟨1, _⟩ => hp
      | ⟨2, _⟩ => hz
      | ⟨3, _⟩ => hy
      | ⟨4, _⟩ => hx
      | ⟨5, _⟩ => hA)

end Lists

theorem _root_.Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Annotated.Extends.toList
    {post : List (Declaration Tower.Head)} (pre : List (Declaration Tower.Head))
    (same : post = pre ++ listProgram) (ext : Extends objectChurch post ds) :
    Extends objectChurch listProgram ds := by
  subst same
  exact (Extends.after pre listProgram).trans ext

section Assoc

variable (ext : Extends objectChurch assocStage ds)
include ext

/-- **Associativity has its type**, in every later package. -/
theorem assoc_in :
    CTyped PD Γ (.const appendAssocN)
      (.pi clist (.pi clist (.pi clist (assocAt (.var 2) (.var 1) (.var 0))))) :=
  (assocStage_admissible.definition_typed ConvRules.objectLevels
    (D := .recursive appendAssocDef) List.mem_cons_self).mono ext.sub

end Assoc

section Rev

variable (ext : Extends objectChurch revStage ds)
include ext

theorem _root_.Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Annotated.Extends.revList :
    Extends objectChurch listProgram ds :=
  ext.toList [.definition (.recursive revDef), .definition (.recursive appendAssocDef)] rfl

/-- **`rev` has its type**, in every later package. -/
theorem rev_in : CTyped PD Γ (.const revN) (.pi clist clist) :=
  (revStage_admissible.definition_typed ConvRules.objectLevels
    (D := .recursive revDef) List.mem_cons_self).mono ext.sub

theorem crev_in {l : CTm Tower.Head n} (hl : CTyped PD Γ l clist) : CTyped PD Γ (crev l) clist :=
  .appElim (B := clist) (rev_in ext) hl

/-- **The first equation of `rev`**, in every later package. -/
theorem rev_nil_in : CEqual PD Γ (crev cnil) cnil clist :=
  have typed : CSubstMor PD (CCtx.nil : CCtx Tower.Head 0) Γ (fun i => i.elim0) :=
    fun i => i.elim0
  definition_equation_holds (ds := ds) (D := .recursive revDef) (ext.mem List.mem_cons_self)
    (e := revNilEquation) List.mem_cons_self (fun i => i.elim0) typed
    (crev_in ext (nil_in ext.revList)) (nil_in ext.revList)

/-- **The second equation of `rev`**, in every later package. -/
theorem rev_cons_in {a as : CTm Tower.Head n} (ha : CTyped PD Γ a cnum)
    (has : CTyped PD Γ as clist) :
    CEqual PD Γ (crev (ccons a as)) (cappend (crev as) (ccons a cnil)) clist :=
  have typed : CSubstMor PD (CCtx.snoc (.snoc .nil cnum) clist) Γ
      (fun i : Fin 2 => [as, a].getD i.val a) :=
    fun j => match j with
      | ⟨0, _⟩ => has
      | ⟨1, _⟩ => ha
  definition_equation_holds (ds := ds) (D := .recursive revDef) (ext.mem List.mem_cons_self)
    (e := revConsEquation) (List.mem_cons_of_mem _ List.mem_cons_self)
    (fun i => [as, a].getD i.val a) typed (crev_in ext (cons_in ext.revList ha has))
    (cappend_in ext.revList (crev_in ext has) (cons_in ext.revList ha (nil_in ext.revList)))

theorem crev_cong {l l' : CTm Tower.Head n} (h : CEqual PD Γ l l' clist) :
    CEqual PD Γ (crev l) (crev l') clist :=
  .appCong (B := clist) (.refl (rev_in ext)) h

end Rev

section Onto

variable (ext : Extends objectChurch ontoStage ds)
include ext

theorem _root_.Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Annotated.Extends.ontoList :
    Extends objectChurch listProgram ds :=
  ext.toList [.definition (.explicit revOntoDef), .definition (.recursive revOntoFirstDef),
    .definition (.recursive revDef), .definition (.recursive appendAssocDef)] rfl

theorem _root_.Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Annotated.Extends.ontoRev :
    Extends objectChurch revStage ds :=
  (Extends.after [.definition (.explicit revOntoDef), .definition (.recursive revOntoFirstDef)]
    revStage).trans ext

theorem revOntoFirst_in : CTyped PD Γ (.const revOntoFirstN) (.pi clist clistFn) :=
  revOntoFirst_typedFirst.mono ((Extends.after [.definition (.explicit revOntoDef)] firstStage).trans ext).sub

/-- **The authored accumulator reversal has its type**, in every later package. -/
theorem revOnto_in : CTyped PD Γ (.const revOntoN) (.pi clist (.pi clist clist)) :=
  (ontoStage_admissible.definition_typed ConvRules.objectLevels
    (D := .explicit revOntoDef) List.mem_cons_self).mono ext.sub

theorem crevOnto_in {acc l : CTm Tower.Head n} (hacc : CTyped PD Γ acc clist)
    (hl : CTyped PD Γ l clist) : CTyped PD Γ (crevOnto acc l) clist :=
  .appElim (B := clist) (.appElim (B := .pi clist clist) (revOnto_in ext) hacc) hl

theorem crevOntoFirst_in {l acc : CTm Tower.Head n} (hl : CTyped PD Γ l clist)
    (hacc : CTyped PD Γ acc clist) : CTyped PD Γ (crevOntoFirst l acc) clist :=
  .appElim (B := clist) (.appElim (B := clistFn) (revOntoFirst_in ext) hl) hacc

/-- The authored reversal unfolds to the form with the list first. -/
theorem revOnto_unfold_in {acc l : CTm Tower.Head n} (hacc : CTyped PD Γ acc clist)
    (hl : CTyped PD Γ l clist) : CEqual PD Γ (crevOnto acc l) (crevOntoFirst l acc) clist :=
  have typed : CSubstMor PD (CCtx.snoc (.snoc .nil clist) clist) Γ
      (fun i : Fin 2 => [l, acc].getD i.val acc) :=
    fun j => match j with
      | ⟨0, _⟩ => hl
      | ⟨1, _⟩ => hacc
  definition_equation_holds (ds := ds) (D := .explicit revOntoDef) (ext.mem List.mem_cons_self)
    (e := revOntoEquation) List.mem_cons_self (fun i => [l, acc].getD i.val acc) typed
    (crevOnto_in ext hacc hl) (crevOntoFirst_in ext hl hacc)

theorem revOntoFirst_nil_in {acc : CTm Tower.Head n} (hacc : CTyped PD Γ acc clist) :
    CEqual PD Γ (crevOntoFirst cnil acc) acc clist :=
  have typed : CSubstMor PD (CCtx.snoc .nil clist) Γ (fun _ : Fin 1 => acc) :=
    fun j => match j with
      | ⟨0, _⟩ => hacc
  definition_equation_holds (ds := ds) (D := .recursive revOntoFirstDef)
    (ext.mem (List.mem_cons_of_mem _ List.mem_cons_self)) (e := revOntoFirstNilEquation)
    List.mem_cons_self (fun _ => acc) typed
    (crevOntoFirst_in ext (nil_in ext.ontoList) hacc) hacc

theorem revOntoFirst_cons_in {x xs acc : CTm Tower.Head n} (hx : CTyped PD Γ x cnum)
    (hxs : CTyped PD Γ xs clist) (hacc : CTyped PD Γ acc clist) :
    CEqual PD Γ (crevOntoFirst (ccons x xs) acc) (crevOntoFirst xs (ccons x acc)) clist :=
  have typed : CSubstMor PD (CCtx.snoc (.snoc (.snoc .nil cnum) clist) clist) Γ
      (fun i : Fin 3 => [acc, xs, x].getD i.val x) :=
    fun j => match j with
      | ⟨0, _⟩ => hacc
      | ⟨1, _⟩ => hxs
      | ⟨2, _⟩ => hx
  definition_equation_holds (ds := ds) (D := .recursive revOntoFirstDef)
    (ext.mem (List.mem_cons_of_mem _ List.mem_cons_self)) (e := revOntoFirstConsEquation)
    (List.mem_cons_of_mem _ List.mem_cons_self) (fun i => [acc, xs, x].getD i.val x) typed
    (crevOntoFirst_in ext (cons_in ext.ontoList hx hxs) hacc)
    (crevOntoFirst_in ext hxs (cons_in ext.ontoList hx hacc))

/-- **The first authored equation of `rev-onto`**, in every later package. -/
theorem revOnto_nil_in {acc : CTm Tower.Head n} (hacc : CTyped PD Γ acc clist) :
    CEqual PD Γ (crevOnto acc cnil) acc clist :=
  .trans (revOnto_unfold_in ext hacc (nil_in ext.ontoList)) (revOntoFirst_nil_in ext hacc)

/-- **The second authored equation of `rev-onto`**, in every later package. -/
theorem revOnto_cons_in {acc x xs : CTm Tower.Head n} (hacc : CTyped PD Γ acc clist)
    (hx : CTyped PD Γ x cnum) (hxs : CTyped PD Γ xs clist) :
    CEqual PD Γ (crevOnto acc (ccons x xs)) (crevOnto (ccons x acc) xs) clist :=
  .trans (revOnto_unfold_in ext hacc (cons_in ext.ontoList hx hxs))
    (.trans (revOntoFirst_cons_in ext hx hxs hacc)
      (.symm (revOnto_unfold_in ext (cons_in ext.ontoList hx hacc) hxs)))

theorem crevOnto_cong {acc acc' l l' : CTm Tower.Head n} (hacc : CEqual PD Γ acc acc' clist)
    (hl : CEqual PD Γ l l' clist) : CEqual PD Γ (crevOnto acc l) (crevOnto acc' l') clist :=
  .appCong (B := clist) (.appCong (B := .pi clist clist) (.refl (revOnto_in ext)) hacc) hl

end Onto

/-! ### The lemma, by induction -/

/-- The later argument of the lemma: the accumulator. -/
abbrev accumulatorLater : CTele Tower.Head 1 2 := .cons clist .nil

/-- The step of the lemma over its context: the hypothesis at the longer accumulator, then
associativity read backwards. -/
abbrev revOntoAppendStep : CTm Tower.Head 4 :=
  transOf clist (crevOnto (ccons (.var 3) (.var 0)) (.var 2))
    (cappend (crev (.var 2)) (ccons (.var 3) (.var 0)))
    (cappend (cappend (crev (.var 2)) (ccons (.var 3) cnil)) (.var 0))
    (.app (.var 1) (ccons (.var 3) (.var 0)))
    (symOf clist (cappend (cappend (crev (.var 2)) (ccons (.var 3) cnil)) (.var 0))
      (cappend (crev (.var 2)) (ccons (.var 3) (.var 0)))
      (.app (.app (.app (.const appendAssocN) (crev (.var 2))) (ccons (.var 3) cnil)) (.var 0)))

/-- **The right sides of the lemma**: reflexivity at the empty list; at a longer list the
hypothesis at the longer accumulator, joined to associativity. -/
def revOntoAppendBody : (k : DeclName) → (fields : List CtorField) →
    CTm Tower.Head (accumulatorLater.endAt (fields.length + (recPositions fields).length))
  | _, [] => (.refl (.var 0) : CTm Tower.Head 1)
  | _, [.closed _, .recursive] => revOntoAppendStep
  | _, _ => .const .anonymous

/-- **The lemma as a declaration**: a proof by structural recursion on the list, with the
accumulator as a later argument that the hypothesis is used at, of type
`Π (l acc : list). Id list (rev-onto acc l) (append (rev l) acc)`. -/
def revOntoAppendDef : RecursiveDefinition Tower.Head where
  name := revOntoAppendN
  datatype := listDecl
  width := 2
  later := accumulatorLater
  result := revOntoAppendAt (.var 1) (.var 0)
  body := revOntoAppendBody

/-- The package of the program of the two reversals. -/
local notation "PO" => withDeclarations objectChurch ontoStage

theorem extOnto : Extends objectChurch ontoStage ontoStage := Extends.refl _

theorem revOntoAppendAt_in {m : Nat} {Δ : CCtx Tower.Head m} {l acc : CTm Tower.Head m}
    (hl : CTyped PO Δ l clist) (hacc : CTyped PO Δ acc clist) :
    CTyped PO Δ (revOntoAppendAt l acc) cU0 :=
  .idForm (list_in extOnto.ontoList) (LevelTower.IsUniverse.sort _) (crevOnto_in extOnto hacc hl)
    (cappend_in extOnto.ontoList (crev_in extOnto.ontoRev hl) hacc)

/-- A dependent function type between types of the lowest universe, in the package of the
program. -/
theorem piU0O {m : Nat} {Δ : CCtx Tower.Head m} {A : CTm Tower.Head m} {B : CTm Tower.Head (m + 1)}
    (domain : CTyped PO Δ A cU0) (codomain : CTyped PO (.snoc Δ A) B cU0) :
    CTyped PO Δ (.pi A B) cU0 :=
  CDerivable.cumul (.piForm domain (.sort _) codomain (.sort _) (.sorts _ _))
    (fun valuation => by simp [LevelExpr.eval])

theorem revOntoAppendFamily_typed {m : Nat} {Δ : CCtx Tower.Head m} :
    CTyped PO (.snoc Δ clist) (.pi clist (revOntoAppendAt (.var 1) (.var 0))) cU0 :=
  piU0O (list_in extOnto.ontoList) (revOntoAppendAt_in (.var 1) (.var 0))

/-- The context of the step of the lemma: a number, a list, the hypothesis, an accumulator. -/
abbrev lemmaStepCtx : CCtx Tower.Head 4 :=
  .snoc (.snoc (.snoc (.snoc .nil cnum) clist) (.pi clist (revOntoAppendAt (.var 1) (.var 0)))) clist

theorem lemmaStepCtx_formed : CCtxFormed PO lemmaStepCtx :=
  .snoc (.snoc (.snoc (.snoc .nil ⟨_, LevelTower.IsUniverse.sort _,
      extOnto.ontoList.liftLists (ofObject cnum_typed)⟩)
      ⟨_, LevelTower.IsUniverse.sort _, list_in extOnto.ontoList⟩)
      ⟨_, LevelTower.IsUniverse.sort _, revOntoAppendFamily_typed⟩)
    ⟨_, LevelTower.IsUniverse.sort _, list_in extOnto.ontoList⟩

/-- **The base of the lemma**: at the empty list both sides compute to the accumulator. -/
theorem revOntoAppendBase_typed :
    CTyped PO (CCtx.snoc .nil clist) (.refl (.var 0) : CTm Tower.Head 1)
      (revOntoAppendAt cnil (.var 0)) := by
  have acc : CTyped PO (CCtx.snoc .nil clist) (.var 0 : CTm Tower.Head 1) clist := .var 0
  have computed : CEqual PO (CCtx.snoc .nil clist) (revOntoAppendAt cnil (.var 0))
      (.id clist (.var 0) (.var 0)) cU0 :=
    .idCong (.refl (list_in extOnto.ontoList)) (LevelTower.IsUniverse.sort _)
      (revOnto_nil_in extOnto acc)
      (.trans (cappend_cong extOnto.ontoList (rev_nil_in extOnto.ontoRev) (.refl acc))
        (append_nil_in extOnto.ontoList acc))
  exact .conv (.reflIntro acc) (.symm computed) (LevelTower.IsUniverse.sort _)

/-- **The step of the lemma**: the longer list reversed onto the accumulator is its rest
reversed onto the longer accumulator, which the hypothesis relates to the reversal of the rest
followed by the longer accumulator; associativity, read backwards, brings it to the reversal
of the longer list followed by the accumulator. -/
theorem revOntoAppendStep_typed :
    CTyped PO lemmaStepCtx revOntoAppendStep (revOntoAppendAt (ccons (.var 3) (.var 2)) (.var 0)) := by
  have hL := extOnto.ontoList
  have hR := extOnto.ontoRev
  have x : CTyped PO lemmaStepCtx (.var 3) cnum := .var 3
  have xs : CTyped PO lemmaStepCtx (.var 2) clist := .var 2
  have acc : CTyped PO lemmaStepCtx (.var 0) clist := .var 0
  have longer : CTyped PO lemmaStepCtx (ccons (.var 3) (.var 0)) clist := cons_in hL x acc
  have one : CTyped PO lemmaStepCtx (ccons (.var 3) cnil) clist := cons_in hL x (nil_in hL)
  have revRest : CTyped PO lemmaStepCtx (crev (.var 2)) clist := crev_in hR xs
  have hypothesis : CTyped PO lemmaStepCtx (.app (.var 1) (ccons (.var 3) (.var 0)))
      (.id clist (crevOnto (ccons (.var 3) (.var 0)) (.var 2))
        (cappend (crev (.var 2)) (ccons (.var 3) (.var 0)))) :=
    .appElim (.var 1) longer
  have associated : CTyped PO lemmaStepCtx
      (.app (.app (.app (.const appendAssocN) (crev (.var 2))) (ccons (.var 3) cnil)) (.var 0))
      (assocAt (crev (.var 2)) (ccons (.var 3) cnil) (.var 0)) :=
    .appElim (.appElim (.appElim (assoc_in (Extends.after
      [.definition (.explicit revOntoDef), .definition (.recursive revOntoFirstDef),
        .definition (.recursive revDef)] assocStage)) revRest) one) acc
  have short : CEqual PO lemmaStepCtx (cappend (ccons (.var 3) cnil) (.var 0))
      (ccons (.var 3) (.var 0)) clist :=
    .trans (append_cons_in hL x (nil_in hL) acc) (ccons_cong hL x (append_nil_in hL acc))
  have associated' : CTyped PO lemmaStepCtx
      (.app (.app (.app (.const appendAssocN) (crev (.var 2))) (ccons (.var 3) cnil)) (.var 0))
      (.id clist (cappend (cappend (crev (.var 2)) (ccons (.var 3) cnil)) (.var 0))
        (cappend (crev (.var 2)) (ccons (.var 3) (.var 0)))) :=
    .conv associated
      (.idCong (.refl (list_in hL)) (LevelTower.IsUniverse.sort _)
        (.refl (cappend_in hL (cappend_in hL revRest one) acc))
        (cappend_cong hL (.refl revRest) short))
      (LevelTower.IsUniverse.sort _)
  have backwards := sym_in hL (list_in hL) (cappend_in hL (cappend_in hL revRest one) acc)
    (cappend_in hL revRest longer) associated'
  have joined := trans_in hL (list_in hL) (crevOnto_in extOnto longer xs)
    (cappend_in hL revRest longer) (cappend_in hL (cappend_in hL revRest one) acc)
    hypothesis backwards
  have computed : CEqual PO lemmaStepCtx (revOntoAppendAt (ccons (.var 3) (.var 2)) (.var 0))
      (.id clist (crevOnto (ccons (.var 3) (.var 0)) (.var 2))
        (cappend (cappend (crev (.var 2)) (ccons (.var 3) cnil)) (.var 0))) cU0 :=
    .idCong (.refl (list_in hL)) (LevelTower.IsUniverse.sort _) (revOnto_cons_in extOnto acc x xs)
      (cappend_cong hL (rev_cons_in hR x xs) (.refl acc))
  exact .conv joined (.symm computed) (LevelTower.IsUniverse.sort _)

theorem revOntoAppendDef_formed {i : Nat} {k : DeclName} {fields : List CtorField}
    (entry : listCtors[i]? = some (k, fields)) :
    CCtxFormed PO
      (laterCtx listN accumulatorLater (revOntoAppendAt (.var 1) (.var 0)) k fields) := by
  match i, entry with
  | 0, entry =>
    obtain ⟨rfl, rfl⟩ : nilN = k ∧ ([] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    have formed : CCtxFormed PO (CCtx.snoc .nil clist) :=
      .snoc .nil ⟨_, LevelTower.IsUniverse.sort _, list_in extOnto.ontoList⟩
    exact formed
  | 1, entry =>
    obtain ⟨rfl, rfl⟩ :
        consN = k ∧ ([.closed (.const numN), .recursive] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    exact lemmaStepCtx_formed
  | i + 2, entry => exact nomatch entry

theorem revOntoAppendDef_resultType {i : Nat} {k : DeclName} {fields : List CtorField}
    (entry : listCtors[i]? = some (k, fields)) :
    CIsType PO (laterCtx listN accumulatorLater (revOntoAppendAt (.var 1) (.var 0)) k fields)
      (laterResult accumulatorLater (revOntoAppendAt (.var 1) (.var 0)) k fields) := by
  match i, entry with
  | 0, entry =>
    obtain ⟨rfl, rfl⟩ : nilN = k ∧ ([] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    have typed : CTyped PO (CCtx.snoc .nil clist) (revOntoAppendAt cnil (.var 0) : CTm Tower.Head 1)
        cU0 := revOntoAppendAt_in (nil_in extOnto.ontoList) (.var 0)
    exact ⟨_, LevelTower.IsUniverse.sort _, typed⟩
  | 1, entry =>
    obtain ⟨rfl, rfl⟩ :
        consN = k ∧ ([.closed (.const numN), .recursive] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    have typed : CTyped PO lemmaStepCtx (revOntoAppendAt (ccons (.var 3) (.var 2)) (.var 0)) cU0 :=
      revOntoAppendAt_in (cons_in extOnto.ontoList (.var 3) (.var 2)) (.var 0)
    exact ⟨_, LevelTower.IsUniverse.sort _, typed⟩
  | i + 2, entry => exact nomatch entry

theorem revOntoAppendDef_bodies {i : Nat} {k : DeclName} {fields : List CtorField}
    (entry : listCtors[i]? = some (k, fields)) :
    CTyped PO (laterCtx listN accumulatorLater (revOntoAppendAt (.var 1) (.var 0)) k fields)
      (revOntoAppendBody k fields)
      (laterResult accumulatorLater (revOntoAppendAt (.var 1) (.var 0)) k fields) := by
  match i, entry with
  | 0, entry =>
    obtain ⟨rfl, rfl⟩ : nilN = k ∧ ([] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    exact revOntoAppendBase_typed
  | 1, entry =>
    obtain ⟨rfl, rfl⟩ :
        consN = k ∧ ([.closed (.const numN), .recursive] : List CtorField) = fields :=
      Prod.mk.inj (Option.some.inj entry)
    exact revOntoAppendStep_typed
  | i + 2, entry => exact nomatch entry

/-- **The lemma is admissible** over the package of the program of the two reversals. -/
theorem revOntoAppendDef_admissible : revOntoAppendDef.Admissible PO where
  new := by decide
  typeFormed := ⟨_, LevelTower.IsUniverse.sort _,
    piU0O (list_in extOnto.ontoList) revOntoAppendFamily_typed⟩
  family := ⟨_, LevelTower.IsUniverse.sort _, revOntoAppendFamily_typed⟩
  formed := revOntoAppendDef_formed
  resultType := revOntoAppendDef_resultType
  bodies := revOntoAppendDef_bodies

/-- The program of the two reversals and the lemma. -/
abbrev lemmaStage : List (Declaration Tower.Head) :=
  .definition (.recursive revOntoAppendDef) :: ontoStage

theorem lemmaStage_admissible : AdmissibleDeclarations objectChurch lemmaStage :=
  ⟨ontoStage_admissible,
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))),
    revOntoAppendDef_admissible⟩

/-! ### The theorem -/

/-- The body of the theorem over a list `l`: the lemma at `l` and the empty accumulator, then
`append-nil` at the reversal of `l`, joined and read backwards. -/
abbrev revIsRevOntoBody : CTm Tower.Head 1 :=
  symOf clist (crevOnto cnil (.var 0)) (crev (.var 0))
    (transOf clist (crevOnto cnil (.var 0)) (cappend (crev (.var 0)) cnil) (crev (.var 0))
      (.app (.app (.const revOntoAppendN) (.var 0)) cnil) (.app (.const appendNilN) (crev (.var 0))))

/-- **The theorem as a declaration**: an explicit definition over a list, of type
`Π (l : list). Id list (rev l) (rev-onto nil l)`. -/
def revIsRevOntoDef : ExplicitDefinition Tower.Head where
  name := revIsRevOntoN
  width := 1
  arguments := .cons clist .nil
  result := revIsRevOntoAt (.var 0)
  body := revIsRevOntoBody

/-- The package of the program and the lemma. -/
local notation "PL" => withDeclarations objectChurch lemmaStage

theorem extLemma : Extends objectChurch ontoStage lemmaStage :=
  Extends.after [.definition (.recursive revOntoAppendDef)] ontoStage

theorem revOntoAppend_inLemma {m : Nat} {Δ : CCtx Tower.Head m} :
    CTyped PL Δ (.const revOntoAppendN) (.pi clist (.pi clist (revOntoAppendAt (.var 1) (.var 0)))) :=
  lemmaStage_admissible.definition_typed ConvRules.objectLevels
    (D := .recursive revOntoAppendDef) List.mem_cons_self

theorem revIsRevOntoBody_typed :
    CTyped PL (CCtx.snoc .nil clist) revIsRevOntoBody (revIsRevOntoAt (.var 0)) := by
  have hL := extLemma.ontoList
  have hR := extLemma.ontoRev
  have l : CTyped PL (CCtx.snoc .nil clist) (.var 0 : CTm Tower.Head 1) clist := .var 0
  have lemmaAt : CTyped PL (CCtx.snoc .nil clist) (.app (.app (.const revOntoAppendN) (.var 0)) cnil)
      (revOntoAppendAt (.var 0) cnil) :=
    .appElim (.appElim revOntoAppend_inLemma l) (nil_in hL)
  have nilAt : CTyped PL (CCtx.snoc .nil clist) (.app (.const appendNilN) (crev (.var 0)))
      (appendNilAt (crev (.var 0))) :=
    .appElim (B := appendNilAt (.var 0)) (appendNil_in hL) (crev_in hR l)
  have joined := trans_in hL (list_in hL) (crevOnto_in extLemma (nil_in hL) l)
    (cappend_in hL (crev_in hR l) (nil_in hL)) (crev_in hR l) lemmaAt nilAt
  exact sym_in hL (list_in hL) (crevOnto_in extLemma (nil_in hL) l) (crev_in hR l) joined

theorem revIsRevOntoAt_typedLemma :
    CTyped PL (CCtx.snoc .nil clist) (revIsRevOntoAt (.var 0) : CTm Tower.Head 1) cU0 :=
  .idForm (list_in extLemma.ontoList) (LevelTower.IsUniverse.sort _)
    (crev_in extLemma.ontoRev (.var 0)) (crevOnto_in extLemma (nil_in extLemma.ontoList) (.var 0))

/-- **The theorem is admissible** over the package of the program and the lemma. -/
theorem revIsRevOntoDef_admissible : revIsRevOntoDef.Admissible PL where
  new := by decide
  formed := .snoc .nil ⟨_, LevelTower.IsUniverse.sort _, list_in extLemma.ontoList⟩
  resultType := ⟨_, LevelTower.IsUniverse.sort _, revIsRevOntoAt_typedLemma⟩
  body := revIsRevOntoBody_typed

/-- **The program with its proofs**: the lists, the append and `append-nil`, associativity,
`rev`, the accumulator reversal with the list first and as authored, the lemma, and the
theorem. The head of the list is the declaration added last. -/
abbrev reversalProgram : List (Declaration Tower.Head) :=
  .definition (.explicit revIsRevOntoDef) :: lemmaStage

/-- **The program is an admissible list of declarations.** -/
theorem reversalProgram_admissible : AdmissibleDeclarations objectChurch reversalProgram :=
  ⟨lemmaStage_admissible, revIsRevOntoDef_admissible⟩

/-- Negative example: **the theorem before the lemma is not admissible.** Its body uses the
lemma, which the package without it does not declare. -/
theorem theorem_before_lemma_not_admissible :
    ¬ AdmissibleDeclarations objectChurch (.definition (.explicit revIsRevOntoDef) :: ontoStage) := by
  rintro ⟨-, stage⟩
  exact CDerivable.consts_declared stage.body revOntoAppendN (by decide) (by decide)

/-- **The object package with the program.** -/
abbrev objectReversal := withDeclarations objectChurch reversalProgram

/-- **The object package with the program has a set model**, relative to
`CofinalInaccessibles`. -/
theorem objectReversal_model (h : CofinalInaccessibles.{u}) :
    SetModel (objHeads h) (objectDeclarationsConsts h reversalProgram) objectReversal :=
  objectDeclarations_model h reversalProgram_admissible

/-- **Consistency**: no closed term of the package with the program has the type
`Π (X : U₀). X`. -/
theorem objectReversal_consistent (h : CofinalInaccessibles.{u}) (t : CTm Tower.Head 0) :
    ¬ CTyped objectReversal .nil t emptyType :=
  objectDeclarations_consistent h reversalProgram_admissible t

/-- The program is an extension of the program of the two reversals. -/
theorem extReversal : Extends objectChurch ontoStage reversalProgram :=
  Extends.after [.definition (.explicit revIsRevOntoDef), .definition (.recursive revOntoAppendDef)]
    ontoStage

/-! ## Typing: what runs is typed, and the theorem as a typed proof -/

/-- The package of the program. -/
local notation "PR" => objectReversal

/-- **The theorem as a typed proof**: the constant `rev-is-rev-onto` is a closed term of
`Π (l : list). Id list (rev l) (rev-onto nil l)`. -/
theorem revIsRevOnto_typed {m : Nat} {Δ : CCtx Tower.Head m} :
    CTyped PR Δ (.const revIsRevOntoN) (.pi clist (revIsRevOntoAt (.var 0))) :=
  reversalProgram_admissible.definition_typed ConvRules.objectLevels
    (D := .explicit revIsRevOntoDef) List.mem_cons_self

/-- **The lemma as a typed proof**: the constant `rev-onto-append` is a closed term of
`Π (l acc : list). Id list (rev-onto acc l) (append (rev l) acc)`. -/
theorem revOntoAppend_typed {m : Nat} {Δ : CCtx Tower.Head m} :
    CTyped PR Δ (.const revOntoAppendN)
      (.pi clist (.pi clist (revOntoAppendAt (.var 1) (.var 0)))) :=
  revOntoAppend_inLemma.mono
    (Extends.after [.definition (.explicit revIsRevOntoDef)] lemmaStage).sub

/-- **Associativity as a typed proof.** -/
theorem appendAssoc_typed {m : Nat} {Δ : CCtx Tower.Head m} :
    CTyped PR Δ (.const appendAssocN)
      (.pi clist (.pi clist (.pi clist (assocAt (.var 2) (.var 1) (.var 0))))) :=
  assoc_in (Extends.after [.definition (.explicit revIsRevOntoDef),
    .definition (.recursive revOntoAppendDef), .definition (.explicit revOntoDef),
    .definition (.recursive revOntoFirstDef), .definition (.recursive revDef)] assocStage)

end Declarations

/-! ## Typing the running expressions -/

section Typing

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
open CodeModel
/-- **The term of a list expression**, in the package of the program. -/
def RevExpr.toTerm : RevExpr → CTm Tower.Head 0
  | .nil => cnil
  | .cons head tail => ccons head.toTerm tail.toTerm
  | .append left right => cappend left.toTerm right.toTerm
  | .rev list => crev list.toTerm
  | .revOnto acc list => crevOnto acc.toTerm list.toTerm

/-- A numeral's term is a number in the object package. -/
theorem numTerm_typedObject : ∀ number : NumExpr, CTyped objectChurch .nil number.toTerm cnum
  | .zero => czero_typed
  | .suc number => csuc_typed (numTerm_typedObject number)

section Generic

variable {ds : List (Declaration Tower.Head)} (ext : Extends objectChurch ontoStage ds)
include ext

/-- A numeral's term is a number in every package of the program. -/
theorem numTerm_typedIn (number : NumExpr) :
    CTyped (withDeclarations objectChurch ds) .nil number.toTerm cnum :=
  ext.ontoList.liftLists (ofObject (numTerm_typedObject number))

/-- A list expression's term is a list in every package of the program. -/
theorem RevExpr.toTerm_typedIn (e : RevExpr) :
    CTyped (withDeclarations objectChurch ds) .nil e.toTerm clist := by
  induction e with
  | nil => exact nil_in ext.ontoList
  | cons head tail ih => exact cons_in ext.ontoList (numTerm_typedIn ext head) ih
  | append left right ihl ihr => exact cappend_in ext.ontoList ihl ihr
  | rev list ih => exact crev_in ext.ontoRev ih
  | revOnto acc list ihacc ihl => exact crevOnto_in ext ihacc ihl

/-- **What runs is typed**, in every package of the program: a step of the source is a
derivable typed equality of the terms. The six equations are equations of the judgment (the
two of `rev-onto` through its form with the list first), and a step inside is a congruence. -/
theorem RevExpr.Step.typedEqualIn {e e' : RevExpr} (step : RevExpr.Step e e') :
    CEqual (withDeclarations objectChurch ds) .nil e.toTerm e'.toTerm clist := by
  induction step with
  | appendNil right => exact append_nil_in ext.ontoList (right.toTerm_typedIn ext)
  | appendCons head tail right =>
      exact append_cons_in ext.ontoList (numTerm_typedIn ext head) (tail.toTerm_typedIn ext)
        (right.toTerm_typedIn ext)
  | revNil => exact rev_nil_in ext.ontoRev
  | revCons head tail =>
      exact rev_cons_in ext.ontoRev (numTerm_typedIn ext head) (tail.toTerm_typedIn ext)
  | revOntoNil acc => exact revOnto_nil_in ext (acc.toTerm_typedIn ext)
  | revOntoCons acc head tail =>
      exact revOnto_cons_in ext (acc.toTerm_typedIn ext) (numTerm_typedIn ext head)
        (tail.toTerm_typedIn ext)
  | @consTail head _ _ _ inside => exact ccons_cong ext.ontoList (numTerm_typedIn ext head) inside
  | @appendLeft _ _ right _ inside =>
      exact cappend_cong ext.ontoList inside (.refl (right.toTerm_typedIn ext))
  | @appendRight left _ _ _ inside =>
      exact cappend_cong ext.ontoList (.refl (left.toTerm_typedIn ext)) inside
  | revArg _ inside => exact crev_cong ext.ontoRev inside
  | @revOntoAcc _ _ list _ inside =>
      exact crevOnto_cong ext inside (.refl (list.toTerm_typedIn ext))
  | @revOntoList acc _ _ _ inside =>
      exact crevOnto_cong ext (.refl (acc.toTerm_typedIn ext)) inside

/-- A run of any number of steps is typed. -/
theorem RevExpr.typedEqualIn_of_steps {e e' : RevExpr}
    (steps : Relation.ReflTransGen RevExpr.Step e e') :
    CEqual (withDeclarations objectChurch ds) .nil e.toTerm e'.toTerm clist := by
  induction steps with
  | refl => exact .refl (e.toTerm_typedIn ext)
  | tail _ step earlier => exact .trans earlier (step.typedEqualIn ext)

end Generic

/-- **Every term is typed**: a list expression's term is a list in the package of the
program. -/
theorem RevExpr.toTerm_typed (e : RevExpr) : CTyped objectReversal .nil e.toTerm clist :=
  e.toTerm_typedIn extReversal

/-- **What runs is typed**: a step of the source is a derivable typed equality of the terms
in the package of the program. -/
theorem RevExpr.Step.typedEqual {e e' : RevExpr} (step : RevExpr.Step e e') :
    CEqual objectReversal .nil e.toTerm e'.toTerm clist :=
  step.typedEqualIn extReversal

/-- A run of any number of steps is typed. -/
theorem RevExpr.typedEqual_of_steps {e e' : RevExpr}
    (steps : Relation.ReflTransGen RevExpr.Step e e') :
    CEqual objectReversal .nil e.toTerm e'.toTerm clist :=
  RevExpr.typedEqualIn_of_steps extReversal steps

/-- **At every closed list the two reversals are equal in the judgment**: both run to one
value, and every step is a typed equality. -/
theorem rev_typedEqual_revOnto (l : RevExpr) :
    CEqual objectReversal .nil (RevExpr.rev l).toTerm (RevExpr.revOnto .nil l).toTerm clist := by
  have toValue := RevExpr.typedEqual_of_steps (RevExpr.reaches_eval (.rev l))
  have fromValue := RevExpr.typedEqual_of_steps (RevExpr.reaches_eval (.revOnto .nil l))
  rw [RevExpr.eval_rev_eq_revOnto] at toValue
  exact .trans toValue (.symm fromValue)

/-- **The theorem as a typed proof, at a closed list**: the constant `rev-is-rev-onto`
applied to the term of `l` is a closed term of `Id list (rev l) (rev-onto nil l)`. -/
theorem revIsRevOnto_at (l : RevExpr) :
    CTyped objectReversal .nil (.app (.const revIsRevOntoN) l.toTerm) (revIsRevOntoAt l.toTerm) :=
  .appElim (B := revIsRevOntoAt (.var 0)) revIsRevOnto_typed l.toTerm_typed

/-- `rev` as a function, `λ l. rev l`. -/
abbrev revFn : CTm Tower.Head 0 := .lam clist (crev (.var 0))

/-- The accumulator reversal from the empty accumulator as a function,
`λ l. rev-onto nil l`. -/
abbrev revOntoNilFn : CTm Tower.Head 0 := .lam clist (crevOnto cnil (.var 0))

theorem listFn_inReversal : CTyped objectReversal .nil (.pi clist clist) cU1 :=
  extReversal.ontoList.liftLists listFn_typed_one

/-- `λ l. rev l` is a function from lists to lists. -/
theorem revFn_typed : CTyped objectReversal .nil revFn (.pi clist clist) :=
  .lamIntro (list_in extReversal.ontoList) (LevelTower.IsUniverse.sort _) listFn_inReversal
    (LevelTower.IsUniverse.sort _) (crev_in extReversal.ontoRev (.var 0))

/-- `λ l. rev-onto nil l` is a function from lists to lists. -/
theorem revOntoNilFn_typed : CTyped objectReversal .nil revOntoNilFn (.pi clist clist) :=
  .lamIntro (list_in extReversal.ontoList) (LevelTower.IsUniverse.sort _) listFn_inReversal
    (LevelTower.IsUniverse.sort _) (crevOnto_in extReversal (nil_in extReversal.ontoList) (.var 0))

/-- **The two functions agree at every closed list in the judgment**: applied to the term of
a closed list expression, `λ l. rev l` and `λ l. rev-onto nil l` are equal. -/
theorem revFn_app_typedEqual (l : RevExpr) :
    CEqual objectReversal .nil (.app revFn l.toTerm) (.app revOntoNilFn l.toTerm) clist :=
  .trans
    (.betaPi (A := clist) (B := clist) (body := crev (.var 0)) (a := l.toTerm) listFn_inReversal
      (LevelTower.IsUniverse.sort _) (crev_in extReversal.ontoRev (.var 0)) l.toTerm_typed)
    (.trans (rev_typedEqual_revOnto l)
      (.symm (.betaPi (A := clist) (B := clist) (body := crevOnto cnil (.var 0)) (a := l.toTerm)
        listFn_inReversal (LevelTower.IsUniverse.sort _)
        (crevOnto_in extReversal (nil_in extReversal.ontoList) (.var 0)) l.toTerm_typed)))

/-- Positive example: the terms of `rev` at the list of zero, one and two and of the list of
two, one and zero are equal in the judgment. -/
example :
    CEqual objectReversal .nil (RevExpr.rev zeroOneTwo).toTerm
      (RevExpr.cons twoN (.cons oneN (.cons .zero .nil))).toTerm clist := by
  have run := RevExpr.typedEqual_of_steps (RevExpr.reaches_eval (.rev zeroOneTwo))
  exact run

end Typing

end Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Reverse
