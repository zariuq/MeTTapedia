import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedTerms.Build

/-!
# Bound names are display: alpha-equivalent terms are one stored node

People write binders with names: `λx. x`. The stored form has none. This module says what names
mean and proves that they do not reach the store.

* `NTerm Head N`: binding trees with names. A variable is a name; a field lists the names it binds
  (the last one innermost). A name that no enclosing field binds is **free**.
* `AlphaEq s t`: the two terms bind the same positions and agree on free names. It is defined by
  comparing the terms under two binder lists, the way HOL's `aconv` compares terms, without any
  translation.
* `toTree env t`: the nameless binding tree. A bound name becomes the index of its binder; a free
  name becomes a constant node (`Sum.inr x`).

Results:

* **Alpha-equivalence is equality of nameless trees** (`alphaEq_iff_toTree_eq`).
* **So alpha-equivalent terms are one reference in a canonical store** (`alphaEq_iff_same_ref`):
  encode the first, encode the second into the result, and compare the two references.

Examples (`Controls`): `λx. x` and `λy. y` are one node; `λx. λy. x` and `λx. λy. y` are not;
under shadowing, `λx. λx. x` is `λy. λz. z`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedTerms

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT

mutual

/-- Binding trees with names. -/
inductive NTerm (Head : Type) (N : Type) where
  | var (x : N)
  | node (head : Head) (fields : NFields Head N)

/-- Fields with the names they bind, the last one innermost. -/
inductive NFields (Head : Type) (N : Type) where
  | nil
  | cons (binders : List N) (term : NTerm Head N) (rest : NFields Head N)

end

variable {Head : Type} {N : Type} [DecidableEq N]

/-- The position of the innermost binder of `x` in a binder list (innermost first). -/
def position (x : N) : List N → Option ℕ
  | [] => none
  | y :: ys => if x = y then some 0 else (position x ys).map (· + 1)

mutual

/-- **The nameless tree**: a bound name becomes the index of its binder, a free name a constant. -/
def toTree (env : List N) : NTerm Head N → Term (Head ⊕ N)
  | .var x =>
      match position x env with
      | some i => .idx i
      | none => .node (.inr x) .nil
  | .node head fields => .node (.inl head) (toTreeFields env fields)

def toTreeFields (env : List N) : NFields Head N → Fields (Head ⊕ N)
  | .nil => .nil
  | .cons binders t rest =>
      .cons binders.length (toTree (binders.reverse ++ env) t) (toTreeFields env rest)

end

mutual

/-- Compare two named terms under two binder lists (innermost first). -/
def alphaAux [DecidableEq Head] (env env' : List N) : NTerm Head N → NTerm Head N → Bool
  | .var x, .var y =>
      match position x env, position y env' with
      | some i, some j => decide (i = j)
      | none, none => decide (x = y)
      | _, _ => false
  | .node head fields, .node head' fields' =>
      decide (head = head') && alphaFieldsAux env env' fields fields'
  | .var _, .node _ _ => false
  | .node _ _, .var _ => false

def alphaFieldsAux [DecidableEq Head] (env env' : List N) :
    NFields Head N → NFields Head N → Bool
  | .nil, .nil => true
  | .cons bs t rest, .cons bs' t' rest' =>
      decide (bs.length = bs'.length) && alphaAux (bs.reverse ++ env) (bs'.reverse ++ env') t t' &&
        alphaFieldsAux env env' rest rest'
  | .nil, .cons _ _ _ => false
  | .cons _ _ _, .nil => false

end

/-- **Alpha-equivalence** of closed-off named terms: compare under empty binder lists. -/
def AlphaEq [DecidableEq Head] (s t : NTerm Head N) : Prop := alphaAux [] [] s t = true

instance [DecidableEq Head] (s t : NTerm Head N) : Decidable (AlphaEq s t) :=
  inferInstanceAs (Decidable (_ = true))

mutual

theorem alphaAux_iff [DecidableEq Head] (env env' : List N) (s t : NTerm Head N) :
    alphaAux env env' s t = true ↔ toTree env s = toTree env' t := by
  cases s with
  | var x =>
      cases t with
      | var y =>
          simp only [alphaAux, toTree]
          cases hx : position x env <;> cases hy : position y env' <;>
            simp [Sum.inr.injEq]
      | node head fields =>
          simp only [alphaAux, toTree, Bool.false_eq_true, false_iff]
          cases position x env <;> simp
  | node head fields =>
      cases t with
      | var y =>
          simp only [alphaAux, toTree, Bool.false_eq_true, false_iff]
          cases position y env' <;> simp
      | node head' fields' =>
          simp only [alphaAux, toTree, Bool.and_eq_true, decide_eq_true_eq, Term.node.injEq,
            Sum.inl.injEq]
          rw [alphaFieldsAux_iff env env' fields fields']

theorem alphaFieldsAux_iff [DecidableEq Head] (env env' : List N) (f g : NFields Head N) :
    alphaFieldsAux env env' f g = true ↔ toTreeFields env f = toTreeFields env' g := by
  cases f with
  | nil =>
      cases g with
      | nil => simp [alphaFieldsAux, toTreeFields]
      | cons _ _ _ => simp [alphaFieldsAux, toTreeFields]
  | cons bs t rest =>
      cases g with
      | nil => simp [alphaFieldsAux, toTreeFields]
      | cons bs' t' rest' =>
          simp only [alphaFieldsAux, toTreeFields, Bool.and_eq_true, decide_eq_true_eq,
            Fields.cons.injEq]
          rw [alphaAux_iff (bs.reverse ++ env) (bs'.reverse ++ env') t t',
            alphaFieldsAux_iff env env' rest rest']
          tauto

end

/-- **Alpha-equivalence is equality of nameless trees.** -/
theorem alphaEq_iff_toTree_eq [DecidableEq Head] (s t : NTerm Head N) :
    AlphaEq s t ↔ toTree [] s = toTree [] t :=
  alphaAux_iff [] [] s t

/-- **Alpha-equivalent terms are one reference.** In a canonical store, encode `s`, then encode
`t` into the result: the two references are equal exactly when `s` and `t` are
alpha-equivalent. -/
theorem alphaEq_iff_same_ref [DecidableEq Head] {St : Store (Head ⊕ N)} (canon : Canonical St)
    (s t : NTerm Head N) :
    AlphaEq s t ↔
      (encode St (toTree [] s)).2 = (encode (encode St (toTree [] s)).1 (toTree [] t)).2 := by
  rw [alphaEq_iff_toTree_eq]
  exact encode_eq_iff canon _ _

/-! ## Controls -/

namespace NameControls

/-- One binder head and application. -/
inductive H where
  | lam
  | app
  deriving DecidableEq

abbrev T := NTerm H String

def lam (x : String) (b : T) : T := .node .lam (.cons [x] b .nil)

def app (f a : T) : T := .node .app (.cons [] f (.cons [] a .nil))

def v (x : String) : T := .var x

/-- Positive: `λx. x` and `λy. y` are one stored node. -/
theorem identity_one_node :
    (encode [] (toTree [] (lam "x" (v "x")))).2 =
      (encode (encode [] (toTree [] (lam "x" (v "x")))).1 (toTree [] (lam "y" (v "y")))).2 := by
  decide +kernel

/-- Negative: `λx. λy. x` and `λx. λy. y` are not alpha-equivalent. -/
theorem first_not_second : ¬ AlphaEq (lam "x" (lam "y" (v "x"))) (lam "x" (lam "y" (v "y"))) := by
  decide +kernel

/-- Positive, with shadowing: in `λx. λx. x` the variable is the inner binder, as in `λy. λz. z`. -/
theorem shadowing : AlphaEq (lam "x" (lam "x" (v "x"))) (lam "y" (lam "z" (v "z"))) := by
  decide +kernel

/-- Negative: free names are not renamed: `λx. f` and `λx. g` differ. -/
theorem free_names_matter : ¬ AlphaEq (lam "x" (v "f")) (lam "x" (v "g")) := by
  decide +kernel

end NameControls

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedTerms
