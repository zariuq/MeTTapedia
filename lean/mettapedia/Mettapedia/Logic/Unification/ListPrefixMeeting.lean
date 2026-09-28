import Mettapedia.Logic.LP.TotalUnification

/-!
# Prefix meeting for first-order list values

The native list matcher separates a list into its fixed prefix and an optional
rest.  Equal prefix positions become equations.  If only one prefix remains,
the other side must have an open rest, and that rest meets the remaining list.
An exhausted closed side contributes the empty list.

This module gives that decomposition its exact solution-set semantics using
the existing first-order LP substitution and unification kernel.  It does not
treat decomposition itself as a unifier.  The optional reference solver below
uses the already-proved total Martelli--Montanari algorithm after decomposition.
The native binding store, ownership and contextual matcher are separate
implementation obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Unification.ListPrefixMeeting

open Mettapedia.Logic.LP

/-- Empty lists are not atom leaves. -/
inductive Constant (Leaf : Type) where
  | atom : Leaf → Constant Leaf
  | nil : Constant Leaf
  deriving DecidableEq

/-- A list cell is not an expression, including a two-child expression. -/
inductive Function where
  | cons
  | expr (arity : Nat)
  deriving DecidableEq

abbrev signature (Leaf : Type) (Var : Type) : LPSignature where
  constants := Constant Leaf
  vars := Var
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Function
  functionArity
    | .cons => 2
    | .expr n => n

abbrev Tm (Leaf : Type) (Var : Type) := Term (signature Leaf Var)
abbrev Substitution (Leaf : Type) (Var : Type) := Subst (signature Leaf Var)

variable {Leaf : Type} {Var : Type}

def nil : Tm Leaf Var := .const .nil

def cons (head tail : Tm Leaf Var) : Tm Leaf Var :=
  .app .cons fun (i : Fin 2) => if i = 0 then head else tail

def expr (children : List (Tm Leaf Var)) : Tm Leaf Var :=
  .app (.expr children.length) children.get

@[simp] theorem cons_inj {a b c d : Tm Leaf Var} :
    cons a b = cons c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have e : (fun i : Fin 2 => if i = 0 then a else b) =
        (fun i : Fin 2 => if i = 0 then c else d) := by
      unfold cons at h
      injection h with e
    exact ⟨by simpa using congrFun e 0, by simpa using congrFun e 1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

@[simp] theorem nil_ne_cons (a b : Tm Leaf Var) : nil ≠ cons a b := by
  intro h
  cases h

@[simp] theorem cons_ne_nil (a b : Tm Leaf Var) : cons a b ≠ nil := by
  exact Ne.symm (nil_ne_cons a b)

@[simp] theorem nil_ne_expr (xs : List (Tm Leaf Var)) : nil ≠ expr xs := by
  intro h
  cases h

@[simp] theorem cons_ne_expr (a b : Tm Leaf Var) (xs : List (Tm Leaf Var)) :
    cons a b ≠ expr xs := by
  intro h
  unfold cons expr at h
  injection h with e
  cases e

@[simp] theorem apply_nil (θ : Substitution Leaf Var) : θ.applyTerm nil = nil := rfl

@[simp] theorem apply_cons (θ : Substitution Leaf Var) (a b : Tm Leaf Var) :
    θ.applyTerm (cons a b) = cons (θ.applyTerm a) (θ.applyTerm b) := by
  simp only [cons, Subst.applyTerm]
  congr 1
  funext i
  split <;> rfl

@[simp] theorem apply_expr (θ : Substitution Leaf Var) (children : List (Tm Leaf Var)) :
    θ.applyTerm (expr children) = expr (children.map θ.applyTerm) := by
  unfold expr
  simp only [Subst.applyTerm_app]
  congr 1
  · simp
  · apply (Fin.heq_fun_iff (List.length_map (f := θ.applyTerm)).symm).mpr
    intro i
    simp [List.get_eq_getElem]

def close (rest : Option (Tm Leaf Var)) : Tm Leaf Var := rest.getD nil

/-- A fixed prefix followed by either a rest term or the empty-list constant.
An arbitrary rest term is allowed: no proper-list typing is assumed. -/
def spine (front : List (Tm Leaf Var)) (rest : Option (Tm Leaf Var)) : Tm Leaf Var :=
  front.foldr cons (close rest)

@[simp] theorem spine_nil (rest : Option (Tm Leaf Var)) : spine [] rest = close rest := rfl

@[simp] theorem spine_cons (x : Tm Leaf Var) (xs : List (Tm Leaf Var))
    (rest : Option (Tm Leaf Var)) : spine (x :: xs) rest = cons x (spine xs rest) := rfl

@[simp] theorem close_none : (close none : Tm Leaf Var) = nil := rfl
@[simp] theorem close_some (t : Tm Leaf Var) : close (some t) = t := rfl

theorem apply_spine (θ : Substitution Leaf Var) (xs : List (Tm Leaf Var))
    (rest : Option (Tm Leaf Var)) :
    θ.applyTerm (spine xs rest) =
      spine (xs.map θ.applyTerm) (rest.map θ.applyTerm) := by
  induction xs with
  | nil => cases rest <;> rfl
  | cons x xs ih => simp [ih]

/-- Order and multiplicity survive list encoding; neither is quotiented away. -/
@[simp] theorem spine_closed_inj (xs ys : List (Tm Leaf Var)) :
    spine xs none = spine ys none ↔ xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp
  | cons x xs ih => cases ys <;> simp [ih]

/-- List/application disjointness holds after substitution, not only for
literal ground examples. -/
theorem closed_spine_ne_expr (θ : Substitution Leaf Var)
    (xs ys : List (Tm Leaf Var)) :
    θ.applyTerm (spine xs none) ≠ θ.applyTerm (expr ys) := by
  cases xs <;> simp

/-- An open pattern is also disjoint from expressions when its prefix is
nonempty. The nonempty condition matters: an empty splice is just its tail. -/
theorem nonempty_spine_ne_expr (θ : Substitution Leaf Var)
    (xs ys : List (Tm Leaf Var)) (rest : Option (Tm Leaf Var))
    (nonempty : xs ≠ []) :
    θ.applyTerm (spine xs rest) ≠ θ.applyTerm (expr ys) := by
  cases xs with
  | nil => exact False.elim (nonempty rfl)
  | cons x xs => simp

abbrev Equations (Leaf : Type) (Var : Type) := List (Tm Leaf Var × Tm Leaf Var)

/-- Recursively emit the common-prefix equations, then the native meeting's
single rest equation.  A closed shorter prefix is a constructor mismatch. -/
def meet : List (Tm Leaf Var) → Option (Tm Leaf Var) →
    List (Tm Leaf Var) → Option (Tm Leaf Var) → Option (Equations Leaf Var)
  | [], none, [], none => some []
  | [], leftRest, [], rightRest => some [(close leftRest, close rightRest)]
  | [], none, _ :: _, _ => none
  | [], some leftRest, y :: ys, rightRest =>
      some [(leftRest, spine (y :: ys) rightRest)]
  | _ :: _, _, [], none => none
  | x :: xs, leftRest, [], some rightRest =>
      some [(spine (x :: xs) leftRest, rightRest)]
  | x :: xs, leftRest, y :: ys, rightRest =>
      (meet xs leftRest ys rightRest).map ((x, y) :: ·)

/-- The length-comparison presentation used by the native list meeting.
Allocation-failure and ownership flags are deliberately not part of this
pure constraint operation. -/
def meetByLength (xs : List (Tm Leaf Var)) (leftRest : Option (Tm Leaf Var))
    (ys : List (Tm Leaf Var)) (rightRest : Option (Tm Leaf Var)) :
    Option (Equations Leaf Var) :=
  let common := min xs.length ys.length
  let pairs := (xs.take common).zip (ys.take common)
  if xs.length = ys.length then
    match leftRest, rightRest with
    | none, none => some pairs
    | _, _ => some (pairs ++ [(close leftRest, close rightRest)])
  else if xs.length < ys.length then
    match leftRest with
    | none => none
    | some rest => some (pairs ++ [(rest, spine (ys.drop common) rightRest)])
  else
    match rightRest with
    | none => none
    | some rest => some (pairs ++ [(spine (xs.drop common) leftRest, rest)])

/-- The recursive proof view emits exactly the native length-comparison view's
equations, in the same order. -/
theorem meetByLength_eq_meet (xs : List (Tm Leaf Var))
    (leftRest : Option (Tm Leaf Var)) (ys : List (Tm Leaf Var))
    (rightRest : Option (Tm Leaf Var)) :
    meetByLength xs leftRest ys rightRest = meet xs leftRest ys rightRest := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => cases leftRest <;> cases rightRest <;> simp [meetByLength, meet]
      | cons y ys => cases leftRest <;> simp [meetByLength, meet]
  | cons x xs ih =>
      cases ys with
      | nil => cases rightRest <;> simp [meetByLength, meet]
      | cons y ys =>
          rw [meet, ← ih ys]
          have minimum : min (xs.length + 1) (ys.length + 1) =
              min xs.length ys.length + 1 := by omega
          by_cases equal : xs.length = ys.length
          · cases leftRest <;> cases rightRest <;>
              simp [meetByLength, equal]
          · by_cases shorter : xs.length < ys.length
            · cases leftRest <;> simp [meetByLength, equal, shorter, minimum]
            · cases rightRest <;> simp [meetByLength, equal, shorter, minimum]

def Satisfies (θ : Substitution Leaf Var) : Option (Equations Leaf Var) → Prop
  | none => False
  | some equations => Unifies θ equations

@[simp] theorem unifies_nil (θ : Substitution Leaf Var) : Unifies θ [] := by
  intro pair member
  cases member

@[simp] theorem unifies_cons (θ : Substitution Leaf Var)
    (x y : Tm Leaf Var) (equations : Equations Leaf Var) :
    Unifies θ ((x, y) :: equations) ↔
      θ.applyTerm x = θ.applyTerm y ∧ Unifies θ equations := by
  simp only [Unifies, List.mem_cons, Prod.forall, Prod.mk.injEq]
  constructor
  · intro h
    exact ⟨h x y (Or.inl ⟨rfl, rfl⟩), fun a b hab => h a b (Or.inr hab)⟩
  · rintro ⟨head, tail⟩ a b (⟨rfl, rfl⟩ | hab)
    · exact head
    · exact tail a b hab

@[simp] theorem satisfies_map_cons (θ : Substitution Leaf Var)
    (x y : Tm Leaf Var) (equations : Option (Equations Leaf Var)) :
    Satisfies θ (equations.map ((x, y) :: ·)) ↔
      θ.applyTerm x = θ.applyTerm y ∧ Satisfies θ equations := by
  cases equations <;> simp [Satisfies]

/-- Decomposition preserves exactly the substitutions solving the original
list equation, including open/open, open/closed and unequal-prefix cases. -/
theorem meet_iff (θ : Substitution Leaf Var) (xs : List (Tm Leaf Var))
    (leftRest : Option (Tm Leaf Var)) (ys : List (Tm Leaf Var))
    (rightRest : Option (Tm Leaf Var)) :
    Satisfies θ (meet xs leftRest ys rightRest) ↔
      θ.applyTerm (spine xs leftRest) = θ.applyTerm (spine ys rightRest) := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => cases leftRest <;> cases rightRest <;> simp [meet, Satisfies]
      | cons y ys => cases leftRest <;> simp [meet, Satisfies]
  | cons x xs ih =>
      cases ys with
      | nil => cases rightRest <;> simp [meet, Satisfies]
      | cons y ys => simp [meet, ih]

theorem meetByLength_iff (θ : Substitution Leaf Var) (xs : List (Tm Leaf Var))
    (leftRest : Option (Tm Leaf Var)) (ys : List (Tm Leaf Var))
    (rightRest : Option (Tm Leaf Var)) :
    Satisfies θ (meetByLength xs leftRest ys rightRest) ↔
      θ.applyTerm (spine xs leftRest) = θ.applyTerm (spine ys rightRest) := by
  rw [meetByLength_eq_meet]
  exact meet_iff θ xs leftRest ys rightRest

theorem meet_some_iff (θ : Substitution Leaf Var) (xs : List (Tm Leaf Var))
    (leftRest : Option (Tm Leaf Var)) (ys : List (Tm Leaf Var))
    (rightRest : Option (Tm Leaf Var)) (equations : Equations Leaf Var)
    (accepted : meet xs leftRest ys rightRest = some equations) :
    Unifies θ equations ↔
      θ.applyTerm (spine xs leftRest) = θ.applyTerm (spine ys rightRest) := by
  have h := meet_iff θ xs leftRest ys rightRest
  simpa only [accepted, Satisfies] using h

/-- A constructor mismatch in the meeting is logically impossible to solve;
it is not a resource or search-fuel failure. -/
theorem meet_none_unsatisfiable (xs : List (Tm Leaf Var))
    (leftRest : Option (Tm Leaf Var)) (ys : List (Tm Leaf Var))
    (rightRest : Option (Tm Leaf Var))
    (rejected : meet xs leftRest ys rightRest = none) :
    ¬∃ θ : Substitution Leaf Var,
      θ.applyTerm (spine xs leftRest) = θ.applyTerm (spine ys rightRest) := by
  rintro ⟨θ, solved⟩
  have h := (meet_iff θ xs leftRest ys rightRest).mpr solved
  simp only [rejected, Satisfies] at h

/-- The fixed common prefix contributes precisely its pairwise equations.
The rest is handled once, after all those equations. -/
theorem meet_common_prefix (xs ys moreLeft moreRight : List (Tm Leaf Var))
    (leftRest rightRest : Option (Tm Leaf Var))
    (sameLength : xs.length = ys.length) :
    meet (xs ++ moreLeft) leftRest (ys ++ moreRight) rightRest =
      (meet moreLeft leftRest moreRight rightRest).map (xs.zip ys ++ ·) := by
  induction xs generalizing ys with
  | nil =>
      have : ys = [] := List.length_eq_zero_iff.mp sameLength.symm
      subst ys
      simp
  | cons x xs ih =>
      cases ys with
      | nil => simp at sameLength
      | cons y ys =>
          have equal : xs.length = ys.length := Nat.succ.inj sameLength
          simp only [List.cons_append, meet, ih ys equal, Option.map_map,
            List.zip_cons_cons]
          rfl

/-- Equal-length closed prefixes produce only element equations, as in the
native `p == q` branch with neither rest present. -/
theorem meet_closed_equal (xs ys : List (Tm Leaf Var))
    (sameLength : xs.length = ys.length) :
    meet xs none ys none = some (xs.zip ys) := by
  simpa [meet] using meet_common_prefix xs ys [] [] none none sameLength

/-- A shorter open left prefix meets exactly the remaining right spine. -/
theorem meet_left_shorter (xs ys moreRight : List (Tm Leaf Var))
    (leftRest : Tm Leaf Var) (rightRest : Option (Tm Leaf Var))
    (sameLength : xs.length = ys.length) (nonempty : moreRight ≠ []) :
    meet xs (some leftRest) (ys ++ moreRight) rightRest =
      some (xs.zip ys ++ [(leftRest, spine moreRight rightRest)]) := by
  cases moreRight with
  | nil => exact False.elim (nonempty rfl)
  | cons z zs =>
      simpa [meet] using
        meet_common_prefix xs ys [] (z :: zs) (some leftRest) rightRest sameLength

/-- A shorter closed left prefix cannot meet a nonempty remaining prefix. -/
theorem meet_closed_left_shorter (xs ys moreRight : List (Tm Leaf Var))
    (rightRest : Option (Tm Leaf Var))
    (sameLength : xs.length = ys.length) (nonempty : moreRight ≠ []) :
    meet xs none (ys ++ moreRight) rightRest = none := by
  cases moreRight with
  | nil => exact False.elim (nonempty rfl)
  | cons z zs =>
      simpa [meet] using
        meet_common_prefix xs ys [] (z :: zs) none rightRest sameLength

/-- Symmetric shorter-right branch. -/
theorem meet_right_shorter (xs ys moreLeft : List (Tm Leaf Var))
    (leftRest : Option (Tm Leaf Var)) (rightRest : Tm Leaf Var)
    (sameLength : xs.length = ys.length) (nonempty : moreLeft ≠ []) :
    meet (xs ++ moreLeft) leftRest ys (some rightRest) =
      some (xs.zip ys ++ [(spine moreLeft leftRest, rightRest)]) := by
  cases moreLeft with
  | nil => exact False.elim (nonempty rfl)
  | cons z zs =>
      simpa [meet] using
        meet_common_prefix xs ys (z :: zs) [] leftRest (some rightRest) sameLength

/-- The head/rest law: one leading pattern element meets the first element;
its rest meets the list containing all remaining elements, not an expression. -/
theorem head_rest_iff (θ : Substitution Leaf Var) (h r x : Tm Leaf Var)
    (xs : List (Tm Leaf Var)) :
    θ.applyTerm (spine [h] (some r)) =
        θ.applyTerm (spine (x :: xs) none) ↔
      θ.applyTerm h = θ.applyTerm x ∧
        θ.applyTerm r = θ.applyTerm (spine xs none) := by
  simp

theorem singleton_rest_is_nil (θ : Substitution Leaf Var) (h r x : Tm Leaf Var) :
    θ.applyTerm (spine [h] (some r)) = θ.applyTerm (spine [x] none) ↔
      θ.applyTerm h = θ.applyTerm x ∧ θ.applyTerm r = nil := by
  simp

theorem head_rest_ne_empty (θ : Substitution Leaf Var) (h r : Tm Leaf Var) :
    θ.applyTerm (spine [h] (some r)) ≠ nil := by
  simp

/-- Repeating a variable is an equality constraint, never two independent
pattern captures.  Unequal fixed target leaves therefore cannot match. -/
theorem repeated_head_unsatisfiable (v : Var) (r : Tm Leaf Var)
    (a b : Leaf) (different : a ≠ b) (more : List (Tm Leaf Var)) :
    ¬∃ θ : Substitution Leaf Var,
      θ.applyTerm (spine [.var v, .var v] (some r)) =
        θ.applyTerm (spine (.const (.atom a) :: .const (.atom b) :: more) none) := by
  rintro ⟨θ, same⟩
  simp only [spine_cons, spine_nil, close_some, apply_cons, Subst.applyTerm_var,
    Subst.applyTerm_const, cons_inj] at same
  have constants : (Term.const (.atom a) : Tm Leaf Var) = .const (.atom b) :=
    same.1.symm.trans same.2.1
  cases constants
  exact different rfl

theorem cons_tail_size (a b : Tm Leaf Var) : b.size < (cons a b).size := by
  have h := Term.size_subterm (σ := signature Leaf Var) (f := .cons)
    (ts := fun (i : Fin 2) => if i = 0 then a else b) (1 : Fin 2)
  simpa only [cons, show (1 : Fin 2) ≠ 0 from by decide, ↓reduceIte] using h

/-- Finite-term occurs checking is necessary: `$r = [h | $r]` has no
substitution solution, even if `h` itself contains variables or lists. -/
theorem occurs_rest_unsatisfiable (v : Var) (h : Tm Leaf Var) :
    ¬∃ θ : Substitution Leaf Var,
      θ.applyTerm (.var v) = θ.applyTerm (spine [h] (some (.var v))) := by
  rintro ⟨θ, same⟩
  have smaller := cons_tail_size (θ.applyTerm h) (θ v)
  simp only [spine_cons, spine_nil, close_some, apply_cons, Subst.applyTerm_var] at same
  rw [← same] at smaller
  exact (Nat.lt_irrefl _) smaller

/-- Nested lists decompose inside the head exactly as at the outer spine. -/
theorem nested_head_rest_iff (θ : Substitution Leaf Var)
    (a r s b : Tm Leaf Var) (inside outside : List (Tm Leaf Var)) :
    θ.applyTerm (spine [spine [a] (some r)] (some s)) =
        θ.applyTerm (spine [spine (b :: inside) none] (some (spine outside none))) ↔
      θ.applyTerm a = θ.applyTerm b ∧
      θ.applyTerm r = θ.applyTerm (spine inside none) ∧
      θ.applyTerm s = θ.applyTerm (spine outside none) := by
  simp [and_assoc]

section ReferenceSolver

variable [DecidableEq Leaf] [DecidableEq Var]

/-- Reference solution of the emitted equations, using the existing total
first-order unifier.  This is not an implementation of the native binding store. -/
def solve (xs : List (Tm Leaf Var)) (leftRest : Option (Tm Leaf Var))
    (ys : List (Tm Leaf Var)) (rightRest : Option (Tm Leaf Var)) :
    Option (Substitution Leaf Var) :=
  (meet xs leftRest ys rightRest).bind unifyTotal

theorem solve_sound (xs : List (Tm Leaf Var)) (leftRest : Option (Tm Leaf Var))
    (ys : List (Tm Leaf Var)) (rightRest : Option (Tm Leaf Var))
    (θ : Substitution Leaf Var) (accepted : solve xs leftRest ys rightRest = some θ) :
    θ.applyTerm (spine xs leftRest) = θ.applyTerm (spine ys rightRest) := by
  cases meeting : meet xs leftRest ys rightRest with
  | none => simp [solve, meeting] at accepted
  | some equations =>
      simp only [solve, meeting, Option.bind_some] at accepted
      exact (meet_some_iff θ xs leftRest ys rightRest equations meeting).mp
        (unifyTotal_sound equations θ accepted)

/-- The reference solver returns a most general unifier, because prefix
meeting preserves the full solution set of the list equation. -/
theorem solve_mgu (xs : List (Tm Leaf Var)) (leftRest : Option (Tm Leaf Var))
    (ys : List (Tm Leaf Var)) (rightRest : Option (Tm Leaf Var))
    (θ : Substitution Leaf Var) (accepted : solve xs leftRest ys rightRest = some θ)
    (candidate : Substitution Leaf Var)
    (solved : candidate.applyTerm (spine xs leftRest) =
      candidate.applyTerm (spine ys rightRest)) : θ.moreGeneral candidate := by
  cases meeting : meet xs leftRest ys rightRest with
  | none => simp [solve, meeting] at accepted
  | some equations =>
      simp only [solve, meeting, Option.bind_some] at accepted
      exact unifyTotal_mgu equations θ accepted candidate
        ((meet_some_iff candidate xs leftRest ys rightRest equations meeting).mpr solved)

theorem solve_complete (xs : List (Tm Leaf Var)) (leftRest : Option (Tm Leaf Var))
    (ys : List (Tm Leaf Var)) (rightRest : Option (Tm Leaf Var))
    (solvable : ∃ θ : Substitution Leaf Var,
      θ.applyTerm (spine xs leftRest) = θ.applyTerm (spine ys rightRest)) :
    ∃ θ, solve xs leftRest ys rightRest = some θ := by
  obtain ⟨candidate, solved⟩ := solvable
  cases meeting : meet xs leftRest ys rightRest with
  | none =>
      exact False.elim
        (meet_none_unsatisfiable xs leftRest ys rightRest meeting ⟨candidate, solved⟩)
  | some equations =>
      obtain ⟨θ, accepted⟩ := unifyTotal_complete
        ⟨candidate, (meet_some_iff candidate xs leftRest ys rightRest equations meeting).mpr solved⟩
      exact ⟨θ, by simp only [solve, meeting, Option.bind_some, accepted]⟩

theorem solve_none_iff (xs : List (Tm Leaf Var)) (leftRest : Option (Tm Leaf Var))
    (ys : List (Tm Leaf Var)) (rightRest : Option (Tm Leaf Var)) :
    solve xs leftRest ys rightRest = none ↔
      ¬∃ θ : Substitution Leaf Var,
        θ.applyTerm (spine xs leftRest) = θ.applyTerm (spine ys rightRest) := by
  constructor
  · intro rejected solvable
    obtain ⟨θ, accepted⟩ := solve_complete xs leftRest ys rightRest solvable
    rw [rejected] at accepted
    cases accepted
  · intro unsatisfiable
    cases result : solve xs leftRest ys rightRest with
    | none => rfl
    | some θ =>
        exact False.elim
          (unsatisfiable ⟨θ, solve_sound xs leftRest ys rightRest θ result⟩)

end ReferenceSolver

end Mettapedia.Logic.Unification.ListPrefixMeeting
