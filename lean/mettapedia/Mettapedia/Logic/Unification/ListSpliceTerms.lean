import Mathlib.Data.List.Basic

/-!
# First-order terms with list splices

An expression, a proper list, and an open list spine are different constructors.
`splice` follows the prefix/tail construction rule: an empty prefix disappears,
a list tail is concatenated, and an open tail contributes its prefix. Neither
construction nor substitution evaluates expression elements.

This module is the algebraic source for a list extension, not an assertion that
an arbitrary native reader or matcher implements it. In particular a raw rest
may be any term; proper lists and open patterns must not be conflated.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Unification.ListSplice

inductive Term (Leaf Var : Type) where
  | atom : Leaf → Term Leaf Var
  | var : Var → Term Leaf Var
  | expr : List (Term Leaf Var) → Term Leaf Var
  | list : List (Term Leaf Var) → Term Leaf Var
  | rest : List (Term Leaf Var) → Term Leaf Var → Term Leaf Var
  deriving Repr

variable {Leaf Var : Type}

/-- Construct one flattened prefix/tail spine. -/
def splice (front : List (Term Leaf Var)) (tail : Term Leaf Var) : Term Leaf Var :=
  match front with
  | [] => tail
  | _ :: _ =>
    match tail with
    | .list suffix => .list (front ++ suffix)
    | .rest suffix rest => .rest (front ++ suffix) rest
    | other => .rest front other

@[simp] theorem splice_nil (tail : Term Leaf Var) : splice [] tail = tail := rfl

@[simp] theorem splice_list (xs ys : List (Term Leaf Var)) :
    splice xs (.list ys) = .list (xs ++ ys) := by
  cases xs <;> rfl

@[simp] theorem splice_rest (xs ys : List (Term Leaf Var)) (tail : Term Leaf Var) :
    splice xs (.rest ys tail) = .rest (xs ++ ys) tail := by
  cases xs <;> rfl

/-- Prefix composition is associative, including empty and open tails. -/
theorem splice_append (xs ys : List (Term Leaf Var)) (tail : Term Leaf Var) :
    splice (xs ++ ys) tail = splice xs (splice ys tail) := by
  cases xs with
  | nil => simp
  | cons x xs =>
    cases ys with
    | nil => simp
    | cons y ys => cases tail <;> simp [splice, List.append_assoc]

/-- Normalize children first, then splice the normalized tail. -/
def normalize : Term Leaf Var → Term Leaf Var
  | .atom a => .atom a
  | .var v => .var v
  | .expr xs => .expr (xs.map normalize)
  | .list xs => .list (xs.map normalize)
  | .rest xs tail => splice (xs.map normalize) (normalize tail)

/-- Raw simultaneous substitution, before the construction normalizer. -/
def subst (σ : Var → Term Leaf Var) : Term Leaf Var → Term Leaf Var
  | .atom a => .atom a
  | .var v => σ v
  | .expr xs => .expr (xs.map (subst σ))
  | .list xs => .list (xs.map (subst σ))
  | .rest xs tail => .rest (xs.map (subst σ)) (subst σ tail)

@[simp] theorem list_ne_expr (xs ys : List (Term Leaf Var)) :
    Term.list xs ≠ Term.expr ys := by intro h; cases h

@[simp] theorem list_injective (xs ys : List (Term Leaf Var)) :
    Term.list xs = Term.list ys ↔ xs = ys := by simp only [Term.list.injEq]

/-- A source prefix/tail splice can be normalized before or after construction. -/
theorem normalize_splice (xs : List (Term Leaf Var)) (tail : Term Leaf Var) :
    normalize (splice xs tail) = splice (xs.map normalize) (normalize tail) := by
  cases tail with
  | rest ys tail =>
    rw [splice_rest]
    simp only [normalize, List.map_append]
    exact splice_append _ _ _
  | list ys => simp [normalize, List.map_append]
  | atom a => cases xs <;> simp [splice, normalize]
  | var v => cases xs <;> simp [splice, normalize]
  | expr ys => cases xs <;> simp [splice, normalize]

/-- Normalization is a retraction, not a repeated flattening pass. -/
theorem normalize_idempotent (term : Term Leaf Var) :
    normalize (normalize term) = normalize term := by
  match term with
  | .atom _ => simp [normalize]
  | .var _ => simp [normalize]
  | .expr xs =>
    simp only [normalize, List.map_map]
    congr 1
    exact List.map_congr_left fun x _ => normalize_idempotent x
  | .list xs =>
    simp only [normalize, List.map_map]
    congr 1
    exact List.map_congr_left fun x _ => normalize_idempotent x
  | .rest xs tail =>
    rw [normalize, normalize_splice, normalize_idempotent tail]
    congr 1
    simp only [List.map_map]
    exact List.map_congr_left fun x _ => normalize_idempotent x
termination_by sizeOf term

/-- Substitution can expose a list tail; normalizing it restores the same spine. -/
theorem normalize_subst_splice (σ : Var → Term Leaf Var)
    (xs : List (Term Leaf Var)) (tail : Term Leaf Var) :
    normalize (subst σ (splice xs tail)) =
      splice (xs.map (fun x => normalize (subst σ x))) (normalize (subst σ tail)) := by
  cases tail with
  | rest ys tail =>
    rw [splice_rest]
    simp only [subst, normalize, List.map_append, List.map_map]
    exact splice_append _ _ _
  | list ys => simp [subst, normalize, List.map_append, List.map_map, Function.comp_def]
  | atom a => cases xs <;> simp [splice, subst, normalize, List.map_map, Function.comp_def]
  | var v => cases xs <;> simp [splice, subst, normalize, List.map_map, Function.comp_def]
  | expr ys => cases xs <;> simp [splice, subst, normalize, List.map_map, Function.comp_def]

/-- Substitution respects the splice equations; it need not preserve raw syntax. -/
theorem normalize_subst_normalize (σ : Var → Term Leaf Var) (term : Term Leaf Var) :
    normalize (subst σ (normalize term)) = normalize (subst σ term) := by
  match term with
  | .atom _ => simp [normalize, subst]
  | .var _ => simp [normalize, subst]
  | .expr xs =>
    simp only [normalize, subst, List.map_map]
    congr 1
    exact List.map_congr_left fun x _ => normalize_subst_normalize σ x
  | .list xs =>
    simp only [normalize, subst, List.map_map]
    congr 1
    exact List.map_congr_left fun x _ => normalize_subst_normalize σ x
  | .rest xs tail =>
    rw [normalize, normalize_subst_splice, normalize_subst_normalize σ tail]
    simp only [subst, normalize, List.map_map]
    congr 1
    exact List.map_congr_left fun x _ => normalize_subst_normalize σ x
termination_by sizeOf term

/-- Head/rest construction with a proper suffix gives the expected proper list. -/
theorem singleton_splice_list (head : Term Leaf Var) (tail : List (Term Leaf Var)) :
    splice [head] (.list tail) = .list (head :: tail) := by simp

mutual
  /-- The congruence generated by the three source splice equations. -/
  inductive Equivalent : Term Leaf Var → Term Leaf Var → Prop where
    | refl (t) : Equivalent t t
    | symm {s t} : Equivalent s t → Equivalent t s
    | trans {r s t} : Equivalent r s → Equivalent s t → Equivalent r t
    | expr {xs ys} : EquivalentList xs ys → Equivalent (.expr xs) (.expr ys)
    | list {xs ys} : EquivalentList xs ys → Equivalent (.list xs) (.list ys)
    | rest {xs ys s t} : EquivalentList xs ys → Equivalent s t →
        Equivalent (.rest xs s) (.rest ys t)
    | emptyRest (t) : Equivalent (.rest [] t) t
    | closedRest (xs ys) : Equivalent (.rest xs (.list ys)) (.list (xs ++ ys))
    | nestedRest (xs ys t) :
        Equivalent (.rest xs (.rest ys t)) (.rest (xs ++ ys) t)

  /-- Ordered, multiplicity-preserving congruence on child sequences. -/
  inductive EquivalentList : List (Term Leaf Var) → List (Term Leaf Var) → Prop where
    | nil : EquivalentList [] []
    | cons {x y xs ys} : Equivalent x y → EquivalentList xs ys →
        EquivalentList (x :: xs) (y :: ys)
end

/-- Every generating equation, in every context, preserves the computed normal form. -/
theorem Equivalent.normalize_eq {s t : Term Leaf Var} (h : Equivalent s t) :
    normalize s = normalize t := by
  induction h using Equivalent.rec
    (motive_2 := fun xs ys _ => xs.map normalize = ys.map normalize) with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih jk => exact ih.trans jk
  | expr _ ih => simpa only [normalize] using congrArg Term.expr ih
  | list _ ih => simpa only [normalize] using congrArg Term.list ih
  | rest _ _ ih jk =>
    simp only [normalize]
    rw [ih, jk]
  | emptyRest t => simp [normalize]
  | closedRest xs ys => simp [normalize, List.map_append]
  | nestedRest xs ys t =>
    simp only [normalize, List.map_append]
    exact (splice_append _ _ _).symm
  | nil => rfl
  | cons _ _ ih jk => simp only [List.map_cons, ih, jk]

theorem EquivalentList.normalize_eq {xs ys : List (Term Leaf Var)}
    (h : EquivalentList xs ys) : xs.map normalize = ys.map normalize := by
  have he := (Equivalent.expr h).normalize_eq
  simpa only [normalize, Term.expr.injEq] using he

theorem rest_equivalent_splice (xs : List (Term Leaf Var)) (tail : Term Leaf Var) :
    Equivalent (.rest xs tail) (splice xs tail) := by
  cases xs with
  | nil => exact .emptyRest tail
  | cons x xs =>
    cases tail with
    | list ys => exact .closedRest _ _
    | rest ys t => exact .nestedRest _ _ _
    | atom a => exact .refl _
    | var v => exact .refl _
    | expr ys => exact .refl _

mutual
  /-- Normalization is obtained using only the declared equations and congruence. -/
  theorem equivalent_normalize (t : Term Leaf Var) : Equivalent t (normalize t) := by
    cases t with
    | atom a => simpa only [normalize] using Equivalent.refl (Term.atom a : Term Leaf Var)
    | var v => simpa only [normalize] using Equivalent.refl (Term.var v : Term Leaf Var)
    | expr xs => simpa only [normalize] using Equivalent.expr (equivalentList_normalize xs)
    | list xs => simpa only [normalize] using Equivalent.list (equivalentList_normalize xs)
    | rest xs t =>
      simp only [normalize]
      exact .trans (.rest (equivalentList_normalize xs) (equivalent_normalize t))
        (rest_equivalent_splice _ _)
  termination_by sizeOf t

  theorem equivalentList_normalize (xs : List (Term Leaf Var)) :
      EquivalentList xs (xs.map normalize) := by
    cases xs with
    | nil => exact .nil
    | cons x xs => exact .cons (equivalent_normalize x) (equivalentList_normalize xs)
  termination_by sizeOf xs
end

/-- The algorithm decides exactly the independently generated splice congruence. -/
theorem equivalent_iff_normalize_eq (s t : Term Leaf Var) :
    Equivalent s t ↔ normalize s = normalize t := by
  constructor
  · exact Equivalent.normalize_eq
  · intro h
    exact .trans (equivalent_normalize s)
      (h ▸ (equivalent_normalize t).symm)

/-- Equivalent fixed points are identical: there is one normal form per congruence class. -/
theorem normal_forms_unique {s t : Term Leaf Var}
    (hs : normalize s = s) (ht : normalize t = t) (h : Equivalent s t) : s = t := by
  simpa only [hs, ht] using h.normalize_eq

/-- Raw substitution preserves the source congruence, even when it exposes new splices. -/
theorem Equivalent.subst {s t : Term Leaf Var} (h : Equivalent s t)
    (σ : Var → Term Leaf Var) : Equivalent (subst σ s) (subst σ t) := by
  apply (equivalent_iff_normalize_eq _ _).mpr
  rw [← normalize_subst_normalize σ s, ← normalize_subst_normalize σ t, h.normalize_eq]

example : normalize (Term.rest [.atom 1] (.list [.atom 2]) : Term Nat Nat) =
    .list [.atom 1, .atom 2] := by simp [normalize]

example : normalize (Term.rest [] (.expr []) : Term Nat Nat) = .expr [] := by simp [normalize]

example : (Term.list [.atom 1, .atom 2] : Term Nat Nat) ≠ .list [.atom 2, .atom 1] := by
  intro h
  cases h

example : (Term.list [.atom 1, .atom 1] : Term Nat Nat) ≠ .list [.atom 1] := by
  intro h
  cases h

end Mettapedia.Logic.Unification.ListSplice
