import Mathlib.Tactic

/-!
# Builtin heads a PeTTa space authors equations for

PeTTa's canonical evaluator lets a space's own equations decide a call of a builtin
head there, except in `&self`, where the builtin is protected. CeTTa's prepared
machine runs a register or intrinsic program for some builtin heads; it refuses one
where the space's equations may match the head
(`space_equations_may_match_known_head`), and the canonical evaluator answers.

**The model**: terms, left sides matched against calls (`Matches`), a space with its
equations (its dependencies' included) and whether it is `&self`.
* `canon`: the canonical evaluator on a call of a builtin head: in `&self` the
  builtin; elsewhere, where an equation's left side matches the call, what the
  space's equations answer (`owned`), and otherwise the builtin;
* `mayMatch`: CeTTa's index read (`eq_lhs_may_match_known_head`): a left side headed
  by the head's symbol, by a variable, or a variable;
* `machine`: refuses where `mayMatch` holds, otherwise runs the program, which
  answers the builtin.

**Theorem** (`machine_eq_canon`): the machine answers what the canonical evaluator
answers on every call of the head. The index read is sound: a left side that
matches a call of the head is one it names (`lhsMayMatch_of_matches`).

**Controls** (`tests/petta/builtin_owned_by_space`): with `(= (+ $a $b) (OwnedPlus
$a $b))` in a space other than `&self`, `(+ 2 1)` answers `(OwnedPlus 2 1)` there,
which a machine without the refusal answers `3` (`Controls.unrefused_differs`); in
`&self` the builtin answers (`Controls.self_protected`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.AdmissionRewriting.BuiltinOwnership

/-- Terms: symbols, variables, numbers and applications. -/
inductive Term where
  | sym (s : String)
  | var (x : String)
  | num (n : ℤ)
  | app (xs : List Term)

mutual
/-- A left side matches a term: a variable anything, a symbol or a number itself,
an application elementwise. -/
inductive Matches : Term → Term → Prop
  | var (x : String) (t : Term) : Matches (.var x) t
  | sym (s : String) : Matches (.sym s) (.sym s)
  | num (n : ℤ) : Matches (.num n) (.num n)
  | app {ps ts : List Term} : MatchesAll ps ts → Matches (.app ps) (.app ts)
/-- Elementwise matching. -/
inductive MatchesAll : List Term → List Term → Prop
  | nil : MatchesAll [] []
  | cons {p t : Term} {ps ts : List Term} : Matches p t → MatchesAll ps ts → MatchesAll (p :: ps) (t :: ts)
end

/-- The symbol heading a left side (`eq_head_symbol`): the symbol itself, or an
application's first element. -/
def headSym : Term → Option String
  | .sym s => some s
  | .app (.sym s :: _) => some s
  | _ => none

/-- **CeTTa's test of one left side** (`eq_lhs_may_match_known_head`). -/
def lhsMayMatch (lhs : Term) (h : String) : Bool :=
  match headSym lhs with
  | some s => s == h
  | none =>
      match lhs with
      | .var _ => true
      | .app (.var _ :: _) => true
      | _ => false

/-- A space: its equations (its dependencies' included), and whether it is `&self`. -/
structure Space where
  self : Bool
  eqs : List (Term × Term)

/-- **CeTTa's index read** (`space_equations_may_match_known_head`). -/
def mayMatch (S : Space) (h : String) : Bool := S.eqs.any fun e => lhsMayMatch e.1 h

/-- The index read is sound: a left side matching a call of `h` is one it names. -/
theorem lhsMayMatch_of_matches {lhs : Term} {h : String} {args : List Term}
    (hm : Matches lhs (.app (.sym h :: args))) : lhsMayMatch lhs h = true := by
  cases hm with
  | var x => rfl
  | app hall =>
      cases hall with
      | cons hp _ =>
          cases hp with
          | var x => rfl
          | sym s => simp [lhsMayMatch, headSym]

theorem mayMatch_of_matches {S : Space} {h : String} {args : List Term}
    (hm : ∃ e ∈ S.eqs, Matches e.1 (.app (.sym h :: args))) : mayMatch S h = true := by
  obtain ⟨e, he, hm⟩ := hm
  exact List.any_eq_true.mpr ⟨e, he, lhsMayMatch_of_matches hm⟩

open Classical in
/-- **The canonical evaluator on a call of a builtin head**: in `&self` the
builtin; elsewhere the space's equations where one matches the call, else the
builtin. -/
noncomputable def canon (S : Space) (builtin owned : Term → List Term) (c : Term) : List Term :=
  if S.self then builtin c
  else if ∃ e ∈ S.eqs, Matches e.1 c then owned c
  else builtin c

/-- **The machine**: refused where the space's equations may match the head (the
canonical evaluator answers), otherwise the program's builtin answer. -/
noncomputable def machine (S : Space) (h : String) (builtin owned : Term → List Term) (c : Term) :
    List Term :=
  if mayMatch S h then canon S builtin owned c else builtin c

/-- **The refusal keeps the canonical answers**: on every call of the head the
machine answers what the canonical evaluator answers. -/
theorem machine_eq_canon (S : Space) (h : String) (args : List Term) (builtin owned : Term → List Term) :
    machine S h builtin owned (.app (.sym h :: args)) = canon S builtin owned (.app (.sym h :: args)) := by
  unfold machine
  split_ifs with hmay
  · rfl
  · have hnone : ¬ ∃ e ∈ S.eqs, Matches e.1 (.app (.sym h :: args)) := fun hm =>
      hmay (mayMatch_of_matches hm)
    unfold canon
    split_ifs <;> rfl

/-! ## Controls -/

namespace Controls

/-- `(= (+ $a $b) (OwnedPlus $a $b))`. -/
def ownedPlus : Term × Term :=
  (.app [.sym "+", .var "a", .var "b"], .app [.sym "OwnedPlus", .var "a", .var "b"])

/-- `(+ 2 1)`. -/
def call : Term := .app [.sym "+", .num 2, .num 1]

/-- The builtin's answer, `3`. -/
def builtin : Term → List Term := fun _ => [.num 3]

/-- The space's answer, `(OwnedPlus 2 1)`. -/
def owned : Term → List Term := fun _ => [.app [.sym "OwnedPlus", .num 2, .num 1]]

theorem ownedPlus_matches : Matches ownedPlus.1 call :=
  .app (.cons (.sym "+") (.cons (.var "a" _) (.cons (.var "b" _) .nil)))

/-- **A space other than `&self` owns `+`**: it answers `(OwnedPlus 2 1)`, the
machine refuses and agrees, and a machine without the refusal answers `3`. -/
theorem unrefused_differs :
    canon ⟨false, [ownedPlus]⟩ builtin owned call = owned call ∧
      mayMatch ⟨false, [ownedPlus]⟩ "+" = true ∧
      builtin call ≠ owned call := by
  refine ⟨?_, by decide, by simp [builtin, owned]⟩
  unfold canon
  rw [if_neg (by decide), if_pos ⟨ownedPlus, List.mem_singleton_self _, ownedPlus_matches⟩]

/-- **In `&self` the builtin is protected**: the same equation there leaves `3`. -/
theorem self_protected : canon ⟨true, [ownedPlus]⟩ builtin owned call = [.num 3] := by
  unfold canon
  rw [if_pos rfl]
  rfl

end Controls

end Mettapedia.Machines.AdmissionRewriting.BuiltinOwnership
