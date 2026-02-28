import Mettapedia.Logic.LP.Substitution
import Mathlib.Algebra.BigOperators.Fin

/-!
# Logic Programming Kernel: Matching (One-Sided Unification)

Matching is the restriction of unification where only one side may contain
variables.  Given a pattern `p` and a ground target `t`, matching finds
`θ` such that `θ(p) = t`.  This is used in:

- Bottom-up evaluation (T_P): matching rule heads against ground atoms.
- Clause selection in SLD resolution (before full unification is needed).

## Design

We collect variable bindings as a `List (σ.vars × GroundTerm σ)`, then build
a `Subst σ`.  Iteration over Fin-indexed subterms converts to `List` for clean
structural recursion on pairs of lists.  Termination uses the sum of `Term.size`
across the pattern list.

## References

- Lloyd, *Foundations of Logic Programming*, Ch. 1 (matching in T_P)
-/

namespace Mettapedia.Logic.LP

/-! ## Section 1: Fin-to-List utilities -/

/-- Convert a Fin-indexed family to a list. -/
def finToList {α : Type*} {n : ℕ} (f : Fin n → α) : List α :=
  (List.finRange n).map f

@[simp]
theorem finToList_length {α : Type*} {n : ℕ} (f : Fin n → α) :
    (finToList f).length = n := by
  simp [finToList]

/-! ## Section 2: Total pattern size (termination measure) -/

/-- Total term size of a list of patterns. -/
def patternListSize {σ : LPSignature} (ps : List (Term σ)) : ℕ :=
  (ps.map Term.size).sum

private theorem patternListSize_cons {σ : LPSignature} (p : Term σ) (ps : List (Term σ)) :
    patternListSize (p :: ps) = p.size + patternListSize ps := by
  simp [patternListSize]

private theorem patternListSize_append {σ : LPSignature}
    (ps qs : List (Term σ)) :
    patternListSize (ps ++ qs) = patternListSize ps + patternListSize qs := by
  simp [patternListSize, List.map_append, List.sum_append]

private theorem patternListSize_finToList {σ : LPSignature} {n : ℕ}
    (ts : Fin n → Term σ) :
    patternListSize (finToList ts) = ∑ i : Fin n, (ts i).size := by
  simp only [patternListSize, finToList, List.map_map, Fin.sum_univ_def]
  rfl

private theorem patternListSize_finToList_app {σ : LPSignature}
    (f : σ.functionSymbols) (ts : Fin (σ.functionArity f) → Term σ)
    (ps : List (Term σ)) :
    patternListSize (finToList ts ++ ps) < patternListSize (Term.app f ts :: ps) := by
  rw [patternListSize_append, patternListSize_cons, Term.size, patternListSize_finToList]
  omega

/-! ## Section 3: Binding collection -/

/-- Collect bindings from paired lists of pattern and ground terms. -/
def collectBindingsList {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols]
    (ps : List (Term σ)) (gs : List (GroundTerm σ)) :
    Option (List (σ.vars × GroundTerm σ)) :=
  match ps, gs with
  | [], [] => some []
  | .var v :: ps', g :: gs' => do
    let rest ← collectBindingsList ps' gs'
    return (v, g) :: rest
  | .const c :: ps', .const c' :: gs' =>
    if c = c' then collectBindingsList ps' gs' else none
  | .const _ :: _, .app _ _ :: _ => none
  | .app _ _ :: _, .const _ :: _ => none
  | .app f ts :: ps', .app g us :: gs' =>
    if h : f = g then
      collectBindingsList (finToList ts ++ ps') (finToList (h ▸ us) ++ gs')
    else none
  | [], _ :: _ => none
  | _ :: _, [] => none
termination_by patternListSize ps
decreasing_by
  all_goals simp only [patternListSize_cons]
  · have := Term.size_pos (.var v); omega
  · have := Term.size_pos (.const c); omega
  · rw [← patternListSize_cons]; exact patternListSize_finToList_app _ _ _

/-- Collect bindings by matching a pattern term against a ground term. -/
def collectBindings {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] (p : Term σ) (gt : GroundTerm σ) :
    Option (List (σ.vars × GroundTerm σ)) :=
  collectBindingsList [p] [gt]

/-- Collect bindings for an atom against a ground atom. -/
def collectAtomBindings {σ : LPSignature} [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
    (a : Atom σ) (ga : GroundAtom σ) :
    Option (List (σ.vars × GroundTerm σ)) :=
  if h : a.symbol = ga.symbol then
    collectBindingsList (finToList a.args) (finToList (h ▸ ga.args))
  else none

/-! ## Section 4: Substitution construction -/

/-- Build a substitution from a binding list. First binding for each variable wins. -/
def bindingsToSubst {σ : LPSignature} [DecidableEq σ.vars]
    (bs : List (σ.vars × GroundTerm σ)) : Subst σ :=
  fun v => match bs.find? (fun p => p.1 == v) with
    | some (_, gt) => gt.toTerm
    | none => .var v

/-- A binding list is consistent if each variable maps to a unique ground term. -/
def BindingsConsistent {σ : LPSignature} (bs : List (σ.vars × GroundTerm σ)) : Prop :=
  ∀ v g₁ g₂, (v, g₁) ∈ bs → (v, g₂) ∈ bs → g₁ = g₂

/-! ## Section 5: Full matching interface -/

/-- Result of a matching attempt. -/
inductive MatchResult (σ : LPSignature) where
  | success : Subst σ → MatchResult σ
  | failure : MatchResult σ

/-- Match a pattern term against a ground term. -/
def matchTerm {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] :
    Term σ → GroundTerm σ → MatchResult σ
  | p, gt =>
    match collectBindings p gt with
    | none => .failure
    | some bs => .success (bindingsToSubst bs)

/-- Match a pattern atom against a ground atom. -/
def matchAtom {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
    [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols] :
    Atom σ → GroundAtom σ → MatchResult σ
  | a, ga =>
    match collectAtomBindings a ga with
    | none => .failure
    | some bs => .success (bindingsToSubst bs)

end Mettapedia.Logic.LP
