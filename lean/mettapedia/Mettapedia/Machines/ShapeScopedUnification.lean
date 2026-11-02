import Mettapedia.Machines.NamedShapeGraph
import Mettapedia.Logic.LP.ConjunctiveUnification

/-!
# Scoped constraints from named shape rows

An open stored term is syntax over constants and variable markers. Markers
remain logic variables when used: storage canonicalization does not make them
rigid constants. Query and row activations each get one variable-renaming
scope. In particular, all holes of one row share the same scope.

The constraint compiler traverses aligned query/shape constructors directly,
then hands the resulting equations to the existing total first-order unifier.
It has exactly the solutions of the independently expanded equation and
returns an MGU. Its reference fallback materializes a subterm when a query
variable faces constructor structure; this is not yet a no-materialization
native unifier or a variable-normalization algorithm.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ShapeScopedUnification

open ShapeStore NamedShapeGraph
open Mettapedia.Logic.LP
open Mettapedia.Logic.LP.ConjunctiveUnification

variable {α Var Name : Type}

abbrev signature (α Var : Type) : LPSignature where
  constants := α
  vars := ScopedVar Var
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Unit
  functionArity := fun _ => 2

abbrev OpenTerm (α Var : Type) := Tm (α ⊕ Var)
abbrev View (α Var Name : Type) := Expr (α ⊕ Var) Name
abbrev LogicTerm (α Var : Type) := Term (signature α Var)

def pair (l r : LogicTerm α Var) : LogicTerm α Var := .app () ![l, r]

theorem pair_eq_iff (a b c d : LogicTerm α Var) :
    pair a b = pair c d ↔ a = c ∧ b = d := by
  constructor
  · intro equal
    have args := eq_of_heq (Term.app.inj equal).2
    exact ⟨congrFun args 0, congrFun args 1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem apply_pair (θ : Mettapedia.Logic.LP.Subst (signature α Var))
    (a b : LogicTerm α Var) :
    θ.applyTerm (pair a b) = pair (θ.applyTerm a) (θ.applyTerm b) := by
  unfold pair
  simp only [Subst.applyTerm]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The one scope is threaded through every constructor and every hole. -/
def encode (scope : Nat) : OpenTerm α Var → LogicTerm α Var
  | .atom (.inl a) => .const a
  | .atom (.inr v) => .var (ScopedVar.at scope v)
  | .node l r => pair (encode scope l) (encode scope r)

def decode : LogicTerm α Var → OpenTerm α (ScopedVar Var)
  | .const a => .atom (.inl a)
  | .var v => .atom (.inr v)
  | .app _ children => .node (decode (children 0)) (decode (children 1))

def rename (scope : Nat) : OpenTerm α Var → OpenTerm α (ScopedVar Var)
  | .atom (.inl a) => .atom (.inl a)
  | .atom (.inr v) => .atom (.inr (ScopedVar.at scope v))
  | .node l r => .node (rename scope l) (rename scope r)

theorem decode_encode (scope : Nat) (t : OpenTerm α Var) :
    decode (encode scope t) = rename scope t := by
  induction t with
  | atom a => cases a <;> rfl
  | node l r ihl ihr =>
      change Tm.node (decode (encode scope l)) (decode (encode scope r)) = _
      exact congrArg₂ Tm.node ihl ihr

/-- Constructor alignment emits smaller constraints without reconstructing
that constructor. Fallbacks include dereferencing a named hole. -/
def constraints (values : Name → OpenTerm α Var) (queryScope rowScope : Nat) :
    OpenTerm α Var → View α Var Name → Equations (signature α Var)
  | .node p q, .node l r =>
      constraints values queryScope rowScope p l ++ constraints values queryScope rowScope q r
  | p, e => [(encode queryScope p, encode rowScope (e.plug values))]

theorem unifies_single (θ : Mettapedia.Logic.LP.Subst (signature α Var))
    (p q : LogicTerm α Var) :
    Unifies θ [(p, q)] ↔ θ.applyTerm p = θ.applyTerm q := by
  simp [Unifies]

/-- All solutions, not just one returned answer, agree with full expansion. -/
theorem constraints_exact (values : Name → OpenTerm α Var) (queryScope rowScope : Nat)
    (p : OpenTerm α Var) (e : View α Var Name)
    (θ : Mettapedia.Logic.LP.Subst (signature α Var)) :
    Unifies θ (constraints values queryScope rowScope p e) ↔
      θ.applyTerm (encode queryScope p) = θ.applyTerm (encode rowScope (e.plug values)) := by
  induction e generalizing p with
  | atom a => cases p <;> simp only [constraints, unifies_single]
  | ref n => cases p <;> simp only [constraints, unifies_single]
  | node l r ihl ihr =>
      cases p with
      | atom a => exact unifies_single θ _ _
      | node p q =>
          simp only [constraints, unifies_append, ihl, ihr, Expr.plug, encode,
            apply_pair, pair_eq_iff]

section Solver

variable [DecidableEq α] [DecidableEq Var]

def solve (values : Name → OpenTerm α Var) (queryScope rowScope : Nat)
    (p : OpenTerm α Var) (e : View α Var Name) :
    Option (Mettapedia.Logic.LP.Subst (signature α Var)) :=
  unifyTotal (constraints values queryScope rowScope p e)

theorem solve_sound (values : Name → OpenTerm α Var) (queryScope rowScope : Nat)
    (p : OpenTerm α Var) (e : View α Var Name)
    (θ : Mettapedia.Logic.LP.Subst (signature α Var))
    (accepted : solve values queryScope rowScope p e = some θ) :
    θ.applyTerm (encode queryScope p) = θ.applyTerm (encode rowScope (e.plug values)) :=
  (constraints_exact values queryScope rowScope p e θ).mp
    (unifyTotal_sound _ θ accepted)

theorem solve_complete (values : Name → OpenTerm α Var) (queryScope rowScope : Nat)
    (p : OpenTerm α Var) (e : View α Var Name)
    (solvable : ∃ θ : Mettapedia.Logic.LP.Subst (signature α Var),
      θ.applyTerm (encode queryScope p) = θ.applyTerm (encode rowScope (e.plug values))) :
    ∃ θ, solve values queryScope rowScope p e = some θ := by
  obtain ⟨θ, solved⟩ := solvable
  exact unifyTotal_complete ⟨θ, (constraints_exact values queryScope rowScope p e θ).mpr solved⟩

theorem solve_mgu (values : Name → OpenTerm α Var) (queryScope rowScope : Nat)
    (p : OpenTerm α Var) (e : View α Var Name)
    (θ candidate : Mettapedia.Logic.LP.Subst (signature α Var))
    (accepted : solve values queryScope rowScope p e = some θ)
    (solved : candidate.applyTerm (encode queryScope p) =
      candidate.applyTerm (encode rowScope (e.plug values))) : θ.moreGeneral candidate :=
  unifyTotal_mgu _ θ accepted candidate
    ((constraints_exact values queryScope rowScope p e candidate).mpr solved)

omit [DecidableEq α] [DecidableEq Var] in
/-- A change of shape and hole placement preserves solvability. Raw MGU
functions may differ, so comparison is by their factorization property. -/
theorem recut_same_solutions (values₁ values₂ : Name → OpenTerm α Var)
    (e₁ e₂ : View α Var Name) (same : e₁.plug values₁ = e₂.plug values₂)
    (queryScope rowScope : Nat) (p : OpenTerm α Var)
    (θ : Mettapedia.Logic.LP.Subst (signature α Var)) :
    Unifies θ (constraints values₁ queryScope rowScope p e₁) ↔
      Unifies θ (constraints values₂ queryScope rowScope p e₂) := by
  rw [constraints_exact, constraints_exact, same]

/-- Successful staged and expanded solvers return mutually factoring MGUs. -/
theorem staged_expanded_mgus (values : Name → OpenTerm α Var) (queryScope rowScope : Nat)
    (p : OpenTerm α Var) (e : View α Var Name)
    (staged expanded : Mettapedia.Logic.LP.Subst (signature α Var))
    (hs : solve values queryScope rowScope p e = some staged)
    (he : unifyTotal [(encode queryScope p, encode rowScope (e.plug values))] = some expanded) :
    staged.moreGeneral expanded ∧ expanded.moreGeneral staged := by
  refine ⟨solve_mgu values queryScope rowScope p e staged expanded hs ?_, ?_⟩
  · exact (unifies_single expanded _ _).mp (unifyTotal_sound _ expanded he)
  · exact unifyTotal_mgu _ expanded he staged
      ((unifies_single staged _ _).mpr (solve_sound values queryScope rowScope p e staged hs))

end Solver

namespace Controls

abbrev Sig := signature Bool Nat
def a : LogicTerm Bool Nat := .const false
def b : LogicTerm Bool Nat := .const true
def logicVar (scope : Nat) : LogicTerm Bool Nat := .var (ScopedVar.at scope 0)

def repeated : View Bool Nat Bool := .node (.ref false) (.ref true)
def holeValues (_ : Bool) : OpenTerm Bool Nat := .atom (.inr 0)
def query : OpenTerm Bool Nat := .node (.atom (.inl false)) (.atom (.inl true))

/-- Two holes containing the same row variable cannot be solved independently. -/
theorem shared_row_refused : solve holeValues 0 1 query repeated = none := by
  cases accepted : solve holeValues 0 1 query repeated with
  | none => rfl
  | some θ =>
      have h := solve_sound holeValues 0 1 query repeated θ accepted
      simp only [query, repeated, Expr.plug, holeValues, encode, apply_pair,
        Subst.applyTerm_const, Subst.applyTerm_var, pair_eq_iff] at h
      have impossible := h.1.trans h.2.symm
      cases impossible

/-- The incorrect per-hole freshening accepts this inconsistent row. -/
theorem freshening_per_hole_is_wrong :
    ∃ θ : Mettapedia.Logic.LP.Subst Sig,
      Unifies θ [(a, logicVar 1), (b, logicVar 2)] := by
  refine ⟨fun v => if v.scope = 1 then a else b, ?_⟩
  intro equation member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

theorem open_marker_is_not_rigid :
    (∃ θ : Mettapedia.Logic.LP.Subst Sig, θ.applyTerm (logicVar 1) = θ.applyTerm a) ∧
    ¬ ∃ θ : Mettapedia.Logic.LP.Subst Sig, θ.applyTerm b = θ.applyTerm a := by
  refine ⟨⟨fun _ => a, rfl⟩, ?_⟩
  rintro ⟨θ, impossible⟩
  cases impossible

theorem occurs_check_needed :
    ¬ ∃ θ : Mettapedia.Logic.LP.Subst Sig,
      θ.applyTerm (logicVar 1) = θ.applyTerm (pair (logicVar 1) a) := by
  rintro ⟨θ, equal⟩
  rw [apply_pair] at equal
  have lower := Term.size_subterm (σ := Sig)
    (f := ()) (ts := ![θ.applyTerm (logicVar 1), θ.applyTerm a]) 0
  change (θ.applyTerm (logicVar 1)).size < (pair (θ.applyTerm (logicVar 1)) (θ.applyTerm a)).size at lower
  rw [← equal] at lower
  omega

example : ScopedVar.at 1 (0 : Nat) ≠ ScopedVar.at 2 0 := by decide

end Controls

#print axioms constraints_exact
#print axioms solve_sound
#print axioms solve_complete
#print axioms solve_mgu
#print axioms staged_expanded_mgus
#print axioms Controls.shared_row_refused

end Mettapedia.Machines.ShapeScopedUnification
