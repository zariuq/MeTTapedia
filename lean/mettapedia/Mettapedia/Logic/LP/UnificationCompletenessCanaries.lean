import Mettapedia.Logic.LP.UnificationComplete

/-!
# Logic Programming Kernel: Unification Completeness Canaries

Finite FO fixtures for the global semantic completeness endpoint
`unifyFuel_exists_of_unifies`, with focused coverage of occurs-check behavior.
-/

namespace Mettapedia.Logic.LP

namespace UnificationCanaries

inductive UConst where
  | c0
  | c1
  deriving DecidableEq

inductive UVar where
  | x
  deriving DecidableEq

inductive URel where
  | r
  deriving DecidableEq

inductive UFun where
  | f
  deriving DecidableEq

def uSig : LPSignature where
  constants := UConst
  vars := UVar
  relationSymbols := URel
  relationArity := fun _ => 0
  functionSymbols := UFun
  functionArity := fun _ => 1

instance : DecidableEq uSig.vars := by
  intro a b
  cases a
  cases b
  exact isTrue rfl

instance : DecidableEq uSig.constants := by
  intro a b
  cases a <;> cases b <;>
    first | exact isTrue rfl | exact isFalse (by intro h; cases h)

instance : DecidableEq uSig.functionSymbols := by
  intro a b
  cases a
  cases b
  exact isTrue rfl

instance : DecidableEq uSig.relationSymbols := by
  intro a b
  cases a
  cases b
  exact isTrue rfl

def xTerm : Term uSig := .var UVar.x

def fxTerm : Term uSig := .app UFun.f (fun _ => .var UVar.x)

def fcTerm : Term uSig := .app UFun.f (fun _ => .const UConst.c0)

def eqOccurs : List (Term uSig × Term uSig) := [(xTerm, fxTerm)]

def eqNonOccurs : List (Term uSig × Term uSig) := [(xTerm, fcTerm)]

def eqConflict : List (Term uSig × Term uSig) :=
  [(.const UConst.c0, .const UConst.c1)]

/-- Operational negative canary at the same boundary: `unifyFuel` always rejects
`x = f(x)` for every fuel budget. -/
theorem canary_occurs_rejects_all_fuel (fuel : ℕ) :
    unifyFuel fuel eqOccurs = none := by
  cases fuel with
  | zero =>
      rfl
  | succ n =>
      simp [eqOccurs, xTerm, fxTerm, uSig, unifyFuel, Term.occursIn]

/-- Semantic negative canary at the occurs-check boundary: `x = f(x)` has no
first-order unifier. -/
theorem canary_occurs_semantic_negative :
    ¬ ∃ δ : Subst uSig, Unifies δ eqOccurs := by
  intro h
  rcases unifyFuel_exists_of_unifies (eqs := eqOccurs) h with ⟨fuel, θ, hθ⟩
  have hnone : unifyFuel fuel eqOccurs = none :=
    canary_occurs_rejects_all_fuel fuel
  rw [hnone] at hθ
  cases hθ

def deltaNonOccurs : Subst uSig := Subst.single UVar.x fcTerm

private theorem deltaNonOccurs_unifies_eqNonOccurs :
    Unifies deltaNonOccurs eqNonOccurs := by
  intro p hp
  simp [eqNonOccurs] at hp
  rcases hp with rfl
  simp [deltaNonOccurs, xTerm, fcTerm, Subst.applyTerm, Subst.single]

/-- Positive completeness canary: for the non-occurs equation `x = f(c0)`,
the global semantic endpoint produces executable success. -/
theorem canary_nonoccurs_semantic_complete :
    ∃ fuel : ℕ, ∃ θ : Subst uSig, unifyFuel fuel eqNonOccurs = some θ := by
  exact unifyFuel_exists_of_unifies (eqs := eqNonOccurs) ⟨deltaNonOccurs, deltaNonOccurs_unifies_eqNonOccurs⟩

/-- Sanity negative canary: constructor conflict (`c0 = c1`) is rejected for all fuel. -/
theorem canary_conflict_rejects_all_fuel (fuel : ℕ) :
    unifyFuel fuel eqConflict = none := by
  cases fuel with
  | zero =>
      rfl
  | succ n =>
      simp [eqConflict, uSig, unifyFuel]

end UnificationCanaries

end Mettapedia.Logic.LP
