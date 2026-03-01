import Mettapedia.Logic.LP.Core

/-!
# Function-Free Fragment of LP (Datalog Territory)

When `IsEmpty σ.functionSymbols`, all ground terms are constants and the Herbrand
universe is finite (given `Fintype σ.constants`).  This file provides:

- `GroundTerm.toConst` / `GroundTerm.ofConst` — equivalence `GroundTerm σ ≃ σ.constants`
- `Term.cases_functionFree` — every term is `var` or `const`
- `GroundAtom.ofFinArgs` — convenience constructor from `Fin n → σ.constants`

## LLM note: `GroundTerm` and `Term` have dependent `app` constructor — when eliminating
impossible cases under `[IsEmpty σ.functionSymbols]`, use explicit `casesOn`/`recOn`
with stated motive to avoid motive elaboration failures.

## References

- Lloyd, *Foundations of Logic Programming*, Ch. 1 (Datalog fragment)
- Tantow et al., *Certifying Datalog Reasoning in Lean 4*, ITP 2025
-/

namespace Mettapedia.Logic.LP

variable {σ : LPSignature} [hFF : IsEmpty σ.functionSymbols]

/-! ## Section 1: Ground terms are constants -/

/-- In a function-free signature, every ground term is a constant. -/
def GroundTerm.toConst (gt : GroundTerm σ) : σ.constants :=
  match gt with
  | .const c => c
  | .app f _ => hFF.false f |>.elim

/-- Lift a constant to a ground term. -/
def GroundTerm.ofConst (c : σ.constants) : GroundTerm σ := .const c

theorem GroundTerm.toConst_ofConst (c : σ.constants) :
    (GroundTerm.ofConst c : GroundTerm σ).toConst = c := rfl

/-- Use explicit `casesOn` to avoid dependent-motive elaboration failure. -/
theorem GroundTerm.ofConst_toConst (gt : GroundTerm σ) :
    GroundTerm.ofConst gt.toConst = gt :=
  @GroundTerm.casesOn σ (fun gt => GroundTerm.ofConst gt.toConst = gt) gt
    (fun _ => rfl)
    (fun f _ => (hFF.false f).elim)

/-- The equivalence `GroundTerm σ ≃ σ.constants` when the signature is function-free. -/
def GroundTerm.equivConst : GroundTerm σ ≃ σ.constants where
  toFun    := GroundTerm.toConst
  invFun   := GroundTerm.ofConst
  left_inv := GroundTerm.ofConst_toConst
  right_inv := GroundTerm.toConst_ofConst

instance [Fintype σ.constants] : Fintype (GroundTerm σ) :=
  Fintype.ofEquiv _ GroundTerm.equivConst.symm

instance [DecidableEq σ.constants] : DecidableEq (GroundTerm σ) :=
  Equiv.decidableEq GroundTerm.equivConst

/-- Decidable equality for ground atoms (dependent structure: symbol + args). -/
instance [DecidableEq σ.constants] [DecidableEq σ.relationSymbols] :
    DecidableEq (GroundAtom σ) := by
  intro a b
  cases a with | mk sa aa =>
  cases b with | mk sb ab =>
  by_cases h : sa = sb
  · subst h
    by_cases h2 : aa = ab
    · exact isTrue (by subst h2; rfl)
    · exact isFalse (fun hab => h2 (by cases hab; rfl))
  · exact isFalse (fun hab => h (by cases hab; rfl))

/-! ## Section 2: All terms are flat -/

/-- In a function-free signature, every term is either `var` or `const`. -/
theorem Term.cases_functionFree (t : Term σ) :
    (∃ v, t = .var v) ∨ (∃ c, t = .const c) :=
  @Term.casesOn σ (fun t => (∃ v, t = .var v) ∨ (∃ c, t = .const c)) t
    (fun v => Or.inl ⟨v, rfl⟩)
    (fun c => Or.inr ⟨c, rfl⟩)
    (fun f _ => (hFF.false f).elim)

/-! ## Section 3: Ground atoms with constant arguments -/

omit hFF in
/-- Build a ground atom from a relation symbol and constant-valued arguments. -/
def GroundAtom.ofFinArgs (r : σ.relationSymbols)
    (args : Fin (σ.relationArity r) → σ.constants) : GroundAtom σ where
  symbol := r
  args := fun i => .const (args i)

omit hFF in
/-- Round-trip: the symbol of `ofFinArgs r args` is `r`. -/
@[simp] theorem GroundAtom.ofFinArgs_symbol (r : σ.relationSymbols)
    (args : Fin (σ.relationArity r) → σ.constants) :
    (GroundAtom.ofFinArgs r args).symbol = r := rfl

/-- Every ground atom in a function-free signature equals `ofFinArgs` applied to its
    constant-extracted arguments. -/
theorem GroundAtom.eq_ofFinArgs (ga : GroundAtom σ) :
    ga = GroundAtom.ofFinArgs ga.symbol (fun i => (ga.args i).toConst) := by
  have h : ga.args = (GroundAtom.ofFinArgs ga.symbol (fun i => (ga.args i).toConst)).args := by
    funext i
    simp only [ofFinArgs]
    exact (GroundTerm.ofConst_toConst (ga.args i)).symm
  cases ga; simp only [ofFinArgs] at h ⊢; congr

end Mettapedia.Logic.LP
