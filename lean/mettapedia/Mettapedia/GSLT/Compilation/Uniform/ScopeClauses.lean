import Mettapedia.GSLT.Compilation.Uniform.UnificationClauses
import Mettapedia.GSLT.Compilation.Uniform.PatternRows

/-!
# Lifting and instantiating indices, as clauses

Terms are locally nameless: a bound occurrence is the index of its binder, counted outward. Two operations move
terms between scopes (`Substitution.liftBVars`, `Substitution.instantiateBVarAt`):

* lifting adds a shift to every index at or beyond a cutoff;
* instantiating replaces the index of one binder by a term, lifted to the depth where it lands, and lowers the
  indices beyond it.

Both are clauses over rows here, with numbers as numerals, beside two clauses of numbers (at most, adding). The
clauses derive exactly the two operations (`lift_iff`, `instantiate_iff`).

Lowering is the converse of lifting, as clauses of its own (`lowerClauses`): a lowered term lifts back to the term it
came from, and every lift is lowered (`lower_lift`, `lift_lower`). An index lowers by subtracting the shift, which is
checked by adding it back.

Abstracting is the converse of instantiating, as clauses of their own (`abstractClauses`): where the instance holds the
substituted term, lifted to its depth, the abstraction may put the index back. The clauses derive exactly the terms
that instantiate to a given term (`abstract_iff`), and each derivation is a derivation of instantiating read backwards
(`abstract_instantiate`, `instantiate_abstract`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.ScopeClauses

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars liftBVarsList instantiateBVarAt)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic
open RuleSyntax.ComputedConditions (Relations)
open RootRewritesOnTheStep (symTerm appTerm encode encodeList numeral)
open DemandTransformation (Goal Clause Moded goalHolds DerivesAt Derives derives_of_clause pick)
open UnificationClauses (unit triple)
open PatternRows (numeral_zero_inv numeral_succ_inv encode_bvar_inv encode_fvar_inv encode_apply_inv
  encode_lambda_inv encode_multiLambda_inv encode_subst_inv encode_collection_inv encodeList_nil_inv
  encodeList_cons_inv)

/-! ## The clauses -/

/-- The row pattern of a successor. -/
def succTerm (n : Tm) : Tm := appTerm (symTerm 1) n

/-- The row pattern of a bound occurrence. -/
def bvarTerm (n : Tm) : Tm := appTerm (symTerm 0) n

/-- The relation of two numbers in order. -/
def atMostRelation : ℕ := 28

/-- The relation of adding two numbers. -/
def addRelation : ℕ := 29

/-- The relation of lifting the indices of a term. -/
def liftRelation : ℕ := 30

/-- The relation of lifting the indices of a list of terms. -/
def liftListRelation : ℕ := 31

/-- The relation of instantiating an index of a term. -/
def instantiateRelation : ℕ := 32

/-- The relation of instantiating an index of a list of terms. -/
def instantiateListRelation : ℕ := 33

def atMostZero : Clause :=
  { relation := atMostRelation, input := appTerm (symTerm 0) (.var 0), output := unit, body := [] }

def atMostSucc : Clause :=
  { relation := atMostRelation, input := appTerm (succTerm (.var 0)) (succTerm (.var 1)), output := unit,
    body := [.ask atMostRelation (appTerm (.var 0) (.var 1)) unit] }

def addZero : Clause :=
  { relation := addRelation, input := appTerm (symTerm 0) (.var 0), output := .var 0, body := [] }

def addSucc : Clause :=
  { relation := addRelation, input := appTerm (succTerm (.var 0)) (.var 1), output := succTerm (.var 2),
    body := [.ask addRelation (appTerm (.var 0) (.var 1)) (.var 2)] }

/-- An index below the cutoff stays. -/
def liftBelow : Clause :=
  { relation := liftRelation, input := triple (.var 0) (.var 1) (bvarTerm (.var 2)), output := bvarTerm (.var 2),
    body := [.ask atMostRelation (appTerm (succTerm (.var 2)) (.var 0)) unit] }

/-- An index at or beyond the cutoff is shifted. -/
def liftAbove : Clause :=
  { relation := liftRelation, input := triple (.var 0) (.var 1) (bvarTerm (.var 2)), output := bvarTerm (.var 3),
    body := [.ask atMostRelation (appTerm (.var 0) (.var 2)) unit,
      .ask addRelation (appTerm (.var 2) (.var 1)) (.var 3)] }

def liftFvar : Clause :=
  { relation := liftRelation, input := triple (.var 0) (.var 1) (appTerm (symTerm 1) (.var 2)),
    output := appTerm (symTerm 1) (.var 2), body := [] }

def liftApply : Clause :=
  { relation := liftRelation, input := triple (.var 0) (.var 1) (appTerm (symTerm 2) (appTerm (.var 2) (.var 3))),
    output := appTerm (symTerm 2) (appTerm (.var 2) (.var 4)),
    body := [.ask liftListRelation (triple (.var 0) (.var 1) (.var 3)) (.var 4)] }

def liftLambda : Clause :=
  { relation := liftRelation, input := triple (.var 0) (.var 1) (appTerm (symTerm 3) (appTerm (.var 2) (.var 3))),
    output := appTerm (symTerm 3) (appTerm (.var 2) (.var 4)),
    body := [.ask liftRelation (triple (succTerm (.var 0)) (.var 1) (.var 3)) (.var 4)] }

def liftMultiLambda : Clause :=
  { relation := liftRelation,
    input := triple (.var 0) (.var 1) (appTerm (symTerm 4) (appTerm (.var 2) (appTerm (.var 3) (.var 4)))),
    output := appTerm (symTerm 4) (appTerm (.var 2) (appTerm (.var 3) (.var 6))),
    body := [.ask addRelation (appTerm (.var 0) (.var 2)) (.var 5),
      .ask liftRelation (triple (.var 5) (.var 1) (.var 4)) (.var 6)] }

def liftSubst : Clause :=
  { relation := liftRelation, input := triple (.var 0) (.var 1) (appTerm (symTerm 5) (appTerm (.var 2) (.var 3))),
    output := appTerm (symTerm 5) (appTerm (.var 4) (.var 5)),
    body := [.ask liftRelation (triple (succTerm (.var 0)) (.var 1) (.var 2)) (.var 4),
      .ask liftRelation (triple (.var 0) (.var 1) (.var 3)) (.var 5)] }

def liftCollection : Clause :=
  { relation := liftRelation,
    input := triple (.var 0) (.var 1) (appTerm (symTerm 6) (appTerm (.var 2) (appTerm (.var 3) (.var 4)))),
    output := appTerm (symTerm 6) (appTerm (.var 2) (appTerm (.var 5) (.var 4))),
    body := [.ask liftListRelation (triple (.var 0) (.var 1) (.var 3)) (.var 5)] }

def liftNil : Clause :=
  { relation := liftListRelation, input := triple (.var 0) (.var 1) (symTerm 0), output := symTerm 0, body := [] }

def liftCons : Clause :=
  { relation := liftListRelation, input := triple (.var 0) (.var 1) (appTerm (.var 2) (.var 3)),
    output := appTerm (.var 4) (.var 5),
    body := [.ask liftRelation (triple (.var 0) (.var 1) (.var 2)) (.var 4),
      .ask liftListRelation (triple (.var 0) (.var 1) (.var 3)) (.var 5)] }

/-- An index below the instantiated one stays. -/
def instantiateBelow : Clause :=
  { relation := instantiateRelation, input := triple (.var 0) (.var 1) (bvarTerm (.var 2)),
    output := bvarTerm (.var 2), body := [.ask atMostRelation (appTerm (succTerm (.var 2)) (.var 0)) unit] }

/-- The instantiated index becomes the term, lifted to where it lands. -/
def instantiateHere : Clause :=
  { relation := instantiateRelation, input := triple (.var 0) (.var 1) (bvarTerm (.var 0)), output := .var 2,
    body := [.ask liftRelation (triple (symTerm 0) (.var 0) (.var 1)) (.var 2)] }

/-- An index beyond the instantiated one is lowered. -/
def instantiateAbove : Clause :=
  { relation := instantiateRelation, input := triple (.var 0) (.var 1) (bvarTerm (succTerm (.var 2))),
    output := bvarTerm (.var 2), body := [.ask atMostRelation (appTerm (.var 0) (.var 2)) unit] }

def instantiateFvar : Clause :=
  { relation := instantiateRelation, input := triple (.var 0) (.var 1) (appTerm (symTerm 1) (.var 2)),
    output := appTerm (symTerm 1) (.var 2), body := [] }

def instantiateApply : Clause :=
  { relation := instantiateRelation,
    input := triple (.var 0) (.var 1) (appTerm (symTerm 2) (appTerm (.var 2) (.var 3))),
    output := appTerm (symTerm 2) (appTerm (.var 2) (.var 4)),
    body := [.ask instantiateListRelation (triple (.var 0) (.var 1) (.var 3)) (.var 4)] }

def instantiateLambda : Clause :=
  { relation := instantiateRelation,
    input := triple (.var 0) (.var 1) (appTerm (symTerm 3) (appTerm (.var 2) (.var 3))),
    output := appTerm (symTerm 3) (appTerm (.var 2) (.var 4)),
    body := [.ask instantiateRelation (triple (succTerm (.var 0)) (.var 1) (.var 3)) (.var 4)] }

def instantiateMultiLambda : Clause :=
  { relation := instantiateRelation,
    input := triple (.var 0) (.var 1) (appTerm (symTerm 4) (appTerm (.var 2) (appTerm (.var 3) (.var 4)))),
    output := appTerm (symTerm 4) (appTerm (.var 2) (appTerm (.var 3) (.var 6))),
    body := [.ask addRelation (appTerm (.var 0) (.var 2)) (.var 5),
      .ask instantiateRelation (triple (.var 5) (.var 1) (.var 4)) (.var 6)] }

def instantiateSubst : Clause :=
  { relation := instantiateRelation,
    input := triple (.var 0) (.var 1) (appTerm (symTerm 5) (appTerm (.var 2) (.var 3))),
    output := appTerm (symTerm 5) (appTerm (.var 4) (.var 5)),
    body := [.ask instantiateRelation (triple (succTerm (.var 0)) (.var 1) (.var 2)) (.var 4),
      .ask instantiateRelation (triple (.var 0) (.var 1) (.var 3)) (.var 5)] }

def instantiateCollection : Clause :=
  { relation := instantiateRelation,
    input := triple (.var 0) (.var 1) (appTerm (symTerm 6) (appTerm (.var 2) (appTerm (.var 3) (.var 4)))),
    output := appTerm (symTerm 6) (appTerm (.var 2) (appTerm (.var 5) (.var 4))),
    body := [.ask instantiateListRelation (triple (.var 0) (.var 1) (.var 3)) (.var 5)] }

def instantiateNil : Clause :=
  { relation := instantiateListRelation, input := triple (.var 0) (.var 1) (symTerm 0), output := symTerm 0,
    body := [] }

def instantiateCons : Clause :=
  { relation := instantiateListRelation, input := triple (.var 0) (.var 1) (appTerm (.var 2) (.var 3)),
    output := appTerm (.var 4) (.var 5),
    body := [.ask instantiateRelation (triple (.var 0) (.var 1) (.var 2)) (.var 4),
      .ask instantiateListRelation (triple (.var 0) (.var 1) (.var 3)) (.var 5)] }

/-- **The clauses of scopes**: numbers, lifting, instantiating. -/
def scopeClauses : List Clause :=
  [atMostZero, atMostSucc, addZero, addSucc, liftBelow, liftAbove, liftFvar, liftApply, liftLambda, liftMultiLambda,
    liftSubst, liftCollection, liftNil, liftCons, instantiateBelow, instantiateHere, instantiateAbove,
    instantiateFvar, instantiateApply, instantiateLambda, instantiateMultiLambda, instantiateSubst,
    instantiateCollection, instantiateNil, instantiateCons]

theorem scopeClauses_moded : ∀ c ∈ scopeClauses, Moded c := by
  intro c inside
  simp only [scopeClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact DemandTransformation.moded_of_check (by decide)

theorem scopeClauses_relation :
    ∀ c ∈ scopeClauses, atMostRelation ≤ c.relation ∧ c.relation ≤ instantiateListRelation := by decide

/-- **A program with the clauses of scopes.** -/
structure ScopeProgram (program : List Clause) : Prop where
  included : ∀ c ∈ scopeClauses, c ∈ program
  only : ∀ c ∈ program, atMostRelation ≤ c.relation → c.relation ≤ instantiateListRelation → c ∈ scopeClauses

/-! ## Numbers -/

section Clauses

variable {R : Relations} {program : List Clause}

theorem scopeClause_of (scope : ScopeProgram program) {c : Clause} (member : c ∈ program) {r : ℕ}
    (isR : c.relation = r) (low : atMostRelation ≤ r) (high : r ≤ instantiateListRelation) : c ∈ scopeClauses :=
  scope.only c member (isR ▸ low) (isR ▸ high)

/-- **Numbers in order are derived in order.** -/
theorem atMost_sound (scope : ScopeProgram program) : ∀ (depth m n : ℕ) (w : Expr),
    DerivesAt R program depth atMostRelation (.app (numeral m) (numeral n)) w → m ≤ n
  | 0, _, _, _, derived => derived.elim
  | depth + 1, m, n, w, derived => by
      obtain ⟨c, member, isR, θ, input, output, goals⟩ := derived
      have inside := scopeClause_of scope member isR (le_refl _) (by decide)
      simp only [scopeClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact absurd isR (by decide)
        | skip
      · simp only [atMostZero, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown, Expr.app.injEq] at input
        rw [numeral_zero_inv input.1]
        exact Nat.zero_le _
      · simp only [atMostSucc, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown, Expr.app.injEq] at input
        obtain ⟨mIs, nIs⟩ := input
        obtain ⟨m', rfl, m'Is⟩ := numeral_succ_inv mIs
        obtain ⟨n', rfl, n'Is⟩ := numeral_succ_inv nIs
        have asked := goals _ List.mem_cons_self
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, m'Is,
          n'Is] at asked
        exact Nat.succ_le_succ (atMost_sound scope depth m' n' _ asked)

theorem atMost_complete (scope : ScopeProgram program) :
    ∀ (m n : ℕ), m ≤ n → Derives R program atMostRelation (.app (numeral m) (numeral n)) (.sym 0)
  | 0, n, _ => by
      have clause := derives_of_clause (R := R) (scope.included atMostZero (by simp [scopeClauses]))
        (pick [numeral n]) (fun _ inside => absurd inside List.not_mem_nil)
      simpa [atMostZero, pick, unit, numeral] using clause
  | m + 1, 0, le => absurd le (by omega)
  | m + 1, n + 1, le => by
      have inner := atMost_complete scope m n (by omega)
      have clause := derives_of_clause (R := R) (scope.included atMostSucc (by simp [scopeClauses]))
        (pick [numeral m, numeral n]) (fun g inside => by
          simp only [atMostSucc, List.mem_cons, List.not_mem_nil, or_false] at inside
          subst inside
          simpa [goalHolds, pick, unit] using inner)
      simpa [atMostSucc, succTerm, pick, unit, numeral] using clause

/-- **A derived sum is the sum.** -/
theorem add_sound (scope : ScopeProgram program) : ∀ (depth m n : ℕ) (w : Expr),
    DerivesAt R program depth addRelation (.app (numeral m) (numeral n)) w → w = numeral (m + n)
  | 0, _, _, _, derived => derived.elim
  | depth + 1, m, n, w, derived => by
      obtain ⟨c, member, isR, θ, input, output, goals⟩ := derived
      have inside := scopeClause_of scope member isR (by decide) (by decide)
      simp only [scopeClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact absurd isR (by decide)
        | skip
      · simp only [addZero, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown, Expr.app.injEq] at input output
        rw [numeral_zero_inv input.1, ← output, input.2, Nat.zero_add]
      · simp only [addSucc, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown, Expr.app.injEq] at input output
        obtain ⟨mIs, nIs⟩ := input
        obtain ⟨m', rfl, m'Is⟩ := numeral_succ_inv mIs
        have asked := goals _ List.mem_cons_self
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, m'Is,
          nIs] at asked
        rw [← output, add_sound scope depth m' n _ asked, Nat.succ_add]
        rfl

theorem add_complete (scope : ScopeProgram program) :
    ∀ (m n : ℕ), Derives R program addRelation (.app (numeral m) (numeral n)) (numeral (m + n))
  | 0, n => by
      have clause := derives_of_clause (R := R) (scope.included addZero (by simp [scopeClauses]))
        (pick [numeral n]) (fun _ inside => absurd inside List.not_mem_nil)
      simpa [addZero, pick, numeral] using clause
  | m + 1, n => by
      have inner := add_complete scope m n
      have clause := derives_of_clause (R := R) (scope.included addSucc (by simp [scopeClauses]))
        (pick [numeral m, numeral n, numeral (m + n)]) (fun g inside => by
          simp only [addSucc, List.mem_cons, List.not_mem_nil, or_false] at inside
          subst inside
          simpa [goalHolds, pick] using inner)
      rw [Nat.succ_add]
      simpa [addSucc, succTerm, pick, numeral] using clause

/-! ## Lifting -/

mutual
  /-- **A derived lift of a term is its lift.** -/
  theorem lift_sound (scope : ScopeProgram program) : ∀ (depth c s : ℕ) (p : Pattern) (w : Expr),
      DerivesAt R program depth liftRelation (.app (.app (numeral c) (numeral s)) (encode p)) w →
        w = encode (liftBVars c s p)
    | 0, _, _, _, _, derived => derived.elim
    | depth + 1, c, s, p, w, derived => by
        obtain ⟨cl, member, isR, θ, input, output, goals⟩ := derived
        have inside := scopeClause_of scope member isR (by decide) (by decide)
        simp only [scopeClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first
          | exact absurd isR (by decide)
          | skip
        · simp only [liftBelow, triple, bvarTerm, RootRewritesOnTheStep.inst_appTerm,
            RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨cIs, -⟩, pIs⟩ := input
          obtain ⟨index, rfl, indexIs⟩ := encode_bvar_inv pIs
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, indexIs, cIs] at asked
          have below := atMost_sound scope depth (index + 1) c _ asked
          rw [← output, indexIs]
          simp [liftBVars, show ¬ c ≤ index by omega, encode]
        · simp only [liftAbove, triple, bvarTerm, RootRewritesOnTheStep.inst_appTerm,
            RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨cIs, sIs⟩, pIs⟩ := input
          obtain ⟨index, rfl, indexIs⟩ := encode_bvar_inv pIs
          have first := goals _ List.mem_cons_self
          have second := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, indexIs, cIs,
            sIs] at first second
          have above := atMost_sound scope depth c index _ first
          rw [← output, add_sound scope depth index s _ second]
          simp [liftBVars, show c ≤ index by omega, encode]
        · simp only [liftFvar, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨-, pIs⟩ := input
          obtain ⟨name, rfl, nameIs⟩ := encode_fvar_inv pIs
          rw [← output, nameIs]
          rfl
        · simp only [liftApply, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨cIs, sIs⟩, pIs⟩ := input
          obtain ⟨label, arguments, rfl, labelIs, argumentsIs⟩ := encode_apply_inv pIs
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, cIs,
            sIs, argumentsIs] at asked
          rw [← output, labelIs, liftList_sound scope depth c s arguments _ asked]
          simp [liftBVars, encode]
        · simp only [liftLambda, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨cIs, sIs⟩, pIs⟩ := input
          obtain ⟨binder, body, rfl, binderIs, bodyIs⟩ := encode_lambda_inv pIs
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, succTerm, RootRewritesOnTheStep.inst_appTerm,
            RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, cIs, sIs, bodyIs] at asked
          rw [← output, binderIs, lift_sound scope depth (c + 1) s body _ asked]
          simp [liftBVars, encode]
        · simp only [liftMultiLambda, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨cIs, sIs⟩, pIs⟩ := input
          obtain ⟨arity, binders, body, rfl, arityIs, bindersIs, bodyIs⟩ := encode_multiLambda_inv pIs
          have first := goals _ List.mem_cons_self
          have second := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, cIs,
            arityIs] at first
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, sIs,
            bodyIs, add_sound scope depth c arity _ first] at second
          rw [← output, arityIs, bindersIs, lift_sound scope depth (c + arity) s body _ second]
          simp [liftBVars, encode]
        · simp only [liftSubst, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨cIs, sIs⟩, pIs⟩ := input
          obtain ⟨body, value, rfl, bodyIs, valueIs⟩ := encode_subst_inv pIs
          have first := goals _ List.mem_cons_self
          have second := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, triple, succTerm, RootRewritesOnTheStep.inst_appTerm,
            RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, cIs, sIs, bodyIs,
            valueIs] at first second
          rw [← output, lift_sound scope depth (c + 1) s body _ first, lift_sound scope depth c s value _ second]
          simp [liftBVars, encode]
        · simp only [liftCollection, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨cIs, sIs⟩, pIs⟩ := input
          obtain ⟨kind, elements, rest, rfl, kindIs, elementsIs, restIs⟩ := encode_collection_inv pIs
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, cIs,
            sIs, elementsIs] at asked
          rw [← output, kindIs, restIs, liftList_sound scope depth c s elements _ asked]
          simp [liftBVars, encode]

  theorem liftList_sound (scope : ScopeProgram program) : ∀ (depth c s : ℕ) (ps : List Pattern) (w : Expr),
      DerivesAt R program depth liftListRelation (.app (.app (numeral c) (numeral s)) (encodeList ps)) w →
        w = encodeList (ps.map (liftBVars c s))
    | 0, _, _, _, _, derived => derived.elim
    | depth + 1, c, s, ps, w, derived => by
        obtain ⟨cl, member, isR, θ, input, output, goals⟩ := derived
        have inside := scopeClause_of scope member isR (by decide) (by decide)
        simp only [scopeClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first
          | exact absurd isR (by decide)
          | skip
        · simp only [liftNil, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨-, psIs⟩ := input
          rw [encodeList_nil_inv psIs, ← output]
          rfl
        · simp only [liftCons, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
            Expr.app.injEq] at input output
          obtain ⟨⟨cIs, sIs⟩, psIs⟩ := input
          obtain ⟨x, rest, rfl, xIs, restIs⟩ := encodeList_cons_inv psIs
          have first := goals _ List.mem_cons_self
          have second := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, cIs,
            sIs, xIs, restIs] at first second
          rw [← output, lift_sound scope depth c s x _ first, liftList_sound scope depth c s rest _ second]
          rfl
end

mutual
  /-- **Every lift of a term is derived.** -/
  theorem lift_complete (scope : ScopeProgram program) (c s : ℕ) : ∀ p : Pattern,
      Derives R program liftRelation (.app (.app (numeral c) (numeral s)) (encode p)) (encode (liftBVars c s p))
    | .bvar index => by
        by_cases above : c ≤ index
        · have ordered := atMost_complete (R := R) scope c index above
          have added := add_complete (R := R) scope index s
          have clause := derives_of_clause (R := R) (scope.included liftAbove (by simp [scopeClauses]))
            (pick [numeral c, numeral s, numeral index, numeral (index + s)]) (fun g inside => by
              simp only [liftAbove, List.mem_cons, List.not_mem_nil, or_false] at inside
              rcases inside with rfl | rfl
              · simpa [goalHolds, pick, unit] using ordered
              · simpa [goalHolds, pick] using added)
          simpa [liftAbove, triple, bvarTerm, pick, encode, liftBVars, above] using clause
        · have ordered := atMost_complete (R := R) scope (index + 1) c (by omega)
          have clause := derives_of_clause (R := R) (scope.included liftBelow (by simp [scopeClauses]))
            (pick [numeral c, numeral s, numeral index]) (fun g inside => by
              simp only [liftBelow, List.mem_cons, List.not_mem_nil, or_false] at inside
              subst inside
              simpa [goalHolds, succTerm, pick, unit, numeral] using ordered)
          simpa [liftBelow, triple, bvarTerm, pick, encode, liftBVars, above] using clause
    | .fvar name => by
        have clause := derives_of_clause (R := R) (scope.included liftFvar (by simp [scopeClauses]))
          (pick [numeral c, numeral s, .sym (RootRewritesOnTheStep.labelCode name)])
          (fun _ inside => absurd inside List.not_mem_nil)
        simpa [liftFvar, triple, pick, encode, liftBVars] using clause
    | .apply label arguments => by
        have inner := liftList_complete scope c s arguments
        have clause := derives_of_clause (R := R) (scope.included liftApply (by simp [scopeClauses]))
          (pick [numeral c, numeral s, .sym (RootRewritesOnTheStep.labelCode label), encodeList arguments,
            encodeList (arguments.map (liftBVars c s))]) (fun g inside => by
            simp only [liftApply, List.mem_cons, List.not_mem_nil, or_false] at inside
            subst inside
            simpa [goalHolds, triple, pick] using inner)
        simpa [liftApply, triple, pick, encode, liftBVars] using clause
    | .lambda binder body => by
        have inner := lift_complete scope (c + 1) s body
        have clause := derives_of_clause (R := R) (scope.included liftLambda (by simp [scopeClauses]))
          (pick [numeral c, numeral s, RootRewritesOnTheStep.optionRow binder, encode body,
            encode (liftBVars (c + 1) s body)]) (fun g inside => by
            simp only [liftLambda, List.mem_cons, List.not_mem_nil, or_false] at inside
            subst inside
            simpa [goalHolds, triple, succTerm, pick, numeral] using inner)
        simpa [liftLambda, triple, pick, encode, liftBVars] using clause
    | .multiLambda arity binders body => by
        have added := add_complete (R := R) scope c arity
        have inner := lift_complete scope (c + arity) s body
        have clause := derives_of_clause (R := R) (scope.included liftMultiLambda (by simp [scopeClauses]))
          (pick [numeral c, numeral s, numeral arity, RootRewritesOnTheStep.namesRow binders, encode body,
            numeral (c + arity), encode (liftBVars (c + arity) s body)]) (fun g inside => by
            simp only [liftMultiLambda, List.mem_cons, List.not_mem_nil, or_false] at inside
            rcases inside with rfl | rfl
            · simpa [goalHolds, pick] using added
            · simpa [goalHolds, triple, pick] using inner)
        simpa [liftMultiLambda, triple, pick, encode, liftBVars] using clause
    | .subst body value => by
        have first := lift_complete scope (c + 1) s body
        have second := lift_complete scope c s value
        have clause := derives_of_clause (R := R) (scope.included liftSubst (by simp [scopeClauses]))
          (pick [numeral c, numeral s, encode body, encode value, encode (liftBVars (c + 1) s body),
            encode (liftBVars c s value)]) (fun g inside => by
            simp only [liftSubst, List.mem_cons, List.not_mem_nil, or_false] at inside
            rcases inside with rfl | rfl
            · simpa [goalHolds, triple, succTerm, pick, numeral] using first
            · simpa [goalHolds, triple, pick] using second)
        simpa [liftSubst, triple, pick, encode, liftBVars] using clause
    | .collection kind elements rest => by
        have inner := liftList_complete scope c s elements
        have clause := derives_of_clause (R := R) (scope.included liftCollection (by simp [scopeClauses]))
          (pick [numeral c, numeral s, .sym (Mettapedia.OSLF.MeTTaIL.PatternCode.collectionCode kind),
            encodeList elements, RootRewritesOnTheStep.optionRow rest,
            encodeList (elements.map (liftBVars c s))]) (fun g inside => by
            simp only [liftCollection, List.mem_cons, List.not_mem_nil, or_false] at inside
            subst inside
            simpa [goalHolds, triple, pick] using inner)
        simpa [liftCollection, triple, pick, encode, liftBVars] using clause

  theorem liftList_complete (scope : ScopeProgram program) (c s : ℕ) : ∀ ps : List Pattern,
      Derives R program liftListRelation (.app (.app (numeral c) (numeral s)) (encodeList ps))
        (encodeList (ps.map (liftBVars c s)))
    | [] => by
        have clause := derives_of_clause (R := R) (scope.included liftNil (by simp [scopeClauses]))
          (pick [numeral c, numeral s]) (fun _ inside => absurd inside List.not_mem_nil)
        simpa [liftNil, triple, pick, encodeList] using clause
    | x :: rest => by
        have first := lift_complete scope c s x
        have second := liftList_complete scope c s rest
        have clause := derives_of_clause (R := R) (scope.included liftCons (by simp [scopeClauses]))
          (pick [numeral c, numeral s, encode x, encodeList rest, encode (liftBVars c s x),
            encodeList (rest.map (liftBVars c s))]) (fun g inside => by
            simp only [liftCons, List.mem_cons, List.not_mem_nil, or_false] at inside
            rcases inside with rfl | rfl
            · simpa [goalHolds, triple, pick] using first
            · simpa [goalHolds, triple, pick] using second)
        simpa [liftCons, triple, pick, encodeList] using clause
end

/-- **The lifting clauses derive exactly the lift of a term.** -/
theorem lift_iff (scope : ScopeProgram program) (c s : ℕ) (p : Pattern) {w : Expr} :
    Derives R program liftRelation (.app (.app (numeral c) (numeral s)) (encode p)) w ↔
      w = encode (liftBVars c s p) := by
  constructor
  · rintro ⟨depth, derived⟩
    exact lift_sound scope depth c s p w derived
  · rintro rfl
    exact lift_complete scope c s p

/-! ## Instantiating -/

theorem instantiateBVarAt_bvar (depth index : ℕ) (replacement : Pattern) :
    instantiateBVarAt depth replacement (.bvar index) =
      if index < depth then .bvar index else if index = depth then liftBVars 0 depth replacement
        else .bvar (index - 1) := by
  rw [instantiateBVarAt]

mutual
  /-- **A derived instance of an index of a term is that instance.** -/
  theorem instantiate_sound (scope : ScopeProgram program) : ∀ (depth d : ℕ) (r p : Pattern) (w : Expr),
      DerivesAt R program depth instantiateRelation (.app (.app (numeral d) (encode r)) (encode p)) w →
        w = encode (instantiateBVarAt d r p)
    | 0, _, _, _, _, derived => derived.elim
    | depth + 1, d, r, p, w, derived => by
        obtain ⟨cl, member, isR, θ, input, output, goals⟩ := derived
        have inside := scopeClause_of scope member isR (by decide) (by decide)
        simp only [scopeClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first
          | exact absurd isR (by decide)
          | skip
        · simp only [instantiateBelow, triple, bvarTerm, RootRewritesOnTheStep.inst_appTerm,
            RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨dIs, -⟩, pIs⟩ := input
          obtain ⟨index, rfl, indexIs⟩ := encode_bvar_inv pIs
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, indexIs, dIs] at asked
          have below := atMost_sound scope depth (index + 1) d _ asked
          rw [← output, indexIs, instantiateBVarAt_bvar, if_pos (by omega)]
          rfl
        · simp only [instantiateHere, triple, bvarTerm, RootRewritesOnTheStep.inst_appTerm,
            RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨dIs, rIs⟩, pIs⟩ := input
          rw [dIs] at pIs
          obtain ⟨index, rfl, indexIs⟩ := encode_bvar_inv pIs
          obtain rfl := RootRewritesOnTheStep.numeral_injective indexIs
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, dIs, rIs] at asked
          rw [← output, lift_sound scope depth 0 d r _ asked, instantiateBVarAt_bvar, if_neg (by omega),
            if_pos rfl]
        · simp only [instantiateAbove, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm,
            RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨dIs, -⟩, pIs⟩ := input
          obtain ⟨index, rfl, indexIs⟩ := encode_bvar_inv pIs
          obtain ⟨m, rfl, mIs⟩ := numeral_succ_inv indexIs
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, dIs,
            mIs] at asked
          have above := atMost_sound scope depth d m _ asked
          rw [← output, mIs, instantiateBVarAt_bvar, if_neg (by omega), if_neg (by omega)]
          rfl
        · simp only [instantiateFvar, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨-, pIs⟩ := input
          obtain ⟨name, rfl, nameIs⟩ := encode_fvar_inv pIs
          rw [← output, nameIs, instantiateBVarAt]
          rfl
        · simp only [instantiateApply, triple, RootRewritesOnTheStep.inst_appTerm,
            RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨dIs, rIs⟩, pIs⟩ := input
          obtain ⟨label, arguments, rfl, labelIs, argumentsIs⟩ := encode_apply_inv pIs
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, dIs,
            rIs, argumentsIs] at asked
          rw [← output, labelIs, instantiateList_sound scope depth d r arguments _ asked, instantiateBVarAt]
          rfl
        · simp only [instantiateLambda, triple, RootRewritesOnTheStep.inst_appTerm,
            RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨dIs, rIs⟩, pIs⟩ := input
          obtain ⟨binder, body, rfl, binderIs, bodyIs⟩ := encode_lambda_inv pIs
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, succTerm, RootRewritesOnTheStep.inst_appTerm,
            RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, dIs, rIs, bodyIs] at asked
          rw [← output, binderIs, instantiate_sound scope depth (d + 1) r body _ asked, instantiateBVarAt]
          rfl
        · simp only [instantiateMultiLambda, triple, RootRewritesOnTheStep.inst_appTerm,
            RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨dIs, rIs⟩, pIs⟩ := input
          obtain ⟨arity, binders, body, rfl, arityIs, bindersIs, bodyIs⟩ := encode_multiLambda_inv pIs
          have first := goals _ List.mem_cons_self
          have second := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, dIs,
            arityIs] at first
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, rIs,
            bodyIs, add_sound scope depth d arity _ first] at second
          rw [← output, arityIs, bindersIs, instantiate_sound scope depth (d + arity) r body _ second,
            instantiateBVarAt]
          rfl
        · simp only [instantiateSubst, triple, RootRewritesOnTheStep.inst_appTerm,
            RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨dIs, rIs⟩, pIs⟩ := input
          obtain ⟨body, value, rfl, bodyIs, valueIs⟩ := encode_subst_inv pIs
          have first := goals _ List.mem_cons_self
          have second := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, triple, succTerm, RootRewritesOnTheStep.inst_appTerm,
            RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, dIs, rIs, bodyIs,
            valueIs] at first second
          rw [← output, instantiate_sound scope depth (d + 1) r body _ first,
            instantiate_sound scope depth d r value _ second, instantiateBVarAt]
          rfl
        · simp only [instantiateCollection, triple, RootRewritesOnTheStep.inst_appTerm,
            RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨dIs, rIs⟩, pIs⟩ := input
          obtain ⟨kind, elements, rest, rfl, kindIs, elementsIs, restIs⟩ := encode_collection_inv pIs
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, dIs,
            rIs, elementsIs] at asked
          rw [← output, kindIs, restIs, instantiateList_sound scope depth d r elements _ asked, instantiateBVarAt]
          rfl

  theorem instantiateList_sound (scope : ScopeProgram program) : ∀ (depth d : ℕ) (r : Pattern) (ps : List Pattern)
      (w : Expr), DerivesAt R program depth instantiateListRelation (.app (.app (numeral d) (encode r)) (encodeList ps))
        w → w = encodeList (ps.map (instantiateBVarAt d r))
    | 0, _, _, _, _, derived => derived.elim
    | depth + 1, d, r, ps, w, derived => by
        obtain ⟨cl, member, isR, θ, input, output, goals⟩ := derived
        have inside := scopeClause_of scope member isR (by decide) (le_refl _)
        simp only [scopeClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first
          | exact absurd isR (by decide)
          | skip
        · simp only [instantiateNil, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨-, psIs⟩ := input
          rw [encodeList_nil_inv psIs, ← output]
          rfl
        · simp only [instantiateCons, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
            Expr.app.injEq] at input output
          obtain ⟨⟨dIs, rIs⟩, psIs⟩ := input
          obtain ⟨x, rest, rfl, xIs, restIs⟩ := encodeList_cons_inv psIs
          have first := goals _ List.mem_cons_self
          have second := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, dIs,
            rIs, xIs, restIs] at first second
          rw [← output, instantiate_sound scope depth d r x _ first,
            instantiateList_sound scope depth d r rest _ second]
          rfl
end

mutual
  /-- **Every instance of an index of a term is derived.** -/
  theorem instantiate_complete (scope : ScopeProgram program) (r : Pattern) : ∀ (d : ℕ) (p : Pattern),
      Derives R program instantiateRelation (.app (.app (numeral d) (encode r)) (encode p))
        (encode (instantiateBVarAt d r p))
    | d, .bvar index => by
        rcases Nat.lt_trichotomy index d with below | rfl | above
        · have ordered := atMost_complete (R := R) scope (index + 1) d below
          have clause := derives_of_clause (R := R) (scope.included instantiateBelow (by simp [scopeClauses]))
            (pick [numeral d, encode r, numeral index]) (fun g inside => by
              simp only [instantiateBelow, List.mem_cons, List.not_mem_nil, or_false] at inside
              subst inside
              simpa [goalHolds, succTerm, pick, unit, numeral] using ordered)
          rw [instantiateBVarAt_bvar, if_pos below]
          simpa [instantiateBelow, triple, bvarTerm, pick, encode] using clause
        · have lifted := lift_complete (R := R) scope 0 index r
          have clause := derives_of_clause (R := R) (scope.included instantiateHere (by simp [scopeClauses]))
            (pick [numeral index, encode r, encode (liftBVars 0 index r)]) (fun g inside => by
              simp only [instantiateHere, List.mem_cons, List.not_mem_nil, or_false] at inside
              subst inside
              simpa [goalHolds, triple, pick, numeral] using lifted)
          rw [instantiateBVarAt_bvar, if_neg (Nat.lt_irrefl _), if_pos rfl]
          simpa [instantiateHere, triple, bvarTerm, pick, encode] using clause
        · obtain ⟨m, rfl⟩ : ∃ m, index = m + 1 := ⟨index - 1, by omega⟩
          have ordered := atMost_complete (R := R) scope d m (by omega)
          have clause := derives_of_clause (R := R) (scope.included instantiateAbove (by simp [scopeClauses]))
            (pick [numeral d, encode r, numeral m]) (fun g inside => by
              simp only [instantiateAbove, List.mem_cons, List.not_mem_nil, or_false] at inside
              subst inside
              simpa [goalHolds, pick, unit] using ordered)
          rw [instantiateBVarAt_bvar, if_neg (by omega), if_neg (by omega)]
          simpa [instantiateAbove, triple, bvarTerm, succTerm, pick, encode, numeral] using clause
    | d, .fvar name => by
        have clause := derives_of_clause (R := R) (scope.included instantiateFvar (by simp [scopeClauses]))
          (pick [numeral d, encode r, .sym (RootRewritesOnTheStep.labelCode name)])
          (fun _ inside => absurd inside List.not_mem_nil)
        rw [instantiateBVarAt]
        simpa [instantiateFvar, triple, pick, encode] using clause
    | d, .apply label arguments => by
        have inner := instantiateList_complete scope r d arguments
        have clause := derives_of_clause (R := R) (scope.included instantiateApply (by simp [scopeClauses]))
          (pick [numeral d, encode r, .sym (RootRewritesOnTheStep.labelCode label), encodeList arguments,
            encodeList (arguments.map (instantiateBVarAt d r))]) (fun g inside => by
            simp only [instantiateApply, List.mem_cons, List.not_mem_nil, or_false] at inside
            subst inside
            simpa [goalHolds, triple, pick] using inner)
        rw [instantiateBVarAt]
        simpa [instantiateApply, triple, pick, encode] using clause
    | d, .lambda binder body => by
        have inner := instantiate_complete scope r (d + 1) body
        have clause := derives_of_clause (R := R) (scope.included instantiateLambda (by simp [scopeClauses]))
          (pick [numeral d, encode r, RootRewritesOnTheStep.optionRow binder, encode body,
            encode (instantiateBVarAt (d + 1) r body)]) (fun g inside => by
            simp only [instantiateLambda, List.mem_cons, List.not_mem_nil, or_false] at inside
            subst inside
            simpa [goalHolds, triple, succTerm, pick, numeral] using inner)
        rw [instantiateBVarAt]
        simpa [instantiateLambda, triple, pick, encode] using clause
    | d, .multiLambda arity binders body => by
        have added := add_complete (R := R) scope d arity
        have inner := instantiate_complete scope r (d + arity) body
        have clause := derives_of_clause (R := R) (scope.included instantiateMultiLambda (by simp [scopeClauses]))
          (pick [numeral d, encode r, numeral arity, RootRewritesOnTheStep.namesRow binders, encode body,
            numeral (d + arity), encode (instantiateBVarAt (d + arity) r body)]) (fun g inside => by
            simp only [instantiateMultiLambda, List.mem_cons, List.not_mem_nil, or_false] at inside
            rcases inside with rfl | rfl
            · simpa [goalHolds, pick] using added
            · simpa [goalHolds, triple, pick] using inner)
        rw [instantiateBVarAt]
        simpa [instantiateMultiLambda, triple, pick, encode] using clause
    | d, .subst body value => by
        have first := instantiate_complete scope r (d + 1) body
        have second := instantiate_complete scope r d value
        have clause := derives_of_clause (R := R) (scope.included instantiateSubst (by simp [scopeClauses]))
          (pick [numeral d, encode r, encode body, encode value, encode (instantiateBVarAt (d + 1) r body),
            encode (instantiateBVarAt d r value)]) (fun g inside => by
            simp only [instantiateSubst, List.mem_cons, List.not_mem_nil, or_false] at inside
            rcases inside with rfl | rfl
            · simpa [goalHolds, triple, succTerm, pick, numeral] using first
            · simpa [goalHolds, triple, pick] using second)
        rw [instantiateBVarAt]
        simpa [instantiateSubst, triple, pick, encode] using clause
    | d, .collection kind elements rest => by
        have inner := instantiateList_complete scope r d elements
        have clause := derives_of_clause (R := R) (scope.included instantiateCollection (by simp [scopeClauses]))
          (pick [numeral d, encode r, .sym (Mettapedia.OSLF.MeTTaIL.PatternCode.collectionCode kind),
            encodeList elements, RootRewritesOnTheStep.optionRow rest,
            encodeList (elements.map (instantiateBVarAt d r))]) (fun g inside => by
            simp only [instantiateCollection, List.mem_cons, List.not_mem_nil, or_false] at inside
            subst inside
            simpa [goalHolds, triple, pick] using inner)
        rw [instantiateBVarAt]
        simpa [instantiateCollection, triple, pick, encode] using clause

  theorem instantiateList_complete (scope : ScopeProgram program) (r : Pattern) : ∀ (d : ℕ) (ps : List Pattern),
      Derives R program instantiateListRelation (.app (.app (numeral d) (encode r)) (encodeList ps))
        (encodeList (ps.map (instantiateBVarAt d r)))
    | d, [] => by
        have clause := derives_of_clause (R := R) (scope.included instantiateNil (by simp [scopeClauses]))
          (pick [numeral d, encode r]) (fun _ inside => absurd inside List.not_mem_nil)
        simpa [instantiateNil, triple, pick, encodeList] using clause
    | d, x :: rest => by
        have first := instantiate_complete scope r d x
        have second := instantiateList_complete scope r d rest
        have clause := derives_of_clause (R := R) (scope.included instantiateCons (by simp [scopeClauses]))
          (pick [numeral d, encode r, encode x, encodeList rest, encode (instantiateBVarAt d r x),
            encodeList (rest.map (instantiateBVarAt d r))]) (fun g inside => by
            simp only [instantiateCons, List.mem_cons, List.not_mem_nil, or_false] at inside
            rcases inside with rfl | rfl
            · simpa [goalHolds, triple, pick] using first
            · simpa [goalHolds, triple, pick] using second)
        simpa [instantiateCons, triple, pick, encodeList] using clause
end

/-- **The instantiating clauses derive exactly the instance of an index of a term.** -/
theorem instantiate_iff (scope : ScopeProgram program) (d : ℕ) (r p : Pattern) {w : Expr} :
    Derives R program instantiateRelation (.app (.app (numeral d) (encode r)) (encode p)) w ↔
      w = encode (instantiateBVarAt d r p) := by
  constructor
  · rintro ⟨depth, derived⟩
    exact instantiate_sound scope depth d r p w derived
  · rintro rfl
    exact instantiate_complete scope r d p

end Clauses

/-! ## Lowering: the converse of lifting -/

/-- The relation of subtracting numbers. -/
def subtractRelation : ℕ := 36

/-- The relation of lowering a term's indices at or beyond a cutoff by a shift: the converse of lifting. -/
def lowerRelation : ℕ := 37

/-- The relation of lowering a list of terms. -/
def lowerListRelation : ℕ := 38

def subtractZero : Clause :=
  { relation := subtractRelation, input := appTerm (.var 0) (symTerm 0), output := .var 0, body := [] }

def subtractSucc : Clause :=
  { relation := subtractRelation, input := appTerm (succTerm (.var 0)) (succTerm (.var 1)), output := .var 2,
    body := [.ask subtractRelation (appTerm (.var 0) (.var 1)) (.var 2)] }

/-- An index below the cutoff stays. -/
def lowerBelow : Clause :=
  { relation := lowerRelation, input := triple (.var 0) (.var 1) (bvarTerm (.var 2)), output := bvarTerm (.var 2),
    body := [.ask atMostRelation (appTerm (succTerm (.var 2)) (.var 0)) unit] }

/-- An index at or beyond the cutoff and the shift is lowered by the shift; adding it back checks the result. -/
def lowerAbove : Clause :=
  { relation := lowerRelation, input := triple (.var 0) (.var 1) (bvarTerm (.var 3)), output := bvarTerm (.var 2),
    body := [.ask subtractRelation (appTerm (.var 3) (.var 1)) (.var 2),
      .ask atMostRelation (appTerm (.var 0) (.var 2)) unit,
      .ask addRelation (appTerm (.var 2) (.var 1)) (.var 3)] }

def lowerFvar : Clause :=
  { relation := lowerRelation, input := triple (.var 0) (.var 1) (appTerm (symTerm 1) (.var 2)),
    output := appTerm (symTerm 1) (.var 2), body := [] }

def lowerApply : Clause :=
  { relation := lowerRelation, input := triple (.var 0) (.var 1) (appTerm (symTerm 2) (appTerm (.var 2) (.var 4))),
    output := appTerm (symTerm 2) (appTerm (.var 2) (.var 3)),
    body := [.ask lowerListRelation (triple (.var 0) (.var 1) (.var 4)) (.var 3)] }

def lowerLambda : Clause :=
  { relation := lowerRelation, input := triple (.var 0) (.var 1) (appTerm (symTerm 3) (appTerm (.var 2) (.var 4))),
    output := appTerm (symTerm 3) (appTerm (.var 2) (.var 3)),
    body := [.ask lowerRelation (triple (succTerm (.var 0)) (.var 1) (.var 4)) (.var 3)] }

def lowerMultiLambda : Clause :=
  { relation := lowerRelation,
    input := triple (.var 0) (.var 1) (appTerm (symTerm 4) (appTerm (.var 2) (appTerm (.var 3) (.var 6)))),
    output := appTerm (symTerm 4) (appTerm (.var 2) (appTerm (.var 3) (.var 4))),
    body := [.ask addRelation (appTerm (.var 0) (.var 2)) (.var 5),
      .ask lowerRelation (triple (.var 5) (.var 1) (.var 6)) (.var 4)] }

def lowerSubst : Clause :=
  { relation := lowerRelation, input := triple (.var 0) (.var 1) (appTerm (symTerm 5) (appTerm (.var 4) (.var 5))),
    output := appTerm (symTerm 5) (appTerm (.var 2) (.var 3)),
    body := [.ask lowerRelation (triple (succTerm (.var 0)) (.var 1) (.var 4)) (.var 2),
      .ask lowerRelation (triple (.var 0) (.var 1) (.var 5)) (.var 3)] }

def lowerCollection : Clause :=
  { relation := lowerRelation,
    input := triple (.var 0) (.var 1) (appTerm (symTerm 6) (appTerm (.var 2) (appTerm (.var 5) (.var 4)))),
    output := appTerm (symTerm 6) (appTerm (.var 2) (appTerm (.var 3) (.var 4))),
    body := [.ask lowerListRelation (triple (.var 0) (.var 1) (.var 5)) (.var 3)] }

def lowerNil : Clause :=
  { relation := lowerListRelation, input := triple (.var 0) (.var 1) (symTerm 0), output := symTerm 0, body := [] }

def lowerCons : Clause :=
  { relation := lowerListRelation, input := triple (.var 0) (.var 1) (appTerm (.var 4) (.var 5)),
    output := appTerm (.var 2) (.var 3),
    body := [.ask lowerRelation (triple (.var 0) (.var 1) (.var 4)) (.var 2),
      .ask lowerListRelation (triple (.var 0) (.var 1) (.var 5)) (.var 3)] }

/-- **The clauses of lowering**: subtracting, lowering a term, lowering a list. -/
def lowerClauses : List Clause :=
  [subtractZero, subtractSucc, lowerBelow, lowerAbove, lowerFvar, lowerApply, lowerLambda, lowerMultiLambda,
    lowerSubst, lowerCollection, lowerNil, lowerCons]

theorem lowerClauses_moded : ∀ c ∈ lowerClauses, Moded c := by
  intro c inside
  simp only [lowerClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact DemandTransformation.moded_of_check (by decide)

theorem lowerClauses_relation :
    ∀ c ∈ lowerClauses, subtractRelation ≤ c.relation ∧ c.relation ≤ lowerListRelation := by decide

/-- **A program with the clauses of lowering**, beside the clauses of scopes. -/
structure LowerProgram (program : List Clause) : Prop where
  scope : ScopeProgram program
  included : ∀ c ∈ lowerClauses, c ∈ program
  only : ∀ c ∈ program, subtractRelation ≤ c.relation → c.relation ≤ lowerListRelation → c ∈ lowerClauses

section Lowering

variable {R : Relations} {program : List Clause}

theorem lowerClause_of (lowers : LowerProgram program) {c : Clause} (member : c ∈ program) {r : ℕ}
    (isR : c.relation = r) (low : subtractRelation ≤ r) (high : r ≤ lowerListRelation) : c ∈ lowerClauses :=
  lowers.only c member (isR ▸ low) (isR ▸ high)

/-- **A derived sum with a number added is of numbers.** -/
theorem add_numeral_inv (scope : ScopeProgram program) : ∀ (depth : ℕ) (x : Expr) (k : ℕ) (w : Expr),
    DerivesAt R program depth addRelation (.app x (numeral k)) w → ∃ m, x = numeral m ∧ w = numeral (m + k)
  | 0, _, _, _, derived => derived.elim
  | depth + 1, x, k, w, derived => by
      obtain ⟨c, member, isR, θ, input, output, goals⟩ := derived
      have inside := scopeClause_of scope member isR (by decide) (by decide)
      simp only [scopeClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact absurd isR (by decide)
        | skip
      · simp only [addZero, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown, Expr.app.injEq] at input output
        refine ⟨0, input.1.symm, ?_⟩
        rw [← output, input.2, Nat.zero_add]
      · simp only [addSucc, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown, Expr.app.injEq] at input output
        obtain ⟨xIs, kIs⟩ := input
        have asked := goals _ List.mem_cons_self
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, kIs] at asked
        obtain ⟨m, mIs, sumIs⟩ := add_numeral_inv scope depth _ k _ asked
        refine ⟨m + 1, by rw [← xIs, mIs]; rfl, ?_⟩
        rw [← output, sumIs, Nat.succ_add]
        rfl

theorem subtract_complete (lowers : LowerProgram program) :
    ∀ (m k : ℕ), Derives R program subtractRelation (.app (numeral (m + k)) (numeral k)) (numeral m)
  | m, 0 => by
      have clause := derives_of_clause (R := R) (lowers.included subtractZero (by simp [lowerClauses]))
        (pick [numeral m]) (fun _ inside => absurd inside List.not_mem_nil)
      simpa [subtractZero, pick, numeral] using clause
  | m, k + 1 => by
      have inner := subtract_complete lowers m k
      have clause := derives_of_clause (R := R) (lowers.included subtractSucc (by simp [lowerClauses]))
        (pick [numeral (m + k), numeral k, numeral m]) (fun g inside => by
          simp only [subtractSucc, List.mem_cons, List.not_mem_nil, or_false] at inside
          subst inside
          simpa [goalHolds, pick] using inner)
      have sum : numeral (m + (k + 1)) = .app (.sym 1) (numeral (m + k)) := rfl
      have shift : numeral (k + 1) = .app (.sym 1) (numeral k) := rfl
      rw [sum, shift]
      simpa [subtractSucc, succTerm, pick] using clause

mutual
  /-- **A lowered term lifts back to the term it came from.** -/
  theorem lower_lift (lowers : LowerProgram program) : ∀ (depth : ℕ) (P x y : Expr),
      DerivesAt R program depth lowerRelation (.app P x) y → Derives R program liftRelation (.app P y) x
    | 0, _, _, _, derived => derived.elim
    | depth + 1, P, x, y, derived => by
        obtain ⟨cl, member, isR, θ, input, output, goals⟩ := derived
        have inside := lowerClause_of lowers member isR (by decide) (by decide)
        simp only [lowerClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first
          | exact absurd isR (by decide)
          | skip
        · simp only [lowerBelow, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have clause := derives_of_clause (R := R) (lowers.scope.included liftBelow (by simp [scopeClauses])) θ
            fun g inside => by
              simp only [liftBelow, List.mem_cons, List.not_mem_nil, or_false] at inside
              subst inside
              exact DemandTransformation.goalHolds_mono (fun _ _ _ held => ⟨depth, held⟩)
                (goals _ List.mem_cons_self)
          simpa [liftBelow, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown] using clause
        · simp only [lowerAbove, triple, bvarTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have clause := derives_of_clause (R := R) (lowers.scope.included liftAbove (by simp [scopeClauses])) θ
            fun g inside => by
              simp only [liftAbove, List.mem_cons, List.not_mem_nil, or_false] at inside
              rcases inside with rfl | rfl
              · exact DemandTransformation.goalHolds_mono (fun _ _ _ held => ⟨depth, held⟩)
                  (goals _ (List.mem_cons_of_mem _ List.mem_cons_self))
              · exact DemandTransformation.goalHolds_mono (fun _ _ _ held => ⟨depth, held⟩)
                  (goals _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
          simpa [liftAbove, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown] using clause
        · simp only [lowerFvar, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have clause := derives_of_clause (R := R) (lowers.scope.included liftFvar (by simp [scopeClauses])) θ
            fun g inside => by
              exact absurd inside List.not_mem_nil
          simpa [liftFvar, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown] using clause
        · simp only [lowerApply, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown] at asked
          have inner := lowerList_lift lowers depth _ _ _ asked
          have clause := derives_of_clause (R := R) (lowers.scope.included liftApply (by simp [scopeClauses])) θ
            fun g inside => by
              simp only [liftApply, List.mem_cons, List.not_mem_nil, or_false] at inside
              subst inside
              simpa [goalHolds, triple] using inner
          simpa [liftApply, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown] using clause
        · simp only [lowerLambda, triple, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] at asked
          have inner := lower_lift lowers depth _ _ _ asked
          have clause := derives_of_clause (R := R) (lowers.scope.included liftLambda (by simp [scopeClauses])) θ
            fun g inside => by
              simp only [liftLambda, List.mem_cons, List.not_mem_nil, or_false] at inside
              subst inside
              simpa [goalHolds, triple, succTerm] using inner
          simpa [liftLambda, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown] using clause
        · simp only [lowerMultiLambda, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have asked := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown] at asked
          have inner := lower_lift lowers depth _ _ _ asked
          have clause := derives_of_clause (R := R) (lowers.scope.included liftMultiLambda (by simp [scopeClauses])) θ
            fun g inside => by
              simp only [liftMultiLambda, List.mem_cons, List.not_mem_nil, or_false] at inside
              rcases inside with rfl | rfl
              · exact DemandTransformation.goalHolds_mono (fun _ _ _ held => ⟨depth, held⟩)
                  (goals _ List.mem_cons_self)
              · simpa [goalHolds, triple] using inner
          simpa [liftMultiLambda, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown] using clause
        · simp only [lowerSubst, triple, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have firstAsked := goals _ List.mem_cons_self
          have secondAsked := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, triple, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] at firstAsked secondAsked
          have first := lower_lift lowers depth _ _ _ firstAsked
          have second := lower_lift lowers depth _ _ _ secondAsked
          have clause := derives_of_clause (R := R) (lowers.scope.included liftSubst (by simp [scopeClauses])) θ
            fun g inside => by
              simp only [liftSubst, List.mem_cons, List.not_mem_nil, or_false] at inside
              rcases inside with rfl | rfl
              · simpa [goalHolds, triple, succTerm] using first
              · simpa [goalHolds, triple] using second
          simpa [liftSubst, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown] using clause
        · simp only [lowerCollection, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown] at asked
          have inner := lowerList_lift lowers depth _ _ _ asked
          have clause := derives_of_clause (R := R) (lowers.scope.included liftCollection (by simp [scopeClauses])) θ
            fun g inside => by
              simp only [liftCollection, List.mem_cons, List.not_mem_nil, or_false] at inside
              subst inside
              simpa [goalHolds, triple] using inner
          simpa [liftCollection, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown] using clause

  theorem lowerList_lift (lowers : LowerProgram program) : ∀ (depth : ℕ) (P x y : Expr),
      DerivesAt R program depth lowerListRelation (.app P x) y →
        Derives R program liftListRelation (.app P y) x
    | 0, _, _, _, derived => derived.elim
    | depth + 1, P, x, y, derived => by
        obtain ⟨cl, member, isR, θ, input, output, goals⟩ := derived
        have inside := lowerClause_of lowers member isR (by decide) (by decide)
        simp only [lowerClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first
          | exact absurd isR (by decide)
          | skip
        · simp only [lowerNil, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have clause := derives_of_clause (R := R) (lowers.scope.included liftNil (by simp [scopeClauses])) θ
            fun g inside => by
              exact absurd inside List.not_mem_nil
          simpa [liftNil, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown] using clause
        · simp only [lowerCons, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have firstAsked := goals _ List.mem_cons_self
          have secondAsked := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown]
            at firstAsked secondAsked
          have first := lower_lift lowers depth _ _ _ firstAsked
          have second := lowerList_lift lowers depth _ _ _ secondAsked
          have clause := derives_of_clause (R := R) (lowers.scope.included liftCons (by simp [scopeClauses])) θ
            fun g inside => by
              simp only [liftCons, List.mem_cons, List.not_mem_nil, or_false] at inside
              rcases inside with rfl | rfl
              · simpa [goalHolds, triple] using first
              · simpa [goalHolds, triple] using second
          simpa [liftCons, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown] using clause
end

mutual
  /-- **Every lift by a number is lowered back.** -/
  theorem lift_lower (lowers : LowerProgram program) : ∀ (depth : ℕ) (c : Expr) (k : ℕ) (y x : Expr),
      DerivesAt R program depth liftRelation (.app (.app c (numeral k)) y) x →
        Derives R program lowerRelation (.app (.app c (numeral k)) x) y
    | 0, _, _, _, _, derived => derived.elim
    | depth + 1, c, k, y, x, derived => by
        obtain ⟨cl, member, isR, θ, input, output, goals⟩ := derived
        have inside := scopeClause_of lowers.scope member isR (by decide) (by decide)
        simp only [scopeClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first
          | exact absurd isR (by decide)
          | skip
        · simp only [liftBelow, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨rfl, kIs⟩, rfl⟩ := input
          subst output
          have clause := derives_of_clause (R := R) (lowers.included lowerBelow (by simp [lowerClauses])) θ
            fun g inside => by
              simp only [lowerBelow, List.mem_cons, List.not_mem_nil, or_false] at inside
              subst inside
              exact DemandTransformation.goalHolds_mono (fun _ _ _ held => ⟨depth, held⟩) (goals _ List.mem_cons_self)
          rw [← kIs]
          simpa [lowerBelow, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown] using clause
        · simp only [liftAbove, triple, bvarTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨rfl, kIs⟩, rfl⟩ := input
          subst output
          have ordered := goals _ List.mem_cons_self
          have added := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, kIs] at added
          obtain ⟨index, indexIs, sumIs⟩ := add_numeral_inv lowers.scope depth _ k _ added
          have subtracted := subtract_complete (R := R) lowers index k
          rw [← indexIs, ← sumIs, ← kIs] at subtracted
          have clause := derives_of_clause (R := R) (lowers.included lowerAbove (by simp [lowerClauses])) θ
            fun g inside => by
              simp only [lowerAbove, List.mem_cons, List.not_mem_nil, or_false] at inside
              rcases inside with rfl | rfl | rfl
              · simpa [goalHolds] using subtracted
              · exact DemandTransformation.goalHolds_mono (fun _ _ _ held => ⟨depth, held⟩) (goals _ List.mem_cons_self)
              · exact DemandTransformation.goalHolds_mono (fun _ _ _ held => ⟨depth, held⟩) (goals _ (List.mem_cons_of_mem _ List.mem_cons_self))
          rw [← kIs]
          simpa [lowerAbove, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown] using clause
        · simp only [liftFvar, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨rfl, kIs⟩, rfl⟩ := input
          subst output
          have clause := derives_of_clause (R := R) (lowers.included lowerFvar (by simp [lowerClauses])) θ
            fun g inside => by
              exact absurd inside List.not_mem_nil
          rw [← kIs]
          simpa [lowerFvar, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown] using clause
        · simp only [liftApply, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨rfl, kIs⟩, rfl⟩ := input
          subst output
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, kIs] at asked
          have inner := liftList_lower lowers depth _ k _ _ asked
          rw [← kIs] at inner
          have clause := derives_of_clause (R := R) (lowers.included lowerApply (by simp [lowerClauses])) θ
            fun g inside => by
              simp only [lowerApply, List.mem_cons, List.not_mem_nil, or_false] at inside
              subst inside
              simpa [goalHolds, triple] using inner
          rw [← kIs]
          simpa [lowerApply, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown] using clause
        · simp only [liftLambda, triple, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨rfl, kIs⟩, rfl⟩ := input
          subst output
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, kIs] at asked
          have inner := lift_lower lowers depth _ k _ _ asked
          rw [← kIs] at inner
          have clause := derives_of_clause (R := R) (lowers.included lowerLambda (by simp [lowerClauses])) θ
            fun g inside => by
              simp only [lowerLambda, List.mem_cons, List.not_mem_nil, or_false] at inside
              subst inside
              simpa [goalHolds, triple, succTerm] using inner
          rw [← kIs]
          simpa [lowerLambda, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown] using clause
        · simp only [liftMultiLambda, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨rfl, kIs⟩, rfl⟩ := input
          subst output
          have asked := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, kIs] at asked
          have inner := lift_lower lowers depth _ k _ _ asked
          rw [← kIs] at inner
          have clause := derives_of_clause (R := R) (lowers.included lowerMultiLambda (by simp [lowerClauses])) θ
            fun g inside => by
              simp only [lowerMultiLambda, List.mem_cons, List.not_mem_nil, or_false] at inside
              rcases inside with rfl | rfl
              · exact DemandTransformation.goalHolds_mono (fun _ _ _ held => ⟨depth, held⟩) (goals _ List.mem_cons_self)
              · simpa [goalHolds, triple] using inner
          rw [← kIs]
          simpa [lowerMultiLambda, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown] using clause
        · simp only [liftSubst, triple, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨rfl, kIs⟩, rfl⟩ := input
          subst output
          have firstAsked := goals _ List.mem_cons_self
          have secondAsked := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, triple, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, kIs] at firstAsked secondAsked
          have bodyLowered := lift_lower lowers depth _ k _ _ firstAsked
          have valueLowered := lift_lower lowers depth _ k _ _ secondAsked
          rw [← kIs] at bodyLowered valueLowered
          have clause := derives_of_clause (R := R) (lowers.included lowerSubst (by simp [lowerClauses])) θ
            fun g inside => by
              simp only [lowerSubst, List.mem_cons, List.not_mem_nil, or_false] at inside
              rcases inside with rfl | rfl
              · simpa [goalHolds, triple, succTerm] using bodyLowered
              · simpa [goalHolds, triple] using valueLowered
          rw [← kIs]
          simpa [lowerSubst, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown] using clause
        · simp only [liftCollection, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨rfl, kIs⟩, rfl⟩ := input
          subst output
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, kIs] at asked
          have inner := liftList_lower lowers depth _ k _ _ asked
          rw [← kIs] at inner
          have clause := derives_of_clause (R := R) (lowers.included lowerCollection (by simp [lowerClauses])) θ
            fun g inside => by
              simp only [lowerCollection, List.mem_cons, List.not_mem_nil, or_false] at inside
              subst inside
              simpa [goalHolds, triple] using inner
          rw [← kIs]
          simpa [lowerCollection, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown] using clause

  theorem liftList_lower (lowers : LowerProgram program) : ∀ (depth : ℕ) (c : Expr) (k : ℕ) (y x : Expr),
      DerivesAt R program depth liftListRelation (.app (.app c (numeral k)) y) x →
        Derives R program lowerListRelation (.app (.app c (numeral k)) x) y
    | 0, _, _, _, _, derived => derived.elim
    | depth + 1, c, k, y, x, derived => by
        obtain ⟨cl, member, isR, θ, input, output, goals⟩ := derived
        have inside := scopeClause_of lowers.scope member isR (by decide) (by decide)
        simp only [scopeClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first
          | exact absurd isR (by decide)
          | skip
        · simp only [liftNil, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨rfl, kIs⟩, rfl⟩ := input
          subst output
          have clause := derives_of_clause (R := R) (lowers.included lowerNil (by simp [lowerClauses])) θ
            fun g inside => by
              exact absurd inside List.not_mem_nil
          rw [← kIs]
          simpa [lowerNil, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown] using clause
        · simp only [liftCons, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨rfl, kIs⟩, rfl⟩ := input
          subst output
          have firstAsked := goals _ List.mem_cons_self
          have secondAsked := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, kIs] at firstAsked secondAsked
          have headLowered := lift_lower lowers depth _ k _ _ firstAsked
          have tailLowered := liftList_lower lowers depth _ k _ _ secondAsked
          rw [← kIs] at headLowered tailLowered
          have clause := derives_of_clause (R := R) (lowers.included lowerCons (by simp [lowerClauses])) θ
            fun g inside => by
              simp only [lowerCons, List.mem_cons, List.not_mem_nil, or_false] at inside
              rcases inside with rfl | rfl
              · simpa [goalHolds, triple] using headLowered
              · simpa [goalHolds, triple] using tailLowered
          rw [← kIs]
          simpa [lowerCons, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown] using clause
end

mutual
  /-- **What lifts to a term is a term.** -/
  theorem lift_decode (scope : ScopeProgram program) : ∀ (depth : ℕ) (c : Expr) (k : ℕ) (y : Expr) (p : Pattern),
      DerivesAt R program depth liftRelation (.app (.app c (numeral k)) y) (encode p) → ∃ q, y = encode q
    | 0, _, _, _, _, derived => derived.elim
    | depth + 1, c, k, y, p, derived => by
        obtain ⟨cl, member, isR, θ, input, output, goals⟩ := derived
        have inside := scopeClause_of scope member isR (by decide) (by decide)
        simp only [scopeClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first
          | exact absurd isR (by decide)
          | skip
        · simp only [liftBelow, triple, bvarTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨-, -⟩, rfl⟩ := input
          exact ⟨p, output⟩
        · simp only [liftAbove, triple, bvarTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨-, kIs⟩, rfl⟩ := input
          have added := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, kIs] at added
          obtain ⟨index, indexIs, -⟩ := add_numeral_inv scope depth _ k _ added
          exact ⟨.bvar index, by rw [indexIs]; rfl⟩
        · simp only [liftFvar, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨-, -⟩, rfl⟩ := input
          exact ⟨p, output⟩
        · simp only [liftApply, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨-, kIs⟩, rfl⟩ := input
          obtain ⟨label, arguments, rfl, labelIs, argumentsIs⟩ := encode_apply_inv output
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, kIs, argumentsIs] at asked
          obtain ⟨qs, qsIs⟩ := liftList_decode scope depth _ k _ arguments asked
          exact ⟨.apply label qs, by rw [labelIs, qsIs]; rfl⟩
        · simp only [liftLambda, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨-, kIs⟩, rfl⟩ := input
          obtain ⟨binder, body, rfl, binderIs, bodyIs⟩ := encode_lambda_inv output
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, kIs, bodyIs] at asked
          obtain ⟨q, qIs⟩ := lift_decode scope depth _ k _ body asked
          exact ⟨.lambda binder q, by rw [binderIs, qIs]; rfl⟩
        · simp only [liftMultiLambda, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨-, kIs⟩, rfl⟩ := input
          obtain ⟨arity, binders, body, rfl, arityIs, bindersIs, bodyIs⟩ := encode_multiLambda_inv output
          have asked := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, kIs, bodyIs] at asked
          obtain ⟨q, qIs⟩ := lift_decode scope depth _ k _ body asked
          exact ⟨.multiLambda arity binders q, by rw [arityIs, bindersIs, qIs]; rfl⟩
        · simp only [liftSubst, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨-, kIs⟩, rfl⟩ := input
          obtain ⟨body, value, rfl, bodyIs, valueIs⟩ := encode_subst_inv output
          have firstAsked := goals _ List.mem_cons_self
          have secondAsked := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, triple, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, kIs, bodyIs, valueIs] at firstAsked secondAsked
          obtain ⟨q, qIs⟩ := lift_decode scope depth _ k _ body firstAsked
          obtain ⟨r, rIs⟩ := lift_decode scope depth _ k _ value secondAsked
          exact ⟨.subst q r, by rw [qIs, rIs]; rfl⟩
        · simp only [liftCollection, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨-, kIs⟩, rfl⟩ := input
          obtain ⟨kind, elements, rest, rfl, kindIs, elementsIs, restIs⟩ := encode_collection_inv output
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, kIs, elementsIs] at asked
          obtain ⟨qs, qsIs⟩ := liftList_decode scope depth _ k _ elements asked
          exact ⟨.collection kind qs rest, by rw [kindIs, restIs, qsIs]; rfl⟩

  theorem liftList_decode (scope : ScopeProgram program) : ∀ (depth : ℕ) (c : Expr) (k : ℕ) (y : Expr)
      (ps : List Pattern), DerivesAt R program depth liftListRelation (.app (.app c (numeral k)) y) (encodeList ps) →
        ∃ qs, y = encodeList qs
    | 0, _, _, _, _, derived => derived.elim
    | depth + 1, c, k, y, ps, derived => by
        obtain ⟨cl, member, isR, θ, input, output, goals⟩ := derived
        have inside := scopeClause_of scope member isR (by decide) (by decide)
        simp only [scopeClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first
          | exact absurd isR (by decide)
          | skip
        · simp only [liftNil, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨-, -⟩, rfl⟩ := input
          exact ⟨[], rfl⟩
        · simp only [liftCons, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨-, kIs⟩, rfl⟩ := input
          obtain ⟨x, rest, rfl, xIs, restIs⟩ := encodeList_cons_inv output
          have firstAsked := goals _ List.mem_cons_self
          have secondAsked := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, kIs, xIs, restIs] at firstAsked secondAsked
          obtain ⟨q, qIs⟩ := lift_decode scope depth _ k _ x firstAsked
          obtain ⟨qs, qsIs⟩ := liftList_decode scope depth _ k _ rest secondAsked
          exact ⟨q :: qs, by rw [qIs, qsIs]; rfl⟩
end

end Lowering

/-! ## Abstracting: the converse of instantiating -/

/-- The relation of abstracting a term over an index: the converse of instantiating. -/
def abstractRelation : ℕ := 39

/-- The relation of abstracting a list of terms. -/
def abstractListRelation : ℕ := 40

/-- An index below the abstracted one stays. -/
def abstractBelow : Clause :=
  { relation := abstractRelation, input := triple (.var 0) (.var 1) (bvarTerm (.var 2)),
    output := bvarTerm (.var 2), body := [.ask atMostRelation (appTerm (succTerm (.var 2)) (.var 0)) unit] }

/-- The term, lifted to where it lands, may be the abstracted index. -/
def abstractHere : Clause :=
  { relation := abstractRelation, input := triple (.var 0) (.var 1) (.var 2), output := bvarTerm (.var 0),
    body := [.ask liftRelation (triple (symTerm 0) (.var 0) (.var 1)) (.var 2)] }

/-- An index at or beyond the abstracted one is raised. -/
def abstractAbove : Clause :=
  { relation := abstractRelation, input := triple (.var 0) (.var 1) (bvarTerm (.var 2)),
    output := bvarTerm (succTerm (.var 2)), body := [.ask atMostRelation (appTerm (.var 0) (.var 2)) unit] }

def abstractFvar : Clause :=
  { relation := abstractRelation, input := triple (.var 0) (.var 1) (appTerm (symTerm 1) (.var 2)),
    output := appTerm (symTerm 1) (.var 2), body := [] }

def abstractApply : Clause :=
  { relation := abstractRelation,
    input := triple (.var 0) (.var 1) (appTerm (symTerm 2) (appTerm (.var 2) (.var 4))),
    output := appTerm (symTerm 2) (appTerm (.var 2) (.var 3)),
    body := [.ask abstractListRelation (triple (.var 0) (.var 1) (.var 4)) (.var 3)] }

def abstractLambda : Clause :=
  { relation := abstractRelation,
    input := triple (.var 0) (.var 1) (appTerm (symTerm 3) (appTerm (.var 2) (.var 4))),
    output := appTerm (symTerm 3) (appTerm (.var 2) (.var 3)),
    body := [.ask abstractRelation (triple (succTerm (.var 0)) (.var 1) (.var 4)) (.var 3)] }

def abstractMultiLambda : Clause :=
  { relation := abstractRelation,
    input := triple (.var 0) (.var 1) (appTerm (symTerm 4) (appTerm (.var 2) (appTerm (.var 3) (.var 6)))),
    output := appTerm (symTerm 4) (appTerm (.var 2) (appTerm (.var 3) (.var 4))),
    body := [.ask addRelation (appTerm (.var 0) (.var 2)) (.var 5),
      .ask abstractRelation (triple (.var 5) (.var 1) (.var 6)) (.var 4)] }

def abstractSubst : Clause :=
  { relation := abstractRelation,
    input := triple (.var 0) (.var 1) (appTerm (symTerm 5) (appTerm (.var 4) (.var 5))),
    output := appTerm (symTerm 5) (appTerm (.var 2) (.var 3)),
    body := [.ask abstractRelation (triple (succTerm (.var 0)) (.var 1) (.var 4)) (.var 2),
      .ask abstractRelation (triple (.var 0) (.var 1) (.var 5)) (.var 3)] }

def abstractCollection : Clause :=
  { relation := abstractRelation,
    input := triple (.var 0) (.var 1) (appTerm (symTerm 6) (appTerm (.var 2) (appTerm (.var 5) (.var 4)))),
    output := appTerm (symTerm 6) (appTerm (.var 2) (appTerm (.var 3) (.var 4))),
    body := [.ask abstractListRelation (triple (.var 0) (.var 1) (.var 5)) (.var 3)] }

def abstractNil : Clause :=
  { relation := abstractListRelation, input := triple (.var 0) (.var 1) (symTerm 0), output := symTerm 0,
    body := [] }

def abstractCons : Clause :=
  { relation := abstractListRelation, input := triple (.var 0) (.var 1) (appTerm (.var 4) (.var 5)),
    output := appTerm (.var 2) (.var 3),
    body := [.ask abstractRelation (triple (.var 0) (.var 1) (.var 4)) (.var 2),
      .ask abstractListRelation (triple (.var 0) (.var 1) (.var 5)) (.var 3)] }

/-- **The clauses of abstracting.** -/
def abstractClauses : List Clause :=
  [abstractBelow, abstractHere, abstractAbove, abstractFvar, abstractApply, abstractLambda, abstractMultiLambda,
    abstractSubst, abstractCollection, abstractNil, abstractCons]

theorem abstractClauses_moded : ∀ c ∈ abstractClauses, Moded c := by
  intro c inside
  simp only [abstractClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact DemandTransformation.moded_of_check (by decide)

theorem abstractClauses_relation :
    ∀ c ∈ abstractClauses, abstractRelation ≤ c.relation ∧ c.relation ≤ abstractListRelation := by decide

/-- **A program with the clauses of abstracting**, beside the clauses of scopes. -/
structure AbstractProgram (program : List Clause) : Prop where
  scope : ScopeProgram program
  included : ∀ c ∈ abstractClauses, c ∈ program
  only : ∀ c ∈ program, abstractRelation ≤ c.relation → c.relation ≤ abstractListRelation → c ∈ abstractClauses

section Abstracting

variable {R : Relations} {program : List Clause}

theorem abstractClause_of (abstracts : AbstractProgram program) {c : Clause} (member : c ∈ program) {r : ℕ}
    (isR : c.relation = r) (low : abstractRelation ≤ r) (high : r ≤ abstractListRelation) : c ∈ abstractClauses :=
  abstracts.only c member (isR ▸ low) (isR ▸ high)

mutual
  /-- **An abstracted term instantiates back to the term it came from.** -/
  theorem abstract_instantiate (abstracts : AbstractProgram program) : ∀ (depth : ℕ) (P x y : Expr),
      DerivesAt R program depth abstractRelation (.app P x) y → Derives R program instantiateRelation (.app P y) x
    | 0, _, _, _, derived => derived.elim
    | depth + 1, P, x, y, derived => by
        obtain ⟨cl, member, isR, θ, input, output, goals⟩ := derived
        have inside := abstractClause_of abstracts member isR (by decide) (by decide)
        simp only [abstractClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first
          | exact absurd isR (by decide)
          | skip
        · simp only [abstractBelow, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have clause := derives_of_clause (R := R) (abstracts.scope.included instantiateBelow
            (by simp [scopeClauses])) θ fun g inside => by
              simp only [instantiateBelow, List.mem_cons, List.not_mem_nil, or_false] at inside
              subst inside
              exact DemandTransformation.goalHolds_mono (fun _ _ _ held => ⟨depth, held⟩)
                (goals _ List.mem_cons_self)
          simpa [instantiateBelow, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] using clause
        · simp only [abstractHere, triple, bvarTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have clause := derives_of_clause (R := R) (abstracts.scope.included instantiateHere
            (by simp [scopeClauses])) θ fun g inside => by
              simp only [instantiateHere, List.mem_cons, List.not_mem_nil, or_false] at inside
              subst inside
              exact DemandTransformation.goalHolds_mono (fun _ _ _ held => ⟨depth, held⟩)
                (goals _ List.mem_cons_self)
          simpa [instantiateHere, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] using clause
        · simp only [abstractAbove, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have clause := derives_of_clause (R := R) (abstracts.scope.included instantiateAbove
            (by simp [scopeClauses])) θ fun g inside => by
              simp only [instantiateAbove, List.mem_cons, List.not_mem_nil, or_false] at inside
              subst inside
              exact DemandTransformation.goalHolds_mono (fun _ _ _ held => ⟨depth, held⟩)
                (goals _ List.mem_cons_self)
          simpa [instantiateAbove, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] using clause
        · simp only [abstractFvar, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have clause := derives_of_clause (R := R) (abstracts.scope.included instantiateFvar
            (by simp [scopeClauses])) θ fun g inside => absurd inside List.not_mem_nil
          simpa [instantiateFvar, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] using clause
        · simp only [abstractApply, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm,
            DemandTransformation.inst_unknown] at asked
          have inner := abstractList_instantiate abstracts depth _ _ _ asked
          have clause := derives_of_clause (R := R) (abstracts.scope.included instantiateApply
            (by simp [scopeClauses])) θ fun g inside => by
              simp only [instantiateApply, List.mem_cons, List.not_mem_nil, or_false] at inside
              subst inside
              simpa [goalHolds, triple, succTerm] using inner
          simpa [instantiateApply, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] using clause
        · simp only [abstractLambda, triple, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] at asked
          have inner := abstract_instantiate abstracts depth _ _ _ asked
          have clause := derives_of_clause (R := R) (abstracts.scope.included instantiateLambda
            (by simp [scopeClauses])) θ fun g inside => by
              simp only [instantiateLambda, List.mem_cons, List.not_mem_nil, or_false] at inside
              subst inside
              simpa [goalHolds, triple, succTerm] using inner
          simpa [instantiateLambda, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] using clause
        · simp only [abstractMultiLambda, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have asked := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm,
            DemandTransformation.inst_unknown] at asked
          have inner := abstract_instantiate abstracts depth _ _ _ asked
          have clause := derives_of_clause (R := R) (abstracts.scope.included instantiateMultiLambda
            (by simp [scopeClauses])) θ fun g inside => by
              simp only [instantiateMultiLambda, List.mem_cons, List.not_mem_nil, or_false] at inside
              rcases inside with rfl | rfl
              · exact DemandTransformation.goalHolds_mono (fun _ _ _ held => ⟨depth, held⟩)
                  (goals _ List.mem_cons_self)
              · simpa [goalHolds, triple] using inner
          simpa [instantiateMultiLambda, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] using clause
        · simp only [abstractSubst, triple, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have firstAsked := goals _ List.mem_cons_self
          have secondAsked := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, triple, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] at firstAsked secondAsked
          have first := abstract_instantiate abstracts depth _ _ _ firstAsked
          have second := abstract_instantiate abstracts depth _ _ _ secondAsked
          have clause := derives_of_clause (R := R) (abstracts.scope.included instantiateSubst
            (by simp [scopeClauses])) θ fun g inside => by
              simp only [instantiateSubst, List.mem_cons, List.not_mem_nil, or_false] at inside
              rcases inside with rfl | rfl
              · simpa [goalHolds, triple, succTerm] using first
              · simpa [goalHolds, triple] using second
          simpa [instantiateSubst, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] using clause
        · simp only [abstractCollection, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm,
            DemandTransformation.inst_unknown] at asked
          have inner := abstractList_instantiate abstracts depth _ _ _ asked
          have clause := derives_of_clause (R := R) (abstracts.scope.included instantiateCollection
            (by simp [scopeClauses])) θ fun g inside => by
              simp only [instantiateCollection, List.mem_cons, List.not_mem_nil, or_false] at inside
              subst inside
              simpa [goalHolds, triple, succTerm] using inner
          simpa [instantiateCollection, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] using clause

  /-- The same, for lists. -/
  theorem abstractList_instantiate (abstracts : AbstractProgram program) : ∀ (depth : ℕ) (P x y : Expr),
      DerivesAt R program depth abstractListRelation (.app P x) y → Derives R program instantiateListRelation (.app P y) x
    | 0, _, _, _, derived => derived.elim
    | depth + 1, P, x, y, derived => by
        obtain ⟨cl, member, isR, θ, input, output, goals⟩ := derived
        have inside := abstractClause_of abstracts member isR (by decide) (by decide)
        simp only [abstractClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first
          | exact absurd isR (by decide)
          | skip
        · simp only [abstractNil, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have clause := derives_of_clause (R := R) (abstracts.scope.included instantiateNil
            (by simp [scopeClauses])) θ fun g inside => absurd inside List.not_mem_nil
          simpa [instantiateNil, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] using clause
        · simp only [abstractCons, triple, RootRewritesOnTheStep.inst_appTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have firstAsked := goals _ List.mem_cons_self
          have secondAsked := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm,
            DemandTransformation.inst_unknown] at firstAsked secondAsked
          have first := abstract_instantiate abstracts depth _ _ _ firstAsked
          have second := abstractList_instantiate abstracts depth _ _ _ secondAsked
          have clause := derives_of_clause (R := R) (abstracts.scope.included instantiateCons
            (by simp [scopeClauses])) θ fun g inside => by
              simp only [instantiateCons, List.mem_cons, List.not_mem_nil, or_false] at inside
              rcases inside with rfl | rfl
              · simpa [goalHolds, triple, succTerm] using first
              · simpa [goalHolds, triple] using second
          simpa [instantiateCons, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] using clause
end

mutual
  /-- **An instantiated term abstracts back to the term it came from.** -/
  theorem instantiate_abstract (abstracts : AbstractProgram program) : ∀ (depth : ℕ) (P x y : Expr),
      DerivesAt R program depth instantiateRelation (.app P x) y → Derives R program abstractRelation (.app P y) x
    | 0, _, _, _, derived => derived.elim
    | depth + 1, P, x, y, derived => by
        obtain ⟨cl, member, isR, θ, input, output, goals⟩ := derived
        have inside := scopeClause_of abstracts.scope member isR (by decide) (by decide)
        simp only [scopeClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first
          | exact absurd isR (by decide)
          | skip
        · simp only [instantiateBelow, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have clause := derives_of_clause (R := R) (abstracts.included abstractBelow
            (by simp [abstractClauses])) θ fun g inside => by
              simp only [abstractBelow, List.mem_cons, List.not_mem_nil, or_false] at inside
              subst inside
              exact DemandTransformation.goalHolds_mono (fun _ _ _ held => ⟨depth, held⟩)
                (goals _ List.mem_cons_self)
          simpa [abstractBelow, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] using clause
        · simp only [instantiateHere, triple, bvarTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have clause := derives_of_clause (R := R) (abstracts.included abstractHere
            (by simp [abstractClauses])) θ fun g inside => by
              simp only [abstractHere, List.mem_cons, List.not_mem_nil, or_false] at inside
              subst inside
              exact DemandTransformation.goalHolds_mono (fun _ _ _ held => ⟨depth, held⟩)
                (goals _ List.mem_cons_self)
          simpa [abstractHere, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] using clause
        · simp only [instantiateAbove, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have clause := derives_of_clause (R := R) (abstracts.included abstractAbove
            (by simp [abstractClauses])) θ fun g inside => by
              simp only [abstractAbove, List.mem_cons, List.not_mem_nil, or_false] at inside
              subst inside
              exact DemandTransformation.goalHolds_mono (fun _ _ _ held => ⟨depth, held⟩)
                (goals _ List.mem_cons_self)
          simpa [abstractAbove, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] using clause
        · simp only [instantiateFvar, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have clause := derives_of_clause (R := R) (abstracts.included abstractFvar
            (by simp [abstractClauses])) θ fun g inside => absurd inside List.not_mem_nil
          simpa [abstractFvar, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] using clause
        · simp only [instantiateApply, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm,
            DemandTransformation.inst_unknown] at asked
          have inner := instantiateList_abstract abstracts depth _ _ _ asked
          have clause := derives_of_clause (R := R) (abstracts.included abstractApply
            (by simp [abstractClauses])) θ fun g inside => by
              simp only [abstractApply, List.mem_cons, List.not_mem_nil, or_false] at inside
              subst inside
              simpa [goalHolds, triple, succTerm] using inner
          simpa [abstractApply, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] using clause
        · simp only [instantiateLambda, triple, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] at asked
          have inner := instantiate_abstract abstracts depth _ _ _ asked
          have clause := derives_of_clause (R := R) (abstracts.included abstractLambda
            (by simp [abstractClauses])) θ fun g inside => by
              simp only [abstractLambda, List.mem_cons, List.not_mem_nil, or_false] at inside
              subst inside
              simpa [goalHolds, triple, succTerm] using inner
          simpa [abstractLambda, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] using clause
        · simp only [instantiateMultiLambda, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have asked := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm,
            DemandTransformation.inst_unknown] at asked
          have inner := instantiate_abstract abstracts depth _ _ _ asked
          have clause := derives_of_clause (R := R) (abstracts.included abstractMultiLambda
            (by simp [abstractClauses])) θ fun g inside => by
              simp only [abstractMultiLambda, List.mem_cons, List.not_mem_nil, or_false] at inside
              rcases inside with rfl | rfl
              · exact DemandTransformation.goalHolds_mono (fun _ _ _ held => ⟨depth, held⟩)
                  (goals _ List.mem_cons_self)
              · simpa [goalHolds, triple] using inner
          simpa [abstractMultiLambda, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] using clause
        · simp only [instantiateSubst, triple, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have firstAsked := goals _ List.mem_cons_self
          have secondAsked := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, triple, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] at firstAsked secondAsked
          have first := instantiate_abstract abstracts depth _ _ _ firstAsked
          have second := instantiate_abstract abstracts depth _ _ _ secondAsked
          have clause := derives_of_clause (R := R) (abstracts.included abstractSubst
            (by simp [abstractClauses])) θ fun g inside => by
              simp only [abstractSubst, List.mem_cons, List.not_mem_nil, or_false] at inside
              rcases inside with rfl | rfl
              · simpa [goalHolds, triple, succTerm] using first
              · simpa [goalHolds, triple] using second
          simpa [abstractSubst, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] using clause
        · simp only [instantiateCollection, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm,
            DemandTransformation.inst_unknown] at asked
          have inner := instantiateList_abstract abstracts depth _ _ _ asked
          have clause := derives_of_clause (R := R) (abstracts.included abstractCollection
            (by simp [abstractClauses])) θ fun g inside => by
              simp only [abstractCollection, List.mem_cons, List.not_mem_nil, or_false] at inside
              subst inside
              simpa [goalHolds, triple, succTerm] using inner
          simpa [abstractCollection, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] using clause

  /-- The same, for lists. -/
  theorem instantiateList_abstract (abstracts : AbstractProgram program) : ∀ (depth : ℕ) (P x y : Expr),
      DerivesAt R program depth instantiateListRelation (.app P x) y → Derives R program abstractListRelation (.app P y) x
    | 0, _, _, _, derived => derived.elim
    | depth + 1, P, x, y, derived => by
        obtain ⟨cl, member, isR, θ, input, output, goals⟩ := derived
        have inside := scopeClause_of abstracts.scope member isR (by decide) (by decide)
        simp only [scopeClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first
          | exact absurd isR (by decide)
          | skip
        · simp only [instantiateNil, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have clause := derives_of_clause (R := R) (abstracts.included abstractNil
            (by simp [abstractClauses])) θ fun g inside => absurd inside List.not_mem_nil
          simpa [abstractNil, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] using clause
        · simp only [instantiateCons, triple, RootRewritesOnTheStep.inst_appTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨rfl, rfl⟩ := input
          subst output
          have firstAsked := goals _ List.mem_cons_self
          have secondAsked := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm,
            DemandTransformation.inst_unknown] at firstAsked secondAsked
          have first := instantiate_abstract abstracts depth _ _ _ firstAsked
          have second := instantiateList_abstract abstracts depth _ _ _ secondAsked
          have clause := derives_of_clause (R := R) (abstracts.included abstractCons
            (by simp [abstractClauses])) θ fun g inside => by
              simp only [abstractCons, List.mem_cons, List.not_mem_nil, or_false] at inside
              rcases inside with rfl | rfl
              · simpa [goalHolds, triple, succTerm] using first
              · simpa [goalHolds, triple] using second
          simpa [abstractCons, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown] using clause
end

mutual
  /-- **A derived abstraction of a term instantiates to it.** -/
  theorem abstract_sound (abstracts : AbstractProgram program) : ∀ (depth d : ℕ) (r u : Pattern) (w : Expr),
      DerivesAt R program depth abstractRelation (.app (.app (numeral d) (encode r)) (encode u)) w →
        ∃ b, w = encode b ∧ instantiateBVarAt d r b = u
    | 0, _, _, _, _, derived => derived.elim
    | depth + 1, d, r, u, w, derived => by
        obtain ⟨cl, member, isR, θ, input, output, goals⟩ := derived
        have inside := abstractClause_of abstracts member isR (by decide) (by decide)
        simp only [abstractClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first
          | exact absurd isR (by decide)
          | skip
        · simp only [abstractBelow, triple, bvarTerm, RootRewritesOnTheStep.inst_appTerm,
            RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨dIs, -⟩, uIs⟩ := input
          obtain ⟨index, rfl, indexIs⟩ := encode_bvar_inv uIs
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, succTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, indexIs, dIs] at asked
          have below := atMost_sound abstracts.scope depth (index + 1) d _ asked
          refine ⟨.bvar index, by rw [← output, indexIs]; rfl, ?_⟩
          rw [instantiateBVarAt_bvar, if_pos (by omega)]
        · simp only [abstractHere, triple, bvarTerm, RootRewritesOnTheStep.inst_appTerm,
            RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨dIs, rIs⟩, uIs⟩ := input
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, dIs, rIs, uIs] at asked
          have lifted := lift_sound abstracts.scope depth 0 d r _ asked
          refine ⟨.bvar d, by rw [← output, dIs]; rfl, ?_⟩
          rw [instantiateBVarAt_bvar, if_neg (by omega), if_pos rfl]
          exact (RootRewritesOnTheStep.encode_injective lifted).symm
        · simp only [abstractAbove, triple, bvarTerm, succTerm, RootRewritesOnTheStep.inst_appTerm,
            RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨dIs, -⟩, uIs⟩ := input
          obtain ⟨index, rfl, indexIs⟩ := encode_bvar_inv uIs
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, dIs,
            indexIs] at asked
          have above := atMost_sound abstracts.scope depth d index _ asked
          refine ⟨.bvar (index + 1), by rw [← output, indexIs]; rfl, ?_⟩
          rw [instantiateBVarAt_bvar, if_neg (by omega), if_neg (by omega)]
          rfl
        · simp only [abstractFvar, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨-, uIs⟩ := input
          obtain ⟨name, rfl, nameIs⟩ := encode_fvar_inv uIs
          refine ⟨.fvar name, by rw [← output, nameIs]; rfl, ?_⟩
          rw [instantiateBVarAt]
        · simp only [abstractApply, triple, RootRewritesOnTheStep.inst_appTerm,
            RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨dIs, rIs⟩, uIs⟩ := input
          obtain ⟨label, arguments, rfl, labelIs, argumentsIs⟩ := encode_apply_inv uIs
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, dIs,
            rIs, argumentsIs] at asked
          obtain ⟨bs, bsIs, instantiated⟩ := abstractList_sound abstracts depth d r arguments _ asked
          refine ⟨.apply label bs, by rw [← output, labelIs, bsIs]; rfl, ?_⟩
          rw [instantiateBVarAt, instantiated]
        · simp only [abstractLambda, triple, RootRewritesOnTheStep.inst_appTerm,
            RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨dIs, rIs⟩, uIs⟩ := input
          obtain ⟨binder, body, rfl, binderIs, bodyIs⟩ := encode_lambda_inv uIs
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, succTerm, RootRewritesOnTheStep.inst_appTerm,
            RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, dIs, rIs, bodyIs] at asked
          obtain ⟨b, bIs, instantiated⟩ := abstract_sound abstracts depth (d + 1) r body _ asked
          refine ⟨.lambda binder b, by rw [← output, binderIs, bIs]; rfl, ?_⟩
          rw [instantiateBVarAt, instantiated]
        · simp only [abstractMultiLambda, triple, RootRewritesOnTheStep.inst_appTerm,
            RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨dIs, rIs⟩, uIs⟩ := input
          obtain ⟨arity, binders, body, rfl, arityIs, bindersIs, bodyIs⟩ := encode_multiLambda_inv uIs
          have first := goals _ List.mem_cons_self
          have second := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, dIs,
            arityIs] at first
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, rIs,
            bodyIs, add_sound abstracts.scope depth d arity _ first] at second
          obtain ⟨b, bIs, instantiated⟩ := abstract_sound abstracts depth (d + arity) r body _ second
          refine ⟨.multiLambda arity binders b, by rw [← output, arityIs, bindersIs, bIs]; rfl, ?_⟩
          rw [instantiateBVarAt, instantiated]
        · simp only [abstractSubst, triple, RootRewritesOnTheStep.inst_appTerm,
            RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨dIs, rIs⟩, uIs⟩ := input
          obtain ⟨body, value, rfl, bodyIs, valueIs⟩ := encode_subst_inv uIs
          have first := goals _ List.mem_cons_self
          have second := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, triple, succTerm, RootRewritesOnTheStep.inst_appTerm,
            RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, dIs, rIs, bodyIs,
            valueIs] at first second
          obtain ⟨b, bIs, bInstantiated⟩ := abstract_sound abstracts depth (d + 1) r body _ first
          obtain ⟨c, cIs, cInstantiated⟩ := abstract_sound abstracts depth d r value _ second
          refine ⟨.subst b c, by rw [← output, bIs, cIs]; rfl, ?_⟩
          rw [instantiateBVarAt, bInstantiated, cInstantiated]
        · simp only [abstractCollection, triple, RootRewritesOnTheStep.inst_appTerm,
            RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨dIs, rIs⟩, uIs⟩ := input
          obtain ⟨kind, elements, rest, rfl, kindIs, elementsIs, restIs⟩ := encode_collection_inv uIs
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, dIs,
            rIs, elementsIs] at asked
          obtain ⟨bs, bsIs, instantiated⟩ := abstractList_sound abstracts depth d r elements _ asked
          refine ⟨.collection kind bs rest, by rw [← output, kindIs, restIs, bsIs]; rfl, ?_⟩
          rw [instantiateBVarAt, instantiated]

  theorem abstractList_sound (abstracts : AbstractProgram program) : ∀ (depth d : ℕ) (r : Pattern)
      (us : List Pattern) (w : Expr), DerivesAt R program depth abstractListRelation
        (.app (.app (numeral d) (encode r)) (encodeList us)) w →
        ∃ bs, w = encodeList bs ∧ bs.map (instantiateBVarAt d r) = us
    | 0, _, _, _, _, derived => derived.elim
    | depth + 1, d, r, us, w, derived => by
        obtain ⟨cl, member, isR, θ, input, output, goals⟩ := derived
        have inside := abstractClause_of abstracts member isR (by decide) (by decide)
        simp only [abstractClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first
          | exact absurd isR (by decide)
          | skip
        · simp only [abstractNil, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨-, usIs⟩ := input
          rw [encodeList_nil_inv usIs]
          exact ⟨[], by rw [← output]; rfl, rfl⟩
        · simp only [abstractCons, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
            Expr.app.injEq] at input output
          obtain ⟨⟨dIs, rIs⟩, usIs⟩ := input
          obtain ⟨x, rest, rfl, xIs, restIs⟩ := encodeList_cons_inv usIs
          have first := goals _ List.mem_cons_self
          have second := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, dIs,
            rIs, xIs, restIs] at first second
          obtain ⟨b, bIs, bInstantiated⟩ := abstract_sound abstracts depth d r x _ first
          obtain ⟨bs, bsIs, bsInstantiated⟩ := abstractList_sound abstracts depth d r rest _ second
          refine ⟨b :: bs, by rw [← output, bIs, bsIs]; rfl, ?_⟩
          rw [List.map_cons, bInstantiated, bsInstantiated]
end

/-- **The abstracting clauses derive exactly the terms that instantiate to a given term.** -/
theorem abstract_iff (abstracts : AbstractProgram program) (d : ℕ) (r u : Pattern) {w : Expr} :
    Derives R program abstractRelation (.app (.app (numeral d) (encode r)) (encode u)) w ↔
      ∃ b, w = encode b ∧ instantiateBVarAt d r b = u := by
  constructor
  · rintro ⟨depth, derived⟩
    exact abstract_sound abstracts depth d r u w derived
  · rintro ⟨b, rfl, rfl⟩
    obtain ⟨depth, derived⟩ := instantiate_complete abstracts.scope r d b
    exact instantiate_abstract abstracts depth _ _ _ derived

end Abstracting


end Mettapedia.GSLT.Compilation.Uniform.ScopeClauses

#print axioms Mettapedia.GSLT.Compilation.Uniform.ScopeClauses.lift_iff
#print axioms Mettapedia.GSLT.Compilation.Uniform.ScopeClauses.instantiate_iff
#print axioms Mettapedia.GSLT.Compilation.Uniform.ScopeClauses.lower_lift
#print axioms Mettapedia.GSLT.Compilation.Uniform.ScopeClauses.lift_lower
#print axioms Mettapedia.GSLT.Compilation.Uniform.ScopeClauses.abstract_instantiate
#print axioms Mettapedia.GSLT.Compilation.Uniform.ScopeClauses.instantiate_abstract
#print axioms Mettapedia.GSLT.Compilation.Uniform.ScopeClauses.abstract_iff
