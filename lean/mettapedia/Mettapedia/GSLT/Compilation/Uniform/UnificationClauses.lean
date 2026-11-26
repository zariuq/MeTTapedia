import Mettapedia.GSLT.Compilation.Uniform.DemandTransformation
import Mettapedia.Logic.LP.UnificationComplete

/-!
# First-order unification as clauses

The rules of Martelli and Montanari as clauses of one relation on rows (`solveRelation`): a list of equations between
first-order terms is solved when the clauses derive it. Substituting a term for a variable, the occurs check and the
pairing of arguments are clauses too. The terms are those of a signature whose constants, function symbols and
variables have rows (`Codes`); two variables are told apart by a relation that the user of these clauses supplies
(`differRelation`).

The clauses derive a list of equations exactly when the logic-programming kernel's derivations do
(`derives_solve_iff`), and those lists are exactly the unifiable ones (`solve_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.UnificationClauses

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic
open RuleSyntax.ComputedConditions (Relations)
open RootRewritesOnTheStep (symTerm appTerm)
open DemandTransformation (Goal Clause goalHolds DerivesAt Derives derives_of_clause)
open Mettapedia.Logic.LP (LPSignature Subst UnifyDerives finPairsToList Unifies)

/-! ## Terms as rows -/

/-- **Rows for a signature**: constants and function symbols by injective codes, and variables by injective rows. -/
structure Codes (σ : LPSignature) where
  constant : σ.constants → ℕ
  constant_injective : Function.Injective constant
  symbol : σ.functionSymbols → ℕ
  symbol_injective : Function.Injective symbol
  unknown : σ.vars → Expr
  unknown_injective : Function.Injective unknown

/-- A list of rows as one row. -/
def listRow : List Expr → Expr
  | [] => .sym 0
  | first :: rest => .app first (listRow rest)

theorem listRow_injective : Function.Injective listRow := by
  intro first
  induction first with
  | nil => intro second same; cases second <;> simp_all [listRow]
  | cons x xs ih =>
      intro second same
      cases second with
      | nil => simp [listRow] at same
      | cons y ys =>
          simp only [listRow, Expr.app.injEq] at same
          rw [same.1, ih same.2]

variable {σ : LPSignature} (codes : Codes σ)

/-- **A term as a row.** -/
def termRow : Mettapedia.Logic.LP.Term σ → Expr
  | .var v => .app (.sym 0) (codes.unknown v)
  | .const c => .app (.sym 1) (.sym (codes.constant c))
  | .app f ts => .app (.sym 2) (.app (.sym (codes.symbol f)) (listRow (List.ofFn fun i => termRow (ts i))))

/-- A list of equations as a row. -/
def eqsRow : List (Mettapedia.Logic.LP.Term σ × Mettapedia.Logic.LP.Term σ) → Expr
  | [] => .sym 0
  | (s, t) :: rest => .app (.app (termRow codes s) (termRow codes t)) (eqsRow rest)

theorem termRow_injective : Function.Injective (termRow codes) := by
  intro first
  induction first with
  | var v =>
      intro second same
      cases second with
      | var w =>
          simp only [termRow, Expr.app.injEq, true_and] at same
          rw [codes.unknown_injective same]
      | const _ => simp [termRow] at same
      | app _ _ => simp [termRow] at same
  | const c =>
      intro second same
      cases second with
      | var _ => simp [termRow] at same
      | const d =>
          simp only [termRow, Expr.app.injEq, Expr.sym.injEq, true_and] at same
          rw [codes.constant_injective same]
      | app _ _ => simp [termRow] at same
  | app f ts ih =>
      intro second same
      cases second with
      | var _ => simp [termRow] at same
      | const _ => simp [termRow] at same
      | app g us =>
          simp only [termRow, Expr.app.injEq, Expr.sym.injEq, true_and] at same
          obtain ⟨symbols, arguments⟩ := same
          obtain rfl := codes.symbol_injective symbols
          have rows := List.ofFn_injective (listRow_injective arguments)
          have pointwise : ∀ i, ts i = us i := fun i => ih i (congrFun rows i)
          rw [funext pointwise]

theorem eqsRow_injective : Function.Injective (eqsRow codes) := by
  intro first
  induction first with
  | nil => intro second same; cases second <;> simp_all [eqsRow]
  | cons pair rest ih =>
      intro second same
      obtain ⟨s, t⟩ := pair
      cases second with
      | nil => simp [eqsRow] at same
      | cons other others =>
          obtain ⟨s', t'⟩ := other
          simp only [eqsRow, Expr.app.injEq] at same
          rw [termRow_injective codes same.1.1, termRow_injective codes same.1.2, ih same.2]

/-- The rows of the arguments of an application. -/
theorem termRow_app (f : σ.functionSymbols) (ts : Fin (σ.functionArity f) → Mettapedia.Logic.LP.Term σ) :
    termRow codes (.app f ts) =
      .app (.sym 2) (.app (.sym (codes.symbol f)) (listRow ((List.ofFn ts).map (termRow codes)))) := by
  rw [termRow, List.map_ofFn]
  rfl

/-! ## The clauses -/

/-- The relation that solves a list of equations. -/
def solveRelation : ℕ := 7

/-- The relation that substitutes a term for a variable in a term. -/
def substituteRelation : ℕ := 8

/-- The relation that substitutes a term for a variable in a list of equations. -/
def substituteEqsRelation : ℕ := 9

/-- The relation that holds when a variable does not occur in a term. -/
def notOccursRelation : ℕ := 10

/-- The relation that holds when a variable does not occur in a list of terms. -/
def notOccursArgsRelation : ℕ := 11

/-- The relation that pairs two lists of arguments before some equations. -/
def pairArgsRelation : ℕ := 12

/-- The relation that substitutes a term for a variable in a list of terms. -/
def substituteArgsRelation : ℕ := 13

/-- The relation that tells two variables apart; its clauses come with the variables. -/
def differRelation : ℕ := 14

/-- The row pattern of a variable whose row is an unknown. -/
def varPattern (x : ℕ) : Tm := appTerm (symTerm 0) (.var x)

/-- The row pattern of a constant whose code row is an unknown. -/
def constPattern (x : ℕ) : Tm := appTerm (symTerm 1) (.var x)

/-- The row pattern of an application whose symbol and arguments are unknowns. -/
def appPattern (f arguments : ℕ) : Tm := appTerm (symTerm 2) (appTerm (.var f) (.var arguments))

/-- Three rows as one. -/
def triple (a b c : Tm) : Tm := appTerm (appTerm a b) c

/-- The row of no information. -/
def unit : Tm := symTerm 0

def solveNil : Clause := { relation := solveRelation, input := symTerm 0, output := unit, body := [] }

def solveSameVar : Clause :=
  { relation := solveRelation, input := appTerm (appTerm (varPattern 0) (varPattern 0)) (.var 1), output := unit,
    body := [.ask solveRelation (.var 1) unit] }

def solveEliminate : Clause :=
  { relation := solveRelation, input := appTerm (appTerm (varPattern 0) (.var 1)) (.var 2), output := unit,
    body := [.ask notOccursRelation (appTerm (.var 0) (.var 1)) unit,
      .ask substituteEqsRelation (triple (.var 0) (.var 1) (.var 2)) (.var 3), .ask solveRelation (.var 3) unit] }

def solveSameConst : Clause :=
  { relation := solveRelation, input := appTerm (appTerm (constPattern 0) (constPattern 0)) (.var 1), output := unit,
    body := [.ask solveRelation (.var 1) unit] }

def solveConstVar : Clause :=
  { relation := solveRelation, input := appTerm (appTerm (constPattern 0) (varPattern 1)) (.var 2), output := unit,
    body := [.ask substituteEqsRelation (triple (.var 1) (constPattern 0) (.var 2)) (.var 3),
      .ask solveRelation (.var 3) unit] }

def solveAppVar : Clause :=
  { relation := solveRelation, input := appTerm (appTerm (appPattern 0 1) (varPattern 2)) (.var 3), output := unit,
    body := [.ask notOccursRelation (appTerm (.var 2) (appPattern 0 1)) unit,
      .ask substituteEqsRelation (triple (.var 2) (appPattern 0 1) (.var 3)) (.var 4),
      .ask solveRelation (.var 4) unit] }

def solveDecompose : Clause :=
  { relation := solveRelation, input := appTerm (appTerm (appPattern 0 1) (appPattern 0 2)) (.var 3), output := unit,
    body := [.ask pairArgsRelation (triple (.var 1) (.var 2) (.var 3)) (.var 4), .ask solveRelation (.var 4) unit] }

def substituteSame : Clause :=
  { relation := substituteRelation, input := triple (.var 0) (.var 1) (varPattern 0), output := .var 1, body := [] }

def substituteOther : Clause :=
  { relation := substituteRelation, input := triple (.var 0) (.var 1) (varPattern 2), output := varPattern 2,
    body := [.ask differRelation (appTerm (.var 0) (.var 2)) unit] }

def substituteConst : Clause :=
  { relation := substituteRelation, input := triple (.var 0) (.var 1) (constPattern 2), output := constPattern 2,
    body := [] }

def substituteApp : Clause :=
  { relation := substituteRelation, input := triple (.var 0) (.var 1) (appPattern 2 3), output := appPattern 2 4,
    body := [.ask substituteArgsRelation (triple (.var 0) (.var 1) (.var 3)) (.var 4)] }

def substituteArgsNil : Clause :=
  { relation := substituteArgsRelation, input := triple (.var 0) (.var 1) (symTerm 0), output := symTerm 0,
    body := [] }

def substituteArgsCons : Clause :=
  { relation := substituteArgsRelation, input := triple (.var 0) (.var 1) (appTerm (.var 2) (.var 3)),
    output := appTerm (.var 4) (.var 5),
    body := [.ask substituteRelation (triple (.var 0) (.var 1) (.var 2)) (.var 4),
      .ask substituteArgsRelation (triple (.var 0) (.var 1) (.var 3)) (.var 5)] }

def substituteEqsNil : Clause :=
  { relation := substituteEqsRelation, input := triple (.var 0) (.var 1) (symTerm 0), output := symTerm 0,
    body := [] }

def substituteEqsCons : Clause :=
  { relation := substituteEqsRelation, input := triple (.var 0) (.var 1) (appTerm (appTerm (.var 2) (.var 3)) (.var 4)),
    output := appTerm (appTerm (.var 5) (.var 6)) (.var 7),
    body := [.ask substituteRelation (triple (.var 0) (.var 1) (.var 2)) (.var 5),
      .ask substituteRelation (triple (.var 0) (.var 1) (.var 3)) (.var 6),
      .ask substituteEqsRelation (triple (.var 0) (.var 1) (.var 4)) (.var 7)] }

def notOccursVar : Clause :=
  { relation := notOccursRelation, input := appTerm (.var 0) (varPattern 1), output := unit,
    body := [.ask differRelation (appTerm (.var 0) (.var 1)) unit] }

def notOccursConst : Clause :=
  { relation := notOccursRelation, input := appTerm (.var 0) (constPattern 1), output := unit, body := [] }

def notOccursApp : Clause :=
  { relation := notOccursRelation, input := appTerm (.var 0) (appPattern 1 2), output := unit,
    body := [.ask notOccursArgsRelation (appTerm (.var 0) (.var 2)) unit] }

def notOccursArgsNil : Clause :=
  { relation := notOccursArgsRelation, input := appTerm (.var 0) (symTerm 0), output := unit, body := [] }

def notOccursArgsCons : Clause :=
  { relation := notOccursArgsRelation, input := appTerm (.var 0) (appTerm (.var 1) (.var 2)), output := unit,
    body := [.ask notOccursRelation (appTerm (.var 0) (.var 1)) unit,
      .ask notOccursArgsRelation (appTerm (.var 0) (.var 2)) unit] }

def pairArgsNil : Clause :=
  { relation := pairArgsRelation, input := triple (symTerm 0) (symTerm 0) (.var 0), output := .var 0, body := [] }

def pairArgsCons : Clause :=
  { relation := pairArgsRelation,
    input := triple (appTerm (.var 0) (.var 1)) (appTerm (.var 2) (.var 3)) (.var 4),
    output := appTerm (appTerm (.var 0) (.var 2)) (.var 5),
    body := [.ask pairArgsRelation (triple (.var 1) (.var 3) (.var 4)) (.var 5)] }

/-- **The clauses of unification.** -/
def unificationClauses : List Clause :=
  [solveNil, solveSameVar, solveEliminate, solveSameConst, solveConstVar, solveAppVar, solveDecompose,
    substituteSame, substituteOther, substituteConst, substituteApp, substituteArgsNil, substituteArgsCons,
    substituteEqsNil, substituteEqsCons, notOccursVar, notOccursConst, notOccursApp, notOccursArgsNil,
    notOccursArgsCons, pairArgsNil, pairArgsCons]

theorem unificationClauses_moded : ∀ c ∈ unificationClauses, DemandTransformation.Moded c := by
  intro c inside
  simp only [unificationClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact DemandTransformation.moded_of_check (by decide)

theorem unificationClauses_relation :
    ∀ c ∈ unificationClauses, solveRelation ≤ c.relation ∧ c.relation ≤ substituteArgsRelation := by decide

/-! ## Reading terms off their rows -/

theorem termRow_var_inv {s : Mettapedia.Logic.LP.Term σ} {u : Expr} (same : Expr.app (.sym 0) u = termRow codes s) :
    ∃ v, s = .var v ∧ u = codes.unknown v := by
  cases s with
  | var v => simp only [termRow, Expr.app.injEq, true_and] at same; exact ⟨v, rfl, same⟩
  | const _ => simp [termRow] at same
  | app _ _ => simp [termRow] at same

theorem termRow_const_inv {s : Mettapedia.Logic.LP.Term σ} {u : Expr} (same : Expr.app (.sym 1) u = termRow codes s) :
    ∃ c, s = .const c ∧ u = .sym (codes.constant c) := by
  cases s with
  | var _ => simp [termRow] at same
  | const c => simp only [termRow, Expr.app.injEq, true_and] at same; exact ⟨c, rfl, same⟩
  | app _ _ => simp [termRow] at same

theorem termRow_app_inv {s : Mettapedia.Logic.LP.Term σ} {a b : Expr}
    (same : Expr.app (.sym 2) (.app a b) = termRow codes s) :
    ∃ f ts, s = .app f ts ∧ a = .sym (codes.symbol f) ∧ b = listRow ((List.ofFn ts).map (termRow codes)) := by
  cases s with
  | var _ => simp [termRow] at same
  | const _ => simp [termRow] at same
  | app f ts =>
      rw [termRow_app] at same
      simp only [Expr.app.injEq, true_and] at same
      exact ⟨f, ts, rfl, same.1, same.2⟩

theorem listRow_nil_inv {xs : List (Mettapedia.Logic.LP.Term σ)} (same : Expr.sym 0 = listRow (xs.map (termRow codes))) :
    xs = [] := by
  cases xs with
  | nil => rfl
  | cons _ _ => simp [listRow] at same

theorem listRow_cons_inv {xs : List (Mettapedia.Logic.LP.Term σ)} {a b : Expr}
    (same : Expr.app a b = listRow (xs.map (termRow codes))) :
    ∃ x rest, xs = x :: rest ∧ a = termRow codes x ∧ b = listRow (rest.map (termRow codes)) := by
  cases xs with
  | nil => simp [listRow] at same
  | cons x rest =>
      simp only [List.map_cons, listRow, Expr.app.injEq] at same
      exact ⟨x, rest, rfl, same.1, same.2⟩

theorem eqsRow_nil_inv {eqs : List (Mettapedia.Logic.LP.Term σ × Mettapedia.Logic.LP.Term σ)}
    (same : Expr.sym 0 = eqsRow codes eqs) : eqs = [] := by
  cases eqs with
  | nil => rfl
  | cons _ _ => simp [eqsRow] at same

theorem eqsRow_cons_inv {eqs : List (Mettapedia.Logic.LP.Term σ × Mettapedia.Logic.LP.Term σ)} {a b c : Expr}
    (same : Expr.app (.app a b) c = eqsRow codes eqs) :
    ∃ s t rest, eqs = (s, t) :: rest ∧ a = termRow codes s ∧ b = termRow codes t ∧ c = eqsRow codes rest := by
  cases eqs with
  | nil => simp [eqsRow] at same
  | cons pair rest =>
      obtain ⟨s, t⟩ := pair
      simp only [eqsRow, Expr.app.injEq] at same
      exact ⟨s, t, rest, rfl, same.1.1, same.1.2, same.2⟩

/-! ## What the clauses derive -/

/-- **A program with the unification clauses**: the relations of unification have exactly these clauses, and the
relation that tells variables apart tells them apart. -/
structure UnificationProgram (R : Relations) (program : List Clause) : Prop where
  included : ∀ c ∈ unificationClauses, c ∈ program
  only : ∀ c ∈ program, solveRelation ≤ c.relation → c.relation ≤ substituteArgsRelation → c ∈ unificationClauses
  differ : ∀ v w, Derives R program differRelation (.app (codes.unknown v) (codes.unknown w)) (.sym 0) ↔ v ≠ w

open DemandTransformation (pick)

variable {R : Relations} {program : List Clause}

theorem clauseOf {c : Clause} (unification : UnificationProgram codes R program) (member : c ∈ program)
    {r : ℕ} (isR : c.relation = r) (low : solveRelation ≤ r) (high : r ≤ substituteArgsRelation) :
    c ∈ unificationClauses :=
  unification.only c member (isR ▸ low) (isR ▸ high)

variable [DecidableEq σ.vars]

theorem single_var_same (v : σ.vars) (t : Mettapedia.Logic.LP.Term σ) :
    (Subst.single v t).applyTerm (.var v) = t := by
  simp [Subst.applyTerm, Subst.single]

theorem single_var_other {v w : σ.vars} (t : Mettapedia.Logic.LP.Term σ) (apart : v ≠ w) :
    (Subst.single v t).applyTerm (.var w) = .var w := by
  simp [Subst.applyTerm, Subst.single, Ne.symm apart]

/-- **What substitution derives is the substituted term**, and in a list, the substituted list. -/
theorem substitute_sound (unification : UnificationProgram codes R program) : ∀ depth : ℕ,
    (∀ (v : σ.vars) (t s : Mettapedia.Logic.LP.Term σ) (w : Expr),
      DerivesAt R program depth substituteRelation (.app (.app (codes.unknown v) (termRow codes t)) (termRow codes s)) w →
        w = termRow codes ((Subst.single v t).applyTerm s)) ∧
    (∀ (v : σ.vars) (t : Mettapedia.Logic.LP.Term σ) (xs : List (Mettapedia.Logic.LP.Term σ)) (w : Expr),
      DerivesAt R program depth substituteArgsRelation
        (.app (.app (codes.unknown v) (termRow codes t)) (listRow (xs.map (termRow codes)))) w →
        w = listRow (xs.map (termRow codes ∘ (Subst.single v t).applyTerm))) := by
  intro depth
  induction depth with
  | zero => exact ⟨fun _ _ _ _ derived => derived.elim, fun _ _ _ _ derived => derived.elim⟩
  | succ depth ih =>
    constructor
    · intro v t s w derived
      obtain ⟨c, member, isSubstitute, θ, input, output, goals⟩ := derived
      have inside := clauseOf codes unification member isSubstitute (by decide) (by decide)
      simp only [unificationClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact absurd isSubstitute (by decide)
        | skip
      · simp only [substituteSame, triple, varPattern, RootRewritesOnTheStep.inst_appTerm,
          RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
        obtain ⟨⟨variableIs, termIs⟩, sIs⟩ := input
        obtain ⟨w', rfl, unknownIs⟩ := termRow_var_inv codes sIs
        rw [variableIs] at unknownIs
        obtain rfl := codes.unknown_injective unknownIs
        rw [← output, termIs, single_var_same]
      · simp only [substituteOther, triple, varPattern, RootRewritesOnTheStep.inst_appTerm,
          RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
        obtain ⟨⟨variableIs, -⟩, sIs⟩ := input
        obtain ⟨w', rfl, unknownIs⟩ := termRow_var_inv codes sIs
        have told := goals _ List.mem_cons_self
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, unit,
          RootRewritesOnTheStep.inst_symTerm, variableIs, unknownIs] at told
        have apart := (unification.differ v w').mp ⟨depth, told⟩
        rw [← output, single_var_other t apart, unknownIs]
        rfl
      · simp only [substituteConst, triple, constPattern, RootRewritesOnTheStep.inst_appTerm,
          RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
        obtain ⟨-, sIs⟩ := input
        obtain ⟨c, rfl, codeIs⟩ := termRow_const_inv codes sIs
        rw [← output, codeIs]
        rfl
      · simp only [substituteApp, triple, appPattern, RootRewritesOnTheStep.inst_appTerm,
          RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
        obtain ⟨⟨variableIs, termIs⟩, sIs⟩ := input
        obtain ⟨f, ts, rfl, symbolIs, argumentsIs⟩ := termRow_app_inv codes sIs
        have asked := goals _ List.mem_cons_self
        simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
          variableIs, termIs, argumentsIs] at asked
        have listed := (ih.2 v t (List.ofFn ts) _ asked)
        rw [← output, symbolIs, listed]
        simp [Subst.applyTerm, termRow_app, List.map_ofFn, Function.comp_def]
    · intro v t xs w derived
      obtain ⟨c, member, isArguments, θ, input, output, goals⟩ := derived
      have inside := clauseOf codes unification member isArguments (by decide) (by decide)
      simp only [unificationClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact absurd isArguments (by decide)
        | skip
      · simp only [substituteArgsNil, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown, Expr.app.injEq] at input output
        obtain ⟨-, listIs⟩ := input
        rw [listRow_nil_inv codes listIs, ← output]
        rfl
      · simp only [substituteArgsCons, triple, RootRewritesOnTheStep.inst_appTerm,
          DemandTransformation.inst_unknown, Expr.app.injEq] at input output
        obtain ⟨⟨variableIs, termIs⟩, listIs⟩ := input
        obtain ⟨x, rest, rfl, headIs, restIs⟩ := listRow_cons_inv codes listIs
        have first := goals _ List.mem_cons_self
        have second := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
        simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
          variableIs, termIs, headIs, restIs] at first second
        rw [← output, ih.1 v t x _ first, ih.2 v t rest _ second]
        rfl

theorem substituteArgs_complete (unification : UnificationProgram codes R program) (v : σ.vars)
    (t : Mettapedia.Logic.LP.Term σ) :
    ∀ (xs : List (Mettapedia.Logic.LP.Term σ)), (∀ x ∈ xs, Derives R program substituteRelation
      (.app (.app (codes.unknown v) (termRow codes t)) (termRow codes x))
        (termRow codes ((Subst.single v t).applyTerm x))) →
      Derives R program substituteArgsRelation
        (.app (.app (codes.unknown v) (termRow codes t)) (listRow (xs.map (termRow codes))))
        (listRow (xs.map (termRow codes ∘ (Subst.single v t).applyTerm)))
  | [], _ => by
      have clause := derives_of_clause (R := R) (unification.included substituteArgsNil (by simp [unificationClauses]))
        (pick [codes.unknown v, termRow codes t]) (fun _ inside => absurd inside List.not_mem_nil)
      simpa [substituteArgsNil, triple, pick, listRow] using clause
  | x :: rest, each => by
      have later := substituteArgs_complete unification v t rest fun y inside => each y (List.mem_cons_of_mem _ inside)
      have clause := derives_of_clause (R := R)
        (unification.included substituteArgsCons (by simp [unificationClauses]))
        (pick [codes.unknown v, termRow codes t, termRow codes x, listRow (rest.map (termRow codes)),
          termRow codes ((Subst.single v t).applyTerm x),
          listRow (rest.map (termRow codes ∘ (Subst.single v t).applyTerm))]) (fun g inside => by
          simp only [substituteArgsCons, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl
          · simpa [goalHolds, triple, pick] using each x List.mem_cons_self
          · simpa [goalHolds, triple, pick] using later)
      simpa [substituteArgsCons, triple, pick, listRow] using clause

/-- **Substitution derives the substituted term.** -/
theorem substitute_complete (unification : UnificationProgram codes R program) (v : σ.vars)
    (t : Mettapedia.Logic.LP.Term σ) : ∀ s : Mettapedia.Logic.LP.Term σ,
    Derives R program substituteRelation (.app (.app (codes.unknown v) (termRow codes t)) (termRow codes s))
      (termRow codes ((Subst.single v t).applyTerm s)) := by
  intro s
  induction s with
  | var w =>
      by_cases same : w = v
      · subst same
        have clause := derives_of_clause (R := R)
          (unification.included substituteSame (by simp [unificationClauses]))
          (pick [codes.unknown w, termRow codes t]) (fun _ inside => absurd inside List.not_mem_nil)
        rw [single_var_same]
        simpa [substituteSame, triple, varPattern, pick, termRow] using clause
      · have told := (unification.differ v w).mpr (Ne.symm same)
        have clause := derives_of_clause (R := R)
          (unification.included substituteOther (by simp [unificationClauses]))
          (pick [codes.unknown v, termRow codes t, codes.unknown w]) (fun g inside => by
            simp only [substituteOther, List.mem_cons, List.not_mem_nil, or_false] at inside
            subst inside
            simpa [goalHolds, unit, pick] using told)
        rw [single_var_other t (Ne.symm same)]
        simpa [substituteOther, triple, varPattern, pick, termRow] using clause
  | const c =>
      have clause := derives_of_clause (R := R)
        (unification.included substituteConst (by simp [unificationClauses]))
        (pick [codes.unknown v, termRow codes t, .sym (codes.constant c)])
        (fun _ inside => absurd inside List.not_mem_nil)
      simpa [substituteConst, triple, constPattern, pick, termRow, Subst.applyTerm] using clause
  | app f ts ih =>
      have listed := substituteArgs_complete codes unification v t (List.ofFn ts) fun x inside => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp inside
        exact ih i
      have clause := derives_of_clause (R := R)
        (unification.included substituteApp (by simp [unificationClauses]))
        (pick [codes.unknown v, termRow codes t, .sym (codes.symbol f),
          listRow ((List.ofFn ts).map (termRow codes)),
          listRow ((List.ofFn ts).map (termRow codes ∘ (Subst.single v t).applyTerm))]) (fun g inside => by
          simp only [substituteApp, List.mem_cons, List.not_mem_nil, or_false] at inside
          subst inside
          simpa [goalHolds, triple, pick] using listed)
      have rowIs : termRow codes ((Subst.single v t).applyTerm (.app f ts)) =
          .app (.sym 2) (.app (.sym (codes.symbol f))
            (listRow ((List.ofFn ts).map (termRow codes ∘ (Subst.single v t).applyTerm)))) := by
        simp [Subst.applyTerm, termRow_app, List.map_ofFn, Function.comp_def]
      rw [rowIs, termRow_app]
      simpa [substituteApp, triple, appPattern, pick] using clause

/-- **Substitution in a list of equations derives the substituted list.** -/
theorem substituteEqs_sound (unification : UnificationProgram codes R program) :
    ∀ (depth : ℕ) (v : σ.vars) (t : Mettapedia.Logic.LP.Term σ)
      (eqs : List (Mettapedia.Logic.LP.Term σ × Mettapedia.Logic.LP.Term σ)) (w : Expr),
      DerivesAt R program depth substituteEqsRelation (.app (.app (codes.unknown v) (termRow codes t)) (eqsRow codes eqs))
        w → w = eqsRow codes ((Subst.single v t).applyEqs eqs)
  | 0, _, _, _, _, derived => derived.elim
  | depth + 1, v, t, eqs, w, derived => by
      obtain ⟨c, member, isEqs, θ, input, output, goals⟩ := derived
      have inside := clauseOf codes unification member isEqs (by decide) (by decide)
      simp only [unificationClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact absurd isEqs (by decide)
        | skip
      · simp only [substituteEqsNil, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          Expr.app.injEq] at input output
        obtain ⟨-, eqsIs⟩ := input
        rw [eqsRow_nil_inv codes eqsIs, ← output]
        rfl
      · simp only [substituteEqsCons, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
          Expr.app.injEq] at input output
        obtain ⟨⟨variableIs, termIs⟩, eqsIs⟩ := input
        obtain ⟨s, s', rest, rfl, sIs, s'Is, restIs⟩ := eqsRow_cons_inv codes eqsIs
        have first := goals _ List.mem_cons_self
        have second := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
        have third := goals _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
          variableIs, termIs, sIs, s'Is, restIs] at first second third
        rw [← output, (substitute_sound codes unification depth).1 v t s _ first,
          (substitute_sound codes unification depth).1 v t s' _ second,
          substituteEqs_sound unification depth v t rest _ third]
        rfl

theorem substituteEqs_complete (unification : UnificationProgram codes R program) (v : σ.vars)
    (t : Mettapedia.Logic.LP.Term σ) :
    ∀ eqs : List (Mettapedia.Logic.LP.Term σ × Mettapedia.Logic.LP.Term σ),
      Derives R program substituteEqsRelation (.app (.app (codes.unknown v) (termRow codes t)) (eqsRow codes eqs))
        (eqsRow codes ((Subst.single v t).applyEqs eqs))
  | [] => by
      have clause := derives_of_clause (R := R) (unification.included substituteEqsNil (by simp [unificationClauses]))
        (pick [codes.unknown v, termRow codes t]) (fun _ inside => absurd inside List.not_mem_nil)
      simpa [substituteEqsNil, triple, pick, eqsRow, Subst.applyEqs] using clause
  | (s, s') :: rest => by
      have later := substituteEqs_complete unification v t rest
      have clause := derives_of_clause (R := R)
        (unification.included substituteEqsCons (by simp [unificationClauses]))
        (pick [codes.unknown v, termRow codes t, termRow codes s, termRow codes s', eqsRow codes rest,
          termRow codes ((Subst.single v t).applyTerm s), termRow codes ((Subst.single v t).applyTerm s'),
          eqsRow codes ((Subst.single v t).applyEqs rest)]) (fun g inside => by
          simp only [substituteEqsCons, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl | rfl
          · simpa [goalHolds, triple, pick] using substitute_complete codes unification v t s
          · simpa [goalHolds, triple, pick] using substitute_complete codes unification v t s'
          · simpa [goalHolds, triple, pick] using later)
      simpa [substituteEqsCons, triple, pick, eqsRow, Subst.applyEqs] using clause

theorem occursIn_app_false {v : σ.vars} {f : σ.functionSymbols}
    {ts : Fin (σ.functionArity f) → Mettapedia.Logic.LP.Term σ} :
    (Mettapedia.Logic.LP.Term.app f ts).occursIn v = false ↔ ∀ x ∈ List.ofFn ts, x.occursIn v = false := by
  simp only [Mettapedia.Logic.LP.Term.occursIn, List.any_eq_false, Bool.not_eq_true, List.mem_finRange, true_implies,
    List.mem_ofFn]
  constructor
  · rintro each x ⟨i, rfl⟩
    exact each i
  · exact fun each i => each _ ⟨i, rfl⟩

/-- **The occurs check derives only of terms the variable does not occur in.** -/
theorem notOccurs_sound (unification : UnificationProgram codes R program) : ∀ depth : ℕ,
    (∀ (v : σ.vars) (s : Mettapedia.Logic.LP.Term σ) (w : Expr),
      DerivesAt R program depth notOccursRelation (.app (codes.unknown v) (termRow codes s)) w → s.occursIn v = false) ∧
    (∀ (v : σ.vars) (xs : List (Mettapedia.Logic.LP.Term σ)) (w : Expr),
      DerivesAt R program depth notOccursArgsRelation (.app (codes.unknown v) (listRow (xs.map (termRow codes)))) w →
        ∀ x ∈ xs, x.occursIn v = false) := by
  intro depth
  induction depth with
  | zero => exact ⟨fun _ _ _ derived => derived.elim, fun _ _ _ derived => derived.elim⟩
  | succ depth ih =>
    constructor
    · intro v s w derived
      obtain ⟨c, member, isNot, θ, input, output, goals⟩ := derived
      have inside := clauseOf codes unification member isNot (by decide) (by decide)
      simp only [unificationClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact absurd isNot (by decide)
        | skip
      · simp only [notOccursVar, varPattern, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown, Expr.app.injEq] at input
        obtain ⟨variableIs, sIs⟩ := input
        obtain ⟨w', rfl, unknownIs⟩ := termRow_var_inv codes sIs
        have told := goals _ List.mem_cons_self
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, unit,
          RootRewritesOnTheStep.inst_symTerm, variableIs, unknownIs] at told
        have apart := (unification.differ v w').mp ⟨depth, told⟩
        simp [Mettapedia.Logic.LP.Term.occursIn, apart]
      · simp only [notOccursConst, constPattern, RootRewritesOnTheStep.inst_appTerm,
          RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input
        obtain ⟨-, sIs⟩ := input
        obtain ⟨c, rfl, -⟩ := termRow_const_inv codes sIs
        rfl
      · simp only [notOccursApp, appPattern, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown, Expr.app.injEq] at input
        obtain ⟨variableIs, sIs⟩ := input
        obtain ⟨f, ts, rfl, -, argumentsIs⟩ := termRow_app_inv codes sIs
        have asked := goals _ List.mem_cons_self
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
          variableIs, argumentsIs] at asked
        exact occursIn_app_false.mpr (ih.2 v (List.ofFn ts) _ asked)
    · intro v xs w derived
      obtain ⟨c, member, isNot, θ, input, output, goals⟩ := derived
      have inside := clauseOf codes unification member isNot (by decide) (by decide)
      simp only [unificationClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact absurd isNot (by decide)
        | skip
      · simp only [notOccursArgsNil, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown, Expr.app.injEq] at input
        obtain ⟨-, listIs⟩ := input
        rw [listRow_nil_inv codes listIs]
        exact fun _ inside => absurd inside List.not_mem_nil
      · simp only [notOccursArgsCons, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
          Expr.app.injEq] at input
        obtain ⟨variableIs, listIs⟩ := input
        obtain ⟨x, rest, rfl, headIs, restIs⟩ := listRow_cons_inv codes listIs
        have first := goals _ List.mem_cons_self
        have second := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
          variableIs, headIs, restIs] at first second
        intro y inside
        rcases List.mem_cons.mp inside with rfl | later
        · exact ih.1 v y _ first
        · exact ih.2 v rest _ second y later

omit [DecidableEq σ.vars] in
theorem notOccursArgs_complete (unification : UnificationProgram codes R program) (v : σ.vars) :
    ∀ (xs : List (Mettapedia.Logic.LP.Term σ)),
      (∀ x ∈ xs, Derives R program notOccursRelation (.app (codes.unknown v) (termRow codes x)) (.sym 0)) →
      Derives R program notOccursArgsRelation (.app (codes.unknown v) (listRow (xs.map (termRow codes)))) (.sym 0)
  | [], _ => by
      have clause := derives_of_clause (R := R) (unification.included notOccursArgsNil (by simp [unificationClauses]))
        (pick [codes.unknown v]) (fun _ inside => absurd inside List.not_mem_nil)
      simpa [notOccursArgsNil, unit, pick, listRow] using clause
  | x :: rest, each => by
      have later := notOccursArgs_complete unification v rest fun y inside => each y (List.mem_cons_of_mem _ inside)
      have clause := derives_of_clause (R := R)
        (unification.included notOccursArgsCons (by simp [unificationClauses]))
        (pick [codes.unknown v, termRow codes x, listRow (rest.map (termRow codes))]) (fun g inside => by
          simp only [notOccursArgsCons, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl
          · simpa [goalHolds, unit, pick] using each x List.mem_cons_self
          · simpa [goalHolds, unit, pick] using later)
      simpa [notOccursArgsCons, unit, pick, listRow] using clause

/-- **The occurs check derives every term the variable does not occur in.** -/
theorem notOccurs_complete (unification : UnificationProgram codes R program) (v : σ.vars) :
    ∀ s : Mettapedia.Logic.LP.Term σ, s.occursIn v = false →
      Derives R program notOccursRelation (.app (codes.unknown v) (termRow codes s)) (.sym 0) := by
  intro s
  induction s with
  | var w =>
      intro absent
      have apart : v ≠ w := by simpa [Mettapedia.Logic.LP.Term.occursIn] using absent
      have told := (unification.differ v w).mpr apart
      have clause := derives_of_clause (R := R) (unification.included notOccursVar (by simp [unificationClauses]))
        (pick [codes.unknown v, codes.unknown w]) (fun g inside => by
          simp only [notOccursVar, List.mem_cons, List.not_mem_nil, or_false] at inside
          subst inside
          simpa [goalHolds, unit, pick] using told)
      simpa [notOccursVar, varPattern, unit, pick, termRow] using clause
  | const c =>
      intro _
      have clause := derives_of_clause (R := R) (unification.included notOccursConst (by simp [unificationClauses]))
        (pick [codes.unknown v, .sym (codes.constant c)]) (fun _ inside => absurd inside List.not_mem_nil)
      simpa [notOccursConst, constPattern, unit, pick, termRow] using clause
  | app f ts ih =>
      intro absent
      have each := occursIn_app_false.mp absent
      have listed := notOccursArgs_complete codes unification v (List.ofFn ts) fun x inside => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp inside
        exact ih i (each _ inside)
      have clause := derives_of_clause (R := R) (unification.included notOccursApp (by simp [unificationClauses]))
        (pick [codes.unknown v, .sym (codes.symbol f), listRow ((List.ofFn ts).map (termRow codes))])
        (fun g inside => by
          simp only [notOccursApp, List.mem_cons, List.not_mem_nil, or_false] at inside
          subst inside
          simpa [goalHolds, unit, pick] using listed)
      rw [termRow_app]
      simpa [notOccursApp, appPattern, unit, pick] using clause

omit [DecidableEq σ.vars] in
theorem finPairsToList_eq_zip {n : ℕ} (ts us : Fin n → Mettapedia.Logic.LP.Term σ) :
    finPairsToList ts us = (List.ofFn ts).zip (List.ofFn us) := by
  apply List.ext_getElem
  · simp [finPairsToList]
  · intro i first second
    simp [finPairsToList, List.getElem_zip]

omit [DecidableEq σ.vars] in
/-- **Pairing derives the paired arguments before the equations**, of arguments of the same number. -/
theorem pairArgs_sound (unification : UnificationProgram codes R program) :
    ∀ (depth : ℕ) (xs ys : List (Mettapedia.Logic.LP.Term σ))
      (rest : List (Mettapedia.Logic.LP.Term σ × Mettapedia.Logic.LP.Term σ)) (w : Expr),
      DerivesAt R program depth pairArgsRelation
        (.app (.app (listRow (xs.map (termRow codes))) (listRow (ys.map (termRow codes)))) (eqsRow codes rest)) w →
        w = eqsRow codes (xs.zip ys ++ rest)
  | 0, _, _, _, _, derived => derived.elim
  | depth + 1, xs, ys, rest, w, derived => by
      obtain ⟨c, member, isPair, θ, input, output, goals⟩ := derived
      have inside := clauseOf codes unification member isPair (by decide) (by decide)
      simp only [unificationClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact absurd isPair (by decide)
        | skip
      · simp only [pairArgsNil, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown, Expr.app.injEq] at input output
        obtain ⟨⟨xsIs, ysIs⟩, restIs⟩ := input
        rw [listRow_nil_inv codes xsIs, listRow_nil_inv codes ysIs, ← output, restIs]
        rfl
      · simp only [pairArgsCons, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
          Expr.app.injEq] at input output
        obtain ⟨⟨xsIs, ysIs⟩, restIs⟩ := input
        obtain ⟨x, xs', rfl, xIs, xs'Is⟩ := listRow_cons_inv codes xsIs
        obtain ⟨y, ys', rfl, yIs, ys'Is⟩ := listRow_cons_inv codes ysIs
        have asked := goals _ List.mem_cons_self
        simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
          xs'Is, ys'Is, restIs] at asked
        rw [← output, xIs, yIs, pairArgs_sound unification depth xs' ys' rest _ asked]
        rfl

omit [DecidableEq σ.vars] in
theorem pairArgs_complete (unification : UnificationProgram codes R program) :
    ∀ (xs ys : List (Mettapedia.Logic.LP.Term σ)) (rest : List (Mettapedia.Logic.LP.Term σ × Mettapedia.Logic.LP.Term σ)),
      xs.length = ys.length → Derives R program pairArgsRelation
        (.app (.app (listRow (xs.map (termRow codes))) (listRow (ys.map (termRow codes)))) (eqsRow codes rest))
        (eqsRow codes (xs.zip ys ++ rest))
  | [], [], rest, _ => by
      have clause := derives_of_clause (R := R) (unification.included pairArgsNil (by simp [unificationClauses]))
        (pick [eqsRow codes rest]) (fun _ inside => absurd inside List.not_mem_nil)
      simpa [pairArgsNil, triple, pick, listRow] using clause
  | [], _ :: _, _, lengths => by simp at lengths
  | _ :: _, [], _, lengths => by simp at lengths
  | x :: xs, y :: ys, rest, lengths => by
      have later := pairArgs_complete unification xs ys rest (by simpa using lengths)
      have clause := derives_of_clause (R := R) (unification.included pairArgsCons (by simp [unificationClauses]))
        (pick [termRow codes x, listRow (xs.map (termRow codes)), termRow codes y, listRow (ys.map (termRow codes)),
          eqsRow codes rest, eqsRow codes (xs.zip ys ++ rest)]) (fun g inside => by
          simp only [pairArgsCons, List.mem_cons, List.not_mem_nil, or_false] at inside
          subst inside
          simpa [goalHolds, triple, pick] using later)
      simpa [pairArgsCons, triple, pick, listRow, eqsRow] using clause

variable [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

/-- **What solving derives is a successful derivation of the kernel.** -/
theorem solve_sound (unification : UnificationProgram codes R program) :
    ∀ (depth : ℕ) (eqs : List (Mettapedia.Logic.LP.Term σ × Mettapedia.Logic.LP.Term σ)) (w : Expr),
      DerivesAt R program depth solveRelation (eqsRow codes eqs) w → UnifyDerives eqs
  | 0, _, _, derived => derived.elim
  | depth + 1, eqs, w, derived => by
      obtain ⟨c, member, isSolve, θ, input, output, goals⟩ := derived
      have inside := clauseOf codes unification member isSolve (by decide) (by decide)
      simp only [unificationClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
        | exact absurd isSolve (by decide)
        | skip
      · simp only [solveNil, RootRewritesOnTheStep.inst_symTerm] at input
        rw [eqsRow_nil_inv codes input]
        exact .nil
      · simp only [solveSameVar, varPattern, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown] at input
        obtain ⟨s, t, rest, rfl, sIs, tIs, restIs⟩ := eqsRow_cons_inv codes input
        obtain ⟨v, rfl, vIs⟩ := termRow_var_inv codes sIs
        obtain ⟨w', rfl, w'Is⟩ := termRow_var_inv codes tIs
        obtain rfl := codes.unknown_injective (vIs.symm.trans w'Is)
        have asked := goals _ List.mem_cons_self
        simp only [goalHolds, DemandTransformation.inst_unknown, restIs] at asked
        exact .var_eq v rest (solve_sound unification depth rest _ asked)
      · simp only [solveEliminate, varPattern, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown] at input
        obtain ⟨s, t, rest, rfl, sIs, tIs, restIs⟩ := eqsRow_cons_inv codes input
        obtain ⟨v, rfl, vIs⟩ := termRow_var_inv codes sIs
        have first := goals _ List.mem_cons_self
        have second := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
        have third := goals _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
          vIs, tIs, restIs] at first second third
        have absent := (notOccurs_sound codes unification depth).1 v t _ first
        rw [substituteEqs_sound codes unification depth v t rest _ second] at third
        exact .var_subst v t rest absent (solve_sound unification depth _ _ third)
      · simp only [solveSameConst, constPattern, RootRewritesOnTheStep.inst_appTerm,
          RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown] at input
        obtain ⟨s, t, rest, rfl, sIs, tIs, restIs⟩ := eqsRow_cons_inv codes input
        obtain ⟨c, rfl, cIs⟩ := termRow_const_inv codes sIs
        obtain ⟨d, rfl, dIs⟩ := termRow_const_inv codes tIs
        obtain rfl := codes.constant_injective (Expr.sym.inj (cIs.symm.trans dIs))
        have asked := goals _ List.mem_cons_self
        simp only [goalHolds, DemandTransformation.inst_unknown, restIs] at asked
        exact .const_eq c rest (solve_sound unification depth rest _ asked)
      · simp only [solveConstVar, constPattern, varPattern, RootRewritesOnTheStep.inst_appTerm,
          RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown] at input
        obtain ⟨s, t, rest, rfl, sIs, tIs, restIs⟩ := eqsRow_cons_inv codes input
        obtain ⟨c, rfl, cIs⟩ := termRow_const_inv codes sIs
        obtain ⟨v, rfl, vIs⟩ := termRow_var_inv codes tIs
        have first := goals _ List.mem_cons_self
        have second := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
        simp only [goalHolds, triple, constPattern, RootRewritesOnTheStep.inst_appTerm,
          RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, vIs, cIs, restIs] at first second
        rw [substituteEqs_sound codes unification depth v (.const c) rest _ first] at second
        exact .const_var c v rest (solve_sound unification depth _ _ second)
      · simp only [solveAppVar, appPattern, varPattern, RootRewritesOnTheStep.inst_appTerm,
          RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown] at input
        obtain ⟨s, t, rest, rfl, sIs, tIs, restIs⟩ := eqsRow_cons_inv codes input
        obtain ⟨f, ts, rfl, fIs, argumentsIs⟩ := termRow_app_inv codes sIs
        obtain ⟨v, rfl, vIs⟩ := termRow_var_inv codes tIs
        have first := goals _ List.mem_cons_self
        have second := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
        have third := goals _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        have appRow : Expr.app (.sym 2) (.app (θ 0) (θ 1)) = termRow codes (.app f ts) := by
          rw [termRow_app, fIs, argumentsIs]
        simp only [goalHolds, triple, appPattern, RootRewritesOnTheStep.inst_appTerm,
          RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, vIs, restIs, appRow] at first second third
        have absent := (notOccurs_sound codes unification depth).1 v _ _ first
        rw [substituteEqs_sound codes unification depth v _ rest _ second] at third
        exact .app_var f ts v rest absent (solve_sound unification depth _ _ third)
      · simp only [solveDecompose, appPattern, RootRewritesOnTheStep.inst_appTerm,
          RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown] at input
        obtain ⟨s, t, rest, rfl, sIs, tIs, restIs⟩ := eqsRow_cons_inv codes input
        obtain ⟨f, ts, rfl, fIs, tsIs⟩ := termRow_app_inv codes sIs
        obtain ⟨g, us, rfl, gIs, usIs⟩ := termRow_app_inv codes tIs
        obtain rfl := codes.symbol_injective (Expr.sym.inj (fIs.symm.trans gIs))
        have first := goals _ List.mem_cons_self
        have second := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
        simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
          tsIs, usIs, restIs] at first second
        rw [pairArgs_sound codes unification depth _ _ rest _ first, ← finPairsToList_eq_zip] at second
        exact .app_eq f ts us rest (solve_sound unification depth _ _ second)

/-- **Every successful derivation of the kernel is derived by solving.** -/
theorem solve_complete (unification : UnificationProgram codes R program)
    {eqs : List (Mettapedia.Logic.LP.Term σ × Mettapedia.Logic.LP.Term σ)} (derived : UnifyDerives eqs) :
    Derives R program solveRelation (eqsRow codes eqs) (.sym 0) := by
  induction derived with
  | nil =>
      have clause := derives_of_clause (R := R) (unification.included solveNil (by simp [unificationClauses]))
        (pick []) (fun _ inside => absurd inside List.not_mem_nil)
      simpa [solveNil, unit, pick, eqsRow] using clause
  | var_eq v rest _ ih =>
      have clause := derives_of_clause (R := R) (unification.included solveSameVar (by simp [unificationClauses]))
        (pick [codes.unknown v, eqsRow codes rest]) (fun g inside => by
          simp only [solveSameVar, List.mem_cons, List.not_mem_nil, or_false] at inside
          subst inside
          simpa [goalHolds, unit, pick] using ih)
      simpa [solveSameVar, varPattern, unit, pick, eqsRow, termRow] using clause
  | var_subst v t rest absent _ ih =>
      have clause := derives_of_clause (R := R) (unification.included solveEliminate (by simp [unificationClauses]))
        (pick [codes.unknown v, termRow codes t, eqsRow codes rest,
          eqsRow codes ((Subst.single v t).applyEqs rest)]) (fun g inside => by
          simp only [solveEliminate, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl | rfl
          · simpa [goalHolds, unit, pick] using notOccurs_complete codes unification v t absent
          · simpa [goalHolds, triple, pick] using substituteEqs_complete codes unification v t rest
          · simpa [goalHolds, unit, pick] using ih)
      simpa [solveEliminate, varPattern, unit, pick, eqsRow, termRow] using clause
  | const_eq c rest _ ih =>
      have clause := derives_of_clause (R := R) (unification.included solveSameConst (by simp [unificationClauses]))
        (pick [.sym (codes.constant c), eqsRow codes rest]) (fun g inside => by
          simp only [solveSameConst, List.mem_cons, List.not_mem_nil, or_false] at inside
          subst inside
          simpa [goalHolds, unit, pick] using ih)
      simpa [solveSameConst, constPattern, unit, pick, eqsRow, termRow] using clause
  | const_var c v rest _ ih =>
      have clause := derives_of_clause (R := R) (unification.included solveConstVar (by simp [unificationClauses]))
        (pick [.sym (codes.constant c), codes.unknown v, eqsRow codes rest,
          eqsRow codes ((Subst.single v (.const c)).applyEqs rest)]) (fun g inside => by
          simp only [solveConstVar, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl
          · simpa [goalHolds, triple, constPattern, pick, termRow] using
              substituteEqs_complete codes unification v (.const c) rest
          · simpa [goalHolds, unit, pick] using ih)
      simpa [solveConstVar, constPattern, varPattern, unit, pick, eqsRow, termRow] using clause
  | app_var f ts v rest absent _ ih =>
      have clause := derives_of_clause (R := R) (unification.included solveAppVar (by simp [unificationClauses]))
        (pick [.sym (codes.symbol f), listRow ((List.ofFn ts).map (termRow codes)), codes.unknown v,
          eqsRow codes rest, eqsRow codes ((Subst.single v (.app f ts)).applyEqs rest)]) (fun g inside => by
          simp only [solveAppVar, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl | rfl
          · have checked := notOccurs_complete codes unification v _ absent
            rw [termRow_app] at checked
            simpa [goalHolds, appPattern, unit, pick] using checked
          · have substituted := substituteEqs_complete codes unification v (.app f ts) rest
            rw [termRow_app] at substituted
            simpa [goalHolds, triple, appPattern, pick] using substituted
          · simpa [goalHolds, unit, pick] using ih)
      have rowIs := termRow_app codes f ts
      simp only [eqsRow, rowIs]
      simpa [solveAppVar, appPattern, varPattern, unit, pick, termRow] using clause
  | app_eq f ts us rest _ ih =>
      have paired := pairArgs_complete codes unification (List.ofFn ts) (List.ofFn us) rest (by simp)
      rw [← finPairsToList_eq_zip] at paired
      have clause := derives_of_clause (R := R) (unification.included solveDecompose (by simp [unificationClauses]))
        (pick [.sym (codes.symbol f), listRow ((List.ofFn ts).map (termRow codes)),
          listRow ((List.ofFn us).map (termRow codes)), eqsRow codes rest,
          eqsRow codes (finPairsToList ts us ++ rest)]) (fun g inside => by
          simp only [solveDecompose, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl
          · simpa [goalHolds, triple, pick] using paired
          · simpa [goalHolds, unit, pick] using ih)
      simp only [eqsRow, termRow_app]
      simpa [solveDecompose, appPattern, unit, pick] using clause

/-- **Solving derives a list of equations exactly when the kernel's derivations do.** -/
theorem derives_solve_iff (unification : UnificationProgram codes R program)
    (eqs : List (Mettapedia.Logic.LP.Term σ × Mettapedia.Logic.LP.Term σ)) :
    Derives R program solveRelation (eqsRow codes eqs) (.sym 0) ↔ UnifyDerives eqs :=
  ⟨fun ⟨depth, derived⟩ => solve_sound codes unification depth eqs _ derived, solve_complete codes unification⟩

/-- **Solving derives exactly the unifiable lists of equations.** -/
theorem solve_iff (unification : UnificationProgram codes R program)
    (eqs : List (Mettapedia.Logic.LP.Term σ × Mettapedia.Logic.LP.Term σ)) :
    Derives R program solveRelation (eqsRow codes eqs) (.sym 0) ↔ ∃ θ : Subst σ, Unifies θ eqs :=
  (derives_solve_iff codes unification eqs).trans
    ⟨Mettapedia.Logic.LP.unifiable_of_derives, Mettapedia.Logic.LP.unifies_to_derives⟩

end Mettapedia.GSLT.Compilation.Uniform.UnificationClauses

#print axioms Mettapedia.GSLT.Compilation.Uniform.UnificationClauses.solve_iff
