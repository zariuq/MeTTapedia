import Mettapedia.GSLT.Compilation.Uniform.UnificationClauses
import Mettapedia.GSLT.Compilation.Uniform.TypingUnknowns
import Mettapedia.GSLT.Compilation.Uniform.PatternRows

/-!
# Typing under unknown contexts, as clauses

The types of `TypingUnknowns` get rows (`typeCodes`): base categories by their names, composite types by their heads,
and unknowns by the name, the index or the position they stand for. Two unknowns are told apart by clauses
(`differ_iff`): names by the source's own freshness check, numbers and positions structurally.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Compilation.Uniform.TypingClauses

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode (collectionCode collectionCode_injective)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open NamesOnTheStep (Expr)
open RuleSyntax.Presentation.Schematic
open RuleSyntax.ComputedConditions (Relations)
open RootRewritesOnTheStep (symTerm appTerm encode labelCode labelCode_injective numeral numeralTerm numeral_inj)
open DemandTransformation (Goal Clause goalHolds DerivesAt Derives derives_of_clause pick)
open TypingUnknowns (TypeHead TypeUnknown typeSignature TypeTerm)
open UnificationClauses (Codes unit)
open PatternRows (numeral_zero_inv numeral_succ_inv encode_bvar_inv encode_fvar_inv encode_apply_inv
  encode_lambda_inv encode_multiLambda_inv encode_subst_inv encode_collection_inv encodeList_nil_inv
  encodeList_cons_inv)

/-! ## Rows of the unknowns of a typing -/

/-- A position as a row: a list of numbers. -/
def pathRow : List ℕ → Expr
  | [] => .sym 0
  | i :: rest => .app (numeral i) (pathRow rest)

@[simp] theorem pathRow_inj {π ρ : List ℕ} : pathRow π = pathRow ρ ↔ π = ρ := by
  constructor
  · intro same
    induction π generalizing ρ with
    | nil =>
        cases ρ with
        | nil => rfl
        | cons j rest =>
            cases j <;> simp [pathRow, numeral] at same
    | cons i rest ih =>
        cases ρ with
        | nil =>
            cases i <;> simp [pathRow, numeral] at same
        | cons j others =>
            simp only [pathRow, Expr.app.injEq, numeral_inj] at same
            rw [same.1, ih same.2]
  · rintro rfl
    rfl

/-- **The row of an unknown**: a free name by the name's own row, a loose index and a position by numbers. -/
def unknownRow : TypeUnknown → Expr
  | .free name => encode (.fvar name)
  | .loose index => .app (.sym 2) (numeral index)
  | .node path slot => .app (.sym 3) (.app (pathRow path) (numeral slot))

theorem unknownRow_injective : Function.Injective unknownRow := by
  intro first second same
  cases first <;> cases second <;>
    simp_all [unknownRow, encode, RootRewritesOnTheStep.labelCode_injective.eq_iff]

/-- The code of a type head. -/
def headCode : TypeHead → ℕ
  | .collection kind => collectionCode kind
  | .arrow => 3
  | .multiBinder => 4

theorem headCode_injective : Function.Injective headCode := by
  intro first second same
  cases first <;> cases second <;> simp_all [headCode]
  case collection.collection kind other => exact collectionCode_injective same
  all_goals
    rename_i kind
    cases kind <;> simp [collectionCode] at same

/-- **Rows of types**: base categories by the codes of their names, heads by their codes, unknowns by their rows. -/
def typeCodes : Codes typeSignature where
  constant := labelCode
  constant_injective := labelCode_injective
  symbol := headCode
  symbol_injective := headCode_injective
  unknown := unknownRow
  unknown_injective := unknownRow_injective

/-! ## Telling unknowns apart -/

/-- The relation that tells two numbers apart. -/
def numeralsDifferRelation : ℕ := 15

/-- The relation that tells two positions apart. -/
def pathsDifferRelation : ℕ := 16

def differNames : Clause :=
  { relation := UnificationClauses.differRelation,
    input := appTerm (appTerm (symTerm 1) (.var 0)) (appTerm (symTerm 1) (.var 1)), output := unit,
    body := [.query ⟨symTerm 0, 0, [appTerm (symTerm 1) (.var 0), appTerm (symTerm 1) (.var 1)]⟩] }

def differLoose : Clause :=
  { relation := UnificationClauses.differRelation,
    input := appTerm (appTerm (symTerm 2) (.var 0)) (appTerm (symTerm 2) (.var 1)), output := unit,
    body := [.ask numeralsDifferRelation (appTerm (.var 0) (.var 1)) unit] }

def differPaths : Clause :=
  { relation := UnificationClauses.differRelation,
    input := appTerm (appTerm (symTerm 3) (appTerm (.var 0) (.var 1))) (appTerm (symTerm 3) (appTerm (.var 2) (.var 3))),
    output := unit, body := [.ask pathsDifferRelation (appTerm (.var 0) (.var 2)) unit] }

def differSlots : Clause :=
  { relation := UnificationClauses.differRelation,
    input := appTerm (appTerm (symTerm 3) (appTerm (.var 0) (.var 1))) (appTerm (symTerm 3) (appTerm (.var 2) (.var 3))),
    output := unit, body := [.ask numeralsDifferRelation (appTerm (.var 1) (.var 3)) unit] }

/-- Unknowns of two different kinds differ. -/
def differKinds (first second : ℕ) : Clause :=
  { relation := UnificationClauses.differRelation,
    input := appTerm (appTerm (symTerm first) (.var 0)) (appTerm (symTerm second) (.var 1)), output := unit,
    body := [] }

def zeroSucc : Clause :=
  { relation := numeralsDifferRelation, input := appTerm (symTerm 0) (appTerm (symTerm 1) (.var 0)), output := unit,
    body := [] }

def succZero : Clause :=
  { relation := numeralsDifferRelation, input := appTerm (appTerm (symTerm 1) (.var 0)) (symTerm 0), output := unit,
    body := [] }

def succSucc : Clause :=
  { relation := numeralsDifferRelation, input := appTerm (appTerm (symTerm 1) (.var 0)) (appTerm (symTerm 1) (.var 1)),
    output := unit, body := [.ask numeralsDifferRelation (appTerm (.var 0) (.var 1)) unit] }

def nilCons : Clause :=
  { relation := pathsDifferRelation, input := appTerm (symTerm 0) (appTerm (.var 0) (.var 1)), output := unit,
    body := [] }

def consNil : Clause :=
  { relation := pathsDifferRelation, input := appTerm (appTerm (.var 0) (.var 1)) (symTerm 0), output := unit,
    body := [] }

def consHeads : Clause :=
  { relation := pathsDifferRelation, input := appTerm (appTerm (.var 0) (.var 1)) (appTerm (.var 2) (.var 3)),
    output := unit, body := [.ask numeralsDifferRelation (appTerm (.var 0) (.var 2)) unit] }

def consTails : Clause :=
  { relation := pathsDifferRelation, input := appTerm (appTerm (.var 0) (.var 1)) (appTerm (.var 0) (.var 2)),
    output := unit, body := [.ask pathsDifferRelation (appTerm (.var 1) (.var 2)) unit] }

/-- **The clauses that tell the unknowns of a typing apart.** -/
def differClauses : List Clause :=
  [differNames, differLoose, differPaths, differSlots, differKinds 1 2, differKinds 1 3, differKinds 2 1,
    differKinds 2 3, differKinds 3 1, differKinds 3 2, zeroSucc, succZero, succSucc, nilCons, consNil, consHeads,
    consTails]

theorem differClauses_moded : ∀ c ∈ differClauses, DemandTransformation.Moded c := by
  intro c inside
  simp only [differClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> exact DemandTransformation.moded_of_check (by decide)

/-! ## What telling apart derives -/

/-- **A program that tells the unknowns of a typing apart**: it has exactly these clauses for the three relations,
and its condition of name 0 on the rows of two names is the source's freshness of one in the other. -/
structure DifferProgram (R : Relations) (program : List Clause) : Prop where
  included : ∀ c ∈ differClauses, c ∈ program
  only : ∀ c ∈ program, UnificationClauses.differRelation ≤ c.relation → c.relation ≤ pathsDifferRelation →
    c ∈ differClauses
  names : ∀ x y : String, R 0 [encode (.fvar x), encode (.fvar y)] (.sym 0) ↔ x ≠ y

section Differ

variable {R : Relations} {program : List Clause}

theorem clauseOf {c : Clause} (differ : DifferProgram R program) (member : c ∈ program) {r : ℕ}
    (isR : c.relation = r) (low : UnificationClauses.differRelation ≤ r) (high : r ≤ pathsDifferRelation) :
    c ∈ differClauses :=
  differ.only c member (isR ▸ low) (isR ▸ high)

/-- **Telling numbers apart derives exactly the different numbers.** -/
theorem numeralsDiffer_sound (differ : DifferProgram R program) :
    ∀ (depth m n : ℕ) (w : Expr),
      DerivesAt R program depth numeralsDifferRelation (.app (numeral m) (numeral n)) w → m ≠ n
  | 0, _, _, _, derived => derived.elim
  | depth + 1, m, n, w, derived => by
      obtain ⟨c, member, isR, θ, input, output, goals⟩ := derived
      have inside := clauseOf differ member isR (by decide) (by decide)
      simp only [differClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;>
        first
        | exact absurd isR (by decide)
        | skip
      · simp only [zeroSucc, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown, Expr.app.injEq] at input
        obtain ⟨mIs, nIs⟩ := input
        rw [numeral_zero_inv mIs]
        obtain ⟨n', rfl, -⟩ := numeral_succ_inv nIs
        omega
      · simp only [succZero, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown, Expr.app.injEq] at input
        obtain ⟨mIs, nIs⟩ := input
        rw [numeral_zero_inv nIs]
        obtain ⟨m', rfl, -⟩ := numeral_succ_inv mIs
        omega
      · simp only [succSucc, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown, Expr.app.injEq] at input
        obtain ⟨mIs, nIs⟩ := input
        obtain ⟨m', rfl, m'Is⟩ := numeral_succ_inv mIs
        obtain ⟨n', rfl, n'Is⟩ := numeral_succ_inv nIs
        have asked := goals _ List.mem_cons_self
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, m'Is,
          n'Is] at asked
        have apart := numeralsDiffer_sound differ depth m' n' _ asked
        omega

theorem numeralsDiffer_complete (differ : DifferProgram R program) :
    ∀ m n : ℕ, m ≠ n → Derives R program numeralsDifferRelation (.app (numeral m) (numeral n)) (.sym 0)
  | 0, 0, apart => absurd rfl apart
  | 0, n + 1, _ => by
      have clause := derives_of_clause (R := R) (differ.included zeroSucc (by simp [differClauses]))
        (pick [numeral n]) (fun _ inside => absurd inside List.not_mem_nil)
      simpa [zeroSucc, unit, pick, numeral] using clause
  | m + 1, 0, _ => by
      have clause := derives_of_clause (R := R) (differ.included succZero (by simp [differClauses]))
        (pick [numeral m]) (fun _ inside => absurd inside List.not_mem_nil)
      simpa [succZero, unit, pick, numeral] using clause
  | m + 1, n + 1, apart => by
      have inner := numeralsDiffer_complete differ m n (by omega)
      have clause := derives_of_clause (R := R) (differ.included succSucc (by simp [differClauses]))
        (pick [numeral m, numeral n]) (fun g inside => by
          simp only [succSucc, List.mem_cons, List.not_mem_nil, or_false] at inside
          subst inside
          simpa [goalHolds, unit, pick] using inner)
      simpa [succSucc, unit, pick, numeral] using clause

theorem pathRow_nil_inv {π : List ℕ} (same : Expr.sym 0 = pathRow π) : π = [] := by
  cases π with
  | nil => rfl
  | cons _ _ => simp [pathRow] at same

theorem pathRow_cons_inv {π : List ℕ} {a b : Expr} (same : Expr.app a b = pathRow π) :
    ∃ i rest, π = i :: rest ∧ a = numeral i ∧ b = pathRow rest := by
  cases π with
  | nil => simp [pathRow] at same
  | cons i rest => simp only [pathRow, Expr.app.injEq] at same; exact ⟨i, rest, rfl, same.1, same.2⟩

/-- **Telling positions apart derives exactly the different positions.** -/
theorem pathsDiffer_sound (differ : DifferProgram R program) :
    ∀ (depth : ℕ) (π ρ : List ℕ) (w : Expr),
      DerivesAt R program depth pathsDifferRelation (.app (pathRow π) (pathRow ρ)) w → π ≠ ρ
  | 0, _, _, _, derived => derived.elim
  | depth + 1, π, ρ, w, derived => by
      obtain ⟨c, member, isR, θ, input, output, goals⟩ := derived
      have inside := clauseOf differ member isR (by decide) (by decide)
      simp only [differClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;>
        first
        | exact absurd isR (by decide)
        | skip
      · simp only [nilCons, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown, Expr.app.injEq] at input
        obtain ⟨πIs, ρIs⟩ := input
        rw [pathRow_nil_inv πIs]
        obtain ⟨j, rest, rfl, -, -⟩ := pathRow_cons_inv ρIs
        simp
      · simp only [consNil, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown, Expr.app.injEq] at input
        obtain ⟨πIs, ρIs⟩ := input
        rw [pathRow_nil_inv ρIs]
        obtain ⟨i, rest, rfl, -, -⟩ := pathRow_cons_inv πIs
        simp
      · simp only [consHeads, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
          Expr.app.injEq] at input
        obtain ⟨πIs, ρIs⟩ := input
        obtain ⟨i, rest, rfl, iIs, -⟩ := pathRow_cons_inv πIs
        obtain ⟨j, others, rfl, jIs, -⟩ := pathRow_cons_inv ρIs
        have asked := goals _ List.mem_cons_self
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, iIs, jIs]
          at asked
        have apart := numeralsDiffer_sound differ depth i j _ asked
        simp [apart]
      · simp only [consTails, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
          Expr.app.injEq] at input
        obtain ⟨πIs, ρIs⟩ := input
        obtain ⟨i, rest, rfl, iIs, restIs⟩ := pathRow_cons_inv πIs
        obtain ⟨j, others, rfl, jIs, othersIs⟩ := pathRow_cons_inv ρIs
        have asked := goals _ List.mem_cons_self
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, restIs,
          othersIs] at asked
        have apart := pathsDiffer_sound differ depth rest others _ asked
        simp [apart]

theorem pathsDiffer_complete (differ : DifferProgram R program) :
    ∀ π ρ : List ℕ, π ≠ ρ → Derives R program pathsDifferRelation (.app (pathRow π) (pathRow ρ)) (.sym 0)
  | [], [], apart => absurd rfl apart
  | [], j :: others, _ => by
      have clause := derives_of_clause (R := R) (differ.included nilCons (by simp [differClauses]))
        (pick [numeral j, pathRow others]) (fun _ inside => absurd inside List.not_mem_nil)
      simpa [nilCons, unit, pick, pathRow] using clause
  | i :: rest, [], _ => by
      have clause := derives_of_clause (R := R) (differ.included consNil (by simp [differClauses]))
        (pick [numeral i, pathRow rest]) (fun _ inside => absurd inside List.not_mem_nil)
      simpa [consNil, unit, pick, pathRow] using clause
  | i :: rest, j :: others, apart => by
      by_cases heads : i = j
      · subst heads
        have inner := pathsDiffer_complete differ rest others (fun same => apart (by rw [same]))
        have clause := derives_of_clause (R := R) (differ.included consTails (by simp [differClauses]))
          (pick [numeral i, pathRow rest, pathRow others]) (fun g inside => by
            simp only [consTails, List.mem_cons, List.not_mem_nil, or_false] at inside
            subst inside
            simpa [goalHolds, unit, pick] using inner)
        simpa [consTails, unit, pick, pathRow] using clause
      · have inner := numeralsDiffer_complete differ i j heads
        have clause := derives_of_clause (R := R) (differ.included consHeads (by simp [differClauses]))
          (pick [numeral i, pathRow rest, numeral j, pathRow others]) (fun g inside => by
            simp only [consHeads, List.mem_cons, List.not_mem_nil, or_false] at inside
            subst inside
            simpa [goalHolds, unit, pick] using inner)
        simpa [consHeads, unit, pick, pathRow] using clause

theorem unknownRow_inv {u : TypeUnknown} {a : ℕ} {x : Expr} (same : Expr.app (.sym a) x = unknownRow u) :
    (a = 1 ∧ ∃ name, u = .free name ∧ x = .sym (labelCode name)) ∨
      (a = 2 ∧ ∃ index, u = .loose index ∧ x = numeral index) ∨
      (a = 3 ∧ ∃ path slot, u = .node path slot ∧ x = .app (pathRow path) (numeral slot)) := by
  cases u with
  | free name =>
      simp only [unknownRow, encode, Expr.app.injEq, Expr.sym.injEq] at same
      exact .inl ⟨same.1, name, rfl, same.2⟩
  | loose index =>
      simp only [unknownRow, Expr.app.injEq, Expr.sym.injEq] at same
      exact .inr (.inl ⟨same.1, index, rfl, same.2⟩)
  | node path slot =>
      simp only [unknownRow, Expr.app.injEq, Expr.sym.injEq] at same
      exact .inr (.inr ⟨same.1, path, slot, rfl, same.2⟩)

/-- **Telling unknowns apart derives exactly the different unknowns.** -/
theorem differ_sound (differ : DifferProgram R program) :
    ∀ (depth : ℕ) (u v : TypeUnknown) (w : Expr),
      DerivesAt R program depth UnificationClauses.differRelation (.app (unknownRow u) (unknownRow v)) w → u ≠ v
  | 0, _, _, _, derived => derived.elim
  | depth + 1, u, v, w, derived => by
      obtain ⟨c, member, isR, θ, input, output, goals⟩ := derived
      have inside := clauseOf differ member isR (by decide) (by decide)
      simp only [differClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl <;>
        first
        | exact absurd isR (by decide)
        | skip
      · simp only [differNames, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown, Expr.app.injEq] at input
        obtain ⟨uIs, vIs⟩ := input
        rcases unknownRow_inv uIs with ⟨-, x, rfl, xIs⟩ | ⟨never, -⟩ | ⟨never, -⟩ <;> try (cases never)
        rcases unknownRow_inv vIs with ⟨-, y, rfl, yIs⟩ | ⟨never, -⟩ | ⟨never, -⟩ <;> try (cases never)
        have asked := goals _ List.mem_cons_self
        simp only [goalHolds, List.map_cons, List.map_nil, RootRewritesOnTheStep.inst_appTerm,
          RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, xIs, yIs] at asked
        have apart := (differ.names x y).mp (by simpa [encode] using asked)
        intro same
        cases same
        exact apart rfl
      · simp only [differLoose, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown, Expr.app.injEq] at input
        obtain ⟨uIs, vIs⟩ := input
        rcases unknownRow_inv uIs with ⟨never, -⟩ | ⟨-, i, rfl, iIs⟩ | ⟨never, -⟩ <;> try (cases never)
        rcases unknownRow_inv vIs with ⟨never, -⟩ | ⟨-, j, rfl, jIs⟩ | ⟨never, -⟩ <;> try (cases never)
        have asked := goals _ List.mem_cons_self
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, iIs, jIs]
          at asked
        have apart := numeralsDiffer_sound differ depth i j _ asked
        intro same
        cases same
        exact apart rfl
      · simp only [differPaths, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown, Expr.app.injEq] at input
        obtain ⟨uIs, vIs⟩ := input
        rcases unknownRow_inv uIs with ⟨never, -⟩ | ⟨never, -⟩ | ⟨-, π, s, rfl, πIs⟩ <;> try (cases never)
        rcases unknownRow_inv vIs with ⟨never, -⟩ | ⟨never, -⟩ | ⟨-, ρ, s', rfl, ρIs⟩ <;> try (cases never)
        simp only [Expr.app.injEq] at πIs ρIs
        have asked := goals _ List.mem_cons_self
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, πIs.1,
          ρIs.1] at asked
        have apart := pathsDiffer_sound differ depth π ρ _ asked
        intro same
        cases same
        exact apart rfl
      · simp only [differSlots, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown, Expr.app.injEq] at input
        obtain ⟨uIs, vIs⟩ := input
        rcases unknownRow_inv uIs with ⟨never, -⟩ | ⟨never, -⟩ | ⟨-, π, s, rfl, πIs⟩ <;> try (cases never)
        rcases unknownRow_inv vIs with ⟨never, -⟩ | ⟨never, -⟩ | ⟨-, ρ, s', rfl, ρIs⟩ <;> try (cases never)
        simp only [Expr.app.injEq] at πIs ρIs
        have asked := goals _ List.mem_cons_self
        simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, πIs.2,
          ρIs.2] at asked
        have apart := numeralsDiffer_sound differ depth s s' _ asked
        intro same
        cases same
        exact apart rfl
      all_goals
        simp only [differKinds, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown, Expr.app.injEq] at input
        obtain ⟨uIs, vIs⟩ := input
        rcases unknownRow_inv uIs with ⟨first, -, rfl, -⟩ | ⟨first, -, rfl, -⟩ | ⟨first, -, -, rfl, -⟩ <;>
          rcases unknownRow_inv vIs with ⟨second, -, rfl, -⟩ | ⟨second, -, rfl, -⟩ | ⟨second, -, -, rfl, -⟩ <;>
          first
          | exact absurd first (by decide)
          | exact absurd second (by decide)
          | exact fun same => by cases same

theorem differ_complete (differ : DifferProgram R program) (u v : TypeUnknown) (apart : u ≠ v) :
    Derives R program UnificationClauses.differRelation (.app (unknownRow u) (unknownRow v)) (.sym 0) := by
  have kinds : ∀ (a b : ℕ) (x y : Expr), (a, b) ∈ [(1, 2), (1, 3), (2, 1), (2, 3), (3, 1), (3, 2)] →
      Derives R program UnificationClauses.differRelation (.app (.app (.sym a) x) (.app (.sym b) y)) (.sym 0) := by
    intro a b x y listed
    have clause := derives_of_clause (R := R) (differ.included (differKinds a b) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at listed
      rcases listed with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [differClauses])) (pick [x, y]) (fun _ inside => absurd inside List.not_mem_nil)
    simpa [differKinds, unit, pick] using clause
  cases u with
  | free x =>
      cases v with
      | free y =>
          have namesApart : x ≠ y := fun same => apart (by rw [same])
          have told := (differ.names x y).mpr namesApart
          have clause := derives_of_clause (R := R) (differ.included differNames (by simp [differClauses]))
            (pick [.sym (labelCode x), .sym (labelCode y)]) (fun g inside => by
              simp only [differNames, List.mem_cons, List.not_mem_nil, or_false] at inside
              subst inside
              simpa [goalHolds, pick, encode] using told)
          simpa [differNames, unit, pick, unknownRow, encode] using clause
      | loose _ => exact kinds 1 2 _ _ (by simp)
      | node _ _ => exact kinds 1 3 _ _ (by simp)
  | loose i =>
      cases v with
      | free _ => exact kinds 2 1 _ _ (by simp)
      | loose j =>
          have inner := numeralsDiffer_complete differ i j (fun same => apart (by rw [same]))
          have clause := derives_of_clause (R := R) (differ.included differLoose (by simp [differClauses]))
            (pick [numeral i, numeral j]) (fun g inside => by
              simp only [differLoose, List.mem_cons, List.not_mem_nil, or_false] at inside
              subst inside
              simpa [goalHolds, unit, pick] using inner)
          simpa [differLoose, unit, pick, unknownRow] using clause
      | node _ _ => exact kinds 2 3 _ _ (by simp)
  | node π s =>
      cases v with
      | free _ => exact kinds 3 1 _ _ (by simp)
      | loose _ => exact kinds 3 2 _ _ (by simp)
      | node ρ s' =>
          by_cases paths : π = ρ
          · subst paths
            have inner := numeralsDiffer_complete differ s s' (fun same => apart (by rw [same]))
            have clause := derives_of_clause (R := R) (differ.included differSlots (by simp [differClauses]))
              (pick [pathRow π, numeral s, pathRow π, numeral s']) (fun g inside => by
                simp only [differSlots, List.mem_cons, List.not_mem_nil, or_false] at inside
                subst inside
                simpa [goalHolds, unit, pick] using inner)
            simpa [differSlots, unit, pick, unknownRow] using clause
          · have inner := pathsDiffer_complete differ π ρ paths
            have clause := derives_of_clause (R := R) (differ.included differPaths (by simp [differClauses]))
              (pick [pathRow π, numeral s, pathRow ρ, numeral s']) (fun g inside => by
                simp only [differPaths, List.mem_cons, List.not_mem_nil, or_false] at inside
                subst inside
                simpa [goalHolds, unit, pick] using inner)
            simpa [differPaths, unit, pick, unknownRow] using clause

/-- **Telling unknowns apart derives exactly the different unknowns.** -/
theorem differ_iff (differ : DifferProgram R program) (u v : TypeUnknown) :
    Derives R program UnificationClauses.differRelation (.app (typeCodes.unknown u) (typeCodes.unknown v)) (.sym 0) ↔
      u ≠ v :=
  ⟨fun ⟨depth, derived⟩ => differ_sound differ depth u v _ derived, differ_complete differ u v⟩

end Differ

/-! ## Rows of types, as row patterns -/

open UnificationClauses (listRow termRow eqsRow triple)

/-- Five rows as one. -/
def quint (a b c d e : Tm) : Tm := appTerm a (appTerm b (appTerm c (appTerm d e)))

/-- Six rows as one. -/
def sext (a b c d e f : Tm) : Tm := appTerm a (quint b c d e f)

/-- The row pattern of the unknown at a position. -/
def nodeTerm (path : Tm) (slot : ℕ) : Tm :=
  appTerm (symTerm 0) (appTerm (symTerm 3) (appTerm path (numeralTerm slot)))

/-- The row pattern of the unknown of a free name, whose code is an unknown. -/
def freeTerm (code : Tm) : Tm := appTerm (symTerm 0) (appTerm (symTerm 1) code)

/-- The row pattern of the unknown of a loose index. -/
def looseTerm (index : Tm) : Tm := appTerm (symTerm 0) (appTerm (symTerm 2) index)

/-- The row pattern of an arrow. -/
def arrowRowTerm (domain codomain : Tm) : Tm :=
  appTerm (symTerm 2) (appTerm (symTerm 3) (appTerm domain (appTerm codomain (symTerm 0))))

/-- The row pattern of the type of a binder of several names. -/
def binderRowTerm (body : Tm) : Tm := appTerm (symTerm 2) (appTerm (symTerm 4) (appTerm body (symTerm 0)))

/-- The row pattern of the type of a collection whose kind's code is a row pattern. -/
def collectionRowTerm (kind element : Tm) : Tm := appTerm (symTerm 2) (appTerm kind (appTerm element (symTerm 0)))

/-- The row pattern of a base category. -/
def constRowTerm (name : String) : Tm := appTerm (symTerm 1) (symTerm (labelCode name))

/-- **A type as a row pattern** with no unknowns. -/
def typeRowTerm : TypeExpr → Tm
  | .base name => constRowTerm name
  | .arrow domain codomain => arrowRowTerm (typeRowTerm domain) (typeRowTerm codomain)
  | .multiBinder body => binderRowTerm (typeRowTerm body)
  | .collection kind element => collectionRowTerm (symTerm (collectionCode kind)) (typeRowTerm element)

theorem termRow_arrowTerm (domain codomain : TypeTerm) :
    termRow typeCodes (TypingUnknowns.arrowTerm domain codomain) =
      .app (.sym 2) (.app (.sym 3) (.app (termRow typeCodes domain) (.app (termRow typeCodes codomain) (.sym 0)))) :=
  rfl

theorem termRow_binderTerm (body : TypeTerm) :
    termRow typeCodes (TypingUnknowns.binderTerm body) =
      .app (.sym 2) (.app (.sym 4) (.app (termRow typeCodes body) (.sym 0))) := rfl

theorem termRow_collectionTerm (kind : CollType) (element : TypeTerm) :
    termRow typeCodes (TypingUnknowns.collectionTerm kind element) =
      .app (.sym 2) (.app (.sym (collectionCode kind)) (.app (termRow typeCodes element) (.sym 0))) := rfl

theorem termRow_unknown (u : TypeUnknown) : termRow typeCodes (TypingUnknowns.unknown u) = .app (.sym 0) (unknownRow u) :=
  rfl

theorem termRow_const (name : String) :
    termRow typeCodes (.const name : TypeTerm) = .app (.sym 1) (.sym (labelCode name)) := rfl

@[simp] theorem inst_typeRowTerm (θ : ℕ → Expr) : ∀ type : TypeExpr,
    inst θ (typeRowTerm type) = termRow typeCodes (TypingUnknowns.typeTerm type)
  | .base _ => rfl
  | .arrow domain codomain => by
      simp only [typeRowTerm, arrowRowTerm, TypingUnknowns.typeTerm, termRow_arrowTerm,
        RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, inst_typeRowTerm θ domain,
        inst_typeRowTerm θ codomain]
  | .multiBinder body => by
      simp only [typeRowTerm, binderRowTerm, TypingUnknowns.typeTerm, termRow_binderTerm,
        RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, inst_typeRowTerm θ body]
  | .collection kind element => by
      simp only [typeRowTerm, collectionRowTerm, TypingUnknowns.typeTerm, termRow_collectionTerm,
        RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm, inst_typeRowTerm θ element]

@[simp] theorem unknowns_typeRowTerm : ∀ type : TypeExpr, RuleSyntax.Machines.unknowns (typeRowTerm type) = []
  | .base _ => rfl
  | .arrow domain codomain => by
      simp [typeRowTerm, arrowRowTerm, unknowns_typeRowTerm domain, unknowns_typeRowTerm codomain]
  | .multiBinder body => by simp [typeRowTerm, binderRowTerm, unknowns_typeRowTerm body]
  | .collection kind element => by simp [typeRowTerm, collectionRowTerm, unknowns_typeRowTerm element]

/-! ## The clauses of typing -/

/-- The relation that generates a pattern's equations. -/
def generateRelation : ℕ := 17

/-- The relation that looks up the type of an index among the binders around. -/
def lookupRelation : ℕ := 18

/-- The relation that puts some copies of a type before the binders around. -/
def replicateRelation : ℕ := 19

/-- The relation that generates the equations of the elements of a collection. -/
def elementsRelation : ℕ := 20

/-- The relation that generates the equations of the arguments of a constructor. -/
def argumentsRelation : ℕ := 21

/-- The relation that holds of a pattern and a type the pattern has under some contexts. -/
def typedRelation : ℕ := 22

def generateBvar : Clause :=
  { relation := generateRelation, input := quint (appTerm (symTerm 0) (.var 0)) (.var 1) (.var 2) (.var 3) (.var 4),
    output := appTerm (appTerm (.var 1) (.var 5)) (.var 4),
    body := [.ask lookupRelation (appTerm (.var 2) (.var 0)) (.var 5)] }

def generateFvar : Clause :=
  { relation := generateRelation, input := quint (appTerm (symTerm 1) (.var 0)) (.var 1) (.var 2) (.var 3) (.var 4),
    output := appTerm (appTerm (.var 1) (freeTerm (.var 0))) (.var 4), body := [] }

def generateLambda : Clause :=
  { relation := generateRelation,
    input := quint (appTerm (symTerm 3) (appTerm (.var 0) (.var 1))) (.var 2) (.var 3) (.var 4) (.var 5),
    output := appTerm (appTerm (.var 2) (arrowRowTerm (nodeTerm (.var 4) 0) (nodeTerm (.var 4) 1))) (.var 6),
    body := [.ask generateRelation (quint (.var 1) (nodeTerm (.var 4) 1) (appTerm (nodeTerm (.var 4) 0) (.var 3))
      (appTerm (numeralTerm 0) (.var 4)) (.var 5)) (.var 6)] }

def generateMultiLambda : Clause :=
  { relation := generateRelation,
    input := quint (appTerm (symTerm 4) (appTerm (.var 0) (appTerm (.var 1) (.var 2)))) (.var 3) (.var 4) (.var 5)
      (.var 6),
    output := appTerm (appTerm (.var 3) (arrowRowTerm (binderRowTerm (nodeTerm (.var 5) 0)) (nodeTerm (.var 5) 1)))
      (.var 8),
    body := [.ask replicateRelation (triple (.var 0) (nodeTerm (.var 5) 0) (.var 4)) (.var 7),
      .ask generateRelation (quint (.var 2) (nodeTerm (.var 5) 1) (.var 7) (appTerm (numeralTerm 0) (.var 5)) (.var 6))
        (.var 8)] }

def generateSubst : Clause :=
  { relation := generateRelation,
    input := quint (appTerm (symTerm 5) (appTerm (.var 0) (.var 1))) (.var 2) (.var 3) (.var 4) (.var 5),
    output := .var 7,
    body := [.ask generateRelation (quint (.var 1) (nodeTerm (.var 4) 0) (.var 3) (appTerm (numeralTerm 1) (.var 4))
        (.var 5)) (.var 6),
      .ask generateRelation (quint (.var 0) (.var 2) (appTerm (nodeTerm (.var 4) 0) (.var 3))
        (appTerm (numeralTerm 0) (.var 4)) (.var 6)) (.var 7)] }

def generateCollection : Clause :=
  { relation := generateRelation,
    input := quint (appTerm (symTerm 6) (appTerm (.var 0) (appTerm (.var 1) (.var 2)))) (.var 3) (.var 4) (.var 5)
      (.var 6),
    output := appTerm (appTerm (.var 3) (collectionRowTerm (.var 0) (nodeTerm (.var 5) 0))) (.var 7),
    body := [.ask elementsRelation (sext (.var 1) (nodeTerm (.var 5) 0) (.var 4) (.var 5) (symTerm 0) (.var 6))
      (.var 7)] }

/-- The clause of a bare collection rule: its collections have the rule's category. -/
def generateCarrier (kind : CollType) (element : TypeExpr) (category : String) : Clause :=
  { relation := generateRelation,
    input := quint (appTerm (symTerm 6) (appTerm (symTerm (collectionCode kind)) (appTerm (.var 0) (.var 1))))
      (.var 2) (.var 3) (.var 4) (.var 5),
    output := appTerm (appTerm (.var 2) (constRowTerm category)) (.var 6),
    body := [.ask elementsRelation (sext (.var 0) (typeRowTerm element) (.var 3) (.var 4) (symTerm 0) (.var 5))
      (.var 6)] }

/-- The representation of a parameter: a pattern, a binder of one name, or a binder of several. -/
def tagOf : TermParam → ℕ
  | .simple _ _ => 0
  | .abstractionNamed _ _ _ => 1
  | .multiAbstractionNamed _ _ _ => 2

/-- The row pattern of the parameters of a rule: each one's representation and expected type. -/
def parametersTerm : List TermParam → Option Tm
  | [] => some (symTerm 0)
  | parameter :: parameters =>
      (Mettapedia.GSLT.LanguageDef.WellSorted.parameterType? parameter).bind fun expected =>
        (parametersTerm parameters).map fun rest =>
          appTerm (appTerm (symTerm (tagOf parameter)) (typeRowTerm expected)) rest

/-- The clause of a constructor rule: its applications have the rule's category. -/
def generateConstructor (label category : String) (parameters : Tm) : Clause :=
  { relation := generateRelation,
    input := quint (appTerm (symTerm 2) (appTerm (symTerm (labelCode label)) (.var 0))) (.var 1) (.var 2) (.var 3)
      (.var 4),
    output := appTerm (appTerm (.var 1) (constRowTerm category)) (.var 5),
    body := [.ask argumentsRelation (sext (.var 0) parameters (.var 2) (.var 3) (symTerm 0) (.var 4)) (.var 5)] }

def lookupHere : Clause :=
  { relation := lookupRelation, input := appTerm (appTerm (.var 0) (.var 1)) (symTerm 0), output := .var 0, body := [] }

def lookupLater : Clause :=
  { relation := lookupRelation, input := appTerm (appTerm (.var 0) (.var 1)) (appTerm (symTerm 1) (.var 2)),
    output := .var 3, body := [.ask lookupRelation (appTerm (.var 1) (.var 2)) (.var 3)] }

def lookupLoose : Clause :=
  { relation := lookupRelation, input := appTerm (symTerm 0) (.var 0), output := looseTerm (.var 0), body := [] }

def replicateZero : Clause :=
  { relation := replicateRelation, input := triple (symTerm 0) (.var 0) (.var 1), output := .var 1, body := [] }

def replicateSucc : Clause :=
  { relation := replicateRelation, input := triple (appTerm (symTerm 1) (.var 0)) (.var 1) (.var 2),
    output := appTerm (.var 1) (.var 3),
    body := [.ask replicateRelation (triple (.var 0) (.var 1) (.var 2)) (.var 3)] }

def elementsNil : Clause :=
  { relation := elementsRelation, input := sext (symTerm 0) (.var 0) (.var 1) (.var 2) (.var 3) (.var 4),
    output := .var 4, body := [] }

def elementsCons : Clause :=
  { relation := elementsRelation,
    input := sext (appTerm (.var 0) (.var 1)) (.var 2) (.var 3) (.var 4) (.var 5) (.var 6), output := .var 8,
    body := [.ask elementsRelation (sext (.var 1) (.var 2) (.var 3) (.var 4) (appTerm (symTerm 1) (.var 5)) (.var 6))
        (.var 7),
      .ask generateRelation (quint (.var 0) (.var 2) (.var 3) (appTerm (.var 5) (.var 4)) (.var 7)) (.var 8)] }

def argumentsNil : Clause :=
  { relation := argumentsRelation, input := sext (symTerm 0) (symTerm 0) (.var 0) (.var 1) (.var 2) (.var 3),
    output := .var 3, body := [] }

/-- An argument of a parameter of a representation, whose argument row pattern checks the representation. -/
def argumentsCons (tag : ℕ) (argument : Tm) : Clause :=
  { relation := argumentsRelation,
    input := sext (appTerm argument (.var 1)) (appTerm (appTerm (symTerm tag) (.var 2)) (.var 3)) (.var 4) (.var 5)
      (.var 6) (.var 7),
    output := .var 9,
    body := [.ask argumentsRelation (sext (.var 1) (.var 3) (.var 4) (.var 5) (appTerm (symTerm 1) (.var 6)) (.var 7))
        (.var 8),
      .ask generateRelation (quint argument (.var 2) (.var 4) (appTerm (.var 6) (.var 5)) (.var 8)) (.var 9)] }

/-- An argument of a simple parameter: any pattern. -/
def argumentsSimple : Clause := argumentsCons 0 (.var 0)

/-- An argument of an abstraction: a binder without a name. -/
def argumentsAbstraction : Clause := argumentsCons 1 (appTerm (symTerm 3) (appTerm (symTerm 0) (.var 0)))

/-- An argument of an abstraction of several names: a binder without names. -/
def argumentsMultiAbstraction : Clause :=
  argumentsCons 2 (appTerm (symTerm 4) (appTerm (.var 10) (appTerm (symTerm 0) (.var 0))))

/-- **The fixed clauses of typing.** -/
def typingClauses : List Clause :=
  [generateBvar, generateFvar, generateLambda, generateMultiLambda, generateSubst, generateCollection, lookupHere,
    lookupLater, lookupLoose, replicateZero, replicateSucc, elementsNil, elementsCons, argumentsNil, argumentsSimple,
    argumentsAbstraction, argumentsMultiAbstraction]

theorem typingClauses_moded : ∀ c ∈ typingClauses, DemandTransformation.Moded c := by
  intro c inside
  simp only [typingClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl <;> exact DemandTransformation.moded_of_check (by decide)

/-- Whether a rule's representation is one bare collection, by computation. -/
def bareCarrier? (rule : GrammarRule) : Option (CollType × TypeExpr) :=
  match rule.bareParams with
  | [.simple _ (.collection kind element)] => some (kind, element)
  | _ => none

theorem bareCarrier?_spec (rule : GrammarRule) :
    (∃ kind element, bareCarrier? rule = some (kind, element) ∧
      ∃ parameterName, rule.bareParams = [.simple parameterName (.collection kind element)]) ∨
    (bareCarrier? rule = none ∧ ¬ Mettapedia.GSLT.LanguageDef.WellSorted.UsesBareCollection rule) := by
  unfold bareCarrier?
  split
  · rename_i parameterName kind element shape
    exact .inl ⟨kind, element, rfl, parameterName, shape⟩
  · rename_i notCarrier
    refine .inr ⟨rfl, fun ⟨parameterName, kind, element, shape⟩ => notCarrier parameterName kind element shape⟩

/-- **The clauses of a grammar rule**: a bare collection rule types its collections, and any other rule types its
applications when every parameter has a type. -/
def ruleClauses (rule : GrammarRule) : List Clause :=
  match bareCarrier? rule with
  | some (kind, element) => [generateCarrier kind element rule.category]
  | none => ((parametersTerm rule.params).map (generateConstructor rule.label rule.category)).toList

/-- The clauses of a language's grammar. -/
def grammarClauses (language : LanguageDef) : List Clause := language.terms.flatMap ruleClauses

/-! ## Reading patterns off their rows -/

open RootRewritesOnTheStep (encodeList optionRow namesRow)

theorem listRow_types_nil_inv {ctx : List TypeTerm} (same : Expr.sym 0 = listRow (ctx.map (termRow typeCodes))) :
    ctx = [] := by
  cases ctx with
  | nil => rfl
  | cons _ _ => simp [listRow] at same

theorem listRow_types_cons_inv {ctx : List TypeTerm} {a b : Expr}
    (same : Expr.app a b = listRow (ctx.map (termRow typeCodes))) :
    ∃ entry rest, ctx = entry :: rest ∧ a = termRow typeCodes entry ∧ b = listRow (rest.map (termRow typeCodes)) := by
  cases ctx with
  | nil => simp [listRow] at same
  | cons entry rest => simp only [List.map_cons, listRow, Expr.app.injEq] at same; exact ⟨entry, rest, rfl, same.1, same.2⟩

/-! ## Looking up and repeating types -/

/-- The type of an index among the binders around: theirs, or the unknown of the loose index beyond them. -/
def lookupType (ctx : List TypeTerm) (index : ℕ) : TypeTerm :=
  (ctx[index]?).getD (TypingUnknowns.unknown (.loose (index - ctx.length)))

/-- **A program with the clauses of typing** for a language. -/
structure TypingProgram (language : LanguageDef) (R : Relations) (program : List Clause) : Prop where
  included : ∀ c ∈ typingClauses, c ∈ program
  grammar : ∀ c ∈ grammarClauses language, c ∈ program
  only : ∀ c ∈ program, generateRelation ≤ c.relation → c.relation ≤ argumentsRelation →
    c ∈ typingClauses ∨ (c.relation = generateRelation ∧ c ∈ grammarClauses language)

section Generate

variable {language : LanguageDef} {R : Relations} {program : List Clause}

theorem clauseOf' {c : Clause} (typing : TypingProgram language R program) (member : c ∈ program) {r : ℕ}
    (isR : c.relation = r) (low : generateRelation ≤ r) (high : r ≤ argumentsRelation) :
    c ∈ typingClauses ∨ (c.relation = generateRelation ∧ c ∈ grammarClauses language) :=
  typing.only c member (isR ▸ low) (isR ▸ high)

/-- **Looking up derives the type of the index.** -/
theorem lookup_sound (typing : TypingProgram language R program) :
    ∀ (depth : ℕ) (ctx : List TypeTerm) (index : ℕ) (w : Expr),
      DerivesAt R program depth lookupRelation (.app (listRow (ctx.map (termRow typeCodes))) (numeral index)) w →
        w = termRow typeCodes (lookupType ctx index)
  | 0, _, _, _, derived => derived.elim
  | depth + 1, ctx, index, w, derived => by
      obtain ⟨c, member, isR, θ, input, output, goals⟩ := derived
      rcases clauseOf' typing member isR (by decide) (by decide) with inside | ⟨isGenerate, -⟩
      · simp only [typingClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl <;>
          first
          | exact absurd isR (by decide)
          | skip
        · simp only [lookupHere, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨ctxIs, indexIs⟩ := input
          rw [numeral_zero_inv indexIs]
          obtain ⟨entry, rest, rfl, entryRow, -⟩ := listRow_types_cons_inv ctxIs
          rw [← output, entryRow]
          rfl
        · simp only [lookupLater, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨ctxIs, indexIs⟩ := input
          obtain ⟨index', rfl, index'Is⟩ := numeral_succ_inv indexIs
          obtain ⟨entry, rest, rfl, -, restIs⟩ := listRow_types_cons_inv ctxIs
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, restIs,
            index'Is] at asked
          rw [← output, lookup_sound typing depth rest index' _ asked]
          simp [lookupType]
        · simp only [lookupLoose, looseTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨ctxIs, indexIs⟩ := input
          rw [listRow_types_nil_inv ctxIs]
          rw [← output, indexIs]
          simp [lookupType, termRow_unknown, unknownRow]
      · exact absurd (isGenerate.symm.trans isR) (by decide)

theorem lookup_complete (typing : TypingProgram language R program) :
    ∀ (ctx : List TypeTerm) (index : ℕ), Derives R program lookupRelation
      (.app (listRow (ctx.map (termRow typeCodes))) (numeral index)) (termRow typeCodes (lookupType ctx index))
  | [], index => by
      have clause := derives_of_clause (R := R) (typing.included lookupLoose (by simp [typingClauses]))
        (pick [numeral index]) (fun _ inside => absurd inside List.not_mem_nil)
      simpa [lookupLoose, looseTerm, pick, listRow, lookupType, termRow_unknown, unknownRow] using clause
  | entry :: rest, 0 => by
      have clause := derives_of_clause (R := R) (typing.included lookupHere (by simp [typingClauses]))
        (pick [termRow typeCodes entry, listRow (rest.map (termRow typeCodes))])
        (fun _ inside => absurd inside List.not_mem_nil)
      simpa [lookupHere, pick, listRow, lookupType, numeral] using clause
  | entry :: rest, index + 1 => by
      have inner := lookup_complete typing rest index
      have clause := derives_of_clause (R := R) (typing.included lookupLater (by simp [typingClauses]))
        (pick [termRow typeCodes entry, listRow (rest.map (termRow typeCodes)), numeral index,
          termRow typeCodes (lookupType rest index)]) (fun g inside => by
          simp only [lookupLater, List.mem_cons, List.not_mem_nil, or_false] at inside
          subst inside
          simpa [goalHolds, pick] using inner)
      have same : lookupType (entry :: rest) (index + 1) = lookupType rest index := by simp [lookupType]
      rw [same]
      simpa [lookupLater, pick, listRow, numeral] using clause

/-- **Repeating derives the copies before the binders.** -/
theorem replicate_sound (typing : TypingProgram language R program) :
    ∀ (depth count : ℕ) (entry : TypeTerm) (ctx : List TypeTerm) (w : Expr),
      DerivesAt R program depth replicateRelation
        (.app (.app (numeral count) (termRow typeCodes entry)) (listRow (ctx.map (termRow typeCodes)))) w →
        w = listRow ((List.replicate count entry ++ ctx).map (termRow typeCodes))
  | 0, _, _, _, _, derived => derived.elim
  | depth + 1, count, entry, ctx, w, derived => by
      obtain ⟨c, member, isR, θ, input, output, goals⟩ := derived
      rcases clauseOf' typing member isR (by decide) (by decide) with inside | ⟨isGenerate, -⟩
      · simp only [typingClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl <;>
          first
          | exact absurd isR (by decide)
          | skip
        · simp only [replicateZero, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨countIs, -⟩, ctxIs⟩ := input
          rw [numeral_zero_inv countIs, ← output, ctxIs]
          rfl
        · simp only [replicateSucc, triple, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
            DemandTransformation.inst_unknown, Expr.app.injEq] at input output
          obtain ⟨⟨countIs, entryIs⟩, ctxIs⟩ := input
          obtain ⟨count', rfl, count'Is⟩ := numeral_succ_inv countIs
          have asked := goals _ List.mem_cons_self
          simp only [goalHolds, triple, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
            count'Is, entryIs, ctxIs] at asked
          rw [← output, entryIs, replicate_sound typing depth count' entry ctx _ asked]
          simp [List.replicate_succ, listRow]
      · exact absurd (isGenerate.symm.trans isR) (by decide)

theorem replicate_complete (typing : TypingProgram language R program) (entry : TypeTerm) (ctx : List TypeTerm) :
    ∀ count : ℕ, Derives R program replicateRelation
      (.app (.app (numeral count) (termRow typeCodes entry)) (listRow (ctx.map (termRow typeCodes))))
      (listRow ((List.replicate count entry ++ ctx).map (termRow typeCodes)))
  | 0 => by
      have clause := derives_of_clause (R := R) (typing.included replicateZero (by simp [typingClauses]))
        (pick [termRow typeCodes entry, listRow (ctx.map (termRow typeCodes))])
        (fun _ inside => absurd inside List.not_mem_nil)
      simpa [replicateZero, triple, pick, numeral] using clause
  | count + 1 => by
      have inner := replicate_complete typing entry ctx count
      have clause := derives_of_clause (R := R) (typing.included replicateSucc (by simp [typingClauses]))
        (pick [numeral count, termRow typeCodes entry, listRow (ctx.map (termRow typeCodes)),
          listRow ((List.replicate count entry ++ ctx).map (termRow typeCodes))]) (fun g inside => by
          simp only [replicateSucc, List.mem_cons, List.not_mem_nil, or_false] at inside
          subst inside
          simpa [goalHolds, triple, pick] using inner)
      simpa [replicateSucc, triple, pick, numeral, List.replicate_succ, listRow] using clause

end Generate

/-! ## What generation derives -/

open Mettapedia.GSLT.LanguageDef.WellSorted (parameterType? MatchesParameterRepresentation UsesBareCollection)
open TypingUnknowns (Generates ElementsGenerate ArgumentsGenerate)

/-- The row of a generation's input. -/
def generateRow (p : Pattern) (τ : TypeTerm) (ctx : List TypeTerm) (π : List ℕ) (acc : List (TypeTerm × TypeTerm)) :
    Expr :=
  .app (encode p) (.app (termRow typeCodes τ) (.app (listRow (ctx.map (termRow typeCodes)))
    (.app (pathRow π) (eqsRow typeCodes acc))))

/-- The row of the input of the elements of a collection. -/
def elementsRow (elements : List Pattern) (τ : TypeTerm) (ctx : List TypeTerm) (π : List ℕ) (index : ℕ)
    (acc : List (TypeTerm × TypeTerm)) : Expr :=
  .app (encodeList elements) (.app (termRow typeCodes τ) (.app (listRow (ctx.map (termRow typeCodes)))
    (.app (pathRow π) (.app (numeral index) (eqsRow typeCodes acc)))))

/-- The row of the input of the arguments of a constructor. -/
def argumentsRow (arguments : List Pattern) (parameters : Expr) (ctx : List TypeTerm) (π : List ℕ) (index : ℕ)
    (acc : List (TypeTerm × TypeTerm)) : Expr :=
  .app (encodeList arguments) (.app parameters (.app (listRow (ctx.map (termRow typeCodes)))
    (.app (pathRow π) (.app (numeral index) (eqsRow typeCodes acc)))))

/-- The row of a row pattern with no unknowns. -/
def groundRow (t : Tm) : Expr := inst (fun _ => .sym 0) t

theorem parametersTerm_ground : ∀ {parameters : List TermParam} {t : Tm}, parametersTerm parameters = some t →
    RuleSyntax.Machines.unknowns t = []
  | [], t, lowered => by
      simp only [parametersTerm, Option.some.injEq] at lowered
      subst lowered
      rfl
  | parameter :: parameters, t, lowered => by
      simp only [parametersTerm, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
      obtain ⟨expected, -, rest, restLowered, rfl⟩ := lowered
      simp [parametersTerm_ground restLowered]

theorem inst_ground {t : Tm} (ground : RuleSyntax.Machines.unknowns t = []) (θ : ℕ → Expr) :
    inst θ t = groundRow t :=
  DemandTransformation.inst_agree t fun x inside => by simp [ground] at inside

theorem parametersTerm_nil_row : ∀ {parameters : List TermParam} {t : Tm}, parametersTerm parameters = some t →
    groundRow t = .sym 0 → parameters = []
  | [], _, _, _ => rfl
  | parameter :: parameters, t, lowered, isNil => by
      simp only [parametersTerm, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
      obtain ⟨expected, -, rest, -, rfl⟩ := lowered
      simp [groundRow] at isNil

theorem parametersTerm_cons_row {parameters : List TermParam} {t : Tm} (lowered : parametersTerm parameters = some t)
    {tag : ℕ} {typeRow rest : Expr} (isCons : groundRow t = .app (.app (.sym tag) typeRow) rest) :
    ∃ parameter others expected restTerm, parameters = parameter :: others ∧ tagOf parameter = tag ∧
      parameterType? parameter = some expected ∧ parametersTerm others = some restTerm ∧
      typeRow = termRow typeCodes (TypingUnknowns.typeTerm expected) ∧ rest = groundRow restTerm := by
  cases parameters with
  | nil =>
      simp only [parametersTerm, Option.some.injEq] at lowered
      subst lowered
      simp [groundRow] at isCons
  | cons parameter others =>
      simp only [parametersTerm, Option.bind_eq_some_iff, Option.map_eq_some_iff] at lowered
      obtain ⟨expected, expectedIs, restTerm, restLowered, rfl⟩ := lowered
      simp only [groundRow, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
        inst_typeRowTerm, Expr.app.injEq, Expr.sym.injEq] at isCons
      exact ⟨parameter, others, expected, restTerm, rfl, isCons.1.1, expectedIs, restLowered, isCons.1.2.symm,
        isCons.2.symm⟩

theorem grammar_clause {language : LanguageDef} {c : Clause} (inside : c ∈ grammarClauses language) :
    ∃ rule ∈ language.terms,
      (∃ kind element, bareCarrier? rule = some (kind, element) ∧ c = generateCarrier kind element rule.category) ∨
      (bareCarrier? rule = none ∧ ∃ t, parametersTerm rule.params = some t ∧
        c = generateConstructor rule.label rule.category t) := by
  simp only [grammarClauses, List.mem_flatMap] at inside
  obtain ⟨rule, member, inRule⟩ := inside
  refine ⟨rule, member, ?_⟩
  unfold ruleClauses at inRule
  split at inRule
  · rename_i kind element carrier
    simp only [List.mem_singleton] at inRule
    exact .inl ⟨kind, element, carrier, inRule⟩
  · rename_i notCarrier
    cases lowered : parametersTerm rule.params with
    | none => simp [lowered] at inRule
    | some t =>
        simp only [lowered, Option.map_some, Option.toList_some, List.mem_singleton] at inRule
        exact .inr ⟨notCarrier, t, rfl, inRule⟩

theorem generateCarrier_moded (kind : CollType) (element : TypeExpr) (category : String) :
    DemandTransformation.Moded (generateCarrier kind element category) :=
  DemandTransformation.moded_of_inputsBound
    (.cons (by simp [generateCarrier, sext, quint, DemandTransformation.goalInputs]) (.nil _))
    (by simp [generateCarrier, quint, constRowTerm, DemandTransformation.goalUnknowns])

theorem generateConstructor_moded (label category : String) {parameters : Tm}
    (ground : RuleSyntax.Machines.unknowns parameters = []) :
    DemandTransformation.Moded (generateConstructor label category parameters) :=
  DemandTransformation.moded_of_inputsBound
    (.cons (by simp [generateConstructor, sext, quint, DemandTransformation.goalInputs, ground]) (.nil _))
    (by simp [generateConstructor, quint, constRowTerm, DemandTransformation.goalUnknowns])

theorem grammarClauses_moded (language : LanguageDef) :
    ∀ c ∈ grammarClauses language, DemandTransformation.Moded c := by
  intro c inside
  obtain ⟨rule, -, ⟨kind, element, -, rfl⟩ | ⟨-, t, lowered, rfl⟩⟩ := grammar_clause inside
  · exact generateCarrier_moded kind element rule.category
  · exact generateConstructor_moded rule.label rule.category (parametersTerm_ground lowered)

theorem grammarClauses_relation {language : LanguageDef} {c : Clause} (inside : c ∈ grammarClauses language) :
    c.relation = generateRelation := by
  obtain ⟨rule, -, ⟨kind, element, -, rfl⟩ | ⟨-, t, -, rfl⟩⟩ := grammar_clause inside <;> rfl

theorem typingClauses_relation :
    ∀ c ∈ typingClauses, generateRelation ≤ c.relation ∧ c.relation ≤ argumentsRelation := by decide

theorem differClauses_relation :
    ∀ c ∈ differClauses, UnificationClauses.differRelation ≤ c.relation ∧ c.relation ≤ pathsDifferRelation := by
  decide

section Generate

variable {language : LanguageDef} {R : Relations} {program : List Clause}

mutual
  /-- **What generation derives is a generated list of equations before the given ones.** -/
  theorem generate_sound (typing : TypingProgram language R program) : ∀ (depth : ℕ) (p : Pattern) (τ : TypeTerm)
      (ctx : List TypeTerm) (π : List ℕ) (acc : List (TypeTerm × TypeTerm)) (w : Expr),
      DerivesAt R program depth generateRelation (generateRow p τ ctx π acc) w →
        ∃ E, Generates language p τ ctx π E ∧ w = eqsRow typeCodes (E ++ acc)
    | 0, _, _, _, _, _, _, derived => derived.elim
    | depth + 1, p, τ, ctx, π, acc, w, derived => by
        obtain ⟨c, member, isR, θ, input, output, goals⟩ := derived
        rcases clauseOf' typing member isR (by decide) (by decide) with inside | ⟨-, inGrammar⟩
        · simp only [typingClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl <;>
            first
            | exact absurd isR (by decide)
            | skip
          · simp only [generateBvar, quint, generateRow, RootRewritesOnTheStep.inst_appTerm,
              RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
            obtain ⟨pIs, τIs, ctxIs, πIs, accIs⟩ := input
            obtain ⟨index, rfl, indexIs⟩ := encode_bvar_inv pIs
            have asked := goals _ List.mem_cons_self
            simp only [goalHolds, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown, ctxIs,
              indexIs] at asked
            have typeIs := lookup_sound typing depth ctx index _ asked
            refine ⟨[(τ, lookupType ctx index)], ?_, ?_⟩
            · by_cases inside : index < ctx.length
              · have found : ctx[index]? = some (lookupType ctx index) := by
                  simp [lookupType, List.getElem?_eq_getElem inside]
                exact .bvarInside found
              · have outside : lookupType ctx index = TypingUnknowns.unknown (.loose (index - ctx.length)) := by
                  simp [lookupType, List.getElem?_eq_none (by omega : ctx.length ≤ index)]
                rw [outside]
                exact .bvarLoose (by omega)
            · rw [← output, τIs, typeIs, accIs]
              rfl
          · simp only [generateFvar, quint, freeTerm, generateRow, RootRewritesOnTheStep.inst_appTerm,
              RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
            obtain ⟨pIs, τIs, -, -, accIs⟩ := input
            obtain ⟨name, rfl, nameIs⟩ := encode_fvar_inv pIs
            refine ⟨_, .fvar, ?_⟩
            rw [← output, τIs, nameIs, accIs]
            rfl
          · simp only [generateLambda, quint, generateRow, RootRewritesOnTheStep.inst_appTerm,
              RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
            obtain ⟨pIs, τIs, ctxIs, πIs, accIs⟩ := input
            obtain ⟨binder, body, rfl, -, bodyIs⟩ := encode_lambda_inv pIs
            have asked := goals _ List.mem_cons_self
            simp only [goalHolds, quint, nodeTerm, RootRewritesOnTheStep.inst_appTerm,
              RootRewritesOnTheStep.inst_symTerm, RootRewritesOnTheStep.inst_numeralTerm,
              DemandTransformation.inst_unknown, bodyIs, ctxIs, πIs, accIs] at asked
            obtain ⟨E, generated, outIs⟩ := generate_sound typing depth body (TypingUnknowns.unknown (.node π 1))
              (TypingUnknowns.unknown (.node π 0) :: ctx) (0 :: π) acc _ asked
            refine ⟨_, .lambda generated, ?_⟩
            rw [← output, τIs, outIs]
            simp only [arrowRowTerm, nodeTerm, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
              RootRewritesOnTheStep.inst_numeralTerm, DemandTransformation.inst_unknown, πIs]
            rfl
          · simp only [generateMultiLambda, quint, generateRow, RootRewritesOnTheStep.inst_appTerm,
              RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
            obtain ⟨pIs, τIs, ctxIs, πIs, accIs⟩ := input
            obtain ⟨arity, binders, body, rfl, arityIs, -, bodyIs⟩ := encode_multiLambda_inv pIs
            have first := goals _ List.mem_cons_self
            have second := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
            simp only [goalHolds, triple, nodeTerm, RootRewritesOnTheStep.inst_appTerm,
              RootRewritesOnTheStep.inst_symTerm, RootRewritesOnTheStep.inst_numeralTerm,
              DemandTransformation.inst_unknown, arityIs, ctxIs, πIs] at first
            have repeated := replicate_sound typing depth arity (TypingUnknowns.unknown (.node π 0)) ctx _ first
            simp only [goalHolds, quint, nodeTerm, RootRewritesOnTheStep.inst_appTerm,
              RootRewritesOnTheStep.inst_symTerm, RootRewritesOnTheStep.inst_numeralTerm,
              DemandTransformation.inst_unknown, bodyIs, repeated, πIs, accIs] at second
            obtain ⟨E, generated, outIs⟩ := generate_sound typing depth body (TypingUnknowns.unknown (.node π 1))
              (List.replicate arity (TypingUnknowns.unknown (.node π 0)) ++ ctx) (0 :: π) acc _ second
            refine ⟨_, .multiLambda generated, ?_⟩
            rw [← output, τIs, outIs]
            simp only [arrowRowTerm, binderRowTerm, nodeTerm, RootRewritesOnTheStep.inst_appTerm,
              RootRewritesOnTheStep.inst_symTerm, RootRewritesOnTheStep.inst_numeralTerm,
              DemandTransformation.inst_unknown, πIs]
            rfl
          · simp only [generateSubst, quint, generateRow, RootRewritesOnTheStep.inst_appTerm,
              RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
            obtain ⟨pIs, τIs, ctxIs, πIs, accIs⟩ := input
            obtain ⟨body, value, rfl, bodyIs, valueIs⟩ := encode_subst_inv pIs
            have first := goals _ List.mem_cons_self
            have second := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
            simp only [goalHolds, quint, nodeTerm, RootRewritesOnTheStep.inst_appTerm,
              RootRewritesOnTheStep.inst_symTerm, RootRewritesOnTheStep.inst_numeralTerm,
              DemandTransformation.inst_unknown, valueIs, ctxIs, πIs, accIs] at first
            obtain ⟨E₂, valueGenerated, middleIs⟩ := generate_sound typing depth value
              (TypingUnknowns.unknown (.node π 0)) ctx (1 :: π) acc _ first
            simp only [goalHolds, quint, nodeTerm, RootRewritesOnTheStep.inst_appTerm,
              RootRewritesOnTheStep.inst_symTerm, RootRewritesOnTheStep.inst_numeralTerm,
              DemandTransformation.inst_unknown, bodyIs, τIs, ctxIs, πIs, middleIs] at second
            obtain ⟨E₁, bodyGenerated, outIs⟩ := generate_sound typing depth body τ
              (TypingUnknowns.unknown (.node π 0) :: ctx) (0 :: π) (E₂ ++ acc) _ second
            refine ⟨_, .subst bodyGenerated valueGenerated, ?_⟩
            rw [← output, outIs, List.append_assoc]
          · simp only [generateCollection, quint, generateRow, RootRewritesOnTheStep.inst_appTerm,
              RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
            obtain ⟨pIs, τIs, ctxIs, πIs, accIs⟩ := input
            obtain ⟨kind, elements, rest, rfl, kindIs, elementsIs, -⟩ := encode_collection_inv pIs
            have asked := goals _ List.mem_cons_self
            simp only [goalHolds, sext, quint, nodeTerm, RootRewritesOnTheStep.inst_appTerm,
              RootRewritesOnTheStep.inst_symTerm, RootRewritesOnTheStep.inst_numeralTerm,
              DemandTransformation.inst_unknown, elementsIs, ctxIs, πIs, accIs] at asked
            obtain ⟨E, generated, outIs⟩ := elements_sound typing depth elements (TypingUnknowns.unknown (.node π 0))
              ctx π 0 acc _ asked
            refine ⟨_, .collection generated, ?_⟩
            rw [← output, τIs, outIs]
            simp only [collectionRowTerm, nodeTerm, RootRewritesOnTheStep.inst_appTerm,
              RootRewritesOnTheStep.inst_symTerm, RootRewritesOnTheStep.inst_numeralTerm,
              DemandTransformation.inst_unknown, kindIs, πIs]
            rfl
        · obtain ⟨rule, ruleIn, ⟨kind, element, carrier, rfl⟩ | ⟨notCarrier, parameters, lowered, rfl⟩⟩ :=
            grammar_clause inGrammar
          · simp only [generateCarrier, quint, generateRow, RootRewritesOnTheStep.inst_appTerm,
              RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
            obtain ⟨pIs, τIs, ctxIs, πIs, accIs⟩ := input
            obtain ⟨kind', elements, rest, rfl, kindIs, elementsIs, -⟩ := encode_collection_inv pIs
            obtain rfl := collectionCode_injective (Expr.sym.inj kindIs)
            have asked := goals _ List.mem_cons_self
            simp only [goalHolds, sext, quint, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
              inst_typeRowTerm, DemandTransformation.inst_unknown, elementsIs, ctxIs, πIs, accIs] at asked
            obtain ⟨E, generated, outIs⟩ := elements_sound typing depth elements (TypingUnknowns.typeTerm element)
              ctx π 0 acc _ (by simpa [elementsRow, numeral] using asked)
            obtain ⟨parameterName, shape⟩ : ∃ parameterName,
                rule.bareParams = [.simple parameterName (.collection kind element)] := by
              rcases bareCarrier?_spec rule with ⟨kind'', element', carrier', parameterName, shape⟩ | ⟨none, -⟩
              · rw [carrier] at carrier'
                simp only [Option.some.injEq, Prod.mk.injEq] at carrier'
                obtain ⟨rfl, rfl⟩ := carrier'
                exact ⟨parameterName, shape⟩
              · rw [carrier] at none
                cases none
            refine ⟨_, .collectionConstructor ruleIn shape generated, ?_⟩
            rw [← output, τIs, outIs]
            rfl
          · simp only [generateConstructor, quint, generateRow, RootRewritesOnTheStep.inst_appTerm,
              RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
            obtain ⟨pIs, τIs, ctxIs, πIs, accIs⟩ := input
            obtain ⟨label, arguments, rfl, labelIs, argumentsIs⟩ := encode_apply_inv pIs
            obtain rfl := labelCode_injective (Expr.sym.inj labelIs)
            have asked := goals _ List.mem_cons_self
            simp only [goalHolds, sext, quint, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
              DemandTransformation.inst_unknown, argumentsIs, ctxIs, πIs, accIs,
              inst_ground (parametersTerm_ground lowered)] at asked
            obtain ⟨E, generated, outIs⟩ := arguments_sound typing depth arguments rule.params parameters lowered
              ctx π 0 acc _ (by simpa [argumentsRow, numeral] using asked)
            have notBare : ¬ UsesBareCollection rule := by
              rcases bareCarrier?_spec rule with ⟨_, _, carrier', -⟩ | ⟨-, notBare⟩
              · rw [notCarrier] at carrier'
                cases carrier'
              · exact notBare
            refine ⟨_, .constructor ruleIn notBare generated, ?_⟩
            rw [← output, τIs, outIs]
            rfl

  theorem elements_sound (typing : TypingProgram language R program) : ∀ (depth : ℕ) (elements : List Pattern)
      (τ : TypeTerm) (ctx : List TypeTerm) (π : List ℕ) (index : ℕ) (acc : List (TypeTerm × TypeTerm)) (w : Expr),
      DerivesAt R program depth elementsRelation (elementsRow elements τ ctx π index acc) w →
        ∃ E, ElementsGenerate language elements τ ctx π index E ∧ w = eqsRow typeCodes (E ++ acc)
    | 0, _, _, _, _, _, _, _, derived => derived.elim
    | depth + 1, elements, τ, ctx, π, index, acc, w, derived => by
        obtain ⟨c, member, isR, θ, input, output, goals⟩ := derived
        rcases clauseOf' typing member isR (by decide) (by decide) with inside | ⟨isGenerate, -⟩
        · simp only [typingClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl <;>
            first
            | exact absurd isR (by decide)
            | skip
          · simp only [elementsNil, sext, quint, elementsRow, RootRewritesOnTheStep.inst_appTerm,
              RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
            obtain ⟨elementsIs, -, -, -, -, accIs⟩ := input
            rw [encodeList_nil_inv elementsIs]
            exact ⟨[], .nil, by rw [← output, accIs]; rfl⟩
          · simp only [elementsCons, sext, quint, elementsRow, RootRewritesOnTheStep.inst_appTerm,
              DemandTransformation.inst_unknown, Expr.app.injEq] at input output
            obtain ⟨elementsIs, τIs, ctxIs, πIs, indexIs, accIs⟩ := input
            obtain ⟨element, rest, rfl, elementIs, restIs⟩ := encodeList_cons_inv elementsIs
            have first := goals _ List.mem_cons_self
            have second := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
            simp only [goalHolds, sext, quint, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
              DemandTransformation.inst_unknown, restIs, τIs, ctxIs, πIs, indexIs, accIs] at first
            obtain ⟨E₂, restGenerated, middleIs⟩ := elements_sound typing depth rest τ ctx π (index + 1) acc _
              (by simpa [elementsRow, numeral] using first)
            simp only [goalHolds, quint, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
              elementIs, τIs, ctxIs, πIs, indexIs, middleIs] at second
            obtain ⟨E₁, elementGenerated, outIs⟩ := generate_sound typing depth element τ ctx (index :: π) (E₂ ++ acc) _
              second
            exact ⟨_, .cons elementGenerated restGenerated, by rw [← output, outIs, List.append_assoc]⟩
        · exact absurd (isGenerate.symm.trans isR) (by decide)

  theorem arguments_sound (typing : TypingProgram language R program) : ∀ (depth : ℕ) (arguments : List Pattern)
      (parameters : List TermParam) (t : Tm), parametersTerm parameters = some t → ∀ (ctx : List TypeTerm)
      (π : List ℕ) (index : ℕ) (acc : List (TypeTerm × TypeTerm)) (w : Expr),
      DerivesAt R program depth argumentsRelation (argumentsRow arguments (groundRow t) ctx π index acc) w →
        ∃ E, ArgumentsGenerate language arguments parameters ctx π index E ∧ w = eqsRow typeCodes (E ++ acc)
    | 0, _, _, _, _, _, _, _, _, _, derived => derived.elim
    | depth + 1, arguments, parameters, t, lowered, ctx, π, index, acc, w, derived => by
        obtain ⟨c, member, isR, θ, input, output, goals⟩ := derived
        rcases clauseOf' typing member isR (by decide) (by decide) with inside | ⟨isGenerate, -⟩
        · simp only [typingClauses, List.mem_cons, List.not_mem_nil, or_false] at inside
          rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl <;>
            first
            | exact absurd isR (by decide)
            | skip
          · simp only [argumentsNil, sext, quint, argumentsRow, RootRewritesOnTheStep.inst_appTerm,
              RootRewritesOnTheStep.inst_symTerm, DemandTransformation.inst_unknown, Expr.app.injEq] at input output
            obtain ⟨argumentsIs, parametersIs, -, -, -, accIs⟩ := input
            rw [encodeList_nil_inv argumentsIs, parametersTerm_nil_row lowered parametersIs.symm]
            exact ⟨[], .nil, by rw [← output, accIs]; rfl⟩
          all_goals
            simp only [argumentsSimple, argumentsAbstraction, argumentsMultiAbstraction, argumentsCons, sext, quint,
              argumentsRow, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
              DemandTransformation.inst_unknown, Expr.app.injEq] at input output
            obtain ⟨argumentsIs, parametersIs, ctxIs, πIs, indexIs, accIs⟩ := input
            obtain ⟨parameter, others, expected, restTerm, rfl, tagIs, expectedIs, restLowered, typeIs, restIs⟩ :=
              parametersTerm_cons_row lowered parametersIs.symm
            obtain ⟨argument, rest, rfl, argumentIs, restArgumentsIs⟩ := encodeList_cons_inv argumentsIs
            have first := goals _ List.mem_cons_self
            have second := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
            simp only [goalHolds, sext, quint, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
              DemandTransformation.inst_unknown, restArgumentsIs, restIs, ctxIs, πIs, indexIs, accIs] at first
            obtain ⟨E₂, restGenerated, middleIs⟩ := arguments_sound typing depth rest others restTerm restLowered ctx
              π (index + 1) acc _ (by simpa [argumentsRow, numeral] using first)
            simp only [goalHolds, quint, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
              DemandTransformation.inst_unknown, typeIs, ctxIs, πIs, indexIs, middleIs] at second
          · rw [argumentIs] at second
            obtain ⟨E₁, argumentGenerated, outIs⟩ := generate_sound typing depth argument _ ctx (index :: π)
              (E₂ ++ acc) _ second
            have representation : MatchesParameterRepresentation parameter argument := by
              cases parameter <;> simp_all [tagOf, MatchesParameterRepresentation]
            exact ⟨_, .cons representation expectedIs argumentGenerated restGenerated,
              by rw [← output, outIs, List.append_assoc]⟩
          · obtain ⟨binder, body, rfl, binderIs, bodyIs⟩ := encode_lambda_inv argumentIs
            have noName : binder = none := by
              cases binder with
              | none => rfl
              | some _ => simp [optionRow] at binderIs
            subst noName
            rw [bodyIs] at second
            obtain ⟨E₁, argumentGenerated, outIs⟩ := generate_sound typing depth (.lambda none body) _ ctx (index :: π)
              (E₂ ++ acc) _ second
            have representation : MatchesParameterRepresentation parameter (.lambda none body) := by
              cases parameter <;> simp_all [tagOf, MatchesParameterRepresentation]
            exact ⟨_, .cons representation expectedIs argumentGenerated restGenerated,
              by rw [← output, outIs, List.append_assoc]⟩
          · obtain ⟨arity, binders, body, rfl, arityIs, bindersIs, bodyIs⟩ := encode_multiLambda_inv argumentIs
            have noNames : binders = [] := by
              cases binders with
              | nil => rfl
              | cons _ _ => simp [namesRow] at bindersIs
            subst noNames
            rw [bodyIs, arityIs] at second
            obtain ⟨E₁, argumentGenerated, outIs⟩ := generate_sound typing depth (.multiLambda arity [] body) _ ctx
              (index :: π) (E₂ ++ acc) _ second
            have representation : MatchesParameterRepresentation parameter (.multiLambda arity [] body) := by
              cases parameter <;> simp_all [tagOf, MatchesParameterRepresentation]
            exact ⟨_, .cons representation expectedIs argumentGenerated restGenerated,
              by rw [← output, outIs, List.append_assoc]⟩
        · exact absurd (isGenerate.symm.trans isR) (by decide)
end

end Generate

theorem parametersTerm_of_arguments {language : LanguageDef} :
    ∀ {arguments : List Pattern} {parameters : List TermParam} {ctx : List TypeTerm} {π : List ℕ} {index : ℕ}
      {E : List (TypeTerm × TypeTerm)}, ArgumentsGenerate language arguments parameters ctx π index E →
      ∃ t, parametersTerm parameters = some t
  | _, _, _, _, _, _, .nil => ⟨_, rfl⟩
  | _, _, _, _, _, _, .cons (parameter := parameter) (expected := expected) _ expectedIs _ rest => by
      obtain ⟨t, lowered⟩ := parametersTerm_of_arguments rest
      exact ⟨appTerm (appTerm (symTerm (tagOf parameter)) (typeRowTerm expected)) t,
        by simp [parametersTerm, expectedIs, lowered]⟩

theorem bareCarrier_of_shape {rule : GrammarRule} {parameterName : String} {kind : CollType} {element : TypeExpr}
    (shape : rule.bareParams = [.simple parameterName (.collection kind element)]) :
    bareCarrier? rule = some (kind, element) := by
  simp [bareCarrier?, shape]

theorem bareCarrier_none {rule : GrammarRule} (notBare : ¬ UsesBareCollection rule) : bareCarrier? rule = none := by
  rcases bareCarrier?_spec rule with ⟨kind, element, -, parameterName, shape⟩ | ⟨none, -⟩
  · exact absurd ⟨parameterName, kind, element, shape⟩ notBare
  · exact none

section Generate

variable {language : LanguageDef} {R : Relations} {program : List Clause}

theorem carrier_included (typing : TypingProgram language R program) {rule : GrammarRule}
    (member : rule ∈ language.terms) {kind : CollType} {element : TypeExpr}
    (carrier : bareCarrier? rule = some (kind, element)) : generateCarrier kind element rule.category ∈ program :=
  typing.grammar _ (List.mem_flatMap.mpr ⟨rule, member, by simp [ruleClauses, carrier]⟩)

theorem constructor_included (typing : TypingProgram language R program) {rule : GrammarRule}
    (member : rule ∈ language.terms) (notCarrier : bareCarrier? rule = none) {t : Tm}
    (lowered : parametersTerm rule.params = some t) : generateConstructor rule.label rule.category t ∈ program :=
  typing.grammar _ (List.mem_flatMap.mpr ⟨rule, member, by simp [ruleClauses, notCarrier, lowered]⟩)

mutual
  /-- **Every generated list of equations is derived by generation**, before any given equations. -/
  theorem generate_complete (typing : TypingProgram language R program) :
      ∀ {p : Pattern} {τ : TypeTerm} {ctx : List TypeTerm} {π : List ℕ} {E : List (TypeTerm × TypeTerm)},
      Generates language p τ ctx π E → ∀ acc : List (TypeTerm × TypeTerm),
        Derives R program generateRelation (generateRow p τ ctx π acc) (eqsRow typeCodes (E ++ acc))
    | .bvar index, τ, ctx, π, _, .bvarInside (T := T) found, acc => by
        have looked := lookup_complete typing ctx index
        have typeIs : lookupType ctx index = T := by simp [lookupType, found]
        rw [typeIs] at looked
        have clause := derives_of_clause (R := R) (typing.included generateBvar (by simp [typingClauses]))
          (pick [numeral index, termRow typeCodes τ, listRow (ctx.map (termRow typeCodes)), pathRow π,
            eqsRow typeCodes acc, termRow typeCodes T]) (fun g inside => by
            simp only [generateBvar, List.mem_cons, List.not_mem_nil, or_false] at inside
            subst inside
            simpa [goalHolds, pick] using looked)
        simpa [generateBvar, quint, pick, generateRow, encode, eqsRow] using clause
    | .bvar index, τ, ctx, π, _, .bvarLoose outside, acc => by
        have looked := lookup_complete typing ctx index
        have typeIs : lookupType ctx index = TypingUnknowns.unknown (.loose (index - ctx.length)) := by
          simp [lookupType, List.getElem?_eq_none outside]
        rw [typeIs] at looked
        have clause := derives_of_clause (R := R) (typing.included generateBvar (by simp [typingClauses]))
          (pick [numeral index, termRow typeCodes τ, listRow (ctx.map (termRow typeCodes)), pathRow π,
            eqsRow typeCodes acc, termRow typeCodes (TypingUnknowns.unknown (.loose (index - ctx.length)))])
          (fun g inside => by
            simp only [generateBvar, List.mem_cons, List.not_mem_nil, or_false] at inside
            subst inside
            simpa [goalHolds, pick] using looked)
        simpa [generateBvar, quint, pick, generateRow, encode, eqsRow] using clause
    | .fvar name, τ, ctx, π, _, .fvar, acc => by
        have clause := derives_of_clause (R := R) (typing.included generateFvar (by simp [typingClauses]))
          (pick [.sym (labelCode name), termRow typeCodes τ, listRow (ctx.map (termRow typeCodes)), pathRow π,
            eqsRow typeCodes acc]) (fun _ inside => absurd inside List.not_mem_nil)
        simpa [generateFvar, quint, freeTerm, pick, generateRow, encode, eqsRow, termRow_unknown, unknownRow]
          using clause
    | .lambda binder body, τ, ctx, π, _, .lambda (E := E) generated, acc => by
        have inner := generate_complete typing generated acc
        have clause := derives_of_clause (R := R) (typing.included generateLambda (by simp [typingClauses]))
          (pick [optionRow binder, encode body, termRow typeCodes τ, listRow (ctx.map (termRow typeCodes)),
            pathRow π, eqsRow typeCodes acc, eqsRow typeCodes (E ++ acc)]) (fun g inside => by
            simp only [generateLambda, List.mem_cons, List.not_mem_nil, or_false] at inside
            subst inside
            simpa [goalHolds, quint, nodeTerm, pick, generateRow, termRow_unknown, unknownRow, pathRow, listRow]
              using inner)
        simpa [generateLambda, quint, arrowRowTerm, nodeTerm, pick, generateRow, encode, eqsRow,
          termRow_arrowTerm, termRow_unknown, unknownRow] using clause
    | .multiLambda arity binders body, τ, ctx, π, _, .multiLambda (E := E) generated, acc => by
        have repeated := replicate_complete typing (TypingUnknowns.unknown (.node π 0)) ctx arity
        have inner := generate_complete typing generated acc
        have clause := derives_of_clause (R := R)
          (typing.included generateMultiLambda (by simp [typingClauses]))
          (pick [numeral arity, namesRow binders, encode body, termRow typeCodes τ,
            listRow (ctx.map (termRow typeCodes)), pathRow π, eqsRow typeCodes acc,
            listRow ((List.replicate arity (TypingUnknowns.unknown (.node π 0)) ++ ctx).map (termRow typeCodes)),
            eqsRow typeCodes (E ++ acc)]) (fun g inside => by
            simp only [generateMultiLambda, List.mem_cons, List.not_mem_nil, or_false] at inside
            rcases inside with rfl | rfl
            · simpa [goalHolds, triple, nodeTerm, pick, termRow_unknown, unknownRow] using repeated
            · simpa [goalHolds, quint, nodeTerm, pick, generateRow, termRow_unknown, unknownRow, pathRow]
                using inner)
        simpa [generateMultiLambda, quint, arrowRowTerm, binderRowTerm, nodeTerm, pick, generateRow, encode, eqsRow,
          termRow_arrowTerm, termRow_binderTerm, termRow_unknown, unknownRow] using clause
    | .subst body value, τ, ctx, π, _, .subst (E₁ := E₁) (E₂ := E₂) bodyGenerated valueGenerated, acc => by
        have valueDerived := generate_complete typing valueGenerated acc
        have bodyDerived := generate_complete typing bodyGenerated (E₂ ++ acc)
        have clause := derives_of_clause (R := R) (typing.included generateSubst (by simp [typingClauses]))
          (pick [encode body, encode value, termRow typeCodes τ, listRow (ctx.map (termRow typeCodes)), pathRow π,
            eqsRow typeCodes acc, eqsRow typeCodes (E₂ ++ acc), eqsRow typeCodes (E₁ ++ (E₂ ++ acc))])
          (fun g inside => by
            simp only [generateSubst, List.mem_cons, List.not_mem_nil, or_false] at inside
            rcases inside with rfl | rfl
            · simpa [goalHolds, quint, nodeTerm, pick, generateRow, termRow_unknown, unknownRow, pathRow]
                using valueDerived
            · simpa [goalHolds, quint, nodeTerm, pick, generateRow, termRow_unknown, unknownRow, pathRow, listRow]
                using bodyDerived)
        rw [List.append_assoc]
        simpa [generateSubst, quint, pick, generateRow, encode] using clause
    | .collection kind elements rest, τ, ctx, π, _, .collection (E := E) generated, acc => by
        have inner := elements_complete typing generated acc
        have clause := derives_of_clause (R := R) (typing.included generateCollection (by simp [typingClauses]))
          (pick [.sym (collectionCode kind), encodeList elements, optionRow rest, termRow typeCodes τ,
            listRow (ctx.map (termRow typeCodes)), pathRow π, eqsRow typeCodes acc, eqsRow typeCodes (E ++ acc)])
          (fun g inside => by
            simp only [generateCollection, List.mem_cons, List.not_mem_nil, or_false] at inside
            subst inside
            simpa [goalHolds, sext, quint, nodeTerm, pick, elementsRow, termRow_unknown, unknownRow, numeral]
              using inner)
        simpa [generateCollection, quint, collectionRowTerm, nodeTerm, pick, generateRow, encode, eqsRow,
          termRow_collectionTerm, termRow_unknown, unknownRow] using clause
    | .collection kind elements rest, τ, ctx, π, _,
        .collectionConstructor (rule := rule) (elementType := element) (E := E) member shape generated, acc => by
        have inner := elements_complete typing generated acc
        have clause := derives_of_clause (R := R)
          (carrier_included typing member (bareCarrier_of_shape shape))
          (pick [encodeList elements, optionRow rest, termRow typeCodes τ, listRow (ctx.map (termRow typeCodes)),
            pathRow π, eqsRow typeCodes acc, eqsRow typeCodes (E ++ acc)]) (fun g inside => by
            simp only [generateCarrier, List.mem_cons, List.not_mem_nil, or_false] at inside
            subst inside
            simpa [goalHolds, sext, quint, pick, elementsRow, numeral] using inner)
        simpa [generateCarrier, quint, constRowTerm, pick, generateRow, encode, eqsRow, termRow_const] using clause
    | .apply _ arguments, τ, ctx, π, _, .constructor (rule := rule) (E := E) member notBare generated, acc => by
        obtain ⟨t, lowered⟩ := parametersTerm_of_arguments generated
        have inner := arguments_complete typing generated t lowered acc
        have clause := derives_of_clause (R := R)
          (constructor_included typing member (bareCarrier_none notBare) lowered)
          (pick [encodeList arguments, termRow typeCodes τ, listRow (ctx.map (termRow typeCodes)), pathRow π,
            eqsRow typeCodes acc, eqsRow typeCodes (E ++ acc)]) (fun g inside => by
            simp only [generateConstructor, List.mem_cons, List.not_mem_nil, or_false] at inside
            subst inside
            simpa [goalHolds, sext, quint, pick, argumentsRow, numeral, inst_ground (parametersTerm_ground lowered)]
              using inner)
        simpa [generateConstructor, quint, constRowTerm, pick, generateRow, encode, eqsRow, termRow_const]
          using clause

  theorem elements_complete (typing : TypingProgram language R program) :
      ∀ {elements : List Pattern} {τ : TypeTerm} {ctx : List TypeTerm} {π : List ℕ} {index : ℕ}
        {E : List (TypeTerm × TypeTerm)}, ElementsGenerate language elements τ ctx π index E →
      ∀ acc : List (TypeTerm × TypeTerm),
        Derives R program elementsRelation (elementsRow elements τ ctx π index acc) (eqsRow typeCodes (E ++ acc))
    | [], τ, ctx, π, index, _, .nil, acc => by
        have clause := derives_of_clause (R := R) (typing.included elementsNil (by simp [typingClauses]))
          (pick [termRow typeCodes τ, listRow (ctx.map (termRow typeCodes)), pathRow π, numeral index,
            eqsRow typeCodes acc]) (fun _ inside => absurd inside List.not_mem_nil)
        simpa [elementsNil, sext, quint, pick, elementsRow, encodeList] using clause
    | element :: rest, τ, ctx, π, index, _, .cons (E₁ := E₁) (E₂ := E₂) first second, acc => by
        have restDerived := elements_complete typing second acc
        have elementDerived := generate_complete typing first (E₂ ++ acc)
        have clause := derives_of_clause (R := R) (typing.included elementsCons (by simp [typingClauses]))
          (pick [encode element, encodeList rest, termRow typeCodes τ, listRow (ctx.map (termRow typeCodes)),
            pathRow π, numeral index, eqsRow typeCodes acc, eqsRow typeCodes (E₂ ++ acc),
            eqsRow typeCodes (E₁ ++ (E₂ ++ acc))]) (fun g inside => by
            simp only [elementsCons, List.mem_cons, List.not_mem_nil, or_false] at inside
            rcases inside with rfl | rfl
            · simpa [goalHolds, sext, quint, pick, elementsRow, numeral] using restDerived
            · simpa [goalHolds, quint, pick, generateRow, pathRow] using elementDerived)
        rw [List.append_assoc]
        simpa [elementsCons, sext, quint, pick, elementsRow, encodeList] using clause

  theorem arguments_complete (typing : TypingProgram language R program) :
      ∀ {arguments : List Pattern} {parameters : List TermParam} {ctx : List TypeTerm} {π : List ℕ} {index : ℕ}
        {E : List (TypeTerm × TypeTerm)}, ArgumentsGenerate language arguments parameters ctx π index E →
      ∀ (t : Tm), parametersTerm parameters = some t → ∀ acc : List (TypeTerm × TypeTerm),
        Derives R program argumentsRelation (argumentsRow arguments (groundRow t) ctx π index acc)
          (eqsRow typeCodes (E ++ acc))
    | [], [], ctx, π, index, _, .nil, t, lowered, acc => by
        simp only [parametersTerm, Option.some.injEq] at lowered
        subst lowered
        have clause := derives_of_clause (R := R) (typing.included argumentsNil (by simp [typingClauses]))
          (pick [listRow (ctx.map (termRow typeCodes)), pathRow π, numeral index, eqsRow typeCodes acc])
          (fun _ inside => absurd inside List.not_mem_nil)
        simpa [argumentsNil, sext, quint, pick, argumentsRow, encodeList, groundRow] using clause
    | argument :: rest, parameter :: parameters, ctx, π, index, _,
        .cons (expected := expected) (E₁ := E₁) (E₂ := E₂) representation expectedIs first second, t, lowered,
        acc => by
        simp only [parametersTerm, expectedIs, Option.bind_some, Option.map_eq_some_iff] at lowered
        obtain ⟨restTerm, restLowered, rfl⟩ := lowered
        have restDerived := arguments_complete typing second restTerm restLowered acc
        have argumentDerived := generate_complete typing first (E₂ ++ acc)
        rw [List.append_assoc]
        cases parameter with
        | simple name type =>
            have clause := derives_of_clause (R := R) (typing.included argumentsSimple (by simp [typingClauses]))
              (pick [encode argument, encodeList rest, termRow typeCodes (TypingUnknowns.typeTerm expected),
                groundRow restTerm, listRow (ctx.map (termRow typeCodes)), pathRow π, numeral index,
                eqsRow typeCodes acc, eqsRow typeCodes (E₂ ++ acc), eqsRow typeCodes (E₁ ++ (E₂ ++ acc))])
              (fun g inside => by
                simp only [argumentsSimple, argumentsCons, List.mem_cons, List.not_mem_nil, or_false] at inside
                rcases inside with rfl | rfl
                · simpa [goalHolds, sext, quint, pick, argumentsRow, numeral] using restDerived
                · simpa [goalHolds, quint, pick, generateRow, pathRow] using argumentDerived)
            simpa [argumentsSimple, argumentsCons, sext, quint, pick, argumentsRow, encodeList, groundRow, tagOf]
              using clause
        | abstractionNamed binderName bodyName type =>
            obtain ⟨body, rfl⟩ : ∃ body, argument = .lambda none body := by
              cases argument <;> simp_all [MatchesParameterRepresentation]
              case lambda binder body =>
                cases binder <;> simp_all
            have clause := derives_of_clause (R := R)
              (typing.included argumentsAbstraction (by simp [typingClauses]))
              (pick [encode body, encodeList rest, termRow typeCodes (TypingUnknowns.typeTerm expected),
                groundRow restTerm, listRow (ctx.map (termRow typeCodes)), pathRow π, numeral index,
                eqsRow typeCodes acc, eqsRow typeCodes (E₂ ++ acc), eqsRow typeCodes (E₁ ++ (E₂ ++ acc))])
              (fun g inside => by
                simp only [argumentsAbstraction, argumentsCons, List.mem_cons, List.not_mem_nil, or_false] at inside
                rcases inside with rfl | rfl
                · simpa [goalHolds, sext, quint, pick, argumentsRow, numeral] using restDerived
                · simpa [goalHolds, quint, pick, generateRow, pathRow, encode, optionRow] using argumentDerived)
            simpa [argumentsAbstraction, argumentsCons, sext, quint, pick, argumentsRow, encodeList, groundRow,
              tagOf, encode, optionRow] using clause
        | multiAbstractionNamed binderNames bodyName type =>
            obtain ⟨arity, body, rfl⟩ : ∃ arity body, argument = .multiLambda arity [] body := by
              cases argument <;> simp_all [MatchesParameterRepresentation]
              case multiLambda arity binders body =>
                cases binders <;> simp_all
            have clause := derives_of_clause (R := R)
              (typing.included argumentsMultiAbstraction (by simp [typingClauses]))
              (pick [encode body, encodeList rest, termRow typeCodes (TypingUnknowns.typeTerm expected),
                groundRow restTerm, listRow (ctx.map (termRow typeCodes)), pathRow π, numeral index,
                eqsRow typeCodes acc, eqsRow typeCodes (E₂ ++ acc), eqsRow typeCodes (E₁ ++ (E₂ ++ acc)),
                numeral arity])
              (fun g inside => by
                simp only [argumentsMultiAbstraction, argumentsCons, List.mem_cons, List.not_mem_nil, or_false]
                  at inside
                rcases inside with rfl | rfl
                · simpa [goalHolds, sext, quint, pick, argumentsRow, numeral] using restDerived
                · simpa [goalHolds, quint, pick, generateRow, pathRow, encode, namesRow] using argumentDerived)
            simpa [argumentsMultiAbstraction, argumentsCons, sext, quint, pick, argumentsRow, encodeList, groundRow,
              tagOf, encode, namesRow] using clause
end

end Generate

/-! ## Typing as clauses -/

/-- **The clause of typing**: a pattern has a type when the equations it generates are solved. -/
def typedClause : Clause :=
  { relation := typedRelation, input := appTerm (.var 0) (.var 1), output := unit,
    body := [.ask generateRelation (quint (.var 0) (.var 1) (symTerm 0) (symTerm 0) (symTerm 0)) (.var 2),
      .ask UnificationClauses.solveRelation (.var 2) unit] }

theorem typedClause_moded : DemandTransformation.Moded typedClause := DemandTransformation.moded_of_check (by decide)

/-- **A program with the clauses of typing, of unification and of telling unknowns apart.** -/
structure TypedProgram (language : LanguageDef) (R : Relations) (program : List Clause) : Prop where
  typing : TypingProgram language R program
  differ : DifferProgram R program
  unificationIncluded : ∀ c ∈ UnificationClauses.unificationClauses, c ∈ program
  unificationOnly : ∀ c ∈ program, UnificationClauses.solveRelation ≤ c.relation →
    c.relation ≤ UnificationClauses.substituteArgsRelation → c ∈ UnificationClauses.unificationClauses
  typed : typedClause ∈ program
  onlyTyped : ∀ c ∈ program, c.relation = typedRelation → c = typedClause

theorem TypedProgram.unification {language : LanguageDef} {R : Relations} {program : List Clause}
    (typed : TypedProgram language R program) : UnificationClauses.UnificationProgram typeCodes R program :=
  ⟨typed.unificationIncluded, typed.unificationOnly, differ_iff typed.differ⟩

/-- **The clauses of typing derive exactly the types a pattern has under some contexts.** -/
theorem typed_iff {language : LanguageDef} {R : Relations} {program : List Clause}
    (typed : TypedProgram language R program) (p : Pattern) (T : TypeExpr) :
    Derives R program typedRelation (.app (encode p) (termRow typeCodes (TypingUnknowns.typeTerm T))) (.sym 0) ↔
      ∃ (free : Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext) (bound : List TypeExpr),
        Mettapedia.GSLT.LanguageDef.WellSorted.HasType language free bound p T := by
  rw [← TypingUnknowns.typed_iff]
  constructor
  · rintro ⟨depth, derived⟩
    cases depth with
    | zero => exact derived.elim
    | succ depth =>
        obtain ⟨c, member, isTyped, θ, input, output, goals⟩ := derived
        obtain rfl := typed.onlyTyped c member isTyped
        simp only [typedClause, RootRewritesOnTheStep.inst_appTerm, DemandTransformation.inst_unknown,
          Expr.app.injEq] at input
        obtain ⟨pIs, TIs⟩ := input
        have first := goals _ List.mem_cons_self
        have second := goals _ (List.mem_cons_of_mem _ List.mem_cons_self)
        simp only [goalHolds, quint, RootRewritesOnTheStep.inst_appTerm, RootRewritesOnTheStep.inst_symTerm,
          DemandTransformation.inst_unknown, pIs, TIs] at first
        obtain ⟨E, generated, eqsIs⟩ := generate_sound typed.typing depth p _ [] [] [] _ first
        simp only [goalHolds, DemandTransformation.inst_unknown, unit, RootRewritesOnTheStep.inst_symTerm, eqsIs,
          List.append_nil] at second
        exact ⟨E, generated, (UnificationClauses.solve_iff typeCodes typed.unification E).mp ⟨depth, second⟩⟩
  · rintro ⟨E, generated, unifiable⟩
    have generatedDerived := generate_complete typed.typing generated []
    have solved := (UnificationClauses.solve_iff typeCodes typed.unification E).mpr unifiable
    rw [List.append_nil] at generatedDerived
    have clause := derives_of_clause (R := R) typed.typed
      (pick [encode p, termRow typeCodes (TypingUnknowns.typeTerm T), eqsRow typeCodes E]) (fun g inside => by
        simp only [typedClause, List.mem_cons, List.not_mem_nil, or_false] at inside
        rcases inside with rfl | rfl
        · simpa [goalHolds, quint, pick, generateRow, listRow, pathRow, eqsRow] using generatedDerived
        · simpa [goalHolds, unit, pick] using solved)
    simpa [typedClause, unit, pick] using clause

end Mettapedia.GSLT.Compilation.Uniform.TypingClauses

#print axioms Mettapedia.GSLT.Compilation.Uniform.TypingClauses.typed_iff
