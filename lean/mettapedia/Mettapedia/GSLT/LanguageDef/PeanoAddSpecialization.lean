import Mathlib.Data.List.Basic

/-!
# Certified specialization of a two-rule unary fold

This module isolates a small rule-machine optimization used by generated
coGSLT runtimes.  The recognizer accepts only the finite-Horn program

```text
R(zero, y, y).
R(succ(x), y, succ(z)) :- R(x, y, z).
```

up to vocabulary and rule order.  The compiled evaluator walks the first
coordinate and constructs the same result without recursive Horn search.
-/

namespace Mettapedia.GSLT.LanguageDef.PeanoAddSpecialization

inductive Term (Symbol : Type) where
  | symbol : Symbol → Term Symbol
  | free : Nat → Term Symbol
  | unary : Symbol → Term Symbol → Term Symbol
  | ternary : Symbol → Term Symbol → Term Symbol → Term Symbol → Term Symbol
deriving DecidableEq, Repr

structure Rule (Symbol : Type) where
  sourceIndex : Nat
  head : Term Symbol
  body : List (Term Symbol)
deriving DecidableEq, Repr

structure Plan (Symbol : Type) where
  relation : Symbol
  zero : Symbol
  successor : Symbol
  zeroStep : Nat
  successorStep : Nat
deriving DecidableEq, Repr

private def recognizeOrdered? [DecidableEq Symbol]
    (zeroRule successorRule : Rule Symbol) : Option (Plan Symbol) :=
  match zeroRule, successorRule with
  | ⟨zeroStep, .ternary relationZero
        (.symbol zero) (.free rightZero) (.free resultZero), []⟩,
    ⟨successorStep, .ternary relationSucc
        (.unary successorLeft (.free left))
        (.free rightSucc)
        (.unary successorResult (.free result)),
      [.ternary relationBody
        (.free bodyLeft) (.free bodyRight) (.free bodyResult)]⟩ =>
      if relationZero = relationSucc && relationSucc = relationBody &&
          successorLeft = successorResult && zero != successorLeft &&
          zeroStep != successorStep &&
          rightZero = resultZero && left = bodyLeft &&
          rightSucc = bodyRight && result = bodyResult then
        some ⟨relationZero, zero, successorLeft, zeroStep, successorStep⟩
      else none
  | _, _ => none

/-- Decidable, fail-closed recognizer; source order is irrelevant. -/
def recognize? [DecidableEq Symbol]
    (first second : Rule Symbol) : Option (Plan Symbol) :=
  (recognizeOrdered? first second).orElse fun _ =>
    recognizeOrdered? second first

/-- Structural source property certified by the zero-clause recognizer. -/
def IsZeroRule (rule : Rule Symbol) (plan : Plan Symbol) : Prop :=
  ∃ right,
    rule.sourceIndex = plan.zeroStep ∧
    rule.head = .ternary plan.relation
      (.symbol plan.zero) (.free right) (.free right) ∧
    rule.body = []

/-- Structural source property certified by the recursive-clause recognizer. -/
def IsSuccessorRule (rule : Rule Symbol) (plan : Plan Symbol) : Prop :=
  ∃ left right result,
    rule.sourceIndex = plan.successorStep ∧
    rule.head = .ternary plan.relation
      (.unary plan.successor (.free left)) (.free right)
      (.unary plan.successor (.free result)) ∧
    rule.body = [.ternary plan.relation
      (.free left) (.free right) (.free result)]

/-- The recognized pair may occur in either source order. -/
def RepresentsRulePair
    (first second : Rule Symbol) (plan : Plan Symbol) : Prop :=
  (IsZeroRule first plan ∧ IsSuccessorRule second plan) ∨
  (IsSuccessorRule first plan ∧ IsZeroRule second plan)

private theorem recognizeOrdered?_sound [DecidableEq Symbol]
    (zeroRule successorRule : Rule Symbol) (plan : Plan Symbol)
    (accepted : recognizeOrdered? zeroRule successorRule = some plan) :
    IsZeroRule zeroRule plan ∧ IsSuccessorRule successorRule plan := by
  simp only [recognizeOrdered?] at accepted
  split at accepted <;> try contradiction
  rename_i zeroStep relationZero zero rightZero resultZero successorStep
    relationSucc successorLeft left rightSucc successorResult result
    relationBody bodyLeft bodyRight bodyResult
  split at accepted <;> try contradiction
  rename_i valid
  simp only [Option.some.injEq] at accepted
  subst plan
  simp_all [IsZeroRule, IsSuccessorRule]

/-- Recognizer acceptance is an independently stated structural certificate. -/
theorem recognize?_sound [DecidableEq Symbol]
    (first second : Rule Symbol) (plan : Plan Symbol)
    (accepted : recognize? first second = some plan) :
    RepresentsRulePair first second plan := by
  unfold recognize? at accepted
  cases firstResult : recognizeOrdered? first second with
  | none =>
      simp only [firstResult, Option.orElse_none] at accepted
      exact Or.inr
        (recognizeOrdered?_sound second first plan accepted).symm
  | some candidate =>
      simp only [firstResult, Option.orElse_some,
        Option.some.injEq] at accepted
      subst candidate
      exact Or.inl
        (recognizeOrdered?_sound first second plan firstResult)

/-- Declarative meaning of the admitted pair of rules. -/
inductive AddRel (zero successor : Symbol) :
    Term Symbol → Term Symbol → Term Symbol → Prop where
  | zero (right : Term Symbol) :
      AddRel zero successor (.symbol zero) right right
  | successor {left right result : Term Symbol} :
      AddRel zero successor left right result →
      AddRel zero successor
        (.unary successor left) right
        (.unary successor result)

def numeralSize? [DecidableEq Symbol]
    (zero successor : Symbol) : Term Symbol → Option Nat
  | .symbol candidate => if candidate = zero then some 0 else none
  | .unary candidate argument =>
      if candidate = successor then
        (numeralSize? zero successor argument).map Nat.succ
      else none
  | _ => none

def wrap (successor : Symbol) : Nat → Term Symbol → Term Symbol
  | 0, right => right
  | n + 1, right => .unary successor (wrap successor n right)

/-- Total compiled evaluator on the recognizable input fragment. -/
def evaluate? [DecidableEq Symbol]
    (plan : Plan Symbol) (left right : Term Symbol) : Option (Term Symbol) :=
  (numeralSize? plan.zero plan.successor left).map fun count =>
    wrap plan.successor count right

theorem numeralSize?_eq_some_iff [DecidableEq Symbol]
    (zero successor : Symbol) (left : Term Symbol) (count : Nat) :
    numeralSize? zero successor left = some count ↔
      left = wrap successor count (.symbol zero) := by
  constructor
  · intro accepted
    induction left generalizing count with
    | symbol candidate =>
        simp only [numeralSize?] at accepted
        split at accepted
        · rename_i equal
          simp only [Option.some.injEq] at accepted
          subst count
          subst candidate
          rfl
        · simp at accepted
    | free index => simp [numeralSize?] at accepted
    | unary candidate argument ih =>
        simp only [numeralSize?] at accepted
        split at accepted
        · rename_i equal
          subst candidate
          cases recursive : numeralSize? zero successor argument with
          | none => simp [recursive] at accepted
          | some inner =>
              simp only [recursive, Option.map_some,
                Option.some.injEq] at accepted
              subst count
              simp only [wrap]
              rw [ih inner recursive]
        · simp at accepted
    | ternary candidate first second third ihFirst ihSecond ihThird =>
        simp [numeralSize?] at accepted
  · intro shape
    subst left
    induction count with
    | zero => simp [numeralSize?, wrap]
    | succ count ih =>
        simp [numeralSize?, wrap, ih]

theorem addRel_iff_wrap (zero successor : Symbol)
    (left right result : Term Symbol) :
    AddRel zero successor left right result ↔
      ∃ count, left = wrap successor count (.symbol zero) ∧
        result = wrap successor count right := by
  constructor
  · intro derivation
    induction derivation with
    | zero right => exact ⟨0, rfl, rfl⟩
    | successor derivation ih =>
        obtain ⟨count, leftShape, resultShape⟩ := ih
        exact ⟨count + 1, by simp [wrap, leftShape], by simp [wrap, resultShape]⟩
  · rintro ⟨count, rfl, rfl⟩
    induction count with
    | zero => exact .zero right
    | succ count ih =>
        simpa [wrap] using AddRel.successor ih

/-- The compiled evaluator is sound and complete for the admitted fold. -/
theorem evaluate?_eq_some_iff [DecidableEq Symbol]
    (plan : Plan Symbol) (left right result : Term Symbol) :
    evaluate? plan left right = some result ↔
      AddRel plan.zero plan.successor left right result := by
  simp only [evaluate?, Option.map_eq_some_iff]
  constructor
  · rintro ⟨count, countEq, rfl⟩
    apply (addRel_iff_wrap plan.zero plan.successor _ _ _).2
    exact ⟨count,
      (numeralSize?_eq_some_iff _ _ _ _).1 countEq, rfl⟩
  · intro derivation
    obtain ⟨count, leftShape, resultShape⟩ :=
      (addRel_iff_wrap plan.zero plan.successor _ _ _).1 derivation
    exact ⟨count,
      (numeralSize?_eq_some_iff _ _ _ _).2 leftShape, resultShape.symm⟩

def sourceRuleMatches [DecidableEq Symbol]
    (plan : Plan Symbol) (left : Term Symbol) : Nat :=
  match numeralSize? plan.zero plan.successor left with
  | none => 0
  | some count => count + 1

def sourceRuleAttempts [DecidableEq Symbol]
    (plan : Plan Symbol) (left : Term Symbol) : Nat :=
  match numeralSize? plan.zero plan.successor left with
  | none => 0
  | some count =>
      if plan.zeroStep < plan.successorStep then 2 * count + 1
      else count + 2

def compiledPhysicalDispatches [DecidableEq Symbol]
    (plan : Plan Symbol) (left : Term Symbol) : Nat :=
  if (numeralSize? plan.zero plan.successor left).isSome then 1 else 0

/-- One physical macro dispatch never exceeds the successful source clauses. -/
theorem compiledPhysicalDispatches_le_sourceRuleMatches [DecidableEq Symbol]
    (plan : Plan Symbol) (left : Term Symbol) :
    compiledPhysicalDispatches plan left ≤ sourceRuleMatches plan left := by
  simp only [compiledPhysicalDispatches, sourceRuleMatches]
  cases numeralSize? plan.zero plan.successor left <;> simp

/-- Source-order failures are charged as attempts, never as matches. -/
theorem sourceRuleMatches_le_sourceRuleAttempts [DecidableEq Symbol]
    (plan : Plan Symbol) (left : Term Symbol) :
    sourceRuleMatches plan left ≤ sourceRuleAttempts plan left := by
  simp only [sourceRuleMatches, sourceRuleAttempts]
  cases numeralSize? plan.zero plan.successor left with
  | none => simp
  | some count =>
      by_cases ordered : plan.zeroStep < plan.successorStep
      · simp [ordered]
        omega
      · simp [ordered]

/-- The compiled fold reduces physical dispatch without hiding source cost. -/
theorem compiledCostRefinement [DecidableEq Symbol]
    (plan : Plan Symbol) (left : Term Symbol) :
    compiledPhysicalDispatches plan left ≤ sourceRuleMatches plan left ∧
      sourceRuleMatches plan left ≤ sourceRuleAttempts plan left :=
  ⟨compiledPhysicalDispatches_le_sourceRuleMatches plan left,
   sourceRuleMatches_le_sourceRuleAttempts plan left⟩

/-! ## Independent witnesses and fail-closed mutations -/

private def rulePair (relation zero successor : String)
    (zeroStep successorStep : Nat) :
    Rule String × Rule String :=
  ( { sourceIndex := zeroStep
      head := .ternary relation
        (.symbol zero) (.free 1) (.free 1)
      body := [] },
    { sourceIndex := successorStep
      head := .ternary relation
        (.unary successor (.free 0)) (.free 1)
        (.unary successor (.free 2))
      body := [.ternary relation
        (.free 0) (.free 1) (.free 2)] } )

private def traceRules :=
  rulePair "TraceNatAdd" "TraceZero" "TraceSucc" 41 42
private def zeroAbtRules :=
  rulePair "qabt-nat-add" "q-zero" "q-succ" 8 7
private def lfRules :=
  rulePair "NatAdd" "Zero" "Succ" 73 74

example : recognize? traceRules.1 traceRules.2 =
    some ⟨"TraceNatAdd", "TraceZero", "TraceSucc", 41, 42⟩ := by decide

example : recognize? zeroAbtRules.2 zeroAbtRules.1 =
    some ⟨"qabt-nat-add", "q-zero", "q-succ", 8, 7⟩ := by decide

example : recognize? lfRules.1 lfRules.2 =
    some ⟨"NatAdd", "Zero", "Succ", 73, 74⟩ := by decide

private def mutatedSuccessorRule : Rule String :=
  { sourceIndex := 42
    head := .ternary "TraceNatAdd"
      (.unary "TraceSucc" (.free 0)) (.free 1)
      (.unary "TraceSucc" (.free 2))
    body := [.ternary "TraceNatAdd"
      (.free 0) (.free 99) (.free 2)] }

example : recognize? traceRules.1 mutatedSuccessorRule = none := by decide

private def aliasedSuccessorRule : Rule String :=
  { mutatedSuccessorRule with
    sourceIndex := 41
    body := [.ternary "TraceNatAdd"
      (.free 0) (.free 1) (.free 2)] }

example : recognize? traceRules.1 aliasedSuccessorRule = none := by decide

example : sourceRuleAttempts
    ⟨"TraceNatAdd", "TraceZero", "TraceSucc", 41, 42⟩
    (wrap "TraceSucc" 2 (.symbol "TraceZero")) = 5 := by decide

example : sourceRuleAttempts
    ⟨"qabt-nat-add", "q-zero", "q-succ", 8, 7⟩
    (wrap "q-succ" 3 (.symbol "q-zero")) = 5 := by decide

end Mettapedia.GSLT.LanguageDef.PeanoAddSpecialization
