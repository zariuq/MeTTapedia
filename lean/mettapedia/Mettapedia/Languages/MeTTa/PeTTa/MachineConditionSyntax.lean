import Mettapedia.Languages.MeTTa.PeTTa.MachineRuleTable
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Syntax

/-!
# Checked condition syntax of the complete production machine table

The reader keeps condition order, duplicate conditions and the complete Atom
payload of computations. Its readback law applies to every successful read,
including rules with open variables. All 185 pinned production rules are read;
the semantic theorem for the smaller ground table is not enlarged by this fact.

A binding condition also exposes its existing computed-condition interface,
with the source computation as its argument. This supplies syntax, not an
extensional interpretation of state-sensitive tests or an execution theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MachineConditionSyntax

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

inductive Unary where
  | take | read | absent | unique
  deriving DecidableEq, Repr

def Unary.name : Unary → String
  | .take => "take"
  | .read => "read"
  | .absent => "absent"
  | .unique => "unique"

def unaryOf (name : String) : Option Unary :=
  if name = "take" then some .take
  else if name = "read" then some .read
  else if name = "absent" then some .absent
  else if name = "unique" then some .unique
  else none

inductive Binary where
  | collect | bind
  deriving DecidableEq, Repr

def Binary.name : Binary → String
  | .collect => "collect"
  | .bind => "let"

def binaryOf (name : String) : Option Binary :=
  if name = "collect" then some .collect
  else if name = "let" then some .bind
  else none

inductive Condition where
  | bare (pattern : Atom)
  | unary (operation : Unary) (pattern : Atom)
  | binary (operation : Binary) (first second : Atom)
  deriving DecidableEq, Repr

def Condition.render : Condition → Atom
  | .bare pattern => pattern
  | .unary operation pattern => .expression [.symbol operation.name, pattern]
  | .binary operation first second => .expression [.symbol operation.name, first, second]

def readCondition : Atom → Option Condition
  | .expression (.symbol name :: arguments) =>
      match unaryOf name with
      | some operation => match arguments with
        | [pattern] => some (.unary operation pattern)
        | _ => none
      | none => match binaryOf name with
        | some operation => match arguments with
          | [first, second] => some (.binary operation first second)
          | _ => none
        | none => some (.bare (.expression (.symbol name :: arguments)))
  | pattern => some (.bare pattern)

theorem unaryOf_name {name : String} {operation : Unary}
    (read : unaryOf name = some operation) : operation.name = name := by
  unfold unaryOf at read
  split_ifs at read <;> cases read <;> simp_all [Unary.name]

theorem binaryOf_name {name : String} {operation : Binary}
    (read : binaryOf name = some operation) : operation.name = name := by
  unfold binaryOf at read
  split_ifs at read <;> cases read <;> simp_all [Binary.name]

/-- Reading and reprinting cannot erase a wrapper or change any payload. -/
theorem condition_readback {source : Atom} {condition : Condition}
    (read : readCondition source = some condition) : condition.render = source := by
  cases source with
  | var _ | symbol _ | grounded _ => cases read; rfl
  | expression items =>
      cases items with
      | nil => cases read; rfl
      | cons first rest =>
          cases first with
          | var _ | grounded _ | expression _ => cases read; rfl
          | symbol name =>
              simp only [readCondition] at read
              cases unary : unaryOf name with
              | some operation =>
                  simp only [unary] at read
                  cases rest with
                  | nil => cases read
                  | cons pattern more =>
                      cases more with
                      | cons _ _ => cases read
                      | nil =>
                          cases read
                          simp [Condition.render, unaryOf_name unary]
              | none =>
                  simp only [unary] at read
                  cases binary : binaryOf name with
                  | none => simp only [binary] at read; cases read; rfl
                  | some operation =>
                      simp only [binary] at read
                      cases rest with
                      | nil => cases read
                      | cons first more =>
                          cases more with
                          | nil => cases read
                          | cons second last =>
                              cases last with
                              | cons _ _ => cases read
                              | nil =>
                                  cases read
                                  simp [Condition.render, binaryOf_name binary]

def readConditions : List Atom → Option (List Condition)
  | [] => some []
  | first :: rest => do
      let condition ← readCondition first
      let conditions ← readConditions rest
      pure (condition :: conditions)

theorem conditions_readback {source : List Atom} {conditions : List Condition}
    (read : readConditions source = some conditions) : conditions.map Condition.render = source := by
  induction source generalizing conditions with
  | nil => cases read; rfl
  | cons first rest ih =>
      simp only [readConditions, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at read
      obtain ⟨condition, firstRead, conditions, restRead, rfl⟩ := read
      simp only [List.map_cons, condition_readback firstRead, ih restRead]

inductive Sources where
  | single (condition : Condition)
  | joint (conditions : List Condition)
  deriving DecidableEq, Repr

def Sources.conditions : Sources → List Condition
  | .single condition => [condition]
  | .joint conditions => conditions

def Sources.render : Sources → Atom
  | .single condition => condition.render
  | .joint conditions => .expression (.symbol "," :: conditions.map Condition.render)

def readSources : Atom → Option Sources
  | .expression (.symbol "," :: conditions) => (readConditions conditions).map .joint
  | source => (readCondition source).map .single

theorem sources_readback {source : Atom} {sources : Sources}
    (read : readSources source = some sources) : sources.render = source := by
  unfold readSources at read
  split at read
  · simp only [Option.map_eq_some_iff] at read
    obtain ⟨conditions, read, rfl⟩ := read
    simp only [Sources.render, conditions_readback read]
  · simp only [Option.map_eq_some_iff] at read
    obtain ⟨condition, read, rfl⟩ := read
    exact condition_readback read

structure Rule where
  key : Atom
  sources : Sources
  template : Atom
  deriving DecidableEq, Repr

def Rule.render (rule : Rule) : Atom :=
  .expression [.symbol "pm:rule!", rule.key, rule.sources.render, rule.template]

def readRule : Atom → Option Rule
  | .expression [.symbol "pm:rule!", key, sources, template] =>
      (readSources sources).map fun read => ⟨key, read, template⟩
  | _ => none

theorem rule_readback {source : Atom} {rule : Rule}
    (read : readRule source = some rule) : rule.render = source := by
  unfold readRule at read
  split at read
  · simp only [Option.map_eq_some_iff] at read
    obtain ⟨sources, read, rfl⟩ := read
    simp only [Rule.render, sources_readback read]
  · cases read

/-- Parsed equality is evidence of equality of the actual written forms. -/
theorem checked_source_injective {left right : Atom} {rule : Rule}
    (first : readRule left = some rule) (second : readRule right = some rule) : left = right :=
  (rule_readback first).symm.trans (rule_readback second)

/-- Ordered variable occurrences, including repetitions, survive the read. -/
theorem rule_variable_occurrences {source : Atom} {rule : Rule}
    (read : readRule source = some rule) :
    Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars rule.render =
      Mettapedia.Languages.ProcessCalculi.MORK.atomFreeVars source := by
  rw [rule_readback read]

def table : List Rule := MachineRuleTable.ruleForms.filterMap readRule

theorem table_length : table.length = 185 := by decide +kernel

/-- The filter above discards no rule of the pinned production table. -/
theorem every_production_rule_reads :
    ∀ source ∈ MachineRuleTable.ruleForms, (readRule source).isSome = true := by decide +kernel

theorem table_readback : table.map Rule.render = MachineRuleTable.ruleForms := by
  unfold table
  have allRead := every_production_rule_reads
  generalize MachineRuleTable.ruleForms = source at *
  induction source with
  | nil => rfl
  | cons first rest ih =>
      have firstRead := allRead first (by simp)
      have restRead : ∀ entry ∈ rest, (readRule entry).isSome = true :=
        fun entry inside => allRead entry (List.mem_cons_of_mem _ inside)
      cases read : readRule first with
      | none => simp [read] at firstRead
      | some rule =>
          simp only [List.filterMap_cons, read, List.map_cons, rule_readback read]
          exact congrArg (first :: ·) (ih restRead)

def conditions : List Condition := table.flatMap (·.sources.conditions)

/-- A computation is retained as syntax for the declared source evaluator.
No assumption of substitution invariance or purity is made here. -/
def Condition.computation? : Condition → Option
    (Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Condition Unit Atom)
  | .binary .bind pattern expression => some ⟨pattern, (), [expression]⟩
  | _ => none

theorem computation_count : (conditions.filterMap Condition.computation?).length = 58 := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.MachineConditionSyntax
