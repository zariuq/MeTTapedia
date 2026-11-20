import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Locality

/-!
# Rules with computed conditions: the syntax and two readings on the step

A **computed condition** asks that a pattern be the value of a function at some arguments:
`value := name(arguments)`. A **rule with conditions** (`RuleWithCondition`) is a rule of the syntax
together with a list of such conditions over a declared type `F` of function names. It is a device for
specifying rules, not an extension of the rule syntax: each reading below is a rule of `RuleSyntax`,
and its meaning is `RuleSyntax.step` itself, at the one frame of a substitution action.

A **tabulation** (`Tabulation`) gives one row former per function name: the row of the function's
table at some arguments and a value (`Tabulation.row`). The **call row** of a condition is that row at
the condition's arguments and value pattern (`callRow`).

## Two readings, both rules of the syntax

* **The table read** (`RuleWithCondition.tableRule`): the rule that also reads the call row of each
  condition. Over stored tables, a program of rules with conditions is a finite program
  (`tabled`).
* **The rule at points** (`RuleWithCondition.at`): the rule specialized at one row of each
  function's table, a *point*, by telling the call row equal to the point. Over an interpretation of
  the function names, whose graph is a set of rows, the program of all specializations at points of
  the graph (`specialized`) is a program of the syntax, infinite when a graph is: the graph is held
  by the program, not by the store. A firing chooses the point; the program's membership
  (`mem_specialized`) is where the function is evaluated.

The module `Tables` proves that the two readings have the same admitted firings and the same results
at every state that stores the points read. The module `Evaluation` adds the reading in which the
arguments are checked rather than told, which is how host code evaluates a condition.

## What is invariant and what composes

* Each reading changes one list of the rule and nothing else: the table read only the reads
  (`tableRule_take`, `tableRule_tell`, `tableRule_checks`, `tableRule_produce`, `tableRule_collect`),
  the specialization only the tells (`at_take`, `at_read`, `at_checks`, `at_produce`, `at_collect`).
* A rule without conditions is its own reading (`tableRule_of_nil`, `at_nil`).
* Both programs send a union of programs to the union of programs (`tabled_union`,
  `specialized_union`); the specialized program grows with the graph (`specialized_mono`), and the
  graph of interpretations with disjoint domains is the union of graphs (`graph_override`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions

open OneFrame (Terms frames ext)

universe uF uT uS

/-! ## Syntax -/

/-- **A computed condition** `value := name(arguments)`: the value pattern, the function's name and its
argument terms. -/
structure Condition (F : Type uF) (T : Type uT) where
  value : T
  name : F
  arguments : List T

/-- **A tabulation**: one row former per function name, giving the row of the function's table at some
arguments and a value. -/
structure Tabulation (F : Type uF) (T : Type uT) where
  row : F → List T → T → T

/-- **A rule with computed conditions**: a rule of the syntax and a list of conditions. -/
structure RuleWithCondition (F : Type uF) (T : Type uT) where
  rule : Rule (Terms T)
  conditions : List (Condition F T)

/-- **An interpretation** of the function names: a partial function on terms for each name. -/
abbrev Interpretation (F : Type uF) (T : Type uT) := F → List T → Option T

variable {F : Type uF} {T : Type uT} (R : Tabulation F T)

/-- **The call row of a condition**: the row of its function's table at its arguments and its value
pattern. -/
def callRow (c : Condition F T) : T := R.row c.name c.arguments c.value

/-- **The graph of an interpretation**, as rows of the tables. -/
def graph (I : Interpretation F T) : Set T :=
  {t | ∃ f args v, I f args = some v ∧ t = R.row f args v}

theorem mem_graph {I : Interpretation F T} {t : T} :
    t ∈ graph R I ↔ ∃ f args v, I f args = some v ∧ t = R.row f args v := Iff.rfl

theorem row_mem_graph {I : Interpretation F T} {f : F} {args : List T} {v : T}
    (defined : I f args = some v) : R.row f args v ∈ graph R I :=
  ⟨f, args, v, defined, rfl⟩

namespace RuleWithCondition

variable (ρ : RuleWithCondition F T)

/-- The call rows of the rule's conditions, in order. -/
def calls : List T := ρ.conditions.map (callRow R)

theorem calls_length : (ρ.calls R).length = ρ.conditions.length := List.length_map _

/-- **The table read**: the rule that also reads the call row of each condition. -/
def tableRule : Rule (Terms T) where
  locals := ρ.rule.locals
  body := { ρ.rule.body with read := ρ.rule.body.read ++ ρ.calls R }
  collect := ρ.rule.collect

/-- **The rule at points**: the rule that also tells the call row of each condition equal to the
corresponding point. -/
def «at» (points : List T) : Rule (Terms T) where
  locals := ρ.rule.locals
  body := { ρ.rule.body with tell := (ρ.calls R).zip points ++ ρ.rule.body.tell }
  collect := ρ.rule.collect

/-! ## What each reading changes -/

@[simp] theorem tableRule_take : (ρ.tableRule R).body.take = ρ.rule.body.take := rfl
@[simp] theorem tableRule_read : (ρ.tableRule R).body.read = ρ.rule.body.read ++ ρ.calls R := rfl
@[simp] theorem tableRule_tell : (ρ.tableRule R).body.tell = ρ.rule.body.tell := rfl
@[simp] theorem tableRule_checks : (ρ.tableRule R).body.checks = ρ.rule.body.checks := rfl
@[simp] theorem tableRule_produce : (ρ.tableRule R).body.produce = ρ.rule.body.produce := rfl
@[simp] theorem tableRule_collect : (ρ.tableRule R).collect = ρ.rule.collect := rfl

@[simp] theorem at_take (points : List T) : (ρ.at R points).body.take = ρ.rule.body.take := rfl
@[simp] theorem at_read (points : List T) : (ρ.at R points).body.read = ρ.rule.body.read := rfl
@[simp] theorem at_tell (points : List T) :
    (ρ.at R points).body.tell = (ρ.calls R).zip points ++ ρ.rule.body.tell := rfl
@[simp] theorem at_checks (points : List T) : (ρ.at R points).body.checks = ρ.rule.body.checks := rfl
@[simp] theorem at_produce (points : List T) : (ρ.at R points).body.produce = ρ.rule.body.produce := rfl
@[simp] theorem at_collect (points : List T) : (ρ.at R points).collect = ρ.rule.collect := rfl

/-- **A rule without conditions is its own table read.** -/
theorem tableRule_of_nil (none : ρ.conditions = []) : ρ.tableRule R = ρ.rule := by
  obtain ⟨⟨locals, ⟨take, read, tell, checks, produce⟩, collected⟩, conditions⟩ := ρ
  simp only at none
  subst none
  simp [tableRule, calls]

/-- **A rule without conditions is its own specialization.** -/
theorem at_nil (none : ρ.conditions = []) : ρ.at R [] = ρ.rule := by
  obtain ⟨⟨locals, ⟨take, read, tell, checks, produce⟩, collected⟩, conditions⟩ := ρ
  simp only at none
  subst none
  simp [«at», calls]

end RuleWithCondition

/-! ## Programs -/

/-- **The program of table reads**: the table read of every rule of a program of rules with
conditions. -/
def tabled (P : Set (RuleWithCondition F T)) : Program (Terms T) :=
  {r | ∃ ρ ∈ P, r = ρ.tableRule R}

/-- **The program at a graph**: every rule of the program specialized at points of the graph, one
point per condition. -/
def specialized (G : Set T) (P : Set (RuleWithCondition F T)) : Program (Terms T) :=
  {r | ∃ ρ ∈ P, ∃ points : List T, points.length = ρ.conditions.length ∧ (∀ g ∈ points, g ∈ G) ∧
    r = ρ.at R points}

variable {R}

theorem mem_tabled {P : Set (RuleWithCondition F T)} {r : Rule (Terms T)} :
    r ∈ tabled R P ↔ ∃ ρ ∈ P, r = ρ.tableRule R := Iff.rfl

/-- **Where the function is evaluated**: a specialization belongs to the program exactly when its
points are points of the graph. -/
theorem mem_specialized {G : Set T} {P : Set (RuleWithCondition F T)} {r : Rule (Terms T)} :
    r ∈ specialized R G P ↔ ∃ ρ ∈ P, ∃ points : List T, points.length = ρ.conditions.length ∧
      (∀ g ∈ points, g ∈ G) ∧ r = ρ.at R points := Iff.rfl

theorem tableRule_mem_tabled {P : Set (RuleWithCondition F T)} {ρ : RuleWithCondition F T}
    (member : ρ ∈ P) : ρ.tableRule R ∈ tabled R P := ⟨ρ, member, rfl⟩

theorem at_mem_specialized {G : Set T} {P : Set (RuleWithCondition F T)} {ρ : RuleWithCondition F T}
    (member : ρ ∈ P) {points : List T} (length : points.length = ρ.conditions.length)
    (onGraph : ∀ g ∈ points, g ∈ G) : ρ.at R points ∈ specialized R G P :=
  ⟨ρ, member, points, length, onGraph, rfl⟩

/-- **The table reads of a union are the union of the table reads.** -/
theorem tabled_union (P Q : Set (RuleWithCondition F T)) :
    tabled R (P ∪ Q) = tabled R P ∪ tabled R Q := by
  ext r
  constructor
  · rintro ⟨ρ, member | member, rfl⟩
    · exact .inl ⟨ρ, member, rfl⟩
    · exact .inr ⟨ρ, member, rfl⟩
  · rintro (⟨ρ, member, rfl⟩ | ⟨ρ, member, rfl⟩)
    · exact ⟨ρ, .inl member, rfl⟩
    · exact ⟨ρ, .inr member, rfl⟩

/-- **The specializations of a union are the union of the specializations.** -/
theorem specialized_union (G : Set T) (P Q : Set (RuleWithCondition F T)) :
    specialized R G (P ∪ Q) = specialized R G P ∪ specialized R G Q := by
  ext r
  constructor
  · rintro ⟨ρ, member | member, points, length, onGraph, rfl⟩
    · exact .inl ⟨ρ, member, points, length, onGraph, rfl⟩
    · exact .inr ⟨ρ, member, points, length, onGraph, rfl⟩
  · rintro (⟨ρ, member, points, length, onGraph, rfl⟩ | ⟨ρ, member, points, length, onGraph, rfl⟩)
    · exact ⟨ρ, .inl member, points, length, onGraph, rfl⟩
    · exact ⟨ρ, .inr member, points, length, onGraph, rfl⟩

/-- **A larger graph specializes to a larger program.** -/
theorem specialized_mono {G G' : Set T} (sub : G ⊆ G') (P : Set (RuleWithCondition F T)) :
    specialized R G P ⊆ specialized R G' P := by
  rintro r ⟨ρ, member, points, length, onGraph, rfl⟩
  exact ⟨ρ, member, points, length, fun g inside => sub (onGraph g inside), rfl⟩

/-- **Interpretations with disjoint domains compose**: the graph of `I` beside an interpretation `J`
defined where `I` is not is the union of the graphs. -/
theorem graph_override (I J : Interpretation F T)
    (apart : ∀ f args, I f args = none ∨ J f args = none) :
    graph R (fun f args => (I f args).or (J f args)) = graph R I ∪ graph R J := by
  ext t
  constructor
  · rintro ⟨f, args, v, defined, rfl⟩
    change (I f args).or (J f args) = some v at defined
    cases first : I f args with
    | some w =>
        rw [first, Option.some_or] at defined
        exact .inl ⟨f, args, v, by rw [first, defined], rfl⟩
    | none =>
        rw [first, Option.none_or] at defined
        exact .inr ⟨f, args, v, defined, rfl⟩
  · rintro (⟨f, args, v, defined, rfl⟩ | ⟨f, args, v, defined, rfl⟩)
    · refine ⟨f, args, v, ?_, rfl⟩
      show (I f args).or (J f args) = some v
      rw [defined, Option.some_or]
    · refine ⟨f, args, v, ?_, rfl⟩
      show (I f args).or (J f args) = some v
      rcases apart f args with none | none
      · rw [none, Option.none_or]
        exact defined
      · rw [defined] at none
        cases none

#print axioms RuleWithCondition.tableRule_of_nil
#print axioms RuleWithCondition.at_nil
#print axioms tabled_union
#print axioms specialized_union
#print axioms specialized_mono
#print axioms graph_override

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions
