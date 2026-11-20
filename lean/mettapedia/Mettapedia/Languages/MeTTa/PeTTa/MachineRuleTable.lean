import Mettapedia.Languages.MeTTa.PeTTa.ProgramQuotation
import Mettapedia.Languages.MeTTa.PeTTa.LibTransformDrive
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.FirstOrderEq

/-!
# The rule table of the machine of transform rules, read from its library

The machine of transform rules is PeTTa's evaluator written as a table of `transform` rules
(CeTTa, `lib/petta/petta_machine.metta`). Each `!(pm:rule! KEY SOURCES TEMPLATE)` of the library
enters one rule, and the driver fires a rule as `(transform &pm SOURCES TEMPLATE &pm)`. This
module reads the table from the library's own text and states what its firings are on the
first-order step.

* `source`: the library's text, pinned by its digest (the copy under `metta/fixtures`).
* `ruleForms`, `ruleForms_length`: its 185 rule forms.
* `madeRuleOf`, `table`, `table_length`: the 137 rules whose conditions are takes, reads and
  absences of one pattern, the absences last, as rules of the transform library's model
  (`MadeRule`). `unread_length`: the other 48 are not read: 42 have a computed condition (a
  `let` conjunct), 4 enter the one clause that meets a call (a `unique` conjunct) and 2 gather
  the clauses that meet it (a `collect` conjunct).
* `table_closed`: every variable of a table rule's template occurs in one of its patterns.
* `calls_are_one_run`: **on a ground store, calls of table rules in any order a driver chooses
  are one run of `firstOrder atomAction label`.** Each firing of the run is a table rule with
  fresh variables, its patterns matched by the step's own equations (`OfProgram`), and under
  every solution of the knowledge at the end the rows are the store the calls leave.
* `program`, `opens_of_numbered`, `calls_are_a_path_of_the_table`: **the same calls are a path
  of `RuleSyntax.step` for the table as a program.** Each move is an admitted firing that opens
  a rule of the table freshly: the rule's own unknowns go to the unknowns of the firing's
  number, which the state does not mention, and its patterns are matched by the solvability
  of the firing's information.
* `offer`, `offer_is_a_schedule`, `offer_is_one_run`, `offer_is_a_path_of_the_table`: the
  driver's offer, the given rules in order until one fires, is such a schedule.
* `quiescent_iff_no_call_fires`: the step admits no table rule exactly when no call of a table
  rule fires.

Scope: a ground store. A store with a row that holds an unknown is outside: the clause row of
an equation with a parameter (`Controls.clause_row_is_not_ground`) and the states of a logic
program. The 48 rules with a computed condition, a `unique` or a `collect` are outside.

Examples: `Controls.literal_returns` (the table's first rule takes the state that evaluates a
literal and makes the state that returns it) and the negative `Controls.returned_is_left` (it
does not fire on the state that returns).

The pin refuses a changed text: when the library changes, the copy and the digest are replaced
together and the counts below are checked again by the kernel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MachineRuleTable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (isGroundAtom)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
  (Selection RuleInstance Configuration SubstitutionAction EquationStore)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison
  (atomAction)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
  (Firing Executable follow firstOrder executable_iff_run follow_eq_last)
open Mettapedia.Languages.MeTTa.PeTTa.ProgramQuotation
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.OneFrame
  (Terms frames ext embed toFirstOrder OpensProgram firstOrderOn keeping firstOrder_eq)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.StepSpan
  (Succ)
open LibTransform
open LibTransformStep

/-! ## The library and its rule forms -/

/-- The machine library, as text with its digest. -/
def source : QuotedProgram := petta_source_file%
  "../../../../../../metta/fixtures/petta_machine.metta"
  sha256 "3e1024d2b70f0670309174ad9500af6cb9226b008e6c52298b8e9ccb709043f4"

/-- A form that enters a rule in the table. -/
def isRuleForm : Atom → Bool
  | .expression (.symbol "pm:rule!" :: _) => true
  | _ => false

/-- The rule forms of the library, in table order. -/
def ruleForms : List Atom := source.program.initializers.filter isRuleForm

/-! ## Reading a rule -/

/-- A condition of a rule's sources: a pattern that is read or taken, the absence of one
pattern, or any other condition. -/
inductive Condition where
  | pattern (mode : Mode) (pattern : Atom)
  | absent (pattern : Atom)
  | other

/-- A comma expression: several patterns matched jointly. -/
def joint : Atom → Bool
  | .expression (.symbol "," :: _) => true
  | _ => false

/-- A condition with exactly one pattern that is not a comma expression. -/
def one (found : Atom → Condition) : List Atom → Condition
  | [pattern] => if joint pattern then .other else found pattern
  | _ => .other

/-- What a written condition is. A pattern written bare is a read. -/
def conditionOf : Atom → Condition
  | .expression (.symbol head :: arguments) =>
      if head = "take" then one (.pattern .take) arguments
      else if head = "read" then one (.pattern .read) arguments
      else if head = "absent" then one .absent arguments
      else if head ∈ ["let", "unique", "collect", "all", "once", ","] then .other
      else .pattern .read (.expression (.symbol head :: arguments))
  | pattern => .pattern .read pattern

/-- The conditions of written sources. -/
def conjuncts : Atom → List Atom
  | .expression (.symbol "," :: parts) => parts
  | single => [single]

/-- Conditions that are all absences. -/
def absentsOnly : List Condition → Option (List Atom)
  | [] => some []
  | .absent pattern :: rest => (absentsOnly rest).map (pattern :: ·)
  | _ => none

/-- Patterns, then absences: the footprint in written order and the absent patterns. -/
def kernelThenAbsents : List Condition → Option (Footprint × List Atom)
  | .pattern mode pattern :: rest =>
      (kernelThenAbsents rest).map fun found => ((mode, pattern) :: found.1, found.2)
  | rest => (absentsOnly rest).map fun absents => ([], absents)

/-- A rule form whose conditions are takes, reads and absences of one pattern, the absences
last, as a rule of the transform library's model. Any other form is not read. -/
def madeRuleOf : Atom → Option MadeRule
  | .expression [.symbol "pm:rule!", _, sources, template] =>
      (kernelThenAbsents ((conjuncts sources).map conditionOf)).map fun found =>
        ⟨found.1, found.2, template⟩
  | _ => none

/-- **The table**: the rules read from the library, in table order. -/
def table : List MadeRule := ruleForms.filterMap madeRuleOf

/-- The library enters 185 rules. -/
theorem ruleForms_length : ruleForms.length = 185 := by decide +kernel

/-- 137 of them are read. -/
theorem table_length : table.length = 137 := by decide +kernel

/-- The other 48 are not: each has a computed condition, a `unique` or a `collect`. -/
theorem unread_length : (ruleForms.filter fun form => (madeRuleOf form).isNone).length = 48 := by
  decide +kernel

instance (pats : Footprint) (template : Atom) : Decidable (Closed pats template) := by
  unfold Closed
  infer_instance

/-- Every variable of a table rule's template occurs in one of the rule's patterns. -/
theorem table_closed : ∀ r ∈ table, Closed r.pats r.template := by decide +kernel

/-! ## Calls of table rules are one run of the step -/

variable {O : Type} [DecidableEq O]

/-- **Calls of table rules, in any order, are one run of the first-order step.** On a ground
store represented by `rows`, with a supply of fresh occurrences, the calls of `schedule` leave
a store that the run's last configuration knows: under every solution of its knowledge the
labels of its rows are that store's atoms. Every firing of the run is a rule of the table
with fresh variables and no predicate query. -/
theorem calls_are_one_run {label : O → Atom}
    (supply : ∀ (X : Finset O) (t : Atom), ∃ o, o ∉ X ∧ label o = t)
    {rows : List O} {s : Store} (rep : Represents label rows s)
    (ground : ∀ a ∈ s, isGroundAtom a = true)
    (schedule : List MadeRule) (fromTable : ∀ r ∈ schedule, r ∈ table) :
    ∃ (run : (firstOrder atomAction label).Run (⟨[], rows.toFinset⟩ : Configuration Atom O))
      (rows' : List O) (n : Nat),
      OfProgram table (run.word.map Sigma.snd) ∧
      run.last.present = rows'.toFinset ∧
      Knows label run.last.equations n rows' (pass schedule s) := by
  obtain ⟨word, rows', K', n', exec, ends, knows', ofTable, _⟩ :=
    pass_executable supply schedule table
      (fun r member => ⟨fromTable r member, table_closed r (fromTable r member)⟩)
      (knows_of_represents rep ground)
  obtain ⟨run, isWord, _⟩ := (executable_iff_run atomAction label _ word).mp exec
  have last : run.last = ⟨K', rows'.toFinset⟩ := by
    rw [← follow_eq_last atomAction label run, isWord]
    exact ends
  refine ⟨run, rows', n', ?_, by rw [last], by rw [last]; exact knows'⟩
  rw [isWord]
  exact ofTable

/-- **The step admits no table rule exactly when no call of a table rule fires.** -/
theorem quiescent_iff_no_call_fires {label : O → Atom}
    (supply : ∀ (X : Finset O) (t : Atom), ∃ o, o ∉ X ∧ label o = t)
    {K : EquationStore Atom} {n : Nat} {rows : List O} {s : Store}
    (knows : Knows label K n rows s) :
    Quiescent label table K n rows ↔ Idle table s :=
  quiescent_iff_idle supply knows table table_closed

/-! ## The same calls in the step of the table's program -/

/-- A rule of the rule-syntax step over atoms at the one frame. -/
abbrev Schema := Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Rule (Terms Atom)

/-- A program of the rule-syntax step over atoms at the one frame. -/
abbrev SchemaProgram := Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Program (Terms Atom)

/-- **The table as a program of the rule-syntax step** at the one frame of atoms: each table
rule as written, with its own unknowns and no census pattern. -/
def program : SchemaProgram :=
  {r | ∃ m ∈ table, r = ⟨PUnit.unit, madeRule m.pats m.absents m.template, []⟩}

omit [DecidableEq O] in
/-- **A rule written with the variables of a fresh number is a fresh opening of the rule.**
At a configuration whose knowledge and present labels mention only smaller numbers, the
first-order firing of `rule` tagged `n` is the image of a firing of the program's step that
opens `rule` by the tagging, and that opening is fresh. -/
theorem opens_of_numbered {label : O → Atom} {P : SchemaProgram}
    {C : Configuration Atom O}
    {f : Firing Atom Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst O}
    {rule : RuleInstance Atom} {n : Nat}
    (member : (⟨PUnit.unit, rule, []⟩ : Schema) ∈ P)
    (isRule : f.rule = rule.map (rename n)) (noQueries : f.queries = [])
    (knowledgeBelow : ∀ e ∈ C.equations, TagsBelow n e.1 ∧ TagsBelow n e.2)
    (labelsBelow : ∀ o ∈ C.present, TagsBelow n (label o)) :
    OpensProgram atomAction label P C f := by
  refine ⟨⟨⟨PUnit.unit, rule, []⟩, member, PUnit.unit, tagging n, f.selection, []⟩, ?_, rfl, ?_⟩
  · intro b g h
    refine ⟨withLocal g n (total h), fun t mentioned => ?_, fun t _ => ?_⟩
    · show SubstitutionAlgebra.subst (withLocal g n (total h))
        (SubstitutionAlgebra.subst SubstitutionAlgebra.empty t) = SubstitutionAlgebra.subst g t
      rw [SubstitutionAlgebra.subst_empty]
      apply subst_withLocal_of_tagsBelow
      rcases mentioned with inside | inside | ⟨o, present, rfl⟩
      · obtain ⟨e, inKnowledge, rfl⟩ := List.mem_map.mp inside
        exact (knowledgeBelow e inKnowledge).1
      · obtain ⟨e, inKnowledge, rfl⟩ := List.mem_map.mp inside
        exact (knowledgeBelow e inKnowledge).2
      · exact labelsBelow o present
    · show SubstitutionAlgebra.subst (withLocal g n (total h))
        (SubstitutionAlgebra.subst (tagging n) t) = SubstitutionAlgebra.subst h t
      rw [subst_tagging, subst_withLocal_total_rename]
  · obtain ⟨written, queries, selection⟩ := f
    simp only at isRule noQueries
    subst isRule noQueries
    have same : SubstitutionAlgebra.subst (tagging n) = rename n := funext (subst_tagging n)
    simp only [toFirstOrder, Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Firing.opened,
      Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Firing.collectOpened, List.map_nil, List.zip_nil_left,
      Firing.mk.injEq, and_true]
    show RuleInstance.map (SubstitutionAlgebra.subst (tagging n)) rule = _
    rw [same]

/-- A numbered executable word of table rules is a path of the label-keeping step of the
table's program. -/
theorem path_of_numbered {label : O → Atom} :
    ∀ (word : List (Firing Atom Mettapedia.Languages.MeTTa.SubstitutionAlgebra.Subst O))
      {C : Configuration Atom O},
      Executable atomAction label C word → Numbered label (InProgram table) C word →
      Relation.ReflTransGen (Succ (keeping atomAction program))
        (embed label C) (embed label (follow label C word))
  | [], _, _, _ => Relation.ReflTransGen.refl
  | f :: rest, C, exec, numbered => by
      obtain ⟨valid, later⟩ := exec
      obtain ⟨⟨rule, n, ⟨r, inTable, isR⟩, isRule, noQueries, knowledgeBelow, labelsBelow⟩,
        numberedLater⟩ := numbered
      have opens : OpensProgram atomAction label program C f :=
        opens_of_numbered (member := ⟨r, inTable, by rw [isR]⟩) isRule noQueries knowledgeBelow
          labelsBelow
      have first : Succ (firstOrderOn atomAction label program) C (f.result label C) :=
        ⟨f, ⟨valid, opens⟩, rfl⟩
      exact Relation.ReflTransGen.head ((firstOrder_eq C (f.result label C)).mp first)
        (path_of_numbered rest later numberedLater)

/-- **Calls of table rules are a path of the step of the table's program.** On a ground store
represented by `rows`, the calls of `schedule` are a path of `RuleSyntax.step` at the one frame
of atoms for the program `program`: each move is an admitted firing that opens a rule of the
table freshly, its patterns matched by the solvability of the firing's information. The
moves are label-keeping (`keeping`): each made identity already carries its made row. The
last state knows the store the calls leave. -/
theorem calls_are_a_path_of_the_table {label : O → Atom}
    (supply : ∀ (X : Finset O) (t : Atom), ∃ o, o ∉ X ∧ label o = t)
    {rows : List O} {s : Store} (rep : Represents label rows s)
    (ground : ∀ a ∈ s, isGroundAtom a = true)
    (schedule : List MadeRule) (fromTable : ∀ r ∈ schedule, r ∈ table) :
    ∃ (K' : EquationStore Atom) (rows' : List O) (n : Nat),
      Relation.ReflTransGen (Succ (keeping atomAction program))
        (embed label ⟨[], rows.toFinset⟩) (embed label ⟨K', rows'.toFinset⟩) ∧
      Knows label K' n rows' (pass schedule s) := by
  obtain ⟨word, rows', K', n', exec, ends, knows', _, numbered⟩ :=
    pass_executable supply schedule table
      (fun r member => ⟨fromTable r member, table_closed r (fromTable r member)⟩)
      (knows_of_represents rep ground)
  refine ⟨K', rows', n', ?_, knows'⟩
  rw [← ends]
  exact path_of_numbered word exec numbered

/-! ## The driver's offer -/

/-- The driver's offer: the calls of the given rules in order, until one fires. -/
def offer : List MadeRule → Store → Store
  | [], s => s
  | r :: rest, s =>
      if ((transformInto r.sources r.template s).drain).1 = [] then offer rest s
      else ((transformInto r.sources r.template s).drain).2

/-- An offer is the call of at most one of its rules. -/
theorem offer_is_a_schedule : ∀ (rules : List MadeRule) (s : Store),
    ∃ schedule : List MadeRule, (∀ r ∈ schedule, r ∈ rules) ∧ offer rules s = pass schedule s
  | [], s => ⟨[], fun _ member => by simp at member, rfl⟩
  | r :: rest, s => by
      by_cases quiet : ((transformInto r.sources r.template s).drain).1 = []
      · obtain ⟨schedule, inside, same⟩ := offer_is_a_schedule rest s
        refine ⟨schedule, fun x member => List.mem_cons_of_mem _ (inside x member), ?_⟩
        simp only [offer, quiet, if_true]
        exact same
      · refine ⟨[r], fun x member => by
          rw [List.mem_singleton] at member
          subst member
          exact List.mem_cons_self .., ?_⟩
        simp only [offer, quiet, if_false, pass, List.foldl_cons, List.foldl_nil]

/-- **An offer of table rules is one run of the first-order step.** -/
theorem offer_is_one_run {label : O → Atom}
    (supply : ∀ (X : Finset O) (t : Atom), ∃ o, o ∉ X ∧ label o = t)
    {rows : List O} {s : Store} (rep : Represents label rows s)
    (ground : ∀ a ∈ s, isGroundAtom a = true)
    (rules : List MadeRule) (fromTable : ∀ r ∈ rules, r ∈ table) :
    ∃ (run : (firstOrder atomAction label).Run (⟨[], rows.toFinset⟩ : Configuration Atom O))
      (rows' : List O) (n : Nat),
      OfProgram table (run.word.map Sigma.snd) ∧
      run.last.present = rows'.toFinset ∧
      Knows label run.last.equations n rows' (offer rules s) := by
  obtain ⟨schedule, inside, same⟩ := offer_is_a_schedule rules s
  rw [same]
  exact calls_are_one_run supply rep ground schedule
    (fun r member => fromTable r (inside r member))

/-- **An offer of table rules is a path of the step of the table's program.** -/
theorem offer_is_a_path_of_the_table {label : O → Atom}
    (supply : ∀ (X : Finset O) (t : Atom), ∃ o, o ∉ X ∧ label o = t)
    {rows : List O} {s : Store} (rep : Represents label rows s)
    (ground : ∀ a ∈ s, isGroundAtom a = true)
    (rules : List MadeRule) (fromTable : ∀ r ∈ rules, r ∈ table) :
    ∃ (K' : EquationStore Atom) (rows' : List O) (n : Nat),
      Relation.ReflTransGen (Succ (keeping atomAction program))
        (embed label ⟨[], rows.toFinset⟩) (embed label ⟨K', rows'.toFinset⟩) ∧
      Knows label K' n rows' (offer rules s) := by
  obtain ⟨schedule, inside, same⟩ := offer_is_a_schedule rules s
  rw [same]
  exact calls_are_a_path_of_the_table supply rep ground schedule
    (fun r member => fromTable r (inside r member))

namespace Controls

/-- A state of the machine with the given control, the halting continuation, depth `0` and no
alternatives. -/
def state (control : Atom) : Atom :=
  .expression [.symbol "pm:state", control, .symbol "pm:halt", .grounded (.int 0), .expression []]

/-- Evaluate the literal `7`. -/
def literal : Atom :=
  .expression [.symbol "pm:eval", .expression [.symbol "pm:lit", .grounded (.int 7)]]

/-- Return `7`. -/
def returned : Atom := .expression [.symbol "pm:ret", .grounded (.int 7)]

/-- The rule for a literal, as the library writes it. -/
def literalRule : MadeRule :=
  ⟨[(.take, .expression [.symbol "pm:state",
      .expression [.symbol "pm:eval", .expression [.symbol "pm:lit", .var "v"]],
      .var "k", .var "d", .var "r"])], [],
    .expression [.symbol "pm:state", .expression [.symbol "pm:ret", .var "v"],
      .var "k", .var "d", .var "r"]⟩

/-- It is the table's first rule. -/
theorem literalRule_first : table.head? = some literalRule := rfl

theorem literalRule_in_table : literalRule ∈ table :=
  List.mem_of_mem_head? (by rw [literalRule_first]; rfl)

/-- The rule takes the state that evaluates the literal and makes the state that returns it. -/
theorem literal_returns : offer [literalRule] [state literal] = [state returned] := by decide

/-- It does not fire on the state that returns: the store is left as it is. -/
theorem returned_is_left : offer [literalRule] [state returned] = [state returned] := by decide

/-- The clause row of an equation with a parameter. -/
def clauseRow : Atom :=
  .expression [.symbol "pm:clause", .symbol "double", .grounded (.int 0),
    .expression [.symbol "pm:head", .expression [.var "x"]],
    .expression [.symbol "*", .var "x", .grounded (.int 2)]]

/-- Such a row holds an unknown, so a store with it is outside `calls_are_one_run`. -/
theorem clause_row_is_not_ground : isGroundAtom clauseRow = false := by decide

end Controls

#print axioms table_closed
#print axioms calls_are_one_run
#print axioms opens_of_numbered
#print axioms calls_are_a_path_of_the_table
#print axioms offer_is_a_path_of_the_table
#print axioms offer_is_one_run
#print axioms quiescent_iff_no_call_fires
#print axioms Controls.literal_returns

end Mettapedia.Languages.MeTTa.PeTTa.MachineRuleTable
