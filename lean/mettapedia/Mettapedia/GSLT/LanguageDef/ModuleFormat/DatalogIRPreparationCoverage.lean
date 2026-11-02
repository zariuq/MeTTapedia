import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRCompilationCoverage
import Mettapedia.Languages.Datalog.ProgramGrounding

/-! The vocabulary extracted from a typed source program covers every
compiled clause, so successful static checking cannot hide a later missing
name or literal during clause compilation. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Join.Program

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.Datalog

theorem source_relation (program : Mettapedia.Languages.Datalog.Program) (known : List GroundFact)
    (statement : Statement) (present : statement ∈ program.statements)
    (name : QualifiedName) (used : name ∈ statementRelations statement) :
    name ∈ (pools program known).relations := by
  simp only [pools, List.mem_dedup, List.mem_append, List.mem_flatMap]
  exact Or.inl ⟨statement,present,used⟩

theorem source_value (program : Mettapedia.Languages.Datalog.Program) (known : List GroundFact)
    (statement : Statement) (present : statement ∈ program.statements)
    (value : Mettapedia.Languages.Datalog.Value) (used : value ∈ statementValues statement) :
    value ∈ (pools program known).literals := by
  simp only [pools, List.mem_dedup, List.mem_append, List.mem_flatMap]
  exact Or.inl ⟨statement,present,used⟩

theorem rule_exists (program : Mettapedia.Languages.Datalog.Program) (known : List GroundFact)
    (ordinal : Nat) (clause : Clause) (present : Statement.rule clause ∈ program.statements)
    (typed : ProgramStatic.ProgramTyped program) :
    ∃ rule, compileClause? (pools program known) ordinal clause = some rule := by
  obtain ⟨context,clauseTyped⟩ := typed.2 (.rule clause) present
  apply clause_exists _ _ _ clauseTyped.1
  · apply source_relation program known (.rule clause) present
    simp [statementRelations]
  · intro value member
    apply source_value program known (.rule clause) present
    simp only [statementValues, List.mem_append, List.mem_flatMap]
    exact Or.inl ⟨.literal value,member,by simp [argumentValues]⟩
  · intro premise member
    cases premise with
    | atom atom =>
        constructor
        · apply source_relation program known (.rule clause) present
          simp only [statementRelations, List.mem_cons, List.mem_map]
          exact Or.inr ⟨atom,List.mem_filterMap.mpr ⟨.atom atom,member,rfl⟩,rfl⟩
        · intro value used
          apply source_value program known (.rule clause) present
          simp only [statementValues, List.mem_append, List.mem_flatMap]
          exact Or.inr ⟨.atom atom,member,by
            simp only [premiseValues, List.mem_flatMap]
            exact ⟨.literal value,used,by simp [argumentValues]⟩⟩
    | comparison comparison =>
        constructor <;> intro value used
        all_goals
          apply source_value program known (.rule clause) present
          simp only [statementValues, List.mem_append, List.mem_flatMap]
          refine Or.inr ⟨.comparison comparison,member,?_⟩
          simp [premiseValues, used, argumentValues]

theorem fact_clause_exists (program : Mettapedia.Languages.Datalog.Program) (known : List GroundFact)
    (ordinal : Nat) (fact : GroundFact) (present : Statement.fact fact ∈ program.statements) :
    ∃ rule, compileClause? (pools program known) ordinal (LPBridge.groundClause fact) = some rule := by
  apply clause_exists
  · simp [Clause.RangeRestricted, Clause.requiredArguments, Clause.requiredVariables,
      Clause.providedVariables, Clause.positiveAtoms, LPBridge.groundClause, Argument.vars]
  · apply source_relation program known (.fact fact) present
    simp [statementRelations, LPBridge.groundClause]
  · intro value member
    apply source_value program known (.fact fact) present
    simpa [LPBridge.groundClause, statementValues] using member
  · simp [LPBridge.groundClause]

theorem numbered_clause_exists (program : Mettapedia.Languages.Datalog.Program) (known : List GroundFact)
    (typed : ProgramStatic.ProgramTyped program) (entry : Nat × Clause)
    (present : entry ∈ LPBridge.numberedClauses program) :
    ∃ rule, compileClause? (pools program known) entry.1 entry.2 = some rule := by
  have source := (ProgramGrounding.clauseAt_iff_numbered program entry.1 entry.2).mpr present
  rcases source with rule | ⟨fact,atFact,same⟩
  · exact rule_exists program known entry.1 entry.2 (List.mem_of_getElem? rule) typed
  · rw [same]
    exact fact_clause_exists program known entry.1 fact (List.mem_of_getElem? atFact)

theorem compileClauses_exists (pools : Pools) (clauses : List (Nat × Clause))
    (total : ∀ entry ∈ clauses, ∃ rule, compileClause? pools entry.1 entry.2 = some rule) :
    ∃ rules, compileClauses? pools clauses = some rules := by
  induction clauses with
  | nil => exact ⟨[],rfl⟩
  | cons entry rest ih =>
      obtain ⟨rule,head⟩ := total entry (by simp)
      obtain ⟨rules,tail⟩ := ih (fun entry member => total entry (by simp [member]))
      exact ⟨rule :: rules,by simp [compileClauses?,head,tail]⟩

theorem prepare_complete (program : Mettapedia.Languages.Datalog.Program) (known : List GroundFact)
    (typed : ProgramStatic.ProgramTyped program)
    (inputs : ∀ fact ∈ known, StaticTyping.FactTyped (ProgramStatic.signature program) fact) :
    ∃ prepared, prepare? program known = some prepared := by
  obtain ⟨rules,compiled⟩ := compileClauses_exists (pools program known) (LPBridge.numberedClauses program)
    (numbered_clause_exists program known typed)
  have checked : ProgramStatic.checkProgram program = true := (ProgramStatic.checkProgram_iff program).mpr typed
  have seeds : known.all (StaticTyping.checkFact (ProgramStatic.signature program)) = true := by
    simpa only [List.all_eq_true, StaticTyping.checkFact_iff] using inputs
  exact ⟨⟨pools program known,rules⟩,by simp [prepare?,checked,seeds,compiled]⟩

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Join.Program
