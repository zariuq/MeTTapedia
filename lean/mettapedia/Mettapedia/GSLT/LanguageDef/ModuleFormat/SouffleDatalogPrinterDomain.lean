import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterAdmissionReflection

/-! Exact agreement between the independent source-admission checker and
the actual whole-program printer. Admission preserves its existing domain. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.Datalog

theorem argument_reflect (argument : Argument) (pattern : Pattern) (built : argument? argument = .ok pattern) :
    ArgumentAdmitted argument := by
  cases argument with
  | literal value =>
    obtain ⟨source, read, _⟩ := bind_ok built
    exact value_reflect value source read
  | var name =>
    obtain ⟨source, read, _⟩ := bind_ok built
    exact identifier_reflect name source read
  | anonymous => trivial

theorem atom_reflect (atom : Mettapedia.Languages.Datalog.Atom) (pattern : Pattern) (built : atom? atom = .ok pattern) :
    AtomAdmitted atom := by
  obtain ⟨name, nameRead, later⟩ := bind_ok built
  obtain ⟨arguments, argumentsRead, _⟩ := bind_ok later
  exact ⟨qualified_reflect atom.relation name nameRead,
    mapM_reflect argument? ArgumentAdmitted argument_reflect atom.arguments arguments argumentsRead⟩

theorem fact_reflect (fact : GroundFact) (pattern : Pattern) (built : fact? fact = .ok pattern) : FactAdmitted fact := by
  obtain ⟨name, nameRead, later⟩ := bind_ok built
  obtain ⟨values, valuesRead, _⟩ := bind_ok later
  exact ⟨qualified_reflect fact.relation name nameRead,
    mapM_reflect value? ValueAdmitted value_reflect fact.values values valuesRead⟩

theorem premise_reflect (premise : Mettapedia.Languages.Datalog.Premise) (pattern : Pattern)
    (built : premise? premise = .ok pattern) : PremiseAdmitted premise := by
  cases premise with
  | atom atom =>
    obtain ⟨source, read, _⟩ := bind_ok built
    exact atom_reflect atom source read
  | comparison comparison =>
    obtain ⟨left, leftRead, later⟩ := bind_ok built
    obtain ⟨right, rightRead, _⟩ := bind_ok later
    exact ⟨argument_reflect comparison.left left leftRead, argument_reflect comparison.right right rightRead⟩

theorem clause_reflect (clause : Clause) (pattern : Pattern) (built : clause? clause = .ok pattern) : ClauseAdmitted clause := by
  unfold clause? at built
  split at built
  · cases built
  · rename_i nonempty
    obtain ⟨head, headRead, later⟩ := bind_ok built
    obtain ⟨body, bodyRead, _⟩ := bind_ok later
    refine ⟨atom_reflect clause.head head headRead, ?_, mapM_reflect premise? PremiseAdmitted premise_reflect clause.body body bodyRead⟩
    intro empty
    simp [empty] at nonempty

theorem attribute_type_reflect (kind : AttributeType) (pattern : Pattern) (built : attributeType? kind = .ok pattern) :
    kind ≠ .floating := by
  cases kind <;> simp_all [attributeType?]

theorem attribute_reflect (column : Attribute) (pattern : Pattern) (built : attribute? column = .ok pattern) :
    AttributeAdmitted column := by
  obtain ⟨name, nameRead, later⟩ := bind_ok built
  obtain ⟨kind, kindRead, _⟩ := bind_ok later
  exact ⟨identifier_reflect column.name name nameRead, attribute_type_reflect column.type kind kindRead⟩

theorem declaration_reflect (declaration : RelationDeclaration) (pattern : Pattern)
    (built : declaration? declaration = .ok pattern) : DeclarationAdmitted declaration := by
  cases names : declaration.name with
  | nil => simp [declaration?, names] at built
  | cons name rest =>
    cases rest with
    | cons _ _ => simp [declaration?, names] at built
    | nil =>
      simp only [declaration?, names] at built
      obtain ⟨identifier, nameRead, later⟩ := bind_ok built
      obtain ⟨columns, columnsRead, _⟩ := bind_ok later
      exact ⟨⟨name, names, identifier_reflect name identifier nameRead⟩,
        mapM_reflect attribute? AttributeAdmitted attribute_reflect declaration.attributes columns columnsRead⟩

theorem statement_reflect (statement : Statement) (pattern : Pattern) (built : statement? statement = .ok pattern) :
    StatementAdmitted statement := by
  cases statement with
  | declaration declaration =>
    obtain ⟨source, read, _⟩ := bind_ok built
    exact declaration_reflect declaration source read
  | fact fact =>
    obtain ⟨source, read, _⟩ := bind_ok built
    exact fact_reflect fact source read
  | rule clause =>
    obtain ⟨source, read, _⟩ := bind_ok built
    exact clause_reflect clause source read
  | input names =>
    obtain ⟨source, read, _⟩ := bind_ok built
    exact qualified_reflect names source read
  | output names =>
    obtain ⟨source, read, _⟩ := bind_ok built
    exact qualified_reflect names source read

theorem program_tree_reflect (program : Program) (pattern : Pattern) (built : programTree? program = .ok pattern) :
    ProgramAdmitted program := by
  obtain ⟨patterns, built, _⟩ := bind_ok built
  exact mapM_reflect statement? StatementAdmitted statement_reflect program.statements patterns built

theorem print_reflect (program : Program) (text : String) (printed : print? program = .ok text) : ProgramAdmitted program := by
  obtain ⟨pattern, built, _⟩ := bind_ok printed
  exact program_tree_reflect program pattern built

theorem checkProgram_iff_prints (program : Program) :
    checkProgram program = true ↔ ∃ text, print? program = .ok text := by
  rw [checkProgram_exact]
  exact ⟨print_total program, fun ⟨text, printed⟩ => print_reflect program text printed⟩

#print axioms print_reflect
#print axioms checkProgram_iff_prints

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter
