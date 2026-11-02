import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterCompoundAdmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterSource

/-! Total source printing for an independently specified Datalog IR domain.
Admission states lexical class membership, integer bounds, supported column
types and ordinary rule/declaration shape. It never assumes printer success. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.Datalog
open Formation

def ClauseAdmitted (clause : Clause) : Prop :=
  AtomAdmitted clause.head ∧ clause.body ≠ [] ∧ ∀ premise ∈ clause.body, PremiseAdmitted premise

def AttributeAdmitted (column : Attribute) : Prop := Identifier column.name ∧ column.type ≠ .floating

def DeclarationAdmitted (declaration : RelationDeclaration) : Prop :=
  (∃ name, declaration.name = [name] ∧ Identifier name) ∧ ∀ column ∈ declaration.attributes, AttributeAdmitted column

def StatementAdmitted : Statement → Prop
  | .declaration declaration => DeclarationAdmitted declaration
  | .fact fact => FactAdmitted fact
  | .rule clause => ClauseAdmitted clause
  | .input name | .output name => Qualified name

def ProgramAdmitted (program : Program) : Prop := ∀ statement ∈ program.statements, StatementAdmitted statement

theorem clause_total (clause : Clause) (admitted : ClauseAdmitted clause) :
    ∃ pattern, clause? clause = .ok pattern ∧ Formed "DlRule" pattern := by
  obtain ⟨head, headRead, headFormed⟩ := atom_total clause.head admitted.1
  obtain ⟨body, bodyRead, length, bodyFormed⟩ := mapM_total premise? "DlPositiveLiteral" clause.body
    (fun premise member => premise_total premise (admitted.2.2 premise member))
  have nonempty : body ≠ [] := by intro same; subst body; exact admitted.2.1 (List.length_eq_zero_iff.mp length.symm)
  have bodyNonempty : clause.body.isEmpty = false := by cases bodyShape : clause.body with
    | nil => exact False.elim (admitted.2.1 bodyShape)
    | cons _ _ => rfl
  cases body with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
    refine ⟨node "rule" [head, space, space, nonemptySeparated "body-one" "body-more" first rest], ?_, ?_⟩
    · simp [clause?, bodyNonempty, headRead, bodyRead, bind, Except.bind, pure, Except.pure]
    · apply Formation.rule headFormed space_formed space_formed
      exact nonempty_separated_formed "DlBody" "DlPositiveLiteral" "body-one" "body-more"
        (fun _ formed => Formation.body_one formed empty_formed)
        (fun _ _ head tail => Formation.body_more head empty_formed space_formed tail)
        first rest (bodyFormed first List.mem_cons_self)
        (fun pattern member => bodyFormed pattern (List.mem_cons_of_mem _ member))

theorem attribute_type_total (kind : AttributeType) (admitted : kind ≠ .floating) :
    ∃ pattern, attributeType? kind = .ok pattern ∧ Formed "DlPrimitiveType" pattern := by
  cases kind with
  | symbol => exact ⟨_, rfl, Formation.type_symbol⟩
  | number => exact ⟨_, rfl, Formation.type_number⟩
  | unsigned => exact ⟨_, rfl, Formation.type_unsigned⟩
  | floating => exact False.elim (admitted rfl)

theorem attribute_total (column : Attribute) (admitted : AttributeAdmitted column) :
    ∃ pattern, attribute? column = .ok pattern ∧ Formed "DlAttribute" pattern := by
  obtain ⟨name, nameRead, nameFormed⟩ := identifier_total column.name admitted.1
  obtain ⟨kind, kindRead, kindFormed⟩ := attribute_type_total column.type admitted.2
  exact ⟨_, by simp [attribute?, nameRead, kindRead, bind, Except.bind, pure, Except.pure],
    Formation.attr nameFormed empty_formed space_formed kindFormed⟩

theorem declaration_total (declaration : RelationDeclaration) (admitted : DeclarationAdmitted declaration) :
    ∃ pattern, declaration? declaration = .ok pattern ∧ Formed "DlDeclaration" pattern := by
  obtain ⟨⟨name, nameShape, nameAllowed⟩, columnsAllowed⟩ := admitted
  obtain ⟨identifier, identifierRead, identifierFormed⟩ := identifier_total name nameAllowed
  obtain ⟨columns, columnsRead, _, columnsFormed⟩ := mapM_total attribute? "DlAttribute" declaration.attributes
    (fun column member => attribute_total column (columnsAllowed column member))
  refine ⟨node "declaration" [directiveSpace, node "relations-one" [identifier], empty, empty,
    separated "attributes-empty" "attributes-one" "attributes-more" columns], ?_, ?_⟩
  · simp [declaration?, nameShape, identifierRead, columnsRead, bind, Except.bind, pure, Except.pure]
  · apply Formation.declaration directive_formed (Formation.relations_one identifierFormed) empty_formed empty_formed
    exact separated_formed "DlAttributes" "DlAttribute" "attributes-empty" "attributes-one" "attributes-more"
      Formation.attributes_empty (fun _ formed => Formation.attributes_one formed empty_formed)
      (fun _ _ head tail => Formation.attributes_more head empty_formed space_formed tail) columns columnsFormed

theorem statement_total (statement : Statement) (admitted : StatementAdmitted statement) :
    ∃ pattern, statement? statement = .ok pattern ∧ Formed "DlItem" pattern := by
  cases statement with
  | declaration declaration =>
    obtain ⟨source, built, formed⟩ := declaration_total declaration admitted
    exact ⟨_, by simp [statement?, built, bind, Except.bind, pure, Except.pure], Formation.item_declaration formed⟩
  | fact fact =>
    obtain ⟨source, built, formed⟩ := fact_total fact admitted
    exact ⟨_, by simp [statement?, built, bind, Except.bind, pure, Except.pure], Formation.item_fact formed⟩
  | rule clause =>
    obtain ⟨source, built, formed⟩ := clause_total clause admitted
    exact ⟨_, by simp [statement?, built, bind, Except.bind, pure, Except.pure], Formation.item_rule formed⟩
  | input names =>
    obtain ⟨source, built, formed⟩ := qualified_total names admitted
    exact ⟨_, by simp [statement?, built, bind, Except.bind, pure, Except.pure],
      Formation.item_input (Formation.input directive_formed formed)⟩
  | output names =>
    obtain ⟨source, built, formed⟩ := qualified_total names admitted
    exact ⟨_, by simp [statement?, built, bind, Except.bind, pure, Except.pure],
      Formation.item_output (Formation.output directive_formed formed)⟩

theorem items_formed (patterns : List Pattern) (formed : ∀ pattern ∈ patterns, Formed "DlItem" pattern) :
    Formed "DlItems" (items patterns) := by
  induction patterns with
  | nil => exact Formation.items_empty
  | cons first rest ih =>
    exact Formation.items_more (formed first List.mem_cons_self) newline_formed
      (ih (fun pattern member => formed pattern (List.mem_cons_of_mem _ member)))

theorem program_tree_total (program : Program) (admitted : ProgramAdmitted program) :
    ∃ pattern, programTree? program = .ok pattern ∧ Formed "DlProgram" pattern := by
  obtain ⟨patterns, built, _, formed⟩ := mapM_total statement? "DlItem" program.statements
    (fun statement member => statement_total statement (admitted statement member))
  exact ⟨_, by simp [programTree?, built, bind, Except.bind, pure, Except.pure],
    Formation.program empty_formed (items_formed patterns formed)⟩

theorem print_total (program : Program) (admitted : ProgramAdmitted program) : ∃ text, print? program = .ok text := by
  obtain ⟨pattern, built, formed⟩ := program_tree_total program admitted
  obtain ⟨text, printed⟩ := ScalarSyntaxCore.formed_prints_text description description_shape formed
  rw [shared_print] at printed
  exact ⟨text, by simp [print?, built, printed, bind, Except.bind, pure, Except.pure]⟩

theorem admitted_prints_source (program : Program) (admitted : ProgramAdmitted program) :
    ∃ text, print? program = .ok text ∧ ReferenceReader.SourceProgram
      (Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter.stringScalars text) program := by
  obtain ⟨text, printed⟩ := print_total program admitted
  exact ⟨text, printed, printed_program_source program text printed⟩

#print axioms program_tree_total
#print axioms print_total
#print axioms admitted_prints_source

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter
