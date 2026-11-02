import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterProgramAdmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPacketCoverage

/-! Executable admission of the independent source-printing domain, and
composition of total printing with checked source reconstruction. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter

open Mettapedia.Languages.Datalog

instance allowedDecidable (row : ScalarCore.Row) (character : Char) : Decidable (Allowed row character) :=
  inferInstanceAs (Decidable (SourceViews.profile.ClassEvidence (ScalarCore.lexicalState row).className character.toNat))

instance identifierDecidable (name : String) : Decidable (Identifier name) := by
  unfold Identifier
  split <;> infer_instance

instance qualifiedDecidable (name : List String) : Decidable (Qualified name) :=
  inferInstanceAs (Decidable (name ≠ [] ∧ ∀ part ∈ name, Identifier part))

instance valueAdmittedDecidable (value : Mettapedia.Languages.Datalog.Value) : Decidable (ValueAdmitted value) := by
  cases value <;> unfold ValueAdmitted <;> infer_instance

instance argumentAdmittedDecidable (argument : Argument) : Decidable (ArgumentAdmitted argument) := by
  cases argument <;> unfold ArgumentAdmitted <;> infer_instance

instance atomAdmittedDecidable (atom : Mettapedia.Languages.Datalog.Atom) : Decidable (AtomAdmitted atom) :=
  inferInstanceAs (Decidable (Qualified atom.relation ∧ ∀ argument ∈ atom.arguments, ArgumentAdmitted argument))

instance factAdmittedDecidable (fact : GroundFact) : Decidable (FactAdmitted fact) :=
  inferInstanceAs (Decidable (Qualified fact.relation ∧ ∀ value ∈ fact.values, ValueAdmitted value))

instance premiseAdmittedDecidable (premise : Mettapedia.Languages.Datalog.Premise) : Decidable (PremiseAdmitted premise) := by
  cases premise <;> unfold PremiseAdmitted <;> infer_instance

instance clauseAdmittedDecidable (clause : Clause) : Decidable (ClauseAdmitted clause) :=
  inferInstanceAs (Decidable (AtomAdmitted clause.head ∧ clause.body ≠ [] ∧ ∀ premise ∈ clause.body, PremiseAdmitted premise))

instance attributeAdmittedDecidable (column : Attribute) : Decidable (AttributeAdmitted column) :=
  inferInstanceAs (Decidable (Identifier column.name ∧ column.type ≠ .floating))

instance declarationAdmittedDecidable (declaration : RelationDeclaration) : Decidable (DeclarationAdmitted declaration) := by
  unfold DeclarationAdmitted
  have shape : (∃ name, declaration.name = [name] ∧ Identifier name) ↔
      match declaration.name with | [name] => Identifier name | _ => False := by
    cases declaration.name with
    | nil => simp
    | cons first rest => cases rest <;> simp
  letI : Decidable (match declaration.name with | [name] => Identifier name | _ => False) := by
    split <;> infer_instance
  exact decidable_of_iff' ((match declaration.name with | [name] => Identifier name | _ => False) ∧
    ∀ column ∈ declaration.attributes, AttributeAdmitted column) (and_congr shape Iff.rfl)

instance statementAdmittedDecidable (statement : Statement) : Decidable (StatementAdmitted statement) := by
  cases statement <;> unfold StatementAdmitted <;> infer_instance

instance programAdmittedDecidable (program : Program) : Decidable (ProgramAdmitted program) :=
  inferInstanceAs (Decidable (∀ statement ∈ program.statements, StatementAdmitted statement))

def checkProgram (program : Program) : Bool := decide (ProgramAdmitted program)

theorem checkProgram_exact (program : Program) : checkProgram program = true ↔ ProgramAdmitted program := by
  simp [checkProgram]

theorem checked_prints_packet (program : Program) (checked : checkProgram program = true) :
    ∃ text packet pattern, print? program = .ok text ∧
      SourcePacketCertificate.core? description PacketCoverage.parser description_shape
        (Mettapedia.GSLT.Parsing.LanguageDefScalarPrinter.stringScalars text) "DlProgram" packet = some pattern ∧
      ((ProgramProjection.Reference.projectProgram? pattern).bind Frontend.normalize?).bind IRCodec.program? = some program := by
  obtain ⟨text, printed⟩ := print_total program ((checkProgram_exact program).mp checked)
  obtain ⟨packet, pattern, read, projected⟩ := PacketCoverage.printed_program_packet program text printed
  exact ⟨text, packet, pattern, printed, read, projected⟩

#print axioms checkProgram_exact
#print axioms checked_prints_packet

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter
