import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterAdmissionCheck
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSourcePrinterControls

/-! Total-printing controls cover admitted programs and independent refusal
conditions. Positive source existence follows from the universal theorem. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter.AdmissionControls

open Mettapedia.Languages.Datalog

theorem acceptance_admitted : checkProgram Controls.basic = true ∧
    checkProgram Controls.literalContents = true ∧ checkProgram Controls.signedBounds = true ∧
    checkProgram Controls.anonymousComparisons = true ∧
    checkProgram ProgramStatic.Controls.cyclicGraph = true ∧ checkProgram ProgramStatic.Controls.pointsTo = true := by
  decide +kernel

theorem duplicate_program_prints : ∃ text, print? Controls.basic = .ok text :=
  print_total _ ((checkProgram_exact _).mp acceptance_admitted.1)

theorem admitted_symbol_strings_print (contents : String) (nonzero : ∀ character ∈ contents.toList, character.toNat ≠ 0) :
    ∃ text, print? ⟨[.fact ⟨["Text"], [.symbol contents]⟩]⟩ = .ok text := by
  apply print_total
  intro statement member
  have same := List.mem_singleton.mp member
  subst statement
  change Qualified ["Text"] ∧ ∀ value ∈ [Value.symbol contents], ValueAdmitted value
  refine ⟨by decide +kernel, ?_⟩
  intro value member
  cases List.mem_singleton.mp member
  exact nonzero

theorem signed_width_boundaries :
    checkProgram ⟨[.fact ⟨["N"], [.number (-(2^63)), .number (2^63-1)]⟩]⟩ = true ∧
    checkProgram ⟨[.fact ⟨["N"], [.number (-(2^63)-1)]⟩]⟩ = false ∧
    checkProgram ⟨[.fact ⟨["N"], [.number (2^63)]⟩]⟩ = false := by decide +kernel

theorem unsigned_width_boundaries :
    checkProgram ⟨[.fact ⟨["N"], [.unsigned (2^64-1)]⟩]⟩ = true ∧
    checkProgram ⟨[.fact ⟨["N"], [.unsigned (2^64)]⟩]⟩ = false := by decide +kernel

theorem malformed_name_refused : checkProgram ⟨[.declaration ⟨["not a name"], []⟩]⟩ = false := by decide +kernel
theorem standalone_underscore_variable_refused :
    checkProgram ⟨[.rule ⟨⟨["N"], [.var "_"]⟩, [.atom ⟨["N"], [.var "_"]⟩]⟩]⟩ = false := by decide +kernel
theorem empty_rule_body_refused : checkProgram ⟨[.rule ⟨⟨["N"], []⟩, []⟩]⟩ = false := by decide +kernel
theorem qualified_declaration_refused : checkProgram ⟨[.declaration ⟨["Namespace", "N"], []⟩]⟩ = false := by decide +kernel
theorem floating_profile_refused : checkProgram ⟨[.fact ⟨["N"], [.floating 0]⟩]⟩ = false := by decide +kernel
theorem empty_program_admitted : checkProgram ⟨[]⟩ = true := rfl

#print axioms acceptance_admitted
#print axioms admitted_symbol_strings_print

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter.AdmissionControls
