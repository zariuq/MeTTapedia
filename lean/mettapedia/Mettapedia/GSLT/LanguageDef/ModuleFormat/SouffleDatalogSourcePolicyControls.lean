import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterAdmissionControls
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketSelection

/-! The authored word policy and independent printer admission agree on
reserved names. String contents are not identifiers, and NUL is outside
the pinned source-string representation. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePolicy.Controls

open Mettapedia.GSLT.Parsing ClassAwarePackedForest
open Mettapedia.Languages.Datalog
open SourcePrinter

theorem every_reserved_identifier_refused (name : String) (reserved : name ∈ reservedWords) :
    identifier? name = .error "source identifier is a reserved word" := by
  simp [identifier?, reserved]

theorem every_reserved_declaration_refused (name : String) (reserved : name ∈ reservedWords) :
    checkProgram ⟨[.declaration ⟨[name], []⟩]⟩ = false := by
  have rejected : ¬ ProgramAdmitted ⟨[.declaration ⟨[name], []⟩]⟩ := by
    intro admitted
    obtain ⟨⟨other, same, identifier⟩, _⟩ := admitted _ List.mem_cons_self
    have equal : name = other := (List.cons.inj same).1
    subst other
    exact identifier.1 reserved
  cases checked : checkProgram ⟨[.declaration ⟨[name], []⟩]⟩ with
  | false => rfl
  | true => exact False.elim (rejected ((checkProgram_exact _).mp checked))

theorem every_reserved_family_refused (name : String) (reserved : name ∈ reservedWords) :
    SourcePacketSelection.allows filters (name.toList.map Char.toNat)
      ⟨⟨"DlIdentifier", 0, name.toList.length⟩, .structural 0, []⟩ = false := by
  simp [SourcePacketSelection.allows, filters, SourceSyntax.FamilyFilter.allows]
  refine ⟨name, reserved, ?_⟩
  have length : name.toList.length = (name.toList.map Char.toNat).length := (List.length_map _).symm
  rw [length, List.take_length]

theorem keyword_in_symbol_is_admitted :
    checkProgram ⟨[.fact ⟨["Text"], [.symbol "count"]⟩]⟩ = true := by decide +kernel
theorem extended_keyword_is_admitted :
    checkProgram ⟨[.declaration ⟨["countX"], []⟩]⟩ = true := by decide +kernel
theorem nul_symbol_is_refused :
    checkProgram ⟨[.fact ⟨["Text"], [.symbol (String.ofList ['a', '\x00', 'b'])]⟩]⟩ = false := by decide +kernel

#print axioms every_reserved_family_refused
#print axioms every_reserved_declaration_refused

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePolicy.Controls
