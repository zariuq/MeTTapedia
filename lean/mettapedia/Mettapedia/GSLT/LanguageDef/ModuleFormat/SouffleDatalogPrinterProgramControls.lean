import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterProgramLaws
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSourcePrinterControls

/-! Positive and separating controls use the universal program readback
theorem. Duplicate statements and source order remain observable in the IR. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter.Controls

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.Datalog

def basicTree : Pattern := (programTree? basic).toOption.get (by decide +kernel)

theorem duplicate_program_readback :
    ((ProgramProjection.Reference.projectProgram? basicTree).bind Frontend.normalize?).bind IRCodec.program? = some basic :=
  program_tree_roundtrip basic basicTree (by decide +kernel)

def missingDuplicate : Program := ⟨[
  .declaration ⟨["N"],[⟨"x",.number⟩]⟩,
  .fact ⟨["N"],[.number (-1)]⟩,.output ["N"]]⟩

theorem duplicate_not_silently_dropped :
    ((ProgramProjection.Reference.projectProgram? basicTree).bind Frontend.normalize?).bind IRCodec.program? ≠
      some missingDuplicate := by
  rw [duplicate_program_readback]
  decide +kernel

theorem malformed_relation_is_refused :
    Frontend.qualifiedName? (.apply "dl-src:qualified-name-more" []) = none := rfl

theorem relation_components_read (source : Pattern)
    (built : qualifiedName? ["namespace","relation"] = .ok source) :
    Frontend.qualifiedName? source = some ["namespace","relation"] :=
  qualified_name_read _ _ built

theorem relation_components_not_flattened (source : Pattern)
    (built : qualifiedName? ["namespace","relation"] = .ok source) :
    Frontend.qualifiedName? source ≠ some ["namespace.relation"] := by
  rw [relation_components_read source built]
  decide +kernel

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter.Controls
