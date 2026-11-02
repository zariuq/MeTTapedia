import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRScopedInstances

/-! The fixed restriction removes unused anonymous slots and retains real
anonymous, logical and pool bindings. Physical sort checks distinguish value
references from relation references. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.BindingTypingControls

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

private def pools : Join.Pools := ⟨[["Pair"],["Out"]],[.number 1,.number 2]⟩
private def clause : Clause := ⟨⟨["Out"],[.var "X"]⟩,[.atom ⟨["Pair"],[.var "X",.anonymous]⟩]⟩
private def sourceEnvironment : BindingTyping.SourceEnvironment := [("X",.number 1)]
private def chosen : List GroundFact := [⟨["Pair"],[.number 1,.number 2]⟩]
private def fixed := BindingTyping.ofClause pools clause sourceEnvironment chosen

#guard ((Bindings.ofInstance pools sourceEnvironment chosen).lookup (Join.anonymousVariable 0 0)).isSome
#guard (fixed.lookup (Join.anonymousVariable 0 0)).isNone
#guard fixed.lookup (Join.anonymousVariable 0 1) == some (Executable.valueRef 1)
#guard fixed.lookup (Join.logicalVariable "X") == some (Executable.valueRef 0)
#guard fixed.lookup (Join.relationSlot 0) == some (Executable.relationRef 0)
#guard fixed.lookup (Join.literalSlot 1) == some (Executable.valueRef 1)
#guard checkHasType Query.baseLanguage (FreeTypeContext.ofList (Executable.freeTypes pools)) []
  (Executable.valueRef 0) (.base "DlValue")
#guard !(checkHasType Query.baseLanguage (FreeTypeContext.ofList (Executable.freeTypes pools)) []
  (Executable.valueRef 0) (.base "DlRelation"))

theorem actual_capture_typing : CapturesTyped Query.baseLanguage
    (FreeTypeContext.ofList (Executable.freeTypes pools)) [] (BindingContext.context pools clause) fixed :=
  BindingTyping.restricted_typed Query.baseLanguage pools clause sourceEnvironment chosen

#print axioms actual_capture_typing

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.BindingTypingControls
