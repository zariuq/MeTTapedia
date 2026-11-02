import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRJoinInstances

/-! Anonymous arguments choose independent values, while repeated named
variables remain equality constraints across body atoms. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.JoinInstanceControls

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax

private def pools : Join.Pools := ⟨[["Edge"],["Path"]],[.symbol "a",.symbol "b",.symbol "c"]⟩
private def facts : List GroundFact := [⟨["Edge"],[.symbol "a",.symbol "b"]⟩,⟨["Edge"],[.symbol "c",.symbol "a"]⟩]
private def environment : Mettapedia.Languages.Datalog.Join.Environment := [("X",.symbol "a"),("Y",.symbol "a")]
private def physical := Bindings.ofInstance pools environment facts
private def anonymousAtoms : List Mettapedia.Languages.Datalog.Atom :=
  [⟨["Edge"],[.var "X",.anonymous]⟩,⟨["Edge"],[.anonymous,.var "Y"]⟩]
private def sharedAtoms : List Mettapedia.Languages.Datalog.Atom :=
  [⟨["Edge"],[.var "X",.var "Z"]⟩,⟨["Edge"],[.var "Z",.var "Y"]⟩]

theorem anonymous_slots_distinct : Join.anonymousVariable 0 1 ≠ Join.anonymousVariable 1 0 := by decide +kernel

theorem first_anonymous_value : physical.lookup (Join.anonymousVariable 0 1) = some (Executable.valueRef 1) := by decide +kernel

theorem second_anonymous_value : physical.lookup (Join.anonymousVariable 1 0) = some (Executable.valueRef 2) := by decide +kernel

#guard (Mettapedia.Languages.Datalog.Join.join anonymousAtoms facts []).any (fun row =>
  row.environment.lookup "X" == some (.symbol "a") && row.environment.lookup "Y" == some (.symbol "a"))
#guard !(Mettapedia.Languages.Datalog.Join.join sharedAtoms facts []).any (fun row =>
  row.environment.lookup "X" == some (.symbol "a") && row.environment.lookup "Y" == some (.symbol "a"))

#print axioms anonymous_slots_distinct
#print axioms first_anonymous_value
#print axioms second_anonymous_value

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.JoinInstanceControls
