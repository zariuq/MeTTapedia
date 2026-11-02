import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceDispatchAdmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlBuildDispatchAdmission
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlRemainingDispatchAdmission

/-! All fourteen indexed O0 instruction forms derive selected-rule
admission, including arbitrary lookup prefixes and recursive groups.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax GeneralExecutionAdmission

theorem instruction_row_admitted (snapshot : Snapshot) (terms : snapshot.language.terms = baseLanguage.terms)
    (types : snapshot.language.typeNames = baseLanguage.typeNames) (pool : List OCaml.MatchPattern)
    (index reference : Nat) (instruction : OCaml.Instruction) (row : RewriteRule)
    (formed : compileInstruction? pool reference instruction = some row) : ruleObligations snapshot index row = [] := by
  cases instruction with
  | literal datum => exact literal_dispatch_admitted snapshot terms types pool index reference datum row formed
  | «variable» slot => exact variable_dispatch_admitted snapshot terms pool index reference slot row formed
  | lambda parameter body => exact lambda_dispatch_admitted snapshot terms types pool index reference parameter body row formed
  | apply function argument => exact application_dispatch_admitted snapshot terms types pool index reference function argument row formed
  | letValue parameter argument body => exact let_dispatch_admitted snapshot terms types pool index reference parameter argument body row formed
  | letRecursive definitions body => exact recursive_dispatch_admitted snapshot terms pool index reference definitions body row formed
  | branch condition yes no => exact branch_dispatch_admitted snapshot terms types pool index reference condition yes no row formed
  | andThen first second => exact and_dispatch_admitted snapshot terms types pool index reference first second row formed
  | orElse first second => exact or_dispatch_admitted snapshot terms types pool index reference first second row formed
  | tuple fields => exact tuple_dispatch_admitted snapshot terms types pool index reference fields row formed
  | variant typeId constructor fields => exact variant_dispatch_admitted snapshot terms types pool index reference typeId constructor fields row formed
  | primitive operator arguments => exact primitive_dispatch_admitted snapshot terms types pool index reference operator arguments row formed
  | cons head tail => exact cons_dispatch_admitted snapshot terms types pool index reference head tail row formed
  | matchValue scrutinee clauses => exact match_dispatch_admitted snapshot terms types pool index reference scrutinee clauses row formed

#print axioms instruction_row_admitted

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
