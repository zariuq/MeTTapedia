import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEpochInvariant
import Mettapedia.OSLF.MeTTaIL.Complete.ClassesChecked

/-! Encoded source match requests are checked in every provider epoch.
Their closedness follows from declaration-derived typing in an empty free
context, independently of provider cache contents.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem epoch_match_request_checked (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value) (body : OCaml.Code)
    (captured : OCaml.Environment) (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    let source := node "MlMatchOne" [patternId index, value argument, code body, environment captured, encodedRest]
    source.freeFvarNames = [] ∧ Complete.Classes.Checked (epochPlan prepared table) [] (.base "MlConfig") source := by
  obtain ⟨_, _, terms, _⟩ := prepare_readback program prepared built
  have grammar : (GeneralPlanEnvironment.environment (epochPlan prepared table)).language.terms = baseLanguage.terms := terms
  have typed := match_request_open _ grammar (epochPlan prepared table).snapshot.free referenced argument body captured rest encodedRest resolved
  have closedTyping := match_request_open baseLanguage rfl FreeTypeContext.empty referenced argument body captured rest encodedRest resolved
  refine ⟨?_, checkOpenPatternWellSorted_complete typed⟩
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name present
  obtain ⟨_, impossible⟩ := closedTyping.1.freeType_of_mem_freeFvarNames_of_isObjectPattern closedTyping.2.2.1 present
  cases impossible

theorem epoch_clause_request_checked (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (index : Nat) (parameter : OCaml.MatchPattern) (argument : OCaml.Value) (body : OCaml.Code)
    (captured : OCaml.Environment) (clauses : List OCaml.Clause) (later : Pattern)
    (rest : OCaml.Continuation) (encodedRest : Pattern)
    (built : prepare program = .ok prepared)
    (referenced : patternReference? (patterns program) parameter = some (patternId index))
    (clauseResolved : clauseList? (patterns program) clauses = some later)
    (resolved : continuation? (patterns program) rest = some encodedRest) :
    let source := node "MlTryClause" [patternId index, value argument, code body, later, environment captured, encodedRest]
    source.freeFvarNames = [] ∧ Complete.Classes.Checked (epochPlan prepared table) [] (.base "MlConfig") source := by
  obtain ⟨_, _, terms, _⟩ := prepare_readback program prepared built
  have grammar : (GeneralPlanEnvironment.environment (epochPlan prepared table)).language.terms = baseLanguage.terms := terms
  have typed := clause_request_open _ grammar (epochPlan prepared table).snapshot.free referenced argument body clauses later clauseResolved
    captured rest encodedRest resolved
  have closedTyping := clause_request_open baseLanguage rfl FreeTypeContext.empty referenced argument body clauses later clauseResolved
    captured rest encodedRest resolved
  refine ⟨?_, checkOpenPatternWellSorted_complete typed⟩
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name present
  obtain ⟨_, impossible⟩ := closedTyping.1.freeType_of_mem_freeFvarNames_of_isObjectPattern closedTyping.2.2.1 present
  cases impossible

#print axioms epoch_match_request_checked
#print axioms epoch_clause_request_checked

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
