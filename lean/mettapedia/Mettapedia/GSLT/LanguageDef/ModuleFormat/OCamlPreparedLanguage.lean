import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparationReadback

/-! Successful preparation preserves the authored grammar and equations;
only the name and generated rewrite list are replaced.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem prepared_language (program : OCaml.Program) (prepared : Prepared) (built : prepare program = .ok prepared) :
    ∃ (dispatch : List RewriteRule) (functions : List (List RewriteRule)), prepared.compiled = {baseLanguage with
      name := "OCamlIndexedMachine", rewrites := baseLanguage.rewrites ++ dispatch ++ functions.flatten ++ allPatternRows (patterns program)} := by
  have expanded : prepare program = (do
      let _ ← if program.checkScope then pure () else throw "OCaml indexed code has invalid scope or unsupported data formation"
      let dispatch ← dispatchRows? program (patterns program)
      let functions ← functionBatches? program (patterns program)
      let language : LanguageDef := { baseLanguage with
        name := "OCamlIndexedMachine"
        rewrites := baseLanguage.rewrites ++ dispatch ++ functions.flatten ++ allPatternRows (patterns program) }
      let _ ← if language.validate.isEmpty then pure () else throw s!"invalid compiled declarations: {reprStr language.validate}"
      pure ⟨program, patterns program, language⟩) := rfl
  rw [expanded] at built
  cases scopeChecked : program.checkScope with
  | false =>
      simp only [scopeChecked, Bool.false_eq_true, if_false, bind, Except.bind, throw] at built
      cases built
  | true =>
      simp only [scopeChecked, if_true, pure, Except.pure, bind, Except.bind] at built
      cases dispatch : dispatchRows? program (patterns program) with
      | error error => rw [dispatch] at built; cases built
      | ok dispatchRows =>
          rw [dispatch] at built
          cases functions : functionBatches? program (patterns program) with
          | error error => rw [functions] at built; cases built
          | ok functionRows =>
              simp only [functions] at built
              split at built
              next valid =>
                cases Except.ok.inj built
                exact ⟨dispatchRows, functionRows, rfl⟩
              next =>
                change Except.error _ = Except.ok prepared at built
                cases built


theorem prepared_equations (program : OCaml.Program) (prepared : Prepared) (built : prepare program = .ok prepared) :
    prepared.compiled.equations = baseLanguage.equations := by
  obtain ⟨dispatch, functions, same⟩ := prepared_language program prepared built
  rw [same]

#print axioms prepared_language
#print axioms prepared_equations

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
