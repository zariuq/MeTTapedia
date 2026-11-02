import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparationReadback

/-! Successful preparation discharges the source scope and authored
language-validation gates, including every generated declaration.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem prepared_validation (program : OCaml.Program) (prepared : Prepared)
    (built : prepare program = .ok prepared) :
    program.checkScope = true ∧ prepared.compiled.validate.isEmpty = true := by
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
                exact ⟨rfl, valid⟩
              next =>
                change Except.error _ = Except.ok prepared at built
                cases built

#print axioms prepared_validation

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
