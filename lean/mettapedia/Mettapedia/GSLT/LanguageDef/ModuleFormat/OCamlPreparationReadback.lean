import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlProgramCompilation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlRecursiveInstantiation

/-! Successful preparation retains the source program, exact pattern pool
and the generated row batches. Origin evidence reads the actual compiler
result rather than a parallel generated-language definition.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

def dispatchRows? (program : OCaml.Program) (pool : List OCaml.MatchPattern) : Except String (List RewriteRule) :=
  program.code.toList.zipIdx.mapM fun (instruction, reference) => do
    let some compiled := compileInstruction? pool reference instruction | throw "instruction compilation refused"
    pure compiled

def functionBatches? (program : OCaml.Program) (pool : List OCaml.MatchPattern) : Except String (List (List RewriteRule)) :=
  program.code.toList.zipIdx.mapM fun (instruction, reference) => do
    let some compiled := functionRules? program pool reference instruction | throw "function compilation refused"
    pure compiled

def allPatternRows (pool : List OCaml.MatchPattern) : List RewriteRule :=
  pool.zipIdx.flatMap fun (parameter, index) => patternRules index parameter

theorem prepare_readback (program : OCaml.Program) (prepared : Prepared)
    (built : prepare program = .ok prepared) :
    prepared.program = program ∧ prepared.patternPool = patterns program ∧
      prepared.compiled.terms = baseLanguage.terms ∧ prepared.compiled.typeNames = baseLanguage.typeNames ∧
      ∃ dispatch functions,
        dispatchRows? program (patterns program) = .ok dispatch ∧
        functionBatches? program (patterns program) = .ok functions ∧
        prepared.compiled.rewrites = baseLanguage.rewrites ++ dispatch ++ functions.flatten ++ allPatternRows (patterns program) := by
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
                exact ⟨rfl, rfl, rfl, rfl, dispatchRows, functionRows, rfl, rfl, rfl⟩
              next =>
                change Except.error _ = Except.ok prepared at built
                cases built

#print axioms prepare_readback

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
