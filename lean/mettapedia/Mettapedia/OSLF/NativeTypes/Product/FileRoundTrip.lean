import Mettapedia.OSLF.NativeTypes.Product.LanguageRows
import Mettapedia.OSLF.NativeTypes.Product.Export
import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.OSLF.NativeTypes.Product.OneCore

/-!
# The certified languages from their files

Each language with certified forms is written as a `.module` file (`moduleText`) and read back as the executable reads
it: elaborated under the names it is written with (`ModuleSource.elaborateAuthored`), its rows read as they are written
(`readingOf`). `#language_file_roundtrip L` checks that the reading is `L` itself, so that the executable answers the
file with `L`'s certified forms and decider:

- the π-calculus with its restriction laws and laws of replication, and its parallel fragment with its flattening
  algebra;
- CCS with its sums and restriction laws, and with replication;
- mobile ambients with restriction and replication, and with communication and paths;
- the ρ-calculus;
- CCS with recursion, whose forms and decider are certified in the environment of its definitions, given beside it.

Rows that declare their binding are written with named binders whose reduction is the declaration, the exchange of
restrictions as `ν x. ν y. P = ν y. ν x. P`; the others with anonymous binders, as they are.

A file's two readings are different languages with one core (`readingOf_core`). The controls below check this for each
certified language: its direct reading is the language, its core reading is another language, and both have the
core of the file. Languages that differ have different cores.
-/

namespace Mettapedia.OSLF.NativeTypes.Product.FileRoundTrip

open Lean Elab Command
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.ModuleSource

/-- The rows in which two languages differ, by field and label. -/
def differences (reading original : LanguageDef) : List String :=
  let rows {α : Type} [DecidableEq α] (field : String) (label : α → String) (read written : List α) :
      List String :=
    (if read.length = written.length then [] else [s!"{field}: {read.length} rows for {written.length}"]) ++
      ((read.zip written).filter fun (first, second) => first ≠ second).map fun (first, _) => s!"{field} {label first}"
  (if reading.name = original.name then [] else [s!"name {reading.name} for {original.name}"]) ++
    rows "sort" TypeDecl.name reading.types original.types ++
    rows "constructor" GrammarRule.label reading.terms original.terms ++
    rows "equation" Equation.name reading.equations original.equations ++
    rows "rewrite" RewriteRule.name reading.rewrites original.rewrites

/-- `#language_file_roundtrip L`: write the language `L` as a `.module` file, read the file as the executable reads it,
and check that the reading is `L`. -/
syntax (name := languageFileRoundtrip) "#language_file_roundtrip " ident : command

@[command_elab languageFileRoundtrip] unsafe def elabLanguageFileRoundtrip : CommandElab := fun stx => do
  match stx with
  | `(#language_file_roundtrip $language:ident) => do
      let constant ← liftCoreM (realizeGlobalConstNoOverload language)
      let original ← liftTermElabM (evalConst LanguageDef constant)
      let text := moduleText original
      let data ← Commands.readModuleText text s!"{original.name}.module"
      match readingOf (elaborateAuthored [] data) with
      | .error problem => throwError "{language.getId}: the file is not read: {problem}\n{text}"
      | .ok reading =>
          if reading = original then
            logInfo m!"{language.getId}: written and read back as the same language ({text.length} characters)"
          else
            throwError "{language.getId}: the file reads as another language: {differences reading original}\n{text}"
  | _ => throwUnsupportedSyntax

#language_file_roundtrip piParallel
#language_file_roundtrip piFull
#language_file_roundtrip ccsRepCalc
#language_file_roundtrip ambientNuCalc
#language_file_roundtrip ambientCommCalc
#language_file_roundtrip Mettapedia.Languages.ProcessCalculi.CCS.ccsCalc
#language_file_roundtrip Mettapedia.OSLF.MeTTaIL.Syntax.rhoCalc
#language_file_roundtrip Mettapedia.Languages.ProcessCalculi.CCS.Recursive.ccsRecCalc

/-! ## One core for both readings -/

/-- A language as its file writes it: its declared rows with named binders. -/
def written (language : LanguageDef) : LanguageDef :=
  { language with «equations» := language.equations.map (namedEquation language),
                  «rewrites» := language.rewrites.map (namedRewrite language) }

/-- The core of a language, if it has one. -/
def coreOf (language : LanguageDef) : Option LanguageDef :=
  (Mettapedia.OSLF.MeTTaIL.CoreReduction.reduce language).toOption

/-- Whether a language's file is read directly as the language, read as its core as another language, and has one
core under both readings. -/
def oneCore (language : LanguageDef) : Bool :=
  let file := written language
  let core := (file.toCore).toOption.map (·.language)
  (directReading file).toOption == some language && core != some language && core.isSome &&
    coreOf language == coreOf file

#guard [piFull, piParallel, ccsRepCalc, ambientNuCalc, ambientCommCalc, Mettapedia.Languages.ProcessCalculi.CCS.ccsCalc,
  Mettapedia.OSLF.MeTTaIL.Syntax.rhoCalc, Mettapedia.Languages.ProcessCalculi.CCS.Recursive.ccsRecCalc].all oneCore

-- A file with declared rows is not its reading: its rows are written with named binders.
#guard !decide (written piFull = piFull) && !decide (written ambientNuCalc = ambientNuCalc)

-- Languages that differ have different cores.
#guard coreOf piFull != coreOf piParallel && coreOf ambientNuCalc != coreOf ambientCommCalc

end Mettapedia.OSLF.NativeTypes.Product.FileRoundTrip
