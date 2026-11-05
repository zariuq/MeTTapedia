import Lean
import Mettapedia.OSLF.NativeTypes.Product.Query
import Mettapedia.GSLT.LanguageDef.ModuleSource.Loader

/-!
# `oslf`: the command-line front door

`lake exe oslf LANGUAGE.module FORMULA TERM [BUDGET ...] [SETTING ...]` reads a language from a `.module` file, with
the files it imports, and asks the front door whether the term has the native type, at each budget in turn, resuming
the question from one budget to the next. It prints the displayed status at each budget: established or refuted with
the evidence, or suspended. Settings are `fuel=N` (premise fuel, two by default) and `hints=N` (the finder looks for a
certificate over carriers of up to `N + 1` values, one by default; none at zero).

`lake exe oslf --matrix ROWS` checks a matrix file, each row `file | formula | term | budget | expected [| settings]`,
the expected answer a status or an answer in brief (`P certificate`, `R closed`, `open`, …).

CCS with recursion is asked in the environment of its definitions: the setting `definitions=FILE` names a definitions
file (`Product.readDefinitions`). A language whose rules query relations is asked beside tables: the setting
`tables=FILE` names a file of rows (`Product.readTables`), each a term `(Relation argument …)`, and lines
`closed Relation Complement` close a table under the name of its complement. Both files are found relative to the
working directory for one question and to the matrix file for a matrix.

The executable runs Lean's frontend on a short source that reads the module files with the format's reader and
evaluates the front door (`Mettapedia.OSLF.NativeTypes.Product.report`), so the language is elaborated exactly as the
library elaborates it, under the names the module writes (`ModuleSource.elaborateAuthored`), and read as
`Product.readingOf` reads it: as written when it is a language with certified forms, through its core otherwise. The
library is linked into the executable, and the frontend prefers its compiled code (`nativeOptions`), so the front door
runs compiled, not interpreted.
-/

open Lean

namespace Mettapedia.OSLF.NativeTypes.Product.Main

/-- The frontend's options: evaluate with the compiled code linked into this executable. -/
def nativeOptions : Options := ({} : Options).setBool `interpreter.prefer_native true

def usage : String :=
  "usage: oslf LANGUAGE.module[#Theory] FORMULA TERM [BUDGET ...] [fuel=N] [hints=N] [definitions=FILE]\n" ++
  "         [tables=FILE]\n" ++
  "       oslf --matrix ROWS   (each row: file | formula | term | budget | expected [| settings])\n" ++
  "  FORMULA and TERM are S-expressions, for example\n" ++
  "    oslf Counters.module '(reach (Halted))' '(Counter (Succ Zero))' 2 4 8"

/-- A setting `definitions=FILE`: the definitions file a language is asked beside. -/
def definitionsFile (word : String) : Option String :=
  match word.splitOn "=" with
  | ["definitions", file] => some file
  | _ => none

/-- A setting `tables=FILE`: the tables a language is asked beside. -/
def tablesFile (word : String) : Option String :=
  match word.splitOn "=" with
  | ["tables", file] => some file
  | _ => none

/-- The settings other than the files, and the definitions and tables texts read from the files that are given. -/
def splitFiles (directory : System.FilePath) (words : List String) :
    IO (List String × Option String × Option String) := do
  if (words.filterMap definitionsFile).length > 1 then
    throw (IO.userError "oslf: definitions may be supplied only once")
  if (words.filterMap tablesFile).length > 1 then
    throw (IO.userError "oslf: tables may be supplied only once")
  let readNamed : Option String → IO (Option String)
    | some file => some <$> IO.FS.readFile (directory / file)
    | none => pure none
  let definitions ← readNamed (words.findSome? definitionsFile)
  let tables ← readNamed (words.findSome? tablesFile)
  return (words.filter fun word => (definitionsFile word).isNone && (tablesFile word).isNone, definitions, tables)

/-- An optional text as a Lean term. -/
def textTerm : Option String → String
  | none => "none"
  | some text => s!"(some {text.quote})"

/-- A file argument `FILE.module` or `FILE.module#Theory`: the file, and the theory it names, if any. A module that
declares theories and no entry, as CeTTa's core modules do, is read through a named theory. -/
def splitTheory (argument : String) : String × Option String :=
  match argument.splitOn "#" with
  | [file, theory] => (file, some theory)
  | _ => (argument, none)

/-- The language a module denotes, under the names it is written with: its entry, or the named theory applied to no
arguments. -/
def languageTerm (base : String) : Option String → String
  | none => s!"(Mettapedia.GSLT.LanguageDef.ModuleSource.elaborateAuthored {base}.library {base}.module)"
  | some theory =>
    s!"(Mettapedia.GSLT.LanguageDef.ModuleSource.elaborateTheoryAuthored {base}.library {base}.module " ++
      s!"{(theory.splitOn ".").map String.quote})"

/-- Load each root with the existing parser and recursive import loader, in its own namespace. -/
def moduleSources (files : List String) : String :=
  "import Mettapedia.GSLT.LanguageDef.ModuleSource.Loader\n" ++
  String.join (files.zipIdx.map fun (file, index) =>
    s!"namespace OslfInput{index}.Source\n#module_tree {file.quote} as _root_.OslfInput{index}.Input\nend OslfInput{index}.Source\n")

/-- The source the frontend runs. -/
def source (file language formula term : String) (budgets : List Nat) (settings : List String)
    (definitions tables : Option String := none) : String :=
  "import Mettapedia.OSLF.NativeTypes.Product.Query\n" ++
  moduleSources [file] ++
  s!"#eval Mettapedia.OSLF.NativeTypes.Product.report {language} {formula.quote} {term.quote} {budgets} " ++
    s!"{settings.map String.quote} {textTerm definitions} {textTerm tables}\n"

/-- A row of a matrix file: `file | formula | term | budget | expected [| settings]`. -/
structure Row where
  file : String
  formula : String
  term : String
  budget : Nat
  expected : String
  settings : List String

/-- The rows of a matrix file; blank lines and lines starting with `#` are skipped. -/
def readRows (text : String) : Except String (List Row) :=
  (text.splitOn "\n").filterMap (fun line =>
      let trimmed := line.trimAscii.toString
      if trimmed.isEmpty || trimmed.startsWith "#" then none else some trimmed)
    |>.mapM fun line =>
      let fields := (line.splitOn "|").map (·.trimAscii.toString)
      match fields with
      | file :: formula :: term :: budget :: expected :: rest =>
        let settings := (rest.flatMap (·.splitOn " ")).filter (· ≠ "")
        if rest.length > 1 then .error s!"a row has at most six fields: {line}" else
        match budget.toNat? with
        | some number => .ok ⟨file, formula, term, number, expected, settings⟩
        | none => .error s!"not a budget: {budget}"
      | _ => .error s!"a row needs five fields: {line}"

/-- The source that checks a matrix. -/
def matrixSource (files : List String) (rows : List (Row × String × List String × Option String × Option String)) :
    String :=
  "import Mettapedia.OSLF.NativeTypes.Product.Query\n" ++
  moduleSources files ++
  "#eval Mettapedia.OSLF.NativeTypes.Product.checkRows [" ++
  ", ".intercalate (rows.map fun (row, base, settings, definitions, tables) =>
    s!"({row.file.quote}, {languageTerm base (splitTheory row.file).2}, {row.formula.quote}, {row.term.quote}, " ++
      s!"{row.budget}, " ++
      s!"{row.expected.quote}, {settings.map String.quote}, {textTerm definitions}, {textTerm tables})") ++
  "]\n"

end Mettapedia.OSLF.NativeTypes.Product.Main

open Mettapedia.OSLF.NativeTypes.Product.Main in
def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["--matrix", matrixFile] =>
    let path : System.FilePath := matrixFile
    let directory := path.parent.getD "."
    match readRows (← IO.FS.readFile path) with
    | .error problem =>
      IO.eprintln s!"oslf: {problem}"
      return 2
    | .ok rows =>
      let mut files : List String := []
      let mut named : List (Row × String × List String × Option String × Option String) := []
      for row in rows do
        let file := (← IO.FS.realPath (directory / (splitTheory row.file).1)).toString
        let index := files.idxOf file
        if index == files.length then files := files ++ [file]
        let (settings, definitions, tables) ← splitFiles directory row.settings
        named := named ++ [(row, s!"OslfInput{index}.Input", settings, definitions, tables)]
      initSearchPath (← findSysroot)
      unsafe Lean.enableInitializersExecution
      let result ← Lean.Elab.runFrontend (matrixSource files named) nativeOptions
        (directory / "OslfMatrix.lean").toString `OslfMatrix
      return if result.isSome then 0 else 1
  | argument :: formula :: term :: words =>
    let (file, theory) := splitTheory argument
    for word in words do
      unless word.toNat?.isSome || word.contains '=' do
        IO.eprintln s!"oslf: unexpected argument {word}"
        return 2
    let budgets := words.filterMap String.toNat?
    let budgets := if budgets.isEmpty then [4] else budgets
    let path ← IO.FS.realPath file
    let directory := path.parent.getD "."
    let (settings, definitions, tables) ← splitFiles "." (words.filter (·.contains '='))
    initSearchPath (← findSysroot)
    unsafe Lean.enableInitializersExecution
    let result ← Lean.Elab.runFrontend
      (source path.toString (languageTerm "OslfInput0.Input" theory) formula term budgets settings definitions tables)
      nativeOptions
      (directory / "OslfQuery.lean").toString `OslfQuery
    return if result.isSome then 0 else 1
  | _ =>
    IO.eprintln usage
    return 2
