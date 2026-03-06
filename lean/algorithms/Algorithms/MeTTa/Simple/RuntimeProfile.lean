import Algorithms.MeTTa.Simple.Session
import Algorithms.MeTTa.Simple.Semantics.Assertions

namespace Algorithms.MeTTa.Simple

structure RuntimeProfile where
  dialect : String
  syntaxSpec : MeTTailCore.MeTTaSyntax.SyntaxSpec
  includeDefaultPeTTaLibrary : Bool
  assertionPolicy : Algorithms.MeTTa.Simple.Semantics.Assertions.Policy
deriving Repr, DecidableEq

def normalizeDialect (dialect : String) : String :=
  String.ofList (dialect.trimAscii.toString.toList.map Char.toLower)

def runtimeProfileHE : RuntimeProfile :=
  { dialect := "he"
    syntaxSpec := MeTTailCore.MeTTaSyntax.he
    includeDefaultPeTTaLibrary := false
    assertionPolicy := { resultStyle := .unitError } }

def runtimeProfilePeTTa : RuntimeProfile :=
  { dialect := "petta"
    syntaxSpec := MeTTailCore.MeTTaSyntax.petta
    includeDefaultPeTTaLibrary := true
    assertionPolicy := {} }

def runtimeProfileOfDialect? (dialect : String) : Option RuntimeProfile :=
  let d := normalizeDialect dialect
  if d = "he" then
    some runtimeProfileHE
  else if d = "petta" then
    some runtimeProfilePeTTa
  else
    none

def runDialectDispatch? : List String → Option (RuntimeProfile × Bool × String)
  | ["run", "--dialect", dialect, "--json", file] => do
      let profile ← runtimeProfileOfDialect? dialect
      some (profile, true, file)
  | ["run", "--dialect", dialect, file] => do
      let profile ← runtimeProfileOfDialect? dialect
      some (profile, false, file)
  | _ => none

def replDialectDispatch? : List String → Option RuntimeProfile
  | ["repl", "--dialect", dialect] => runtimeProfileOfDialect? dialect
  | _ => none

end Algorithms.MeTTa.Simple
