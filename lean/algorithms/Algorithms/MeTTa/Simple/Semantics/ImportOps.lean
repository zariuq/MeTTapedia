import MeTTailCore

namespace Algorithms.MeTTa.Simple.Semantics.ImportOps

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaSyntax

def stripMettaExt (name : String) : String :=
  match name.splitOn "." with
  | [] => name
  | stem :: rest =>
      if rest.isEmpty then name else stem

def unquoteToken (tok : String) : String :=
  match tok.toList with
  | '"' :: rest =>
      match rest.reverse with
      | '"' :: innerRev => String.ofList innerRev.reverse
      | _ => tok
  | _ => tok

private def normalizeModuleName (name : String) : Option String :=
  let n := name.trimAscii.toString
  if n.isEmpty then none else some n

private def basenameOfPathLike (name : String) : String :=
  match name.splitOn "/" with
  | [] => name
  | parts =>
      match parts.reverse with
      | [] => name
      | base :: _ => if base.isEmpty then name else base

def canonicalModuleKey (name : String) : String :=
  let n := name.trimAscii.toString
  if n.isEmpty then
    ""
  else
    stripMettaExt (basenameOfPathLike n)

private def moduleNameOfPathPattern? : Pattern → Option String
  | .apply "library" [name] =>
      match name with
      | .apply tok [] => normalizeModuleName (unquoteToken tok)
      | .fvar v => normalizeModuleName v
      | _ => none
  | .apply tok [] => normalizeModuleName (unquoteToken tok)
  | .fvar v => normalizeModuleName v
  | _ => none

def moduleNameOfTerm? : Pattern → Option String
  | .apply "import!" [_space, path] =>
      moduleNameOfPathPattern? path
  | .apply "import!" [_space, path, _opts] =>
      moduleNameOfPathPattern? path
  | _ => none

def moduleNameOfStmt? : SyntaxCommand → Option String
  | .import _space path => moduleNameOfPathPattern? path
  | .eval term => moduleNameOfTerm? term
  | _ => none

private def moduleLookupKeys (name : String) : List String :=
  let pushUnique (acc : List String) (k : String) : List String :=
    let k' := k.trimAscii.toString
    if k'.isEmpty || acc.contains k' then acc else acc ++ [k']
  let addForms (acc : List String) (k : String) : List String :=
    let acc1 := pushUnique acc k
    if k.endsWith ".metta" then
      pushUnique acc1 (stripMettaExt k)
    else
      pushUnique acc1 (k ++ ".metta")
  let n := name.trimAscii.toString
  if n.isEmpty then
    []
  else
    let base := basenameOfPathLike n
    addForms (addForms [] n) base

def lookupModuleSource? (sources : List (String × String)) (name : String) : Option String :=
  (moduleLookupKeys name).findSome? (fun k => (sources.find? (fun p => p.1 == k)).map Prod.snd)

end Algorithms.MeTTa.Simple.Semantics.ImportOps
