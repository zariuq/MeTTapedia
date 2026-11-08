import Lean

/-!
# Declaration roots and reconstruction dependencies

The manifest follows declaration types, definition and opaque bodies,
inductive blocks and constructors, and recursor computation rules. Theorem
proofs are deliberately not followed: their statements are reconstructed by
the target prover. This exporter is an untrusted inventory producer, not an
interpretation or a proof that a target implements a declaration.

Root files contain one fully qualified printed name per line. Resolution
checks the imported environment and refuses ambiguous printed names. The
manifest also records structural names, so numeric name components are not
confused with strings. Hashes identify observations; they grant no authority.
-/

namespace Mettapedia.Languages.Lean.Declarations.Manifest

open _root_.Lean

def nameJson : Name → Json
  | .anonymous => toJson (["anonymous"] : List String)
  | .str parent component => Json.arr #[toJson "str", nameJson parent, toJson component]
  | .num parent component => Json.arr #[toJson "num", nameJson parent, toJson component]

def moduleOf (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some index => env.header.moduleNames[index.toNat]!
  | none => .anonymous

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- Dependencies of reconstruction, including each recursor rule's body. -/
def dependencies (info : ConstantInfo) : NameSet := Id.run do
  let mut names := info.type.getUsedConstantsAsSet
  match info with
  | .defnInfo value => names := names.union value.value.getUsedConstantsAsSet
  | .opaqueInfo value => names := names.union value.value.getUsedConstantsAsSet
  | .inductInfo value =>
      for name in value.all ++ value.ctors do names := names.insert name
  | .ctorInfo value => names := names.insert value.induct
  | .recInfo value =>
      for name in value.all do names := names.insert name
      for rule in value.rules do
        names := (names.insert rule.ctor).union rule.rhs.getUsedConstantsAsSet
  | _ => pure ()
  return names

def sorted (names : NameSet) : Array Name :=
  names.toList.toArray.qsort (fun a b => a.toString < b.toString)

/-- Missing references are errors, rather than silently dropped constants. -/
def closure (env : Environment) (roots : Array Name) : Except String NameSet := do
  let mut seen : NameSet := {}
  let mut todo := roots
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    let some info := env.find? name
      | throw s!"missing declaration {name}"
    seen := seen.insert name
    for dependency in dependencies info do
      unless seen.contains dependency do todo := todo.push dependency
  return seen

def ownDeclarations (env : Environment) (owner : Name) : Array Name :=
  (env.constants.toList.filterMap fun (name, _) =>
    if moduleOf env name == owner then some name else none).toArray.qsort
      (fun a b => a.toString < b.toString)

/-- These are explicit presentation exclusions, not dependency filters.
An excluded root still enters the closure if an admitted root uses it. -/
def displayReason (name : Name) : Option String :=
  let components := name.components.map toString
  if components.any (fun part =>
      part.startsWith "instRepr" || part == "repr" || part == "reprPrec" ||
      part.startsWith "instToString" || part.startsWith "instToFormat" ||
      part.startsWith "instToJson" || part.startsWith "instHashable") then
    some "derived display or serialization instance"
  else none

def rootsText (roots : Array Name) : String :=
  String.intercalate "\n" (roots.toList.map toString) ++ "\n"

def resolveRoots (env : Environment) (text : String) : Except String (Array Name) := do
  let mut index : Std.HashMap String (Array Name) := {}
  for (name, _) in env.constants.toList do
    let key := name.toString
    index := index.insert key ((index.getD key #[]).push name)
  let mut roots := #[]
  for line in text.splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    match index.getD line #[] with
    | #[name] =>
        if roots.contains name then throw s!"duplicate root {line}"
        roots := roots.push name
    | #[] => throw s!"unknown root {line}"
    | _ => throw s!"ambiguous printed root {line}"
  return roots

def directFamilies (env : Environment) (names : NameSet) : Array Name :=
  (sorted names).filter fun name =>
    match env.find? name with
    | some (.inductInfo _) => true
    | _ => false

def namesJson (names : Array Name) : String :=
  (Json.arr (names.map nameJson)).compress

def nearestDeclaredParent (env : Environment) : Name → Option Name
  | .anonymous => none
  | .str parent _ | .num parent _ =>
      if env.contains parent then some parent else nearestDeclaredParent env parent

/-- Registered equation/recursor metadata is distinguished from a naming hint.
Neither kind of association is itself source-correspondence evidence. -/
def helperParent (env : Environment) (name : Name) (info : ConstantInfo) : Option (Name × String) :=
  if let some parent := (Meta.eqnsExt.getState env).mapInv.find? name then
    some (parent, "registered-equation")
  else if let some (parent, _) := Meta.declFromEqLikeName env name then
    some (parent, "lean-equation-name-resolution")
  else match info with
    | .recInfo value => value.all.head?.map (·, "recursor-block")
    | _ =>
      let part := match name with | .str _ part => part | _ => ""
      if Meta.isMatcherCore env name || name.isInternal ||
          ["_", "brecOn", "below", "ibelow", "binductionOn", "casesOn", "recOn",
           "noConfusion", "sizeOf", "eq_", "inj", "elim"].any (fun stem => part.startsWith stem) then
        (nearestDeclaredParent env name).map (·, "name-hint-only")
      else none

def manifestText (env : Environment) (roots : Array Name) (names : NameSet) : String := Id.run do
  let mut lines := #["constant\tkind\tmodule\troot\tunsafe\ttype_hash\tstructural_name\tdependencies\trole\tparent\tparent_basis"]
  for name in sorted names do
    let some info := env.find? name | continue
    let parent := helperParent env name info
    let role := if parent.isSome then "generated-helper"
      else if roots.contains name then "declaration" else "dependency"
    lines := lines.push (String.intercalate "\t"
      [name.toString, kind info, (moduleOf env name).toString,
       toString (roots.contains name), toString info.isUnsafe, toString info.type.hash,
       (nameJson name).compress, namesJson (sorted (dependencies info)), role,
       parent.map (fun p => p.1.toString) |>.getD "", parent.map Prod.snd |>.getD ""])
  return String.intercalate "\n" lines.toList ++ "\n"

def exclusionsText (own : Array Name) : String :=
  "constant\treason\n" ++ String.join (own.toList.filterMap fun name =>
    (displayReason name).map fun reason => s!"{name}\t{reason}\n")

end Mettapedia.Languages.Lean.Declarations.Manifest
