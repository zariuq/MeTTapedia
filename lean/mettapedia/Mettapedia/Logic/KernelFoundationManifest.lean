import Lean.Elab.Command
import Lean.Elab.Term
import Lean.PrettyPrinter
import Lean.Util.CollectAxioms
import Lean.Data.Json.Printer
import Lean.Compiler.Old

/-!
# Inspecting foundations in the checked environment

`#foundation_manifest [declaration, ...]` prints a JSON manifest of declarations
and their transitive axiom dependencies. The complete types retain hypotheses
and universe parameters: an assumption passed as a theorem argument is not an
axiom declaration, and must not disappear from a foundation report.

`#foundation_manifest_module Module.Name` inspects the safe mathematical
declarations owned by an imported module, including private and generated
declarations. Unsafe and partial environment entries are recorded separately
from that count, as are compiler entries without a kernel entry. A recursive
definition can have both a checked mathematical body and a separate partial
runtime implementation; the latter is not a second checked proof.

These commands inspect the actual checked environment. They do not infer a
set-theory profile from its name, certify that a proposed model satisfies its
advertised axioms, or treat absence of axiom constants as absence of kernel
rules. Definitions, theorem arguments, kernel rules and primitive axioms have
different roles. A theory profile must still supply its signature and laws;
the manifests expose the checking environment of the supplied declarations.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.KernelFoundationManifest

open Lean Elab Command

/-- A declaration's role in the checked environment. -/
def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "kernelQuotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

/-- Presence in the kernel environment alone does not certify a body: unsafe
and partial declarations may also have entries there. -/
def hasCheckedBody (info : ConstantInfo) : Bool :=
  !info.isUnsafe && !info.isPartial && match info with
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ => true
    | _ => false

/-- Distinguish checked bodies, kernel typing rules, primitive assumptions and
nonlogical implementations. This is not a set-theory-profile classification. -/
def checkingRole (info : ConstantInfo) : String :=
  if info.isUnsafe || info.isPartial then "nonLogicalImplementation"
  else match info with
    | .axiomInfo _ => "primitiveAxiom"
    | .quotInfo _ => "kernelQuotientPrimitive"
    | .inductInfo _ | .ctorInfo _ | .recInfo _ => "kernelInductiveTyping"
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ => "checkedBody"

private def namesJson (names : Array Name) : Json :=
  .arr (names.map fun name => .str name.toString)

private def declarationOrigin (env : Environment) (name : Name) : Name :=
  match (env.getModuleIdxFor? name).bind (env.header.modules[·]?) with
  | some moduleInfo => moduleInfo.module
  | none => env.mainModule

/-- Record a runtime-recursion naming pair only when the corresponding safe
definition or opaque body has the same recorded type, levels and owner. Lean
may generate an opaque mathematical printer and a partial runtime helper for
recursive `Repr` instances. The pair does not verify the runtime implementation
or prove that it realizes the checked body. -/
def runtimeCounterpart? (env : Environment) (name : Name) : Option Name := do
  let info ← env.checked.get.find? name
  if !info.isUnsafe && !info.isPartial then none else do
    let parent ← Lean.Compiler.isUnsafeRecName? name
    let parentInfo ← env.checked.get.find? parent
    if parentInfo.isUnsafe || parentInfo.isPartial then none else do
      match parentInfo with
      | .defnInfo _ | .opaqueInfo _ =>
          if info.type == parentInfo.type && info.levelParams == parentInfo.levelParams &&
              declarationOrigin env name == declarationOrigin env parent then some parent
          else none
      | _ => none

private def renderType (type : Expr) : MetaM String :=
  withOptions (fun options => options.setBool `pp.all true) do
    return (← Meta.ppExpr type).pretty

/-- Full declaration metadata, without recursively expanding dependency types. -/
def declarationSummary (name : Name) : MetaM Json := do
  let env ← getEnv
  let some info := env.checked.get.find? name
    | throwError "no checked kernel declaration named {name}"
  return Json.mkObj [
    ("name", .str name.toString),
    ("originModule", .str (declarationOrigin env name).toString),
    ("kind", .str (declarationKind info)),
    ("checkingRole", .str (checkingRole info)),
    ("hasCheckedBody", .bool (hasCheckedBody info)),
    ("universeParameters", namesJson info.levelParams.toArray),
    ("fullType", .str (← renderType info.type)),
    ("unsafe", .bool info.isUnsafe),
    ("partial", .bool info.isPartial),
    ("runtimeCounterpart", match runtimeCounterpart? env name with
      | some parent => .str parent.toString
      | none => .null)
  ]

/-- Primitive axioms actually reachable through both the type and proof/body.
The entry for every axiom includes its type and owning module. -/
def declarationManifest (name : Name) : MetaM Json := do
  let env ← getEnv
  let some info := env.checked.get.find? name
    | throwError "no checked kernel declaration named {name}"
  if info.isUnsafe || info.isPartial then
    throwError "{name} is unsafe or partial; no checked mathematical body is certified"
  let summary ← declarationSummary name
  let dependencies ← collectAxioms name
  let axioms ← dependencies.mapM declarationSummary
  return Json.mkObj [
    ("declaration", summary),
    ("transitiveAxioms", .arr axioms),
    ("containsAdmission", .bool (dependencies.contains ``sorryAx))
  ]

/-- The host kernel is part of the interpretation's checking foundation.
Its rules are distinguished from axiom declarations collected above. -/
def checkingEnvironment : CoreM Json := do
  let env ← getEnv
  return Json.mkObj [
    ("leanVersion", .str Lean.versionString),
    ("mainModule", .str env.mainModule.toString),
    ("importClosure", namesJson env.header.moduleNames),
    ("kernelQuotientsInitialized", .bool env.checked.get.quotInit),
    ("kernelRules", .arr #[
      .str "universe-polymorphic dependent function types and cumulative sorts",
      .str "inductive families and their kernel-checked eliminators",
      .str "impredicative Prop and kernel proof irrelevance",
      .str "definitional conversion; quotient primitives when initialized"
    ]),
    ("axiomScope", .str
      "transitive primitive axiom constants; hypotheses remain in each complete type"),
    ("interpretationScope", .str
      "the listed declarations and their host checking environment; no profile is selected")
  ]

/-- Assemble the actual declaration manifests under one recorded host. -/
def declarationsManifest (names : Array Name) : MetaM Json := do
  return Json.mkObj [
    ("schemaVersion", toJson (2 : Nat)),
    ("checkingEnvironment", ← checkingEnvironment),
    ("declarations", .arr (← names.mapM declarationManifest))
  ]

/-- Inspect an entire imported module by recorded ownership rather than a
namespace prefix. Nonlogical and compiler-only entries are never assigned an
empty proof-dependency list or counted as safe mathematical declarations. -/
def moduleManifest (moduleName : Name) : MetaM Json := do
  let env ← getEnv
  let some moduleIndex := env.header.moduleNames.toList.idxOf? moduleName
    | throwError "module {moduleName} is not imported in this environment"
  let moduleData := env.header.moduleData[moduleIndex]!
  let names := (moduleData.constNames ++ moduleData.extraConstNames).toList.eraseDups
    |>.toArray.qsort Name.lt
  let mut checked := #[]
  let mut checkedBodyCount : Nat := 0
  let mut nonLogical := #[]
  let mut compilerOnly := #[]
  for name in names do
    if let some info := env.checked.get.find? name then
      if info.isUnsafe || info.isPartial then
        nonLogical := nonLogical.push (← declarationSummary name)
      else
        checked := checked.push (← declarationManifest name)
        if hasCheckedBody info then checkedBodyCount := checkedBodyCount + 1
    else if moduleData.extraConstNames.contains name then
      compilerOnly := compilerOnly.push name
    else
      throwError "module {moduleName} has no checked kernel entry for {name}"
  return Json.mkObj [
    ("schemaVersion", toJson (2 : Nat)),
    ("checkingEnvironment", ← checkingEnvironment),
    ("ownerModule", .str moduleName.toString),
    ("kernelDeclarationCount", toJson checked.size),
    ("checkedBodyDeclarationCount", toJson checkedBodyCount),
    ("nonLogicalDeclarationCount", toJson nonLogical.size),
    ("declarations", .arr checked),
    ("nonLogicalDeclarations", .arr nonLogical),
    ("compilerOnlyDeclarations", namesJson compilerOnly)
  ]

syntax (name := foundationManifestCommand)
  "#foundation_manifest " "[" ident,* "]" : command

@[command_elab foundationManifestCommand]
def elaborateDeclarationManifest : CommandElab := fun stx => do
  let manifest ← liftTermElabM do
    let names ← stx[2].getSepArgs.mapM fun identifier =>
      realizeGlobalConstNoOverloadWithInfo identifier
    declarationsManifest names
  logInfo manifest.pretty

syntax (name := foundationModuleManifestCommand)
  "#foundation_manifest_module " ident : command

@[command_elab foundationModuleManifestCommand]
def elaborateModuleManifest : CommandElab := fun stx => do
  let manifest ← liftTermElabM <| moduleManifest stx[1].getId
  logInfo manifest.pretty

end Mettapedia.Logic.KernelFoundationManifest
