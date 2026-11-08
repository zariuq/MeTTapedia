import Mettapedia.Languages.Lean.Recursion.Derive

/-!
# Source wrappers around represented recursion implementations

A wrapper is read from its actual definition. Its called implementation is
replaced by the already-proved accessible interpretation. Congruence transports
the implementation equality through that exact source context. A dependency
that does not occur is refused rather than yielding an identity construction.
-/

namespace Mettapedia.Languages.Lean.Recursion.Wrappers

open _root_.Lean Meta Elab Command

structure Record where
  source : Name
  accessible : Name
  bridge : Name
  dependencies : Array Name
  unfoldings : Array (Name × Name)
  deriving Inhabited

initialize registry : SimplePersistentEnvExtension Record (Array Record) ←
  registerSimplePersistentEnvExtension {
    name := `Mettapedia.Languages.Lean.Recursion.Wrappers.registry
    addImportedFn := fun entries => entries.foldl (· ++ ·) #[]
    addEntryFn := Array.push }

def implementation (source : Name) : MetaM (Name × Name) := do
  if let some entry := (Derive.registry.getState (← getEnv)).find? (·.source == source) then
    return (entry.accessible, entry.functionBridge)
  if let some entry := (registry.getState (← getEnv)).find? (·.source == source) then
    return (entry.accessible, entry.bridge)
  throwError "no represented recursion implementation for {source}"

def generate (source baseName : Name) (dependencies : Array Name) : MetaM Unit := do
  let .defnInfo info ← getConstInfo source | throwError "wrapper source is not a definition: {source}"
  if dependencies.isEmpty then throwError "wrapper has no implementation dependencies"
  let levels := info.levelParams
  let mut value := info.value
  let mut proof ← mkEqRefl value
  for dependency in dependencies do
    let dependencyInfo ← getConstInfo dependency
    unless dependencyInfo.levelParams.isEmpty do
      throwError "polymorphic wrapper dependency needs a universe-instance inventory: {dependency}"
    let (represented, bridge) ← implementation dependency
    let original := mkConst dependency
    let replacement := mkConst represented
    let context ← withLocalDeclD `implementation dependencyInfo.type fun parameter => do
      let changed := value.replace fun expression => if expression == original then some parameter else none
      unless changed.hasFVar do throwError "wrapper does not call its declared dependency: {dependency}"
      mkLambdaFVars #[parameter] changed
    let step ← mkCongrArg context (mkConst bridge)
    proof ← mkEqTrans step proof
    value := value.replace fun expression => if expression == original then some replacement else none
  let accessible := baseName ++ `accessible
  let bridge := baseName ++ `bridge
  Derive.define accessible levels value
  Derive.prove bridge levels
    (← mkEq (mkConst accessible (levels.map Level.param)) (mkConst source (levels.map Level.param))) proof
  let unfoldings ← Derive.transportEquations source accessible bridge baseName
  modifyEnv fun env => registry.addEntry env ⟨source, accessible, bridge, dependencies, unfoldings⟩

syntax (name := deriveWrapper) "derive_recursion_wrapper " ident " using " "[" ident,* "]" " as " ident : command

@[command_elab deriveWrapper] def elabDeriveWrapper : CommandElab
  | `(derive_recursion_wrapper $source:ident using [$dependencies:ident,*] as $baseName:ident) => do
      let source ← liftCoreM (realizeGlobalConstNoOverloadWithInfo source)
      let dependencies ← dependencies.getElems.mapM fun syntaxTree =>
        liftCoreM (realizeGlobalConstNoOverloadWithInfo syntaxTree)
      let baseName := (← getCurrNamespace) ++ baseName.getId
      liftTermElabM (generate source baseName dependencies)
  | _ => throwUnsupportedSyntax

end Mettapedia.Languages.Lean.Recursion.Wrappers
