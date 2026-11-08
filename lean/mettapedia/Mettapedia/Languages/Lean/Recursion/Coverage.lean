import Mettapedia.Languages.Lean.Recursion.Wrappers
import Mettapedia.Languages.Lean.Declarations.Reader

/-!
# Recursion coverage of the source code-equation closure

Follow computational constants in equation right-hand sides. Types and proof
terms are not executable dependencies. Definitions without equation theorems
are followed through their bodies. The audited requirement is every
well-founded definition and every explicit proof-argument function. Ordinary
structural recursion without proof parameters remains in the existing
code-equation lane. Nonrecursive proof interfaces are emitted separately.
-/

namespace Mettapedia.Languages.Lean.Recursion.Coverage

open _root_.Lean Meta

partial def dependencies (expression : Expr) : MetaM NameSet := do
  let expression := expression.consumeMData
  if (← isProof expression) || (← isType expression) then return {}
  match expression with
  | .lam name type body binder =>
      withLocalDecl name binder type fun x => dependencies (body.instantiate1 x)
  | .letE name type value body _ =>
      let first ← dependencies value
      withLetDecl name type value fun x => return first.union (← dependencies (body.instantiate1 x))
  | .app .. =>
      if expression.getAppFn.isLambda then return ← dependencies expression.headBeta
      let mut result := match expression.getAppFn.constName? with
        | some name => ({} : NameSet).insert name
        | none => {}
      for argument in expression.getAppArgs do result := result.union (← dependencies argument)
      return result
  | .const name _ => return ({} : NameSet).insert name
  | .proj _ _ value => dependencies value
  | _ => return {}

structure Finding where
  source : Name
  implementation : Name
  required : Bool
  recorded : Bool
  recursive : Bool
  deriving Repr, Inhabited

def auditWith (records : Array Derive.Record) (wrappers : Array Wrappers.Record)
    (roots : Array Name) : MetaM (Array Finding) := do
  let mut seen : NameSet := {}
  let mut queue := roots
  let mut findings := #[]
  while !queue.isEmpty do
    let name := queue.back!
    queue := queue.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some (.defnInfo info) := (← getEnv).find? name | continue
    if info.safety != .safe || (← Declarations.erasedType info.type) then continue
    let proofArguments ← forallTelescope info.type fun parameters _ => parameters.anyM isProof
    let finding ← Inspect4331.measured name fun reading => do
      let required := reading.method != .natBrec || proofArguments
      let recorded := records.any (fun entry => entry.source == name || entry.implementation == name) ||
        wrappers.any (·.source == name)
      pure (Finding.mk name reading.implementation required recorded true)
    if let some finding := finding then findings := findings.push finding
    else
      let nested := info.value.getUsedConstants.any (fun dependency =>
        dependency == ``WellFounded.fix || dependency == ``WellFounded.Nat.fix)
      if proofArguments || nested then
        findings := findings.push ⟨name, name, true,
          records.any (·.source == name) || wrappers.any (·.source == name), nested⟩
    let mut called : NameSet := {}
    if let some equations ← getEqnsFor? name then
      for equation in equations do
        let found ← forallTelescope (← getConstInfo equation).type fun _ body => do
          let some (_, _, right) := body.eq? | throwError "non-equation in code-equation closure: {equation}"
          dependencies right
        called := called.union found
    else
      called := ← dependencies info.value
    queue := queue ++ called.toList.toArray
  return findings.qsort (fun a b => a.source.toString < b.source.toString)

def audit (roots : Array Name) : MetaM (Array Finding) := do
  auditWith (Derive.registry.getState (← getEnv)) (Wrappers.registry.getState (← getEnv)) roots

end Mettapedia.Languages.Lean.Recursion.Coverage
