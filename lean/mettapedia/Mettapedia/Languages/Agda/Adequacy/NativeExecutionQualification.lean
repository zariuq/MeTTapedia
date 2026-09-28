import Mettapedia.Languages.Agda.Adequacy.NativeFoundationQualification
import Mettapedia.Languages.Agda.Adequacy.NativeProducedData
import Mettapedia.Languages.Agda.Native.SyntaxControls
import Mettapedia.Languages.Agda.Native.ProofControls
import Mettapedia.Languages.Agda.Native.SelectionControls
import Mettapedia.OSLF.Syntax.FiniteRuleLabelledProofWireControls
import Mettapedia.OSLF.Syntax.FiniteRuleSearchWire
import Mettapedia.OSLF.Syntax.FiniteRuleSearchControls
import Mettapedia.OSLF.Syntax.FiniteRuleProofDataControls

/-!
# Native proof-execution qualification

This extends the mathematical foundation with partial structural proof
production, exact native proof data, and independent source soundness for
accepted data. Every selected module origin and the types and bodies of its
transitive dependencies are audited, including opaque bodies.

The bounded Agda selector has partial coverage. Failure to produce a tree is
incomplete, not a negative typing decision. Rejected wire data rejects that
certificate only. JSON transport, external Agda reflection, declaration
admission, complete conversion and C execution are outside this theorem scope.
-/

open Lean Lean.Elab.Command

private structure BodyAuditState where
  seen : NameSet := {}
  opaqueBodies : Nat := 0

private partial def auditBodyConstant (env : Environment) (name : Name) :
    StateT BodyAuditState (Except String) Unit := do
  if (← get).seen.contains name then return
  modify fun state => { state with seen := state.seen.insert name }
  let inspect (value : Expr) := value.getUsedConstants.forM (auditBodyConstant env)
  match env.checked.get.find? name with
  | none => throw s!"Missing checked constant: {name}"
  | some (.axiomInfo value) =>
      unless [``propext, ``Quot.sound].contains name do
        throw s!"Excess axiom: {name}"
      inspect value.type
  | some (.defnInfo value) => inspect value.type; inspect value.value
  | some (.thmInfo value) => inspect value.type; inspect value.value
  | some (.opaqueInfo value) =>
      modify fun state => { state with opaqueBodies := state.opaqueBodies + 1 }
      inspect value.type
      inspect value.value
  | some (.quotInfo _) => pure ()
  | some (.ctorInfo value) => inspect value.type
  | some (.recInfo value) => inspect value.type
  | some (.inductInfo value) =>
      inspect value.type
      value.ctors.forM (auditBodyConstant env)

run_cmd do
  let modules := [
    `Mettapedia.OSLF.Syntax.FiniteRuleSearch,
    `Mettapedia.OSLF.Syntax.FiniteRuleSearchCompleteness,
    `Mettapedia.OSLF.Syntax.FiniteRuleSearchControls,
    `Mettapedia.Languages.Agda.Native.Selection,
    `Mettapedia.Languages.Agda.Native.SelectionControls,
    `Mettapedia.Languages.Agda.Adequacy.NativeProductionSoundness,
    `Mettapedia.OSLF.Syntax.FiniteRuleLabelledProofWire,
    `Mettapedia.OSLF.Syntax.FiniteRuleLabelledProofWireControls,
    `Mettapedia.OSLF.Syntax.FiniteRuleSearchWire,
    `Mettapedia.OSLF.Syntax.FiniteRuleProofData,
    `Mettapedia.OSLF.Syntax.FiniteRuleProofDataControls,
    `Mettapedia.OSLF.Syntax.BindingWireData,
    `Mettapedia.OSLF.Syntax.BindingWireString,
    `Mettapedia.OSLF.Syntax.BindingWireCodec,
    `Mettapedia.OSLF.Syntax.BindingTelescopeWireCodec,
    `Mettapedia.Languages.Agda.Native.SyntaxCodec,
    `Mettapedia.Languages.Agda.Native.ParameterCodec,
    `Mettapedia.Languages.Agda.Native.JudgmentCodec,
    `Mettapedia.Languages.Agda.Native.CoreRuleCodec,
    `Mettapedia.Languages.Agda.Native.SpineRuleCodec,
    `Mettapedia.Languages.Agda.Native.RuleCodec,
    `Mettapedia.Languages.Agda.Native.ProofCodec,
    `Mettapedia.Languages.Agda.Native.SyntaxControls,
    `Mettapedia.Languages.Agda.Native.ProofControls,
    `Mettapedia.Languages.Agda.Adequacy.NativeProducedData,
    `Mettapedia.OSLF.Syntax.FiniteRuleProofWire,
    `Mettapedia.OSLF.Syntax.FiniteRuleProofWireControls]
  let env := (← getEnv).setExporting false
  let selected := env.constants.toList.filterMap fun (name, _) =>
    match env.getModuleIdxFor? name |>.bind (env.header.modules[·]?) with
    | some origin => if modules.contains origin.module then some name else none
    | none => none
  for origin in modules do
    let count := selected.countP fun name =>
      ((env.getModuleIdxFor? name).bind (env.header.modules[·]?)).any (·.module == origin)
    if count == 0 then throwError "Missing module origin: {origin}"
    logInfo m!"ORIGIN AUDIT: {origin}: {count} declarations."
  match (selected.forM (auditBodyConstant env)).run {} with
  | .error message => throwError "{message}"
  | .ok (_, state) =>
      logInfo m!"BODY AUDIT: {selected.length} selected declarations; {state.seen.size} transitive checked constants; {state.opaqueBodies} opaque bodies; axioms <= [propext, Quot.sound]."
