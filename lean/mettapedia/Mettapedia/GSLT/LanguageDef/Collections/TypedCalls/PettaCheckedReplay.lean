import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaReplayWitnesses
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeEquationScalarReduction
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTerminalReadout
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSourceClassGuardReduction

/-!
# Kernel-checked finite runs of the actual scoped typed machine

Native evaluation proposes transitions only. Safe data declarations and every
one-step equality are independently checked, then composed through the existing
machine-run theorems. No evaluated proposition, runtime Boolean or supplied
whole-run equality is accepted as a proof.

The witness codec retains the initial store expression. A proposed store
change cannot pass the step check under that codec; this is a read-only-store
replay tool, not an implementation of mutable-store serialization.

An exhausted prefix exposes its `residual`; a suspension exposes its
`retained` state. These are data aliases. The accompanying `run` theorem,
not the alias alone, certifies the actual execution and its disposition.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckedReplay

open Lean Meta Elab Command Term
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open PettaOccurrenceOverlay
open PettaReplayWitnesses

private def prependEvents {Event Result : Type} (events : List Event) (reply : List Event × Result) : List Event × Result :=
  (events ++ reply.1, reply.2)

initialize registerTraceClass `Meta.Tactic.pettaReplay

meta section

private def checkedOptions (options : Options) : Options :=
  debug.skipKernelTC.set (Elab.async.set options false) false

private def requireSafe (type value : Expr) : TermElabM Unit := do
  let environment ← getEnv
  if type.hasSorry || value.hasSorry || type.hasMVar || value.hasMVar || type.hasFVar || value.hasFVar then
    throwError "Replay certificates must be closed and contain no admitted proof"
  if environment.hasUnsafe type || environment.hasUnsafe value then
    throwError "Replay certificates cannot depend on unsafe declarations"

private def closeProof (type proof : Expr) : TermElabM Expr := do
  let proof ← instantiateMVars proof
  let type ← instantiateMVars type
  requireSafe type proof
  let name ← withOptions checkedOptions <| mkAuxLemma [] type proof (cache := false)
  let axioms ← liftM (collectAxioms name : CoreM (Array Name))
  let extra := axioms.filter (· ∉ [``propext, ``Classical.choice, ``Quot.sound])
  unless extra.isEmpty do throwError "Replay certificate uses unsupported axioms: {extra.toList}"
  return mkConst name

private def closeCertificate (proof : Expr) : TermElabM Expr := do
  let proof ← instantiateMVars proof
  closeProof (← inferType proof) proof

private def quoteData (type value : Expr) : TermElabM Expr := do
  requireSafe type value
  let name ← mkAuxDeclName `_typedReplayData
  withOptions checkedOptions <| addAndCompile <| .defnDecl {
    name, levelParams := [], type, value, hints := .regular 0, safety := .safe }
  return mkConst name

private def proveAtomic (type : Expr) : TermElabM Expr := do
  let proof ← elabTerm (← `(by
    try dsimp only
    all_goals cbv
    all_goals simp_all [PettaReplayWitnesses.stringSet, Finset.ext_iff, or_comm, or_left_comm, or_assoc])) (some type)
  synthesizeSyntheticMVarsNoPostponing
  closeProof type proof

/-- Factor a typed terminal through its separately checked source readout.
Native values select a candidate lemma instance; every shape premise, read
and resulting transition still receives an ordinary kernel certificate. -/
private def terminalCertificate? (type machine state : Expr) (actual : State Unit) : TermElabM (Option Expr) := do
  let scope :: parents := actual.2.scopes | return none
  let (branchControl, context, origins) :: pending := scope.frontier | return none
  let frame :: outside := context.calls | return none
  unless branchControl.goals.isEmpty && frame.scopeDepth == actual.2.scopes.length do return none
  if frame.phase matches .nextArgument then return none
  let some environment := EagerDFS.Destination.resolve branchControl.bindings | return none
  let delivered := EagerDFS.Destination.read environment branchControl.destination
  let parts? ← withLocalDeclD `source stateType fun stateVariable => do
    let application ← whnf (← mkAppM ``Machine.step #[machine, stateVariable])
    let_expr Option.some _ step := application | return none
    unless step.isAppOfArity ``PettaOccurrenceOverlay.step 5 do return none
    let arguments := step.getAppArgs
    return some (arguments[1]!, arguments[2]!, arguments[3]!)
  let some (services, policy, program) := parts? | return none
  let shared : Array (Option Expr) :=
    #[some (mkConst ``Unit), some services, some policy, some program, some state,
      some (toExpr scope), some (toExpr parents), some (toExpr branchControl),
      some (toExpr context), some (toExpr origins), some (toExpr pending),
      some (toExpr frame), some (toExpr outside)]
  let remaining := match frame.phase with
    | .argument formal slot => #[some (toExpr formal), some (toExpr slot), some (toExpr delivered)]
    | .body => #[some (toExpr delivered)]
    | .nextArgument => #[]
  let theoremName := match frame.phase with
    | .argument _ _ => ``PettaTerminalReadout.argument
    | _ => ``PettaTerminalReadout.body
  let mut proof ← mkAppOptM theoremName (shared ++ remaining)
  for index in [:7] do
    let .forallE _ obligationType _ _ ← whnf (← inferType proof)
      | throwError "Expected a terminal readout premise"
    trace[Meta.Tactic.pettaReplay] "Checking terminal certificate field {index + 1}"
    let checked ← if index < 6 then do
        let_expr Eq _ left right := obligationType | proveAtomic obligationType
        if ← isDefEq left right then closeProof obligationType (← mkEqRefl left)
        else proveAtomic obligationType
      else proveAtomic obligationType
    proof := mkApp proof checked
  let closedProof ← closeCertificate (← instantiateMVars proof)
  let transitionType ← mkAppM ``PettaOccurrenceOverlay.Step #[mkConst ``Unit]
  let lift ← withLocalDeclD `transition transitionType fun transition => do
    mkLambdaFVars #[transition] (← mkSome transitionType transition)
  let lifted ← mkAppM ``congrArg #[lift, closedProof]
  let liftedType ← inferType lifted
  let_expr Eq _ _ reduced := liftedType | throwError "Expected a terminal transition equality"
  let_expr Eq _ _ expected := type | throwError "Expected a replay equation"
  let remaining ← proveAtomic (← mkEq reduced expected)
  let complete ← mkAppM ``Eq.trans #[lifted, remaining]
  trace[Meta.Tactic.pettaReplay] "Checked typed terminal through its actual readout"
  return some (← closeProof type complete)

private def proveStep (type machine state : Expr) (actual : State Unit) : TermElabM Expr := do
  if let some proof ← terminalCertificate? type machine state actual then return proof
  proveAtomic type

private def addProof (name : Name) (proof : Expr) : TermElabM Unit := do
  let proof ← instantiateMVars proof
  let type ← inferType proof
  requireSafe type proof
  withOptions checkedOptions <| addDecl <| .thmDecl {name, levelParams := [], type, value := proof}

private def parameterTypes : Array Expr :=
  #[stateType, toTypeExpr EagerDFS.Destination.CollectedAnswer, stateType, toTypeExpr Request]

private def transitionType : Expr := mkAppN (mkConst ``Transition) parameterTypes

private def outcomeType : Expr := mkApp3 (mkConst ``Outcome) stateType stateType (toTypeExpr Request)

private def replyType : Expr := mkApp2 (mkConst ``Prod [0, 0])
  (mkApp (mkConst ``List [0]) (toTypeExpr EagerDFS.Destination.CollectedAnswer)) outcomeType

private def sourceStep (machine state : Expr) : TermElabM Expr := mkAppM ``Machine.step #[machine, state]

private def runEquation (name : Name) (machine fuel step : Expr) : TermElabM Expr :=
  mkAppOptM name #[none, none, none, none, some machine, some fuel, none, none, some step]

private def replay (name : Name) (machineStx fuelStx initialStx : TSyntax `term) : CommandElabM Unit := do
  liftTermElabM do
    let machineType := mkAppN (mkConst ``Machine) parameterTypes
    let machine ← elabTermEnsuringType machineStx machineType
    let fuelExpr ← elabTermEnsuringType fuelStx (mkConst ``Nat)
    let initial ← elabTermEnsuringType initialStx stateType
    synthesizeSyntheticMVarsNoPostponing
    let machine ← instantiateMVars machine
    let fuelExpr ← instantiateMVars fuelExpr
    let initial ← instantiateMVars initial
    requireSafe machineType machine
    requireSafe (mkConst ``Nat) fuelExpr
    requireSafe stateType initial
    let config ← mkAppM ``Prod.snd #[initial]
    let world ← mkAppM ``EagerDFS.Configuration.world #[config]
    let store ← mkAppM ``EagerDFS.World.state #[world]
    let backing ← quoteData (← inferType store) store
    let backingName := backing.constName!
    -- These native computations propose data, never proofs.
    let fuel ← unsafe evalExpr Nat (mkConst ``Nat) fuelExpr
    let mut actual ← unsafe evalExpr (State Unit) stateType initial
    let stepType ← mkArrow stateType (mkApp (mkConst ``Option [0]) transitionType)
    let nativeStep ← unsafe evalExpr
      ((State Unit) → Option (Transition (State Unit) EagerDFS.Destination.CollectedAnswer (State Unit) Request))
      stepType (← mkAppM ``Machine.step #[machine])
    let mut state := initial
    let mut receipts : Array (Bool × Expr × Expr) := #[]
    let mut terminal : Option Expr := none
    for index in [:fuel] do
      let remaining := fuel - index - 1
      let observed := nativeStep actual
      match observed with
      | none =>
          let missing := mkApp (mkConst ``Option.none [0]) transitionType
          let checked ← proveStep (← mkEq (← sourceStep machine state) missing) machine state actual
          terminal := some (← closeCertificate (← mkAppOptM ``Machine.run_succ_stuck
            #[none, none, none, none, some machine, some (toExpr remaining), none, some checked]))
          break
      | some next =>
          let (constructor, fields, nextActual) ← match next with
            | .silent following => do
                let quoted ← quoteData stateType (stateExpr backingName following)
                pure (``Transition.silent, #[quoted], some following)
            | .publish events following => do
                let quoted ← quoteData stateType (stateExpr backingName following)
                pure (``Transition.publish, #[toExpr events, quoted], some following)
            | .finish verdict => do
                let quoted ← quoteData stateType (stateExpr backingName verdict)
                pure (``Transition.finish, #[quoted], none)
            | .fail events => pure (``Transition.fail, #[toExpr events], none)
            | .call request saved => do
                let quoted ← quoteData stateType (stateExpr backingName saved)
                pure (``Transition.call, #[toExpr request, quoted], none)
          let transition := mkAppN (mkConst constructor) (parameterTypes ++ fields)
          let proposed := mkApp2 (mkConst ``Option.some [0]) transitionType transition
          trace[Meta.Tactic.pettaReplay] "Checking transition {index + 1} for {name}"
          let checked ← proveStep (← mkEq (← sourceStep machine state) proposed) machine state actual
          if (index + 1) % 20 = 0 then
            logInfo m!"Checked transition {index + 1} for {name}"
          if let some following := nextActual then
            receipts := receipts.push (constructor == ``Transition.publish, checked,
              if constructor == ``Transition.publish then fields[0]! else mkApp (mkConst ``List.nil [0]) (toTypeExpr EagerDFS.Destination.CollectedAnswer))
            state := fields.back!
            actual := following
          else
            if constructor == ``Transition.call then
              withOptions checkedOptions <| addAndCompile <| .defnDecl {
                name := name ++ `retained, levelParams := [], type := stateType, value := fields[1]!,
                hints := .regular 0, safety := .safe }
            let theoremName := if constructor == ``Transition.finish then ``Machine.run_succ_finish
              else if constructor == ``Transition.call then ``Machine.run_succ_call else ``Machine.run_succ_fail
            let proof ← if constructor == ``Transition.call then
                mkAppOptM theoremName #[none, none, none, none, some machine, some (toExpr remaining), none, none, none, some checked]
              else runEquation theoremName machine (toExpr remaining) checked
            terminal := some (← closeCertificate proof)
            break
    let mut proof ← match terminal with
      | some proof => pure proof
      | none => do
          let exhausted := mkAppN (mkConst ``Outcome.exhausted)
            #[stateType, stateType, toTypeExpr Request, state]
          let empty := mkApp (mkConst ``List.nil [0]) (toTypeExpr EagerDFS.Destination.CollectedAnswer)
          let result := mkApp4 (mkConst ``Prod.mk [0, 0])
            (mkApp (mkConst ``List [0]) (toTypeExpr EagerDFS.Destination.CollectedAnswer)) outcomeType empty exhausted
          let run ← mkAppM ``Machine.run #[machine, toExpr (0 : Nat), state]
          closeProof (← mkEq run result) (← mkEqRefl result)
    for reverse in [:receipts.size] do
      let index := receipts.size - reverse - 1
      let (published, checked, events) := receipts[index]!
      let tailFuel := fuel - index - 1
      let prefixProof ← if published then
          mkAppOptM ``Machine.run_succ_publish
            #[none, none, none, none, some machine, some (toExpr tailFuel), none, none, none, some checked]
        else runEquation ``Machine.run_succ_silent machine (toExpr tailFuel) checked
      if published then
        let append ← withLocalDeclD `reply replyType fun reply => do
          mkLambdaFVars #[reply] (← mkAppM ``prependEvents #[events, reply])
        proof ← closeCertificate (← mkAppM ``Eq.trans #[prefixProof, ← mkAppM ``congrArg #[append, proof]])
      else
        proof ← closeCertificate (← mkAppM ``Eq.trans #[prefixProof, proof])
    if terminal.isNone then
      requireSafe stateType state
      withOptions checkedOptions <| addAndCompile <| .defnDecl {
        name := name ++ `residual, levelParams := [], type := stateType, value := state,
        hints := .regular 0, safety := .safe }
    addProof (name ++ `run) proof
    logInfo m!"Kernel-checked {receipts.size} continuing transitions for {name}"

elab "kernel_petta_run " name:ident " using " machine:term:max " for " fuel:term:max " from " initial:term : command => do
  replay ((← getCurrNamespace) ++ name.getId) machine fuel initial

end

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCheckedReplay
