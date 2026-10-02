import Mettapedia.Languages.MeTTa.OSLFCore.Atom
import Lean

/-!
# Kernel-checked replay of finite Atom runs

Native evaluation supplies candidate states only. Safe constructor/literal
snapshots, their initial-state equality, every transition, and optional
per-state invariant checks are independently checked by Lean's kernel.
The supplied equations compose these receipts for the actual runner.
-/

open Lean Meta Elab Command Term
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

namespace Mettapedia.Languages.ProcessCalculi.MORK.CheckedAtomReplay

/-- Equations of an existing runner and its state-threaded invariant check.
No executable realization is defined by this record. -/
structure Spec where
  step : List Atom → Option (List Atom)
  run : Nat → List Atom → List Atom × Nat
  runZero : ∀ space, run 0 space = (space, 0)
  runStep : ∀ {fuel used : Nat} {space next final : List Atom},
    step space = some next → run fuel next = (final, used) →
    run (fuel + 1) space = (final, used + 1)
  runStop : ∀ {space}, step space = none → ∀ fuel, run fuel space = (space, 0)
  check : List Atom → Bool
  checkRun : Nat → List Atom → Bool
  checkZero : ∀ {space}, check space = true → checkRun 0 space = true
  checkStep : ∀ {fuel : Nat} {space next : List Atom},
    check space = true → step space = some next → checkRun fuel next = true →
    checkRun (fuel + 1) space = true
  checkStop : ∀ {space}, check space = true → step space = none →
    ∀ fuel, checkRun fuel space = true

meta section

private def checkedOptions (options : Options) : Options :=
  debug.skipKernelTC.set (Elab.async.set options false) false

private def requireSafe (type value : Expr) : TermElabM Unit := do
  let environment ← getEnv
  if type.hasSorry || value.hasSorry then
    throwError "Kernel replay certificates cannot contain admitted proofs"
  if environment.hasUnsafe type || environment.hasUnsafe value then
    throwError "Kernel replay certificates cannot mention unsafe declarations"

private def atomType : Expr := mkConst ``Atom
private def spaceType : Expr := mkApp (mkConst ``List [.zero]) atomType

private def groundedExpr : GroundedValue → Expr
  | .int n => mkApp (mkConst ``GroundedValue.int) (toExpr n)
  | .string s => mkApp (mkConst ``GroundedValue.string) (mkStrLit s)
  | .bool b => mkApp (mkConst ``GroundedValue.bool) (toExpr b)
  | .custom n s => mkApp2 (mkConst ``GroundedValue.custom) (mkStrLit n) (mkStrLit s)

private partial def atomExpr : Atom → Expr
  | .symbol s => mkApp (mkConst ``Atom.symbol) (mkStrLit s)
  | .var s => mkApp (mkConst ``Atom.var) (mkStrLit s)
  | .grounded g => mkApp (mkConst ``Atom.grounded) (groundedExpr g)
  | .expression xs => mkApp (mkConst ``Atom.expression) (listExpr xs)
where
  listExpr : List Atom → Expr
    | [] => mkApp (mkConst ``List.nil [.zero]) atomType
    | x :: xs => mkApp3 (mkConst ``List.cons [.zero]) atomType
        (atomExpr x) (listExpr xs)

private def quoteSpace (space : List Atom) : TermElabM Expr := do
  let name ← mkAuxDeclName `_atomReplayState
  withOptions checkedOptions <| addDecl <| .defnDecl {
    name, levelParams := [], type := spaceType, value := atomExpr.listExpr space,
    hints := .regular 0, safety := .safe }
  return mkConst name

private def closeCertificate (proof : Expr) : TermElabM Expr := do
  let proof ← instantiateMVars proof
  let type ← inferType proof
  requireSafe type proof
  let name ← withOptions checkedOptions <| mkAuxLemma [] type proof
  return mkConst name

private def kernelCertificate (type : Expr) : TermElabM Expr := do
  closeCertificate (← mkDecideProof type)

private def field (spec : Expr) (name : Name) : Expr := mkApp (mkConst name) spec

private def addProof (name : Name) (proof : Expr) : TermElabM Unit := do
  let proof ← instantiateMVars proof
  let type ← Core.betaReduce (← inferType proof)
  requireSafe type proof
  withOptions checkedOptions <| addDecl <| .thmDecl {
    name, levelParams := [], type, value := proof }

/-- Transfer a certificate across an equality of unapplied function heads.
This avoids converting fully applied recursive runners during elaboration. -/
private def actualHeadCertificate (original actual fuel source proof : Expr) :
    TermElabM Expr := do
  let headType ← mkEq original actual
  let headProof ← mkEqRefl actual
  requireSafe headType headProof
  let headName ← withOptions checkedOptions <| mkAuxLemma [] headType headProof
  let applyFunction := mkLambda `function .default (← inferType original)
    (mkApp2 (mkBVar 0) fuel source)
  let applied ← closeCertificate (← mkAppM ``congrArg
    #[applyFunction, Lean.mkConst headName])
  mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[applied], proof]

private def candidateSource (source : Expr) : TermElabM (List Atom) := do
  try
    unsafe evalExpr (List Atom) spaceType source
      (safety := .unsafe) (checkMeta := false)
  catch _ =>
    -- Projection normalization can erase noncomputable type-index arguments.
    -- The original expression still supplies the independent initial equality.
    let projected ← withTransparency .all <| reduce source
    unsafe evalExpr (List Atom) spaceType projected
      (safety := .unsafe) (checkMeta := false)

private def replay (name : Name) (specStx fuelStx sourceStx : TSyntax `term)
    (checkInvariant : Bool) : CommandElabM Unit := do
  liftTermElabM do
    let spec ← elabTermEnsuringType specStx (mkConst ``Spec)
    let fuelExpr ← elabTermEnsuringType fuelStx (mkConst ``Nat)
    let source ← elabTermEnsuringType sourceStx spaceType
    synthesizeSyntheticMVarsNoPostponing
    let spec ← instantiateMVars spec
    let fuelExpr ← instantiateMVars fuelExpr
    let source ← instantiateMVars source
    let step := field spec ``Spec.step
    let run := field spec ``Spec.run
    let check := field spec ``Spec.check
    let checkRun := field spec ``Spec.checkRun
    let specValue ← whnf spec
    unless specValue.isAppOfArity ``Spec.mk 10 do
      throwError "Replay specification did not reduce to its constructor"
    let actualRun := specValue.getAppArgs[1]!
    let actualCheckRun := specValue.getAppArgs[6]!
    let stepType ← mkArrow spaceType (mkApp (mkConst ``Option [.zero]) spaceType)
    -- These evaluations select candidate data. Their results are not proofs.
    let fuel ← unsafe evalExpr Nat (mkConst ``Nat) fuelExpr
      (safety := .unsafe) (checkMeta := false)
    let mut actual ← candidateSource source
    let nextCandidate ← unsafe evalExpr (List Atom → Option (List Atom)) stepType step
      (safety := .unsafe) (checkMeta := false)
    let initial ← quoteSpace actual
    let initialType ← mkEq source initial
    let initialProof ← elabTerm (← `(by cbv)) (some initialType)
    synthesizeSyntheticMVarsNoPostponing
    let initialProof ← instantiateMVars initialProof
    requireSafe initialType initialProof
    let initialName ← withOptions checkedOptions <|
      mkAuxLemma [] initialType initialProof
    let initialProof : Expr := Lean.mkConst initialName
    let mut state := initial
    let mut receipts : Array (Expr × Option Expr × Expr) := #[]
    let mut stopped := false
    for _ in [:fuel] do
      let here ← if checkInvariant then
          some <$> kernelCertificate (← mkEq (mkApp check state) (toExpr true))
        else pure none
      match nextCandidate actual with
      | none =>
          let stop ← kernelCertificate (← mkEq (mkApp step state)
            (mkApp (mkConst ``Option.none [.zero]) spaceType))
          receipts := receipts.push (state, here, stop)
          stopped := true
          break
      | some next =>
          let quoted ← quoteSpace next
          let moved ← kernelCertificate (← mkEq (mkApp step state)
            (mkApp2 (mkConst ``Option.some [.zero]) spaceType quoted))
          receipts := receipts.push (state, here, moved)
          state := quoted
          actual := next
    let used := if stopped then receipts.size - 1 else receipts.size
    let remaining := fuel - used
    let mut runProof ← if stopped then do
        let (_, _, stop) := receipts.back!
        mkAppM ``Spec.runStop #[spec, stop, toExpr remaining]
      else
        mkAppM ``Spec.runZero #[spec, state]
    runProof ← closeCertificate runProof
    let mut checkProof : Option Expr ← if checkInvariant then do
        let proof ← if stopped then do
            let (_, here, stop) := receipts.back!
            mkAppM ``Spec.checkStop #[spec, here.get!, stop, toExpr remaining]
          else do
            let here ← kernelCertificate (← mkEq (mkApp check state) (toExpr true))
            mkAppM ``Spec.checkZero #[spec, here]
        some <$> closeCertificate proof
      else pure none
    -- Closing each tail prevents repeated checking of a long transparent proof.
    for index in [:used] do
      let (_, here, moved) := receipts[used - 1 - index]!
      runProof ← closeCertificate (← mkAppM ``Spec.runStep #[spec, moved, runProof])
      if let some checked := checkProof then
        checkProof := some (← closeCertificate
          (← mkAppM ``Spec.checkStep #[spec, here.get!, moved, checked]))
    let runFunction := mkLambda `space .default spaceType
      (mkApp2 run fuelExpr (mkBVar 0))
    runProof ← mkAppM ``Eq.trans #[← mkAppM ``congrArg #[runFunction, initialProof], runProof]
    runProof ← actualHeadCertificate run actualRun fuelExpr source runProof
    if let some checked := checkProof then
      let checkFunction := mkLambda `space .default spaceType
        (mkApp2 checkRun fuelExpr (mkBVar 0))
      let checked ← mkAppM ``Eq.trans
        #[← mkAppM ``congrArg #[checkFunction, initialProof], checked]
      checkProof := some (← actualHeadCertificate checkRun actualCheckRun fuelExpr source checked)
    withOptions checkedOptions <| addDecl <| .defnDecl {
      name := name ++ `final, levelParams := [], type := spaceType, value := state,
      hints := .regular 0, safety := .safe }
    addProof (name ++ `run) runProof
    if let some checked := checkProof then addProof (name ++ `invariant) checked
    logInfo m!"Kernel-checked {used} transitions for {name}"

/-- Generate exact-run and visited-state invariant certificates. -/
elab "kernel_atom_replay " name:ident " using " specStx:term:max
    " for " fuelStx:term:max " from " sourceStx:term : command => do
  replay ((← getCurrNamespace) ++ name.getId) specStx fuelStx sourceStx true

/-- Generate only an exact-run certificate, without making an invariant claim. -/
elab "kernel_atom_run " name:ident " using " specStx:term:max
    " for " fuelStx:term:max " from " sourceStx:term : command => do
  replay ((← getCurrNamespace) ++ name.getId) specStx fuelStx sourceStx false

end

end Mettapedia.Languages.ProcessCalculi.MORK.CheckedAtomReplay
