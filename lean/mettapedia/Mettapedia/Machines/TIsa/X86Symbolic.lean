import Mettapedia.Machines.TIsa.X86StateFrame
import Mettapedia.Machines.TIsa.X86FuelPrefix
import Mettapedia.Machines.TIsa.X86MovCapture
import Mettapedia.Machines.TIsa.X86FrameStore
import Mettapedia.Machines.TIsa.Memory
import Mettapedia.Machines.TIsa.Funding
import Mathlib.Data.Finset.Range
import Lean.Elab.Tactic

/-!
# Proof-producing symbolic stepping of the pinned Sail x86 model

The evaluator reduces only a blocked match's discriminator. Register and memory
facts come from the local proof context; updates use the byte-map laws. Recursive
model code uses its generated unfolding equations. No instruction-specific
execution theorem or second decoder is used. Every reduction produces an equality
that Lean's kernel checks. The frame tactic checks the resulting state updates.

Unknown branch conditions, absent facts and unsupported model actions leave an
explicit proof failure. This tool does not establish whole-emitter refinement.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

open Lean Meta Elab Tactic

namespace Mettapedia.Machines.TIsa.X86Symbolic

open _root_.X86Registers

simproc_decl reduceClosedNat (_) := fun e => do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then return .continue
  unless (← inferType e).isConstOf ``Nat do return .continue
  let reduced ← withTransparency .all (whnf e)
  if reduced == e then return .continue
  match reduced with
  | .lit (.natVal _) => return .done { expr := reduced }
  | _ => return .continue

theorem register_insert_other (mapping : Std.ExtDHashMap Register RegisterType)
    (written observed : Register) (value : RegisterType written) (outside : observed ≠ written) :
    (mapping.insert written value).get? observed = mapping.get? observed := by
  simp [Std.ExtDHashMap.get?_insert, Ne.symm outside]

theorem byte_insert_other (mapping : Std.ExtHashMap Nat (BitVec 8))
    (written observed : Nat) (value : BitVec 8) (outside : observed ≠ written) :
    (mapping.insert written value)[observed]? = mapping[observed]? := by
  simp [Std.ExtHashMap.getElem?_insert, Ne.symm outside]

theorem byte_insert (mapping : Std.ExtHashMap Nat (BitVec 8))
    (written observed : Nat) (value : BitVec 8) :
    (mapping.insert written value).get? observed =
      if written == observed then some value else mapping.get? observed := by
  change (mapping.insert written value)[observed]? =
    if written == observed then some value else mapping[observed]?
  exact Std.ExtHashMap.getElem?_insert

private theorem wordRepack {width : Nat} (value : BitVec width) :
    BitVec.ofNat width value.toNat = value := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt value.isLt]

private partial def structuralNat? (expression : Expr) (remaining : Nat) : MetaM (Option Nat) := do
  if remaining == 0 then return none
  let value ← withTransparency .all (whnf expression)
  if let .lit (.natVal number) := value then return some number
  if value.isConstOf ``Nat.zero then return some 0
  if value.isAppOfArity ``Nat.succ 1 then
    return (← structuralNat? value.appArg! (remaining - 1)).map (· + 1)
  return none

private def canonicalByteRhs (rhs : Expr) : MetaM Expr := do
  let result ← withTransparency .all (whnf rhs)
  unless result.isAppOfArity ``Option.some 2 do return rhs
  let value := result.appArg!
  let byteType := mkApp (mkConst ``BitVec) (mkNatLit 8)
  unless ← withReducible (isDefEq (← inferType value) byteType) do return rhs
  unless value.isAppOfArity ``BitVec.ofNat 2 do return rhs
  let number ← withCanUnfoldPred (fun config info => do
      if info.name == ``BitVec.toNat then return false
      canUnfoldDefault config info) do
    withTransparency .all (whnf value.appArg!)
  let some number ← getNatValue? number | return rhs
  let literal := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 8) (mkNatLit number)
  let canonical ← mkAppM ``Option.some #[literal]
  unless ← withTransparency .all (isDefEq rhs canonical) do return rhs
  return canonical

/-- Materialize finite read facts, preserving unknown byte values as symbolic data. -/
elab "tisa_sail_bytes" "[" names:ident,* "]" : tactic => withMainContext do
  let mut goal ← getMainGoal
  for name in names.getElems do
    let original ← getLocalDeclFromUserName name.getId
    let .forallE _ domain _ _ := original.type | throwError "expected finite indexed facts"
    let domain ← whnf domain
    unless domain.isAppOfArity ``Fin 1 do throwError "expected a Fin index"
    let some count ← structuralNat? domain.appArg! 1000 | throwError "nonconstant finite domain"
    for index in [:count] do
      let (factType, proof) ← goal.withContext do
        let within ← mkDecideProof (← mkLT (mkNatLit index) (mkNatLit count))
        let argument := mkApp3 (mkConst ``Fin.mk) (mkNatLit count) (mkNatLit index) within
        let proof := mkApp original.toExpr argument
        let some (_, lhs, rhs) := (← inferType proof).eq? | throwError "expected read equality"
        pure (← mkEq lhs (← canonicalByteRhs rhs), proof)
      let (_, next) ← goal.note (← mkFreshUserName `readByte) proof (some factType)
      goal := next
    goal ← goal.clear original.fvarId
  replaceMainGoal [goal]

private def applyFact? (expression proof : Expr) : MetaM (Option (Expr × Expr)) := do
  let some (_, lhs, rhs) := (← inferType proof).eq? | return none
  unless lhs.getAppFn == expression.getAppFn do return none
  if expression.isAppOf ``Std.ExtDHashMap.get? || expression.isAppOf ``Std.ExtHashMap.get? then
    let leftArguments := lhs.getAppArgs
    let rightArguments := expression.getAppArgs
    unless ← withReducible (isDefEq leftArguments[leftArguments.size - 2]!
        rightArguments[rightArguments.size - 2]!) do return none
  if ← withTransparency .all (isDefEq lhs expression) then return some (rhs, proof)
  return none

private def inheritRead? (frame fact : Expr) : MetaM (Option Expr) := do
  let some (_, lhs, _) := (← inferType fact).eq? | return none
  let projection ←
    if lhs.isAppOf ``Std.ExtDHashMap.get? then
      pure ``X86StateFrame.Frame.registers
    else if lhs.isAppOf ``Std.ExtHashMap.get? then
      pure ``X86StateFrame.Frame.memory
    else return none
  let preserved ← mkAppM projection #[frame, lhs.appArg!]
  let .forallE _ outside _ _ ← whnf (← inferType preserved) | return none
  -- mkDecideProof constructs the term; its decision must first be checked.
  unless ← withTransparency .all (isDefEq (← mkDecide outside) (mkConst ``Bool.true)) do
    return none
  let valid ← mkDecideProof outside
  let preserved := mkApp preserved valid
  let some (_, _, original) := (← inferType preserved).eq? | return none
  unless ← withReducible (isDefEq original lhs) do return none
  return some (← mkEqTrans preserved fact)

/-- Carry read facts through checked frames while keeping successor states opaque. -/
elab "tisa_sail_inherit" "[" names:ident,* "]" : tactic => withMainContext do
  let mut goal ← getMainGoal
  for name in names.getElems do
    let frame ← getLocalDeclFromUserName name.getId
    let frameType ← whnf frame.type
    unless frameType.isAppOfArity ``X86StateFrame.Frame 4 do
      throwError "expected a machine-state frame"
    let facts ← goal.withContext do
      pure ((← getLCtx).foldl (fun facts decl =>
        if decl.isImplementationDetail then facts else facts.push decl.toExpr) #[])
    for fact in facts do
      let inherited ← goal.withContext do
        let saved ← saveState
        try inheritRead? frame.toExpr fact
        catch _ => saved.restore; pure none
      if let some proof := inherited then
        let (_, next) ← goal.note (← mkFreshUserName `framedRead) proof
        goal := next
  replaceMainGoal [goal]

private partial def reduceHead (goal : MVarId) (expression : Expr) (fuel : Nat) : MetaM (Expr × Expr) := do
  if fuel == 0 then throwError "head reduction budget"
  for declaration in (← getLCtx) do
    unless declaration.isImplementationDetail do
      if let some found ← applyFact? expression declaration.toExpr then return found
      if let .forallE _ domain body _ := declaration.type then
        let some (_, indexedLeft, _) := body.eq? | continue
        unless indexedLeft.getAppFn == expression.getAppFn do continue
        let domain ← whnf domain
        unless domain.isAppOfArity ``Fin 1 do continue
        let some count ← structuralNat? domain.appArg! 1000 | continue
        if expression.isAppOf ``Std.ExtDHashMap.get? || expression.isAppOf ``Std.ExtHashMap.get? then
          let indexedArguments := indexedLeft.getAppArgs
          let rightArguments := expression.getAppArgs
          let indexedMap := indexedArguments[indexedArguments.size - 2]!
          if !indexedMap.hasLooseBVars then
            unless ← withReducible (isDefEq indexedMap rightArguments[rightArguments.size - 2]!) do continue
        for index in [:count] do
          let bound ← mkDecideProof (← mkLT (mkNatLit index) (mkNatLit count))
          let argument := mkApp3 (mkConst ``Fin.mk) (mkNatLit count) (mkNatLit index) bound
          let proof := mkApp declaration.toExpr argument
          if let some found ← applyFact? expression proof then return found
  for (accessor, law) in #[( ``Std.ExtDHashMap.get?, ``Std.ExtDHashMap.get?_insert),
      (``Std.ExtHashMap.get?, ``byte_insert)] do
    if expression.isAppOf accessor then
      let saved ← saveState
      let mut matched : Option RewriteResult := none
      try
        let rewritten ← goal.rewrite expression (← mkConstWithFreshMVarLevels law)
        unless rewritten.mvarIds.isEmpty do throwError "unresolved map rewrite"
        matched := some rewritten
      catch _ => saved.restore
      if let some rewritten := matched then
        let (finished, rest) ← reduceHead goal rewritten.eNew (fuel - 1)
        return (finished, ← mkEqTrans rewritten.eqProof rest)
  let reduced ← withCanUnfoldPred (fun config info => do
      if info.name == ``Std.ExtDHashMap.get? || info.name == ``Std.ExtHashMap.get? then
        return false
      canUnfoldDefault config info) do
    withTransparency .default (whnf expression)
  if let some matcher ← matchMatcherApp? reduced (alsoCasesOn := true) then
    for index in [:matcher.discrs.size] do
      let discriminator := matcher.discrs[index]!
      let (next, proof) ← reduceHead goal discriminator (fuel - 1)
      if next != discriminator then
        let context ← withLocalDeclD `decision (← inferType discriminator) fun decision => do
          mkLambdaFVars #[decision] ({ matcher with discrs := matcher.discrs.set! index decision }.toExpr)
        let congruence ← mkAppM ``congrArg #[context, proof]
        let updated := { matcher with discrs := matcher.discrs.set! index next }.toExpr
        let (finished, rest) ← reduceHead goal updated (fuel - 1)
        return (finished, ← mkEqTrans congruence rest)
  if let .const function _ := reduced.getAppFn then
    if (← getUnfoldEqnFor? function).isSome then
      let unfolded ← unfold reduced function
      if unfolded.expr != reduced then
        let proof ← unfolded.getProof
        let (finished, rest) ← reduceHead goal unfolded.expr (fuel - 1)
        return (finished, ← mkEqTrans proof rest)
  return (reduced, ← mkEqRefl expression)

structure StepConfig where
  maxSteps : Nat := 1000
  finish : Bool := true

declare_config_elab elabStepConfig StepConfig

elab "tisa_sail_step" config:optConfig : tactic => withMainContext do
  let config ← elabStepConfig config
  for counter in [:300] do
    let goal ← getMainGoal
    let target ← instantiateMVars (← goal.getType)
    let some (_, lhs, rhs) := target.eq? | throwError "expected execution equality"
    let (reduced, reduction) ← reduceHead goal lhs config.maxSteps
    let newTarget ← mkEq reduced rhs
    let context ← withLocalDeclD `left (← inferType lhs) fun left => do
      mkLambdaFVars #[left] (← mkEq left rhs)
    let transport ← mkAppM ``congrArg #[context, reduction]
    let changed ← goal.replaceTargetEq newTarget transport
    replaceMainGoal [changed]
    try
      evalTactic (← `(tactic| rfl))
      return
    catch _ => pure ()
    if counter == 299 then throwError "head evaluation limit"
    let next ← instantiateMVars (← (← getMainGoal).getType)
    if next == target then
      if config.finish then throwError "head evaluator stuck at {next}"
      return

elab "tisa_sail_frame" : tactic => do
  evalTactic (← `(tactic| (
    constructor <;> intros
    all_goals try simp_all only [Finset.mem_insert, Finset.mem_singleton, not_or]
    all_goals first | rfl | simp_all [↓reduceClosedNat, register_insert_other, byte_insert_other])))

end Mettapedia.Machines.TIsa.X86Symbolic

namespace Mettapedia.Machines.TIsa.X86Symbolic.Controls
open _root_.X86Registers X86RegisterRefinement
local instance : MemoryPrimitives := X86Memory.ordinary

private def control : Vector (BitVec 64) 7 :=
  Vector.ofFn (fun index => if index.val = 0 then (0x400#64) else (0#64))
private def attributes : Vector (BitVec 16) 6 :=
  Vector.ofFn (fun index => if index.val = 1 then (0x200#16) else (0#16))

theorem frame_reads (before after : X86RegisterRefinement.State) (value : Word)
    (frame : X86StateFrame.Frame {.rip, .r14} ∅ before after)
    (valueKnown : before.regs.get? .r15 = some value)
    (_writtenKnown : before.regs.get? .r14 = some value)
    (byteKnown : before.mem.get? 1234 = some (17#8)) :
    after.regs.get? .r15 = some value ∧ after.mem.get? 1234 = some (17#8) := by
  tisa_sail_inherit [frame]
  fail_if_success have : after.regs.get? .r14 = some value := by assumption
  clear _writtenKnown
  constructor <;> assumption

theorem changed_register_not_inherited (before : X86RegisterRefinement.State) (value : Word) :
    ¬ (∀ state : X86RegisterRefinement.State, X86StateFrame.Frame {.rip, .r14} ∅ before state →
      state.regs.get? .r14 = some value) := by
  intro always
  let changed : X86RegisterRefinement.State := { before with regs := before.regs.insert .r14 (value + 1) }
  have changedFrame : X86StateFrame.Frame {.rip, .r14} ∅ before changed := by
    dsimp only [changed]
    tisa_sail_frame
  have valueChanged := always changed changedFrame
  simp only [changed, Std.ExtDHashMap.get?_insert_self] at valueChanged
  have distinct : value + 1 ≠ value := by
    intro same
    exact (by decide : (1 : Word) ≠ 0) (BitVec.add_right_eq_self.mp same)
  exact distinct (Option.some.inj valueChanged)

theorem symbolic_mov [OtherOpcodeHandlers] [VectorOpcodeHandlers] (state : X86RegisterRefinement.State) (value : Word)
    (status : state.regs.get? .ms_reg = some false) (fault : state.regs.get? .fault_reg = some false)
    (mode : state.regs.get? .msrs = some control) (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true) (quiet : state.regs.get? .log_register_writes = some false)
    (rip : state.regs.get? .rip = some (0x1000#64)) (source : state.regs.get? .r8 = some value)
    (byte0 : state.mem.get? 4096 = some (0x4d#8)) (byte1 : state.mem.get? 4097 = some (0x89#8))
    (byte2 : state.mem.get? 4098 = some (0xc1#8)) :
    ∃ after, (Functions.x86_fetch_decode_execute ()).run state = .ok () after ∧
      X86StateFrame.Frame {.r9, .rip} ∅ state after ∧
      after.regs.get? .r9 = some value ∧ after.regs.get? .rip = some (4099#64) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  tisa_sail_step
  · tisa_sail_frame
  · simp [Std.ExtDHashMap.get?_insert, Functions.regval_into_reg, Functions.regval_from_reg,
      Sail.BitVec.truncate, Sail.BitVec.zeroExtend]
  · simp only [Std.ExtDHashMap.get?_insert]
    rfl

theorem symbolic_changed_destination [OtherOpcodeHandlers] [VectorOpcodeHandlers] (state : X86RegisterRefinement.State) (value : Word)
    (status : state.regs.get? .ms_reg = some false) (fault : state.regs.get? .fault_reg = some false)
    (mode : state.regs.get? .msrs = some control) (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true) (quiet : state.regs.get? .log_register_writes = some false)
    (rip : state.regs.get? .rip = some (0x1000#64)) (source : state.regs.get? .r8 = some value)
    (byte0 : state.mem.get? 4096 = some (0x4d#8)) (byte1 : state.mem.get? 4097 = some (0x89#8))
    (byte2 : state.mem.get? 4098 = some (0xc2#8)) :
    ∃ after, (Functions.x86_fetch_decode_execute ()).run state = .ok () after ∧
      X86StateFrame.Frame {.r10, .rip} ∅ state after ∧
      after.regs.get? .r10 = some value ∧ after.regs.get? .rip = some (4099#64) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  tisa_sail_step
  · tisa_sail_frame
  · simp [Std.ExtDHashMap.get?_insert, Functions.regval_into_reg, Functions.regval_from_reg,
      Sail.BitVec.truncate, Sail.BitVec.zeroExtend]
  · simp only [Std.ExtDHashMap.get?_insert]
    rfl


theorem symbolic_mov32 [OtherOpcodeHandlers] [VectorOpcodeHandlers] (state : X86RegisterRefinement.State) (value : Word)
    (status : state.regs.get? .ms_reg = some false) (fault : state.regs.get? .fault_reg = some false)
    (mode : state.regs.get? .msrs = some control) (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true) (quiet : state.regs.get? .log_register_writes = some false)
    (rip : state.regs.get? .rip = some (0x1000#64)) (source : state.regs.get? .r8 = some value)
    (byte0 : state.mem.get? 4096 = some (0x45#8)) (byte1 : state.mem.get? 4097 = some (0x89#8))
    (byte2 : state.mem.get? 4098 = some (0xc1#8)) :
    ∃ after, (Functions.x86_fetch_decode_execute ()).run state = .ok () after ∧
      X86StateFrame.Frame {.r9, .rip} ∅ state after ∧
      after.regs.get? .r9 = some ((value.setWidth 32).zeroExtend 64) ∧ after.regs.get? .rip = some (4099#64) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  tisa_sail_step
  · tisa_sail_frame
  · simp [Std.ExtDHashMap.get?_insert, Functions.regval_into_reg, Functions.regval_from_reg,
      Sail.BitVec.truncate, Sail.BitVec.zeroExtend]
  · simp only [Std.ExtDHashMap.get?_insert]
    rfl


theorem two_moves [OtherOpcodeHandlers] [VectorOpcodeHandlers] (state : X86RegisterRefinement.State) (value : Word)
    (status : state.regs.get? .ms_reg = some false) (fault : state.regs.get? .fault_reg = some false)
    (mode : state.regs.get? .msrs = some control) (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true) (quiet : state.regs.get? .log_register_writes = some false)
    (rip : state.regs.get? .rip = some (0x1000#64)) (source : state.regs.get? .r8 = some value)
    (byte0 : state.mem.get? 4096 = some (0x4d#8)) (byte1 : state.mem.get? 4097 = some (0x89#8))
    (byte2 : state.mem.get? 4098 = some (0xc1#8))
    (byte3 : state.mem.get? 4099 = some (0x4d#8)) (byte4 : state.mem.get? 4100 = some (0x89#8))
    (byte5 : state.mem.get? 4101 = some (0xca#8)) :
    ∃ after, (X86FuelPrefix.fetches 2).run state = .ok () after ∧
      X86StateFrame.Frame {.r9, .r10, .rip} ∅ state after ∧
      after.regs.get? .r10 = some value ∧ after.regs.get? .rip = some (4102#64) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  tisa_sail_step
  · tisa_sail_frame
  · simp [Std.ExtDHashMap.get?_insert, Functions.regval_into_reg, Functions.regval_from_reg,
      Sail.BitVec.truncate, Sail.BitVec.zeroExtend]
  · simp only [Std.ExtDHashMap.get?_insert]
    rfl


theorem add_wraps (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : X86RegisterRefinement.State)
    (status : state.regs.get? .ms_reg = some false) (fault : state.regs.get? .fault_reg = some false)
    (mode : state.regs.get? .msrs = some control) (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true) (quiet : state.regs.get? .log_register_writes = some false)
    (rip : state.regs.get? .rip = some (0x1000#64))
    (source : state.regs.get? .r8 = some (1#64))
    (destination : state.regs.get? .r9 = some (0xffffffffffffffff#64))
    (flags : state.regs.get? .rflags = some (0#32))
    (byte0 : state.mem.get? 4096 = some (0x4d#8)) (byte1 : state.mem.get? 4097 = some (0x01#8))
    (byte2 : state.mem.get? 4098 = some (0xc1#8)) :
    letI : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run state = .ok () after ∧
      X86StateFrame.Frame {.r9, .rip, .rflags} ∅ state after ∧
      after.regs.get? .r9 = some (0#64) ∧ after.regs.get? .rflags = some (0x55#32) ∧
      after.regs.get? .rip = some (4099#64) := by
  let : OtherOpcodeHandlers := X86Arithmetic.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  tisa_sail_step
  · tisa_sail_frame
  all_goals simp only [Std.ExtDHashMap.get?_insert]
  all_goals first | rfl | cbv

theorem altered_modrm_refuses_original_answer [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (state : X86RegisterRefinement.State) (value old : Word)
    (status : state.regs.get? .ms_reg = some false) (fault : state.regs.get? .fault_reg = some false)
    (mode : state.regs.get? .msrs = some control) (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true) (quiet : state.regs.get? .log_register_writes = some false)
    (rip : state.regs.get? .rip = some (0x1000#64)) (source : state.regs.get? .r8 = some value)
    (byte0 : state.mem.get? 4096 = some (0x4d#8)) (byte1 : state.mem.get? 4097 = some (0x89#8))
    (byte2 : state.mem.get? 4098 = some (0xc2#8))
    (prior : state.regs.get? .r9 = some old) (different : old ≠ value) :
    ¬ ∃ after, (Functions.x86_fetch_decode_execute ()).run state = .ok () after ∧
      after.regs.get? .r9 = some value := by
  obtain ⟨computed, executed, frame, _⟩ := symbolic_changed_destination state value
    status fault mode segments application quiet rip source byte0 byte1 byte2
  rintro ⟨after, observed, wrong⟩
  have same := (EStateM.Result.ok.inj (executed.symm.trans observed)).2
  have retained := frame.registers .r9 (by decide)
  rw [same, wrong, prior] at retained
  exact different (Option.some.inj retained).symm

theorem captured_mov [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (state : X86RegisterRefinement.State) (value : Word) (bytes : List Nat)
    (status : state.regs.get? .ms_reg = some false) (fault : state.regs.get? .fault_reg = some false)
    (mode : state.regs.get? .msrs = some control) (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true) (quiet : state.regs.get? .log_register_writes = some false)
    (rip : state.regs.get? .rip = some (0x1000#64)) (source : state.regs.get? .r8 = some value)
    (emitted : X86MovCapture.lookup 5 4 = some bytes)
    (loaded : X86Execution.codeLoaded state 4096 bytes) :
    ∃ after, (Functions.x86_fetch_decode_execute ()).run state = .ok () after ∧
      X86StateFrame.Frame {.r9, .rip} ∅ state after ∧
      after.regs.get? .r9 = some value ∧ after.regs.get? .rip = some (4099#64) := by
  have actual : X86MovCapture.lookup 5 4 = some [77, 137, 193] := by kernel_reflexivity
  have same := Option.some.inj (emitted.symm.trans actual)
  subst bytes
  have byte0 := loaded 0 77 rfl
  have byte1 := loaded 1 137 rfl
  have byte2 := loaded 2 193 rfl
  exact symbolic_mov state value status fault mode segments application quiet rip source byte0 byte1 byte2

theorem missing_byte [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (state : X86RegisterRefinement.State)
    (status : state.regs.get? .ms_reg = some false) (fault : state.regs.get? .fault_reg = some false)
    (mode : state.regs.get? .msrs = some control) (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true)
    (rip : state.regs.get? .rip = some (0x1000#64))
    (byte0 : state.mem.get? 4096 = some (0x4d#8)) (byte1 : state.mem.get? 4097 = some (0x89#8))
    (absent : state.mem.get? 4098 = none) :
    ∃ after, (Functions.x86_fetch_decode_execute ()).run state =
      .error (.OutOfMemoryRange 4098) after ∧ X86StateFrame.Frame ∅ ∅ state after := by
  refine ⟨?_, ?_, ?_⟩
  rotate_left
  tisa_sail_step
  tisa_sail_frame

private def visible : Vector (BitVec 16) 6 := Vector.replicate 6 (0#16)
private def controls : Vector (BitVec 64) 17 := Vector.replicate 17 (0#64)

private def storeRex : Memory.Width → BitVec 8
  | .word64 => 0x4c#8
  | _ => 0x44#8
private def storeOpcode : Memory.Width → BitVec 8
  | .byte => 0x88#8
  | _ => 0x89#8


theorem symbolic_store_width [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (width : Memory.Width) (state : X86RegisterRefinement.State) (value : Word)
    (status : state.regs.get? .ms_reg = some false) (fault : state.regs.get? .fault_reg = some false)
    (mode : state.regs.get? .msrs = some control) (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true) (quiet : state.regs.get? .log_register_writes = some false)
    (controlKnown : state.regs.get? .ctrs = some controls) (flagsKnown : state.regs.get? .rflags = some (2#32))
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (rip : state.regs.get? .rip = some (0x1000#64))
    (base : state.regs.get? .rdi = some (0x100000#64)) (source : state.regs.get? .r8 = some value)
    (byte0 : state.mem.get? 4096 = some (storeRex width)) (byte1 : state.mem.get? 4097 = some (storeOpcode width))
    (byte2 : state.mem.get? 4098 = some (0x87#8)) (byte3 : state.mem.get? 4099 = some (0x98#8))
    (byte4 : state.mem.get? 4100 = some (0#8)) (byte5 : state.mem.get? 4101 = some (0#8))
    (byte6 : state.mem.get? 4102 = some (0#8)) :
    ∃ after, (Functions.x86_fetch_decode_execute ()).run state = .ok () after ∧
      X86StateFrame.Frame {.rip} ((Finset.range width.bytes).image (1048728 + ·)) state after ∧
      (∀ offset : Fin width.bytes, after.mem.get? (1048728 + offset.val) =
        some (value.extractLsb' (8 * offset.val) 8)) ∧
      after.regs.get? .rip = some (4103#64) := by
  cases width <;>
    simp only [storeRex, storeOpcode, Memory.Width.bytes, Finset.range_add_one,
      Finset.range_zero, Finset.image_insert, Finset.image_empty] at *
  all_goals
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    rotate_left
    tisa_sail_step
    · tisa_sail_frame
    · intro offset
      fin_cases offset <;>
        simp [↓X86Symbolic.reduceClosedNat, Std.ExtHashMap.getElem_insert, Functions.regval_from_reg,
          Sail.BitVec.truncate, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
      all_goals first | rfl | simp [BitVec.extractLsb, BitVec.extractLsb'_setWidth_of_le]
    · simp only [Std.ExtDHashMap.get?_insert]
      rfl

theorem store_then_load (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : X86RegisterRefinement.State) (value : Word)
    (status : state.regs.get? .ms_reg = some false) (fault : state.regs.get? .fault_reg = some false)
    (mode : state.regs.get? .msrs = some control) (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true) (quiet : state.regs.get? .log_register_writes = some false)
    (controlKnown : state.regs.get? .ctrs = some controls) (flagsKnown : state.regs.get? .rflags = some (2#32))
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (rip : state.regs.get? .rip = some (0x1000#64))
    (base : state.regs.get? .rdi = some (0x100000#64)) (source : state.regs.get? .r8 = some value)
    (byte0 : state.mem.get? 4096 = some (0x4c#8)) (byte1 : state.mem.get? 4097 = some (0x89#8))
    (byte2 : state.mem.get? 4098 = some (0x87#8)) (byte3 : state.mem.get? 4099 = some (0x98#8))
    (byte4 : state.mem.get? 4100 = some (0#8)) (byte5 : state.mem.get? 4101 = some (0#8))
    (byte6 : state.mem.get? 4102 = some (0#8))
    (byte7 : state.mem.get? 4103 = some (0x4c#8)) (byte8 : state.mem.get? 4104 = some (0x8b#8))
    (byte9 : state.mem.get? 4105 = some (0x8f#8)) (byte10 : state.mem.get? 4106 = some (0x98#8))
    (byte11 : state.mem.get? 4107 = some (0#8)) (byte12 : state.mem.get? 4108 = some (0#8))
    (byte13 : state.mem.get? 4109 = some (0#8)) :
    letI : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run state = .ok () after ∧
      X86StateFrame.Frame {.r9, .rip} {1048728,1048729,1048730,1048731,1048732,1048733,1048734,1048735} state after ∧
      (∀ offset : Fin 8, after.mem.get? (1048728 + offset.val) =
        some (value.extractLsb' (8 * offset.val) 8)) ∧
      after.regs.get? .r9 = some value ∧ after.regs.get? .rip = some (4110#64) := by
  let : OtherOpcodeHandlers := X86FrameLoad.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  tisa_sail_step
  · tisa_sail_frame
  · intro offset
    fin_cases offset <;>
      simp [↓X86Symbolic.reduceClosedNat, Std.ExtHashMap.getElem_insert, Functions.regval_from_reg,
        Sail.BitVec.truncate, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
    all_goals rfl
  · simp [Std.ExtDHashMap.get?_insert, Functions.regval_from_reg, Functions.regval_into_reg,
      Sail.BitVec.truncate, Sail.BitVec.zeroExtend, Sail.BitVec.extractLsb]
    exact X86ReadWords.assembled_exact value
  · simp only [Std.ExtDHashMap.get?_insert]
    rfl

theorem big_endian_refused [OtherOpcodeHandlers] [VectorOpcodeHandlers]
    (state : X86RegisterRefinement.State) (value : Word)
    (status : state.regs.get? .ms_reg = some false) (fault : state.regs.get? .fault_reg = some false)
    (mode : state.regs.get? .msrs = some control) (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true) (quiet : state.regs.get? .log_register_writes = some false)
    (controlKnown : state.regs.get? .ctrs = some controls) (flagsKnown : state.regs.get? .rflags = some (2#32))
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (rip : state.regs.get? .rip = some (0x1000#64))
    (base : state.regs.get? .rdi = some (0x100000#64)) (source : state.regs.get? .r8 = some value)
    (byte0 : state.mem.get? 4096 = some (0x4c#8)) (byte1 : state.mem.get? 4097 = some (0x89#8))
    (byte2 : state.mem.get? 4098 = some (0x87#8)) (byte3 : state.mem.get? 4099 = some (0x98#8))
    (byte4 : state.mem.get? 4100 = some (0#8)) (byte5 : state.mem.get? 4101 = some (0#8))
    (byte6 : state.mem.get? 4102 = some (0#8))
    (different : value.extractLsb' 0 8 ≠ value.extractLsb' 56 8) :
    ¬ ∃ after, (Functions.x86_fetch_decode_execute ()).run state = .ok () after ∧
      after.mem.get? 1048728 = some (value.extractLsb' 56 8) := by
  obtain ⟨computed, executed, _, bytes, _⟩ := symbolic_store_width .word64 state value
    status fault mode segments application quiet controlKnown flagsKnown visibleKnown rip base source
    byte0 byte1 byte2 byte3 byte4 byte5 byte6
  rintro ⟨after, observed, wrong⟩
  have same := (EStateM.Result.ok.inj (executed.symm.trans observed)).2
  have low : computed.mem.get? 1048728 = some (value.extractLsb' 0 8) := bytes (0 : Fin 8)
  rw [same, wrong] at low
  exact different (Option.some.inj low).symm

example : (0x0102030405060708#64).extractLsb' 0 8 ≠
    (0x0102030405060708#64).extractLsb' 56 8 := by decide

private def subMemoryCode : List Nat := [0x4c,0x2b,0xb7,0xa8,0,0,0]

private abbrev registerMemoryHandlers (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  { other with x86_add_adc_sub_sbb_or_and_xor_cmp_g_e :=
    Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_g_e }

theorem subtract_memory (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : X86RegisterRefinement.State) (left right : Word) (flags : BitVec 32)
    (status : state.regs.get? .ms_reg = some false) (fault : state.regs.get? .fault_reg = some false)
    (mode : state.regs.get? .msrs = some control) (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true) (quiet : state.regs.get? .log_register_writes = some false)
    (controlKnown : state.regs.get? .ctrs = some controls) (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (rip : state.regs.get? .rip = some (4096#64)) (base : state.regs.get? .rdi = some (1048576#64))
    (operand : state.regs.get? .r14 = some left)
    (loaded : ∀ index : Fin subMemoryCode.length,
      state.mem.get? (4096 + index.val) = some (BitVec.ofNat 8 subMemoryCode[index.val]))
    (receipt : ∀ index : Fin 8,
      state.mem.get? (1048744 + index.val) = some (right.extractLsb' (8 * index.val) 8)) :
    letI : OtherOpcodeHandlers := registerMemoryHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (Functions.x86_fetch_decode_execute ()).run state = .ok () after ∧
      X86StateFrame.Frame {.rip, .rflags, .r14} ∅ state after ∧
      after.regs.get? .r14 = some (left - right) ∧ after.regs.get? .rflags = some nextFlags ∧
      after.regs.get? .rip = some (4103#64) := by
  let : OtherOpcodeHandlers := registerMemoryHandlers other
  let : VectorOpcodeHandlers := vector
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 2
  tisa_sail_step
  · tisa_sail_frame
  · simp [Std.ExtDHashMap.get?_insert, Functions.regval_from_reg, Functions.regval_into_reg,
      Sail.BitVec.truncate, Sail.BitVec.zeroExtend]
    change BitVec.setWidth 64 (Functions.bits_of_int
      (left.toInt - (X86ReadWords.assembled right).toInt) 65) = left - right
    rw [X86ReadWords.assembled_exact]
    exact X86Alu.sub_result left right
  · simp only [Std.ExtDHashMap.get?_insert]
    rfl
  · simp only [Std.ExtDHashMap.get?_insert]
    rfl

private def gradeCode (grade : Funding.Grade) : List Nat :=
  [0x41, 0xbf] ++ (List.range 4).map (fun index => (grade.units.extractLsb' (8 * index) 8).toNat)

theorem symbolic_grade (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : X86RegisterRefinement.State) (grade : Funding.Grade)
    (status : state.regs.get? .ms_reg = some false) (fault : state.regs.get? .fault_reg = some false)
    (mode : state.regs.get? .msrs = some control) (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true) (quiet : state.regs.get? .log_register_writes = some false)
    (rip : state.regs.get? .rip = some (4096#64))
    (loaded : ∀ index : Fin (gradeCode grade).length,
      state.mem.get? (4096 + index.val) = some (BitVec.ofNat 8 (gradeCode grade)[index.val])) :
    letI : OtherOpcodeHandlers := X86FrameStore.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (Functions.x86_fetch_decode_execute ()).run state = .ok () after ∧
      X86StateFrame.Frame {.rip, .r15} ∅ state after ∧
      after.regs.get? .r15 = some grade.word ∧ after.regs.get? .rip = some (4102#64) := by
  let : OtherOpcodeHandlers := X86FrameStore.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  tisa_sail_bytes [loaded]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  tisa_sail_step
  · tisa_sail_frame
  · simp [Std.ExtDHashMap.get?_insert, Functions.regval_from_reg, Functions.regval_into_reg,
      Sail.BitVec.truncate, Sail.BitVec.zeroExtend, Funding.Grade.word]
    simpa only [gradeCode, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.getElem_cons_zero, List.getElem_cons_succ,
      X86ReadWords.assembled32, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', Nat.reduceMul,
      Nat.reduceSub, Nat.reduceAdd, wordRepack] using
      congrArg (BitVec.setWidth 64) (X86ReadWords.assembled32_exact grade.units)
  · simp only [Std.ExtDHashMap.get?_insert]
    rfl

theorem wrong_grade_refused (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : X86RegisterRefinement.State) (grade : Funding.Grade) (wanted : Word)
    (status : state.regs.get? .ms_reg = some false) (fault : state.regs.get? .fault_reg = some false)
    (mode : state.regs.get? .msrs = some control) (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true) (quiet : state.regs.get? .log_register_writes = some false)
    (rip : state.regs.get? .rip = some (4096#64))
    (loaded : ∀ index : Fin (gradeCode grade).length,
      state.mem.get? (4096 + index.val) = some (BitVec.ofNat 8 (gradeCode grade)[index.val]))
    (different : wanted ≠ grade.word) :
    letI : OtherOpcodeHandlers := X86FrameStore.linkedHandlers other
    letI : VectorOpcodeHandlers := vector
    ¬ ∃ after, (Functions.x86_fetch_decode_execute ()).run state = .ok () after ∧
      after.regs.get? .r15 = some wanted := by
  let : OtherOpcodeHandlers := X86FrameStore.linkedHandlers other
  let : VectorOpcodeHandlers := vector
  obtain ⟨computed, executed, _, value, _⟩ := symbolic_grade other vector state grade
    status fault mode segments application quiet rip loaded
  rintro ⟨after, observed, wrong⟩
  have same := (EStateM.Result.ok.inj (executed.symm.trans observed)).2
  rw [same, wrong] at value
  exact different (Option.some.inj value)

private def fundInputCode (grade : Funding.Grade) : List Nat :=
  gradeCode grade ++ [0x4c,0x8b,0xb7,0xa0,0,0,0]

private noncomputable abbrev fundHandlers (other : OtherOpcodeHandlers) : OtherOpcodeHandlers :=
  { X86FrameStore.linkedHandlers (X86FrameLoad.linkedHandlers other) with
    x86_add_adc_sub_sbb_or_and_xor_cmp_g_e := Functions.x86_add_adc_sub_sbb_or_and_xor_cmp_g_e }

private theorem fund_inputs (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : X86RegisterRefinement.State) (grade : Funding.Grade) (allowance : Word) (flags : BitVec 32)
    (status : state.regs.get? .ms_reg = some false) (fault : state.regs.get? .fault_reg = some false)
    (mode : state.regs.get? .msrs = some control) (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true) (quiet : state.regs.get? .log_register_writes = some false)
    (controlKnown : state.regs.get? .ctrs = some controls) (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (rip : state.regs.get? .rip = some (4096#64)) (base : state.regs.get? .rdi = some (1048576#64))
    (loaded : ∀ index : Fin (fundInputCode grade).length,
      state.mem.get? (4096 + index.val) = some (BitVec.ofNat 8 (fundInputCode grade)[index.val]))
    (budget : ∀ index : Fin 8,
      state.mem.get? (1048736 + index.val) = some (allowance.extractLsb' (8 * index.val) 8)) :
    letI : OtherOpcodeHandlers := fundHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after, (X86FuelPrefix.fetches 2).run state = .ok () after ∧
      X86StateFrame.Frame {.rip, .r14, .r15} ∅ state after ∧
      after.regs.get? .r15 = some grade.word ∧ after.regs.get? .r14 = some allowance ∧
      after.regs.get? .rip = some (4109#64) := by
  let : OtherOpcodeHandlers := fundHandlers other
  let : VectorOpcodeHandlers := vector
  tisa_sail_bytes [loaded, budget]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  tisa_sail_step
  · tisa_sail_frame
  · simp [Std.ExtDHashMap.get?_insert, Functions.regval_from_reg, Functions.regval_into_reg,
      Sail.BitVec.truncate, Sail.BitVec.zeroExtend, Funding.Grade.word]
    simpa only [fundInputCode, gradeCode, List.range_succ, List.range_zero, List.map_append,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.getElem_cons_zero,
      List.getElem_cons_succ, X86ReadWords.assembled32, List.foldl_append, List.foldl_cons,
      List.foldl_nil, Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', Nat.reduceMul,
      Nat.reduceSub, Nat.reduceAdd, wordRepack] using
      congrArg (BitVec.setWidth 64) (X86ReadWords.assembled32_exact grade.units)
  · simp [Std.ExtDHashMap.get?_insert, Functions.regval_from_reg, Functions.regval_into_reg,
      Sail.BitVec.truncate, Sail.BitVec.zeroExtend]
    exact X86ReadWords.assembled_exact allowance
  · simp only [Std.ExtDHashMap.get?_insert]
    rfl

private def fundPrefixCode (grade : Funding.Grade) : List Nat :=
  fundInputCode grade ++ subMemoryCode

/-- A fixed-placement FUND prefix control, composed through an opaque intermediate state. -/
theorem fund_remaining (other : OtherOpcodeHandlers) (vector : VectorOpcodeHandlers)
    (state : X86RegisterRefinement.State) (grade : Funding.Grade) (allowance receiptWord : Word)
    (flags : BitVec 32)
    (status : state.regs.get? .ms_reg = some false) (fault : state.regs.get? .fault_reg = some false)
    (mode : state.regs.get? .msrs = some control) (segments : state.regs.get? .seg_hidden_attrs = some attributes)
    (application : state.regs.get? .app_view = some true) (quiet : state.regs.get? .log_register_writes = some false)
    (controlKnown : state.regs.get? .ctrs = some controls) (flagsKnown : state.regs.get? .rflags = some flags)
    (visibleKnown : state.regs.get? .seg_visibles = some visible)
    (rip : state.regs.get? .rip = some (4096#64)) (base : state.regs.get? .rdi = some (1048576#64))
    (loaded : ∀ index : Fin (fundPrefixCode grade).length,
      state.mem.get? (4096 + index.val) = some (BitVec.ofNat 8 (fundPrefixCode grade)[index.val]))
    (budget : ∀ index : Fin 8,
      state.mem.get? (1048736 + index.val) = some (allowance.extractLsb' (8 * index.val) 8))
    (receipt : ∀ index : Fin 8,
      state.mem.get? (1048744 + index.val) = some (receiptWord.extractLsb' (8 * index.val) 8)) :
    letI : OtherOpcodeHandlers := fundHandlers other
    letI : VectorOpcodeHandlers := vector
    ∃ after nextFlags, (X86FuelPrefix.fetches 3).run state = .ok () after ∧
      X86StateFrame.Frame {.rip, .rflags, .r14, .r15} ∅ state after ∧
      after.regs.get? .r14 = some (allowance - receiptWord) ∧
      after.regs.get? .r15 = some grade.word ∧ after.regs.get? .rflags = some nextFlags ∧
      after.regs.get? .rip = some (4116#64) := by
  let : OtherOpcodeHandlers := fundHandlers other
  let : VectorOpcodeHandlers := vector
  have prefixLoaded : ∀ index : Fin (fundInputCode grade).length,
      state.mem.get? (4096 + index.val) = some (BitVec.ofNat 8 (fundInputCode grade)[index.val]) := by
    intro index
    have within : index.val < (fundPrefixCode grade).length := by
      simp only [fundPrefixCode, List.length_append]
      omega
    have known := loaded ⟨index.val, within⟩
    simpa only [fundPrefixCode, List.getElem_append_left index.isLt] using known
  obtain ⟨middle, first, framed, gradeRead, allowanceRead, middleRip⟩ :=
    fund_inputs other vector state grade allowance flags status fault mode segments application quiet
      controlKnown flagsKnown visibleKnown rip base prefixLoaded budget
  tisa_sail_bytes [loaded, receipt]
  have final : ∃ after nextFlags,
      (Functions.x86_fetch_decode_execute ()).run middle = .ok () after ∧
      X86StateFrame.Frame {.rip, .rflags, .r14} ∅ middle after ∧
      after.regs.get? .r14 = some (allowance - receiptWord) ∧
      after.regs.get? .rflags = some nextFlags ∧ after.regs.get? .rip = some (4116#64) := by
    tisa_sail_inherit [framed]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left 2
    tisa_sail_step
    · tisa_sail_frame
    · simp [Std.ExtDHashMap.get?_insert, Functions.regval_from_reg, Functions.regval_into_reg,
        Sail.BitVec.truncate, Sail.BitVec.zeroExtend]
      change BitVec.setWidth 64 (Functions.bits_of_int
        (allowance.toInt - (X86ReadWords.assembled receiptWord).toInt) 65) = allowance - receiptWord
      rw [X86ReadWords.assembled_exact]
      exact X86Alu.sub_result allowance receiptWord
    · simp only [Std.ExtDHashMap.get?_insert]
      rfl
    · simp only [Std.ExtDHashMap.get?_insert]
      rfl
  obtain ⟨after, nextFlags, last, lastFrame, resultRead, nextFlagsRead, finalRip⟩ := final
  refine ⟨after, nextFlags,
    X86FuelPrefix.fetches_then 2 1 state middle after first (X86FuelPrefix.fetches_one middle after last),
    ?_, resultRead, ?_, nextFlagsRead, finalRip⟩
  · apply (framed.trans lastFrame).mono
    · intro register member
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at member ⊢
      tauto
    · simp
  · exact (lastFrame.registers .r15 (by decide)).trans gradeRead

end Mettapedia.Machines.TIsa.X86Symbolic.Controls

#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.frame_reads
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.changed_register_not_inherited
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.fund_remaining
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.symbolic_mov
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.symbolic_changed_destination
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.symbolic_mov32
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.two_moves
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.add_wraps
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.altered_modrm_refuses_original_answer
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.missing_byte
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.captured_mov
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.symbolic_store_width
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.store_then_load
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.big_endian_refused
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.subtract_memory
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.symbolic_grade
#print axioms Mettapedia.Machines.TIsa.X86Symbolic.Controls.wrong_grade_refused
