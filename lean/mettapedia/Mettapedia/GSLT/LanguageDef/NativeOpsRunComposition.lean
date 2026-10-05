import Mettapedia.GSLT.LanguageDef.NativeOpsTargetEval

/-!
# Ordered composition of native expression fragments

Expression fragments contain no outward label transfer. The syntactic check
below covers nested branches, switch arms, initialization loops and scopes.
Finite target executions then split and compose at an operand boundary,
retaining early returns and the exact state without executing a suffix after
an early return. These laws concern the existing native target relation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Instruction)

mutual
  def jumpFreeCode : List Instruction → Bool
    | [] => true
    | first :: rest => jumpFreeInstruction first && jumpFreeCode rest
  termination_by code => sizeOf code
  decreasing_by all_goals simp_wf; all_goals omega

  def jumpFreeInstruction : Instruction → Bool
    | .jump _ => false
    | .forWord _ _ body | .scope body => jumpFreeCode body
    | .branch _ yes no => jumpFreeCode yes && jumpFreeCode no
    | .switch _ arms otherwise => jumpFreeArms arms && jumpFreeCode otherwise
    | _ => true
  termination_by instruction => sizeOf instruction
  decreasing_by all_goals simp_wf; all_goals omega

  def jumpFreeArms : List (BitVec 64 × List Instruction) → Bool
    | [] => true
    | (_, body) :: rest => jumpFreeCode body && jumpFreeArms rest
  termination_by arms => sizeOf arms
  decreasing_by all_goals simp_wf; all_goals omega
end

theorem jump_free_selected_case (value : BitVec 64)
    {arms : List (BitVec 64 × List Instruction)} {otherwise : List Instruction}
    (armChecks : jumpFreeArms arms = true) (otherwiseCheck : jumpFreeCode otherwise = true) :
    jumpFreeCode (targetSelectCase value arms otherwise) = true := by
  induction arms with
  | nil => simpa only [targetSelectCase, List.find?_nil] using otherwiseCheck
  | cons arm rest ih =>
      rcases arm with ⟨selector, body⟩
      simp only [jumpFreeArms] at armChecks
      have checks := Bool.and_eq_true_iff.mp armChecks
      by_cases same : selector == value
      · simpa [targetSelectCase, same] using checks.1
      · simpa [targetSelectCase, same] using ih checks.2

local macro "jump_free_execution_cases" : tactic => `(tactic| (
  all_goals repeat intro
  case temporary => rename_i label checked jumped; cases jumped
  case assign => rename_i label checked jumped; cases jumped
  case helper => rename_i label checked jumped; cases jumped
  case call => rename_i label checked jumped; cases jumped
  case contextExists => rename_i label checked jumped; cases jumped
  case contextClear => rename_i label checked jumped; cases jumped
  case contextFault => rename_i label checked jumped; cases jumped
  case numericClear => rename_i label checked jumped; cases jumped
  case numericFault => rename_i label checked jumped; cases jumped
  case declareLocal => rename_i label checked jumped; cases jumped
  case write => rename_i label checked jumped; cases jumped
  case writeElement => rename_i label checked jumped; cases jumped
  case forWord =>
    rename_i unused loop ih label checked jumped
    simp only [jumpFreeInstruction] at checked
    exact ih label checked jumped
  case branch =>
    rename_i tested selected ih label checked jumped
    simp only [jumpFreeInstruction] at checked
    have checks := Bool.and_eq_true_iff.mp checked
    apply ih label ?_ jumped
    split <;> first | exact checks.1 | exact checks.2
  case switch =>
    rename_i read selected ih label checked jumped
    simp only [jumpFreeInstruction] at checked
    have checks := Bool.and_eq_true_iff.mp checked
    exact ih label (jump_free_selected_case _ checks.1 checks.2) jumped
  case scope =>
    rename_i ran ih label checked jumped
    simp only [jumpFreeInstruction] at checked
    exact ih label checked jumped
  case label => rename_i label checked jumped; cases jumped
  case jump =>
    rename_i label checked jumped
    simp only [jumpFreeInstruction, Bool.false_eq_true] at checked
  case «return» => rename_i label checked jumped; cases jumped
  case nil => rename_i label checked jumped; cases jumped
  case next =>
    rename_i first rest ihFirst ihRest label checked jumped
    simp only [jumpFreeCode] at checked
    exact ihRest label (Bool.and_eq_true_iff.mp checked).2 jumped
  case «return» => rename_i label checked jumped; cases jumped
  case resume =>
    rename_i first found rest ihFirst ihRest label checked jumped
    simp only [jumpFreeCode] at checked
    exact ihFirst _ (Bool.and_eq_true_iff.mp checked).1 rfl
  case escape =>
    rename_i first outside ih label checked jumped
    simp only [jumpFreeCode] at checked
    exact ih _ (Bool.and_eq_true_iff.mp checked).1 rfl
  case done => rename_i label checked jumped; cases jumped
  case next =>
    rename_i readCounter readBound within ran normal counterAfter rest ihRun ihRest label checked jumped
    exact ihRest label checked jumped
  case stop =>
    rename_i readCounter readBound within ran abrupt ih label checked jumped
    exact ih label checked jumped))

theorem jump_free_instruction_cannot_jump {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {instruction : Instruction} {frame : TargetFrame} {state : TargetState World}
    {out : TargetBlockOutcome World}
    (ran : TargetInstructionEval interface heap calls result instruction frame state out) :
    ∀ label, jumpFreeInstruction instruction = true → out.flow ≠ .jumped label := by
  induction ran using TargetInstructionEval.rec
    (motive_2 := fun _ remaining _ _ out _ =>
      ∀ label, jumpFreeCode remaining = true → out.flow ≠ .jumped label)
    (motive_3 := fun _ _ body _ _ out _ =>
      ∀ label, jumpFreeCode body = true → out.flow ≠ .jumped label)
  jump_free_execution_cases

theorem jump_free_run_cannot_jump {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {root remaining : List Instruction} {frame : TargetFrame} {state : TargetState World}
    {out : TargetBlockOutcome World}
    (ran : TargetRun interface heap calls result root remaining frame state out) :
    ∀ label, jumpFreeCode remaining = true → out.flow ≠ .jumped label := by
  induction ran using TargetRun.rec
    (motive_1 := fun instruction _ _ out _ =>
      ∀ label, jumpFreeInstruction instruction = true → out.flow ≠ .jumped label)
    (motive_3 := fun _ _ body _ _ out _ =>
      ∀ label, jumpFreeCode body = true → out.flow ≠ .jumped label)
  jump_free_execution_cases

theorem jump_free_loop_cannot_jump {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {counter : Nat} {bound : NativeIR.Atom} {body : List Instruction}
    {frame : TargetFrame} {state : TargetState World} {out : TargetBlockOutcome World}
    (ran : TargetForEval interface heap calls result counter bound body frame state out) :
    ∀ label, jumpFreeCode body = true → out.flow ≠ .jumped label := by
  induction ran using TargetForEval.rec
    (motive_1 := fun instruction _ _ out _ =>
      ∀ label, jumpFreeInstruction instruction = true → out.flow ≠ .jumped label)
    (motive_2 := fun _ remaining _ _ out _ =>
      ∀ label, jumpFreeCode remaining = true → out.flow ≠ .jumped label)
  jump_free_execution_cases

theorem target_append_normal {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    (root fragment suffix : List Instruction) (checked : jumpFreeCode fragment = true)
    {before middle : TargetFrame} {pre post : TargetState World} {out : TargetBlockOutcome World}
    (prefixRan : TargetRun interface heap calls result root fragment before pre ⟨.normal, middle, post⟩)
    (suffixRan : TargetRun interface heap calls result root suffix middle post out) :
    TargetRun interface heap calls result root (fragment ++ suffix) before pre out := by
  induction fragment generalizing before middle pre post with
  | nil => cases prefixRan; exact suffixRan
  | cons first rest ih =>
      simp only [jumpFreeCode] at checked
      have checks := Bool.and_eq_true_iff.mp checked
      cases prefixRan with
      | next head tail => exact .next head (ih checks.2 tail suffixRan)
      | resume head _ _ =>
          exact False.elim (jump_free_instruction_cannot_jump head _ checks.1 rfl)

theorem target_append_returned {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    (root fragment suffix : List Instruction) (checked : jumpFreeCode fragment = true)
    {before after : TargetFrame} {pre post : TargetState World} {value : TargetValue}
    (prefixRan : TargetRun interface heap calls result root fragment before pre ⟨.returned value, after, post⟩) :
    TargetRun interface heap calls result root (fragment ++ suffix) before pre ⟨.returned value, after, post⟩ := by
  induction fragment generalizing before after pre post with
  | nil => cases prefixRan
  | cons first rest ih =>
      simp only [jumpFreeCode] at checked
      have checks := Bool.and_eq_true_iff.mp checked
      cases prefixRan with
      | next head tail => exact .next head (ih checks.2 tail)
      | «return» head => exact .return head
      | resume head _ _ =>
          exact False.elim (jump_free_instruction_cannot_jump head _ checks.1 rfl)

theorem target_split_jump_free_prefix {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    (root fragment suffix : List Instruction) (checked : jumpFreeCode fragment = true)
    {before : TargetFrame} {pre : TargetState World} {out : TargetBlockOutcome World}
    (ran : TargetRun interface heap calls result root (fragment ++ suffix) before pre out) :
    (∃ middle post,
      TargetRun interface heap calls result root fragment before pre ⟨.normal, middle, post⟩ ∧
      TargetRun interface heap calls result root suffix middle post out) ∨
    (∃ value after post,
      TargetRun interface heap calls result root fragment before pre ⟨.returned value, after, post⟩ ∧
      out = ⟨.returned value, after, post⟩) := by
  induction fragment generalizing before pre with
  | nil => exact .inl ⟨before, pre, .nil root before pre, ran⟩
  | cons first rest ih =>
      simp only [jumpFreeCode] at checked
      have checks := Bool.and_eq_true_iff.mp checked
      cases ran with
      | next head tail =>
          rcases ih checks.2 tail with
            ⟨middle, post, prefixRan, suffixRan⟩ | ⟨value, after, post, prefixRan, equal⟩
          · exact .inl ⟨middle, post, .next head prefixRan, suffixRan⟩
          · exact .inr ⟨value, after, post, .next head prefixRan, equal⟩
      | «return» head => exact .inr ⟨_, _, _, .return head, rfl⟩
      | resume head _ _ =>
          exact False.elim (jump_free_instruction_cannot_jump head _ checks.1 rfl)
      | escape head _ =>
          exact False.elim (jump_free_instruction_cannot_jump head _ checks.1 rfl)

theorem target_run_append_exact {World : Type} (interface : Interface)
    (heap : TargetHeapSemantics World) (calls : TargetCalls World) (result : NativeType)
    (root fragment suffix : List Instruction) (checked : jumpFreeCode fragment = true)
    (before : TargetFrame) (pre : TargetState World) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root (fragment ++ suffix) before pre out ↔
      ((∃ middle post,
        TargetRun interface heap calls result root fragment before pre ⟨.normal, middle, post⟩ ∧
        TargetRun interface heap calls result root suffix middle post out) ∨
      (∃ value after post,
        TargetRun interface heap calls result root fragment before pre ⟨.returned value, after, post⟩ ∧
        out = ⟨.returned value, after, post⟩)) := by
  constructor
  · exact target_split_jump_free_prefix root fragment suffix checked
  · rintro (⟨middle, post, prefixRan, suffixRan⟩ | ⟨value, after, post, prefixRan, equal⟩)
    · exact target_append_normal root fragment suffix checked prefixRan suffixRan
    · rw [equal]
      exact target_append_returned root fragment suffix checked prefixRan

/-- A proved, normally returning prefix passes its complete post-frame and
state to the suffix. The prefix can contain several loads or calls; its
absence of outward jumps remains explicit. -/
theorem target_normal_prefix_then_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {root fragment : List Instruction} {before after : TargetFrame}
    {pre post : TargetState World}
    (checked : jumpFreeCode fragment = true)
    (prefixExact : ∀ out, TargetRun interface heap calls result root fragment before pre out ↔
      out = ⟨.normal, after, post⟩)
    (suffix : List Instruction) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root (fragment ++ suffix) before pre out ↔
      TargetRun interface heap calls result root suffix after post out := by
  rw [target_run_append_exact interface heap calls result root fragment suffix checked before pre out]
  constructor
  · rintro (⟨middle, final, first, rest⟩ | ⟨value, final, state, first, same⟩)
    · cases (prefixExact _).mp first
      exact rest
    · have impossible := (prefixExact _).mp first
      cases impossible
  · intro rest
    exact .inl ⟨after, post, (prefixExact _).mpr rfl, rest⟩

/-- An instruction's complete outcome determines the remaining execution.
Label lookup uses the enclosing root; an unresolved jump and a return skip
the suffix. The statement includes both execution and reflection. -/
theorem target_run_cons_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    (root : List Instruction) (first : Instruction) (rest : List Instruction)
    (frame : TargetFrame) (state : TargetState World) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root (first :: rest) frame state out ↔
      ∃ firstOut, TargetInstructionEval interface heap calls result first frame state firstOut ∧
        match firstOut.flow with
        | .normal => TargetRun interface heap calls result root rest firstOut.frame firstOut.state out
        | .returned _ => out = firstOut
        | .jumped label =>
            match targetAfterLabel? root label with
            | some suffix =>
                TargetRun interface heap calls result root suffix firstOut.frame firstOut.state out
            | none => out = firstOut := by
  constructor
  · intro ran
    cases ran with
    | next head tail => exact ⟨_, head, tail⟩
    | «return» head => exact ⟨_, head, rfl⟩
    | resume head found tail => exact ⟨_, head, by simpa only [found] using tail⟩
    | escape head outside => exact ⟨_, head, by simp only [outside]⟩
  · rintro ⟨⟨flow, after, post⟩, head, following⟩
    cases flow with
    | normal => exact .next head following
    | returned value => cases following; exact .return head
    | jumped label =>
        cases found : targetAfterLabel? root label with
        | none => simp only [found] at following; cases following; exact .escape head found
        | some suffix =>
            simp only [found] at following
            exact .resume head found following

theorem target_label_cons_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    (root : List Instruction) (label : NativeIR.Label) (rest : List Instruction)
    (frame : TargetFrame) (state : TargetState World) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root (.label label :: rest) frame state out ↔
      TargetRun interface heap calls result root rest frame state out := by
  rw [target_run_cons_exact]
  constructor
  · rintro ⟨firstOut, head, following⟩
    cases head with
    | label => exact following
  · intro following
    exact ⟨_, .label label frame state, following⟩

/-- Scope cleanup occurs before the outer root resolves a jump. The inner
derivation remains an execution of the actual scoped body. -/
theorem target_scope_cons_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    (root body rest : List Instruction) (frame : TargetFrame) (state : TargetState World)
    (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result root (.scope body :: rest) frame state out ↔
      ∃ inner, TargetRun interface heap calls result body body frame state inner ∧
        match inner.flow with
        | .normal => TargetRun interface heap calls result root rest
            (targetCloseBlock frame inner).frame (targetCloseBlock frame inner).state out
        | .returned _ => out = targetCloseBlock frame inner
        | .jumped label =>
            match targetAfterLabel? root label with
            | some suffix => TargetRun interface heap calls result root suffix
                (targetCloseBlock frame inner).frame (targetCloseBlock frame inner).state out
            | none => out = targetCloseBlock frame inner := by
  rw [target_run_cons_exact]
  constructor
  · rintro ⟨firstOut, head, following⟩
    cases head with
    | scope ran => exact ⟨_, ran, following⟩
  · rintro ⟨inner, ran, following⟩
    exact ⟨_, .scope ran, following⟩

end Mettapedia.GSLT.LanguageDef.NativeOps
