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

end Mettapedia.GSLT.LanguageDef.NativeOps
